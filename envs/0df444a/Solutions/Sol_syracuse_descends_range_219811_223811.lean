-- Prove2me | solution 1 for syracuse_descends_range_219811_223811
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:56.711902+00:00
-- url     : https://prove2.me/submissions/192cd865-adfe-46b6-b530-643d31e0e34b

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


theorem B557077 : Blo 219811 557077 := bbase (se 6 (by rfl) ⟨13056, by rfl⟩ : syracuseStep 557077 = 26113) (by norm_num)
theorem B557189 : Blo 219811 557189 := bbase (se 4 (by rfl) ⟨52236, by rfl⟩ : syracuseStep 557189 = 104473) (by norm_num)
theorem B852133 : Blo 219811 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B753893 : Blo 219811 753893 := bbase (se 4 (by rfl) ⟨70677, by rfl⟩ : syracuseStep 753893 = 141355) (by norm_num)
theorem B557381 : Blo 219811 557381 := bbase (se 4 (by rfl) ⟨52254, by rfl⟩ : syracuseStep 557381 = 104509) (by norm_num)
theorem B2523797 : Blo 219811 2523797 := bbase (se 6 (by rfl) ⟨59151, by rfl⟩ : syracuseStep 2523797 = 118303) (by norm_num)
theorem B754325 : Blo 219811 754325 := bbase (se 6 (by rfl) ⟨17679, by rfl⟩ : syracuseStep 754325 = 35359) (by norm_num)
theorem B557725 : Blo 219811 557725 := bbase (se 3 (by rfl) ⟨104573, by rfl⟩ : syracuseStep 557725 = 209147) (by norm_num)
theorem B557837 : Blo 219811 557837 := bbase (se 3 (by rfl) ⟨104594, by rfl⟩ : syracuseStep 557837 = 209189) (by norm_num)
theorem B1606549 : Blo 219811 1606549 := bbase (se 6 (by rfl) ⟨37653, by rfl⟩ : syracuseStep 1606549 = 75307) (by norm_num)
theorem B1115045 : Blo 219811 1115045 := bbase (se 4 (by rfl) ⟨104535, by rfl⟩ : syracuseStep 1115045 = 209071) (by norm_num)
theorem B1344437 : Blo 219811 1344437 := bbase (se 5 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 1344437 = 126041) (by norm_num)
theorem B558029 : Blo 219811 558029 := bbase (se 3 (by rfl) ⟨104630, by rfl⟩ : syracuseStep 558029 = 209261) (by norm_num)
theorem B426989 : Blo 219811 426989 := bbase (se 3 (by rfl) ⟨80060, by rfl⟩ : syracuseStep 426989 = 160121) (by norm_num)
theorem B754757 : Blo 219811 754757 := bbase (se 4 (by rfl) ⟨70758, by rfl⟩ : syracuseStep 754757 = 141517) (by norm_num)
theorem B2819285 : Blo 219811 2819285 := bbase (se 7 (by rfl) ⟨33038, by rfl⟩ : syracuseStep 2819285 = 66077) (by norm_num)
theorem B853237 : Blo 219811 853237 := bbase (se 5 (by rfl) ⟨39995, by rfl⟩ : syracuseStep 853237 = 79991) (by norm_num)
theorem B558373 : Blo 219811 558373 := bbase (se 4 (by rfl) ⟨52347, by rfl⟩ : syracuseStep 558373 = 104695) (by norm_num)
theorem B558485 : Blo 219811 558485 := bbase (se 6 (by rfl) ⟨13089, by rfl⟩ : syracuseStep 558485 = 26179) (by norm_num)
theorem B755189 : Blo 219811 755189 := bbase (se 5 (by rfl) ⟨35399, by rfl⟩ : syracuseStep 755189 = 70799) (by norm_num)
theorem B558677 : Blo 219811 558677 := bbase (se 8 (by rfl) ⟨3273, by rfl⟩ : syracuseStep 558677 = 6547) (by norm_num)
theorem B1509205 : Blo 219811 1509205 := bbase (se 9 (by rfl) ⟨4421, by rfl⟩ : syracuseStep 1509205 = 8843) (by norm_num)
theorem B952165 : Blo 219811 952165 := bbase (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) (by norm_num)
theorem B559021 : Blo 219811 559021 := bbase (se 3 (by rfl) ⟨104816, by rfl⟩ : syracuseStep 559021 = 209633) (by norm_num)
theorem B329717 : Blo 219811 329717 := bbase (se 5 (by rfl) ⟨15455, by rfl⟩ : syracuseStep 329717 = 30911) (by norm_num)
theorem B329741 : Blo 219811 329741 := bbase (se 3 (by rfl) ⟨61826, by rfl⟩ : syracuseStep 329741 = 123653) (by norm_num)
theorem B559133 : Blo 219811 559133 := bbase (se 3 (by rfl) ⟨104837, by rfl⟩ : syracuseStep 559133 = 209675) (by norm_num)
theorem B329765 : Blo 219811 329765 := bbase (se 4 (by rfl) ⟨30915, by rfl⟩ : syracuseStep 329765 = 61831) (by norm_num)
theorem B329789 : Blo 219811 329789 := bbase (se 3 (by rfl) ⟨61835, by rfl⟩ : syracuseStep 329789 = 123671) (by norm_num)
theorem B329813 : Blo 219811 329813 := bbase (se 8 (by rfl) ⟨1932, by rfl⟩ : syracuseStep 329813 = 3865) (by norm_num)
theorem B329837 : Blo 219811 329837 := bbase (se 3 (by rfl) ⟨61844, by rfl⟩ : syracuseStep 329837 = 123689) (by norm_num)
theorem B329861 : Blo 219811 329861 := bbase (se 4 (by rfl) ⟨30924, by rfl⟩ : syracuseStep 329861 = 61849) (by norm_num)
theorem B329885 : Blo 219811 329885 := bbase (se 3 (by rfl) ⟨61853, by rfl⟩ : syracuseStep 329885 = 123707) (by norm_num)
theorem B329909 : Blo 219811 329909 := bbase (se 5 (by rfl) ⟨15464, by rfl⟩ : syracuseStep 329909 = 30929) (by norm_num)
theorem B1116341 : Blo 219811 1116341 := bbase (se 5 (by rfl) ⟨52328, by rfl⟩ : syracuseStep 1116341 = 104657) (by norm_num)
theorem B329933 : Blo 219811 329933 := bbase (se 3 (by rfl) ⟨61862, by rfl⟩ : syracuseStep 329933 = 123725) (by norm_num)
theorem B559325 : Blo 219811 559325 := bbase (se 3 (by rfl) ⟨104873, by rfl⟩ : syracuseStep 559325 = 209747) (by norm_num)
theorem B329957 : Blo 219811 329957 := bbase (se 4 (by rfl) ⟨30933, by rfl⟩ : syracuseStep 329957 = 61867) (by norm_num)
theorem B329981 : Blo 219811 329981 := bbase (se 3 (by rfl) ⟨61871, by rfl⟩ : syracuseStep 329981 = 123743) (by norm_num)
theorem B330005 : Blo 219811 330005 := bbase (se 6 (by rfl) ⟨7734, by rfl⟩ : syracuseStep 330005 = 15469) (by norm_num)
theorem B330029 : Blo 219811 330029 := bbase (se 3 (by rfl) ⟨61880, by rfl⟩ : syracuseStep 330029 = 123761) (by norm_num)
theorem B330053 : Blo 219811 330053 := bbase (se 4 (by rfl) ⟨30942, by rfl⟩ : syracuseStep 330053 = 61885) (by norm_num)
theorem B264529 : Blo 219811 264529 := bbase (se 2 (by rfl) ⟨99198, by rfl⟩ : syracuseStep 264529 = 198397) (by norm_num)
theorem B330077 : Blo 219811 330077 := bbase (se 3 (by rfl) ⟨61889, by rfl⟩ : syracuseStep 330077 = 123779) (by norm_num)
theorem B330101 : Blo 219811 330101 := bbase (se 5 (by rfl) ⟨15473, by rfl⟩ : syracuseStep 330101 = 30947) (by norm_num)
theorem B330125 : Blo 219811 330125 := bbase (se 3 (by rfl) ⟨61898, by rfl⟩ : syracuseStep 330125 = 123797) (by norm_num)
theorem B330149 : Blo 219811 330149 := bbase (se 4 (by rfl) ⟨30951, by rfl⟩ : syracuseStep 330149 = 61903) (by norm_num)
theorem B330173 : Blo 219811 330173 := bbase (se 3 (by rfl) ⟨61907, by rfl⟩ : syracuseStep 330173 = 123815) (by norm_num)
theorem B330197 : Blo 219811 330197 := bbase (se 7 (by rfl) ⟨3869, by rfl⟩ : syracuseStep 330197 = 7739) (by norm_num)
theorem B330221 : Blo 219811 330221 := bbase (se 3 (by rfl) ⟨61916, by rfl⟩ : syracuseStep 330221 = 123833) (by norm_num)
theorem B330245 : Blo 219811 330245 := bbase (se 4 (by rfl) ⟨30960, by rfl⟩ : syracuseStep 330245 = 61921) (by norm_num)
theorem B330269 : Blo 219811 330269 := bbase (se 3 (by rfl) ⟨61925, by rfl⟩ : syracuseStep 330269 = 123851) (by norm_num)
theorem B330293 : Blo 219811 330293 := bbase (se 5 (by rfl) ⟨15482, by rfl⟩ : syracuseStep 330293 = 30965) (by norm_num)
theorem B559669 : Blo 219811 559669 := bbase (se 5 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 559669 = 52469) (by norm_num)
theorem B330317 : Blo 219811 330317 := bbase (se 3 (by rfl) ⟨61934, by rfl⟩ : syracuseStep 330317 = 123869) (by norm_num)
theorem B330341 : Blo 219811 330341 := bbase (se 4 (by rfl) ⟨30969, by rfl⟩ : syracuseStep 330341 = 61939) (by norm_num)
theorem B330365 : Blo 219811 330365 := bbase (se 3 (by rfl) ⟨61943, by rfl⟩ : syracuseStep 330365 = 123887) (by norm_num)
theorem B330389 : Blo 219811 330389 := bbase (se 6 (by rfl) ⟨7743, by rfl⟩ : syracuseStep 330389 = 15487) (by norm_num)
theorem B559781 : Blo 219811 559781 := bbase (se 4 (by rfl) ⟨52479, by rfl⟩ : syracuseStep 559781 = 104959) (by norm_num)
theorem B330413 : Blo 219811 330413 := bbase (se 3 (by rfl) ⟨61952, by rfl⟩ : syracuseStep 330413 = 123905) (by norm_num)
theorem B330437 : Blo 219811 330437 := bbase (se 4 (by rfl) ⟨30978, by rfl⟩ : syracuseStep 330437 = 61957) (by norm_num)
theorem B330461 : Blo 219811 330461 := bbase (se 3 (by rfl) ⟨61961, by rfl⟩ : syracuseStep 330461 = 123923) (by norm_num)
theorem B330485 : Blo 219811 330485 := bbase (se 5 (by rfl) ⟨15491, by rfl⟩ : syracuseStep 330485 = 30983) (by norm_num)
theorem B330509 : Blo 219811 330509 := bbase (se 3 (by rfl) ⟨61970, by rfl⟩ : syracuseStep 330509 = 123941) (by norm_num)
theorem B330533 : Blo 219811 330533 := bbase (se 4 (by rfl) ⟨30987, by rfl⟩ : syracuseStep 330533 = 61975) (by norm_num)
theorem B330557 : Blo 219811 330557 := bbase (se 3 (by rfl) ⟨61979, by rfl⟩ : syracuseStep 330557 = 123959) (by norm_num)
theorem B330581 : Blo 219811 330581 := bbase (se 9 (by rfl) ⟨968, by rfl⟩ : syracuseStep 330581 = 1937) (by norm_num)
theorem B559973 : Blo 219811 559973 := bbase (se 4 (by rfl) ⟨52497, by rfl⟩ : syracuseStep 559973 = 104995) (by norm_num)
theorem B330605 : Blo 219811 330605 := bbase (se 3 (by rfl) ⟨61988, by rfl⟩ : syracuseStep 330605 = 123977) (by norm_num)
theorem B330629 : Blo 219811 330629 := bbase (se 4 (by rfl) ⟨30996, by rfl⟩ : syracuseStep 330629 = 61993) (by norm_num)
theorem B330653 : Blo 219811 330653 := bbase (se 3 (by rfl) ⟨61997, by rfl⟩ : syracuseStep 330653 = 123995) (by norm_num)
theorem B330677 : Blo 219811 330677 := bbase (se 5 (by rfl) ⟨15500, by rfl⟩ : syracuseStep 330677 = 31001) (by norm_num)
theorem B330701 : Blo 219811 330701 := bbase (se 3 (by rfl) ⟨62006, by rfl⟩ : syracuseStep 330701 = 124013) (by norm_num)
theorem B330725 : Blo 219811 330725 := bbase (se 4 (by rfl) ⟨31005, by rfl⟩ : syracuseStep 330725 = 62011) (by norm_num)
theorem B396269 : Blo 219811 396269 := bbase (se 3 (by rfl) ⟨74300, by rfl⟩ : syracuseStep 396269 = 148601) (by norm_num)
theorem B330749 : Blo 219811 330749 := bbase (se 3 (by rfl) ⟨62015, by rfl⟩ : syracuseStep 330749 = 124031) (by norm_num)
theorem B330773 : Blo 219811 330773 := bbase (se 6 (by rfl) ⟨7752, by rfl⟩ : syracuseStep 330773 = 15505) (by norm_num)
theorem B494621 : Blo 219811 494621 := bbase (se 3 (by rfl) ⟨92741, by rfl⟩ : syracuseStep 494621 = 185483) (by norm_num)
theorem B330797 : Blo 219811 330797 := bbase (se 3 (by rfl) ⟨62024, by rfl⟩ : syracuseStep 330797 = 124049) (by norm_num)
theorem B330821 : Blo 219811 330821 := bbase (se 4 (by rfl) ⟨31014, by rfl⟩ : syracuseStep 330821 = 62029) (by norm_num)
theorem B330845 : Blo 219811 330845 := bbase (se 3 (by rfl) ⟨62033, by rfl⟩ : syracuseStep 330845 = 124067) (by norm_num)
theorem B494693 : Blo 219811 494693 := bbase (se 4 (by rfl) ⟨46377, by rfl⟩ : syracuseStep 494693 = 92755) (by norm_num)
theorem B330869 : Blo 219811 330869 := bbase (se 5 (by rfl) ⟨15509, by rfl⟩ : syracuseStep 330869 = 31019) (by norm_num)
theorem B330893 : Blo 219811 330893 := bbase (se 3 (by rfl) ⟨62042, by rfl⟩ : syracuseStep 330893 = 124085) (by norm_num)
theorem B330917 : Blo 219811 330917 := bbase (se 4 (by rfl) ⟨31023, by rfl⟩ : syracuseStep 330917 = 62047) (by norm_num)
theorem B494765 : Blo 219811 494765 := bbase (se 3 (by rfl) ⟨92768, by rfl⟩ : syracuseStep 494765 = 185537) (by norm_num)
theorem B330941 : Blo 219811 330941 := bbase (se 3 (by rfl) ⟨62051, by rfl⟩ : syracuseStep 330941 = 124103) (by norm_num)
theorem B560317 : Blo 219811 560317 := bbase (se 3 (by rfl) ⟨105059, by rfl⟩ : syracuseStep 560317 = 210119) (by norm_num)
theorem B330965 : Blo 219811 330965 := bbase (se 7 (by rfl) ⟨3878, by rfl⟩ : syracuseStep 330965 = 7757) (by norm_num)
theorem B330989 : Blo 219811 330989 := bbase (se 3 (by rfl) ⟨62060, by rfl⟩ : syracuseStep 330989 = 124121) (by norm_num)
theorem B494837 : Blo 219811 494837 := bbase (se 5 (by rfl) ⟨23195, by rfl⟩ : syracuseStep 494837 = 46391) (by norm_num)
theorem B331013 : Blo 219811 331013 := bbase (se 4 (by rfl) ⟨31032, by rfl⟩ : syracuseStep 331013 = 62065) (by norm_num)
theorem B855317 : Blo 219811 855317 := bbase (se 6 (by rfl) ⟨20046, by rfl⟩ : syracuseStep 855317 = 40093) (by norm_num)
theorem B331037 : Blo 219811 331037 := bbase (se 3 (by rfl) ⟨62069, by rfl⟩ : syracuseStep 331037 = 124139) (by norm_num)
theorem B560429 : Blo 219811 560429 := bbase (se 3 (by rfl) ⟨105080, by rfl⟩ : syracuseStep 560429 = 210161) (by norm_num)
theorem B331061 : Blo 219811 331061 := bbase (se 5 (by rfl) ⟨15518, by rfl⟩ : syracuseStep 331061 = 31037) (by norm_num)
theorem B953653 : Blo 219811 953653 := bbase (se 5 (by rfl) ⟨44702, by rfl⟩ : syracuseStep 953653 = 89405) (by norm_num)
theorem B494909 : Blo 219811 494909 := bbase (se 3 (by rfl) ⟨92795, by rfl⟩ : syracuseStep 494909 = 185591) (by norm_num)
theorem B953669 : Blo 219811 953669 := bbase (se 4 (by rfl) ⟨89406, by rfl⟩ : syracuseStep 953669 = 178813) (by norm_num)
theorem B331085 : Blo 219811 331085 := bbase (se 3 (by rfl) ⟨62078, by rfl⟩ : syracuseStep 331085 = 124157) (by norm_num)
theorem B1412437 : Blo 219811 1412437 := bbase (se 11 (by rfl) ⟨1034, by rfl⟩ : syracuseStep 1412437 = 2069) (by norm_num)
theorem B331109 : Blo 219811 331109 := bbase (se 4 (by rfl) ⟨31041, by rfl⟩ : syracuseStep 331109 = 62083) (by norm_num)
theorem B331133 : Blo 219811 331133 := bbase (se 3 (by rfl) ⟨62087, by rfl⟩ : syracuseStep 331133 = 124175) (by norm_num)
theorem B494981 : Blo 219811 494981 := bbase (se 4 (by rfl) ⟨46404, by rfl⟩ : syracuseStep 494981 = 92809) (by norm_num)
theorem B331157 : Blo 219811 331157 := bbase (se 6 (by rfl) ⟨7761, by rfl⟩ : syracuseStep 331157 = 15523) (by norm_num)
theorem B331181 : Blo 219811 331181 := bbase (se 3 (by rfl) ⟨62096, by rfl⟩ : syracuseStep 331181 = 124193) (by norm_num)
theorem B1117637 : Blo 219811 1117637 := bbase (se 4 (by rfl) ⟨104778, by rfl⟩ : syracuseStep 1117637 = 209557) (by norm_num)
theorem B331205 : Blo 219811 331205 := bbase (se 4 (by rfl) ⟨31050, by rfl⟩ : syracuseStep 331205 = 62101) (by norm_num)
theorem B495053 : Blo 219811 495053 := bbase (se 3 (by rfl) ⟨92822, by rfl⟩ : syracuseStep 495053 = 185645) (by norm_num)
theorem B331229 : Blo 219811 331229 := bbase (se 3 (by rfl) ⟨62105, by rfl⟩ : syracuseStep 331229 = 124211) (by norm_num)
theorem B560621 : Blo 219811 560621 := bbase (se 3 (by rfl) ⟨105116, by rfl⟩ : syracuseStep 560621 = 210233) (by norm_num)
theorem B331253 : Blo 219811 331253 := bbase (se 5 (by rfl) ⟨15527, by rfl⟩ : syracuseStep 331253 = 31055) (by norm_num)
theorem B265717 : Blo 219811 265717 := bbase (se 5 (by rfl) ⟨12455, by rfl⟩ : syracuseStep 265717 = 24911) (by norm_num)
theorem B331277 : Blo 219811 331277 := bbase (se 3 (by rfl) ⟨62114, by rfl⟩ : syracuseStep 331277 = 124229) (by norm_num)
theorem B495125 : Blo 219811 495125 := bbase (se 6 (by rfl) ⟨11604, by rfl⟩ : syracuseStep 495125 = 23209) (by norm_num)
theorem B1510933 : Blo 219811 1510933 := bbase (se 6 (by rfl) ⟨35412, by rfl⟩ : syracuseStep 1510933 = 70825) (by norm_num)
theorem B331301 : Blo 219811 331301 := bbase (se 4 (by rfl) ⟨31059, by rfl⟩ : syracuseStep 331301 = 62119) (by norm_num)
theorem B331325 : Blo 219811 331325 := bbase (se 3 (by rfl) ⟨62123, by rfl⟩ : syracuseStep 331325 = 124247) (by norm_num)
theorem B331349 : Blo 219811 331349 := bbase (se 8 (by rfl) ⟨1941, by rfl⟩ : syracuseStep 331349 = 3883) (by norm_num)
theorem B495197 : Blo 219811 495197 := bbase (se 3 (by rfl) ⟨92849, by rfl⟩ : syracuseStep 495197 = 185699) (by norm_num)
theorem B331373 : Blo 219811 331373 := bbase (se 3 (by rfl) ⟨62132, by rfl⟩ : syracuseStep 331373 = 124265) (by norm_num)
theorem B331397 : Blo 219811 331397 := bbase (se 4 (by rfl) ⟨31068, by rfl⟩ : syracuseStep 331397 = 62137) (by norm_num)
theorem B331421 : Blo 219811 331421 := bbase (se 3 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 331421 = 124283) (by norm_num)
theorem B495269 : Blo 219811 495269 := bbase (se 4 (by rfl) ⟨46431, by rfl⟩ : syracuseStep 495269 = 92863) (by norm_num)
theorem B331445 : Blo 219811 331445 := bbase (se 5 (by rfl) ⟨15536, by rfl⟩ : syracuseStep 331445 = 31073) (by norm_num)
theorem B265909 : Blo 219811 265909 := bbase (se 5 (by rfl) ⟨12464, by rfl⟩ : syracuseStep 265909 = 24929) (by norm_num)
theorem B331469 : Blo 219811 331469 := bbase (se 3 (by rfl) ⟨62150, by rfl⟩ : syracuseStep 331469 = 124301) (by norm_num)
theorem B331493 : Blo 219811 331493 := bbase (se 4 (by rfl) ⟨31077, by rfl⟩ : syracuseStep 331493 = 62155) (by norm_num)
theorem B495341 : Blo 219811 495341 := bbase (se 3 (by rfl) ⟨92876, by rfl⟩ : syracuseStep 495341 = 185753) (by norm_num)
theorem B331517 : Blo 219811 331517 := bbase (se 3 (by rfl) ⟨62159, by rfl⟩ : syracuseStep 331517 = 124319) (by norm_num)
theorem B331541 : Blo 219811 331541 := bbase (se 6 (by rfl) ⟨7770, by rfl⟩ : syracuseStep 331541 = 15541) (by norm_num)
theorem B266009 : Blo 219811 266009 := bbase (se 2 (by rfl) ⟨99753, by rfl⟩ : syracuseStep 266009 = 199507) (by norm_num)
theorem B331565 : Blo 219811 331565 := bbase (se 3 (by rfl) ⟨62168, by rfl⟩ : syracuseStep 331565 = 124337) (by norm_num)
theorem B495413 : Blo 219811 495413 := bbase (se 5 (by rfl) ⟨23222, by rfl⟩ : syracuseStep 495413 = 46445) (by norm_num)
theorem B331589 : Blo 219811 331589 := bbase (se 4 (by rfl) ⟨31086, by rfl⟩ : syracuseStep 331589 = 62173) (by norm_num)
theorem B560965 : Blo 219811 560965 := bbase (se 4 (by rfl) ⟨52590, by rfl⟩ : syracuseStep 560965 = 105181) (by norm_num)
theorem B331613 : Blo 219811 331613 := bbase (se 3 (by rfl) ⟨62177, by rfl⟩ : syracuseStep 331613 = 124355) (by norm_num)
theorem B331637 : Blo 219811 331637 := bbase (se 5 (by rfl) ⟨15545, by rfl⟩ : syracuseStep 331637 = 31091) (by norm_num)
theorem B495485 : Blo 219811 495485 := bbase (se 3 (by rfl) ⟨92903, by rfl⟩ : syracuseStep 495485 = 185807) (by norm_num)
theorem B331661 : Blo 219811 331661 := bbase (se 3 (by rfl) ⟨62186, by rfl⟩ : syracuseStep 331661 = 124373) (by norm_num)
theorem B331685 : Blo 219811 331685 := bbase (se 4 (by rfl) ⟨31095, by rfl⟩ : syracuseStep 331685 = 62191) (by norm_num)
theorem B561077 : Blo 219811 561077 := bbase (se 5 (by rfl) ⟨26300, by rfl⟩ : syracuseStep 561077 = 52601) (by norm_num)
theorem B331709 : Blo 219811 331709 := bbase (se 3 (by rfl) ⟨62195, by rfl⟩ : syracuseStep 331709 = 124391) (by norm_num)
theorem B495557 : Blo 219811 495557 := bbase (se 4 (by rfl) ⟨46458, by rfl⟩ : syracuseStep 495557 = 92917) (by norm_num)
theorem B331733 : Blo 219811 331733 := bbase (se 7 (by rfl) ⟨3887, by rfl⟩ : syracuseStep 331733 = 7775) (by norm_num)
theorem B430037 : Blo 219811 430037 := bbase (se 7 (by rfl) ⟨5039, by rfl⟩ : syracuseStep 430037 = 10079) (by norm_num)
theorem B331757 : Blo 219811 331757 := bbase (se 3 (by rfl) ⟨62204, by rfl⟩ : syracuseStep 331757 = 124409) (by norm_num)
theorem B331781 : Blo 219811 331781 := bbase (se 4 (by rfl) ⟨31104, by rfl⟩ : syracuseStep 331781 = 62209) (by norm_num)
theorem B495629 : Blo 219811 495629 := bbase (se 3 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 495629 = 185861) (by norm_num)
theorem B331805 : Blo 219811 331805 := bbase (se 3 (by rfl) ⟨62213, by rfl⟩ : syracuseStep 331805 = 124427) (by norm_num)
theorem B331829 : Blo 219811 331829 := bbase (se 5 (by rfl) ⟨15554, by rfl⟩ : syracuseStep 331829 = 31109) (by norm_num)
theorem B856133 : Blo 219811 856133 := bbase (se 4 (by rfl) ⟨80262, by rfl⟩ : syracuseStep 856133 = 160525) (by norm_num)
theorem B331853 : Blo 219811 331853 := bbase (se 3 (by rfl) ⟨62222, by rfl⟩ : syracuseStep 331853 = 124445) (by norm_num)
theorem B495701 : Blo 219811 495701 := bbase (se 8 (by rfl) ⟨2904, by rfl⟩ : syracuseStep 495701 = 5809) (by norm_num)
theorem B331877 : Blo 219811 331877 := bbase (se 4 (by rfl) ⟨31113, by rfl⟩ : syracuseStep 331877 = 62227) (by norm_num)
theorem B561269 : Blo 219811 561269 := bbase (se 5 (by rfl) ⟨26309, by rfl⟩ : syracuseStep 561269 = 52619) (by norm_num)
theorem B331901 : Blo 219811 331901 := bbase (se 3 (by rfl) ⟨62231, by rfl⟩ : syracuseStep 331901 = 124463) (by norm_num)
theorem B331925 : Blo 219811 331925 := bbase (se 6 (by rfl) ⟨7779, by rfl⟩ : syracuseStep 331925 = 15559) (by norm_num)
theorem B495773 : Blo 219811 495773 := bbase (se 3 (by rfl) ⟨92957, by rfl⟩ : syracuseStep 495773 = 185915) (by norm_num)
theorem B331949 : Blo 219811 331949 := bbase (se 3 (by rfl) ⟨62240, by rfl⟩ : syracuseStep 331949 = 124481) (by norm_num)
theorem B331973 : Blo 219811 331973 := bbase (se 4 (by rfl) ⟨31122, by rfl⟩ : syracuseStep 331973 = 62245) (by norm_num)
theorem B331997 : Blo 219811 331997 := bbase (se 3 (by rfl) ⟨62249, by rfl⟩ : syracuseStep 331997 = 124499) (by norm_num)
theorem B495845 : Blo 219811 495845 := bbase (se 4 (by rfl) ⟨46485, by rfl⟩ : syracuseStep 495845 = 92971) (by norm_num)
theorem B332021 : Blo 219811 332021 := bbase (se 5 (by rfl) ⟨15563, by rfl⟩ : syracuseStep 332021 = 31127) (by norm_num)
theorem B332045 : Blo 219811 332045 := bbase (se 3 (by rfl) ⟨62258, by rfl⟩ : syracuseStep 332045 = 124517) (by norm_num)
theorem B332069 : Blo 219811 332069 := bbase (se 4 (by rfl) ⟨31131, by rfl⟩ : syracuseStep 332069 = 62263) (by norm_num)
theorem B495917 : Blo 219811 495917 := bbase (se 3 (by rfl) ⟨92984, by rfl⟩ : syracuseStep 495917 = 185969) (by norm_num)
theorem B332093 : Blo 219811 332093 := bbase (se 3 (by rfl) ⟨62267, by rfl⟩ : syracuseStep 332093 = 124535) (by norm_num)
theorem B332117 : Blo 219811 332117 := bbase (se 10 (by rfl) ⟨486, by rfl⟩ : syracuseStep 332117 = 973) (by norm_num)
theorem B332141 : Blo 219811 332141 := bbase (se 3 (by rfl) ⟨62276, by rfl⟩ : syracuseStep 332141 = 124553) (by norm_num)
theorem B495989 : Blo 219811 495989 := bbase (se 5 (by rfl) ⟨23249, by rfl⟩ : syracuseStep 495989 = 46499) (by norm_num)
theorem B627077 : Blo 219811 627077 := bbase (se 4 (by rfl) ⟨58788, by rfl⟩ : syracuseStep 627077 = 117577) (by norm_num)
theorem B332165 : Blo 219811 332165 := bbase (se 4 (by rfl) ⟨31140, by rfl⟩ : syracuseStep 332165 = 62281) (by norm_num)
theorem B332189 : Blo 219811 332189 := bbase (se 3 (by rfl) ⟨62285, by rfl⟩ : syracuseStep 332189 = 124571) (by norm_num)
theorem B332213 : Blo 219811 332213 := bbase (se 5 (by rfl) ⟨15572, by rfl⟩ : syracuseStep 332213 = 31145) (by norm_num)
theorem B496061 : Blo 219811 496061 := bbase (se 3 (by rfl) ⟨93011, by rfl⟩ : syracuseStep 496061 = 186023) (by norm_num)
theorem B332237 : Blo 219811 332237 := bbase (se 3 (by rfl) ⟨62294, by rfl⟩ : syracuseStep 332237 = 124589) (by norm_num)
theorem B561613 : Blo 219811 561613 := bbase (se 3 (by rfl) ⟨105302, by rfl⟩ : syracuseStep 561613 = 210605) (by norm_num)
theorem B332261 : Blo 219811 332261 := bbase (se 4 (by rfl) ⟨31149, by rfl⟩ : syracuseStep 332261 = 62299) (by norm_num)
theorem B332285 : Blo 219811 332285 := bbase (se 3 (by rfl) ⟨62303, by rfl⟩ : syracuseStep 332285 = 124607) (by norm_num)
theorem B496133 : Blo 219811 496133 := bbase (se 4 (by rfl) ⟨46512, by rfl⟩ : syracuseStep 496133 = 93025) (by norm_num)
theorem B332309 : Blo 219811 332309 := bbase (se 6 (by rfl) ⟨7788, by rfl⟩ : syracuseStep 332309 = 15577) (by norm_num)
theorem B332333 : Blo 219811 332333 := bbase (se 3 (by rfl) ⟨62312, by rfl⟩ : syracuseStep 332333 = 124625) (by norm_num)
theorem B266797 : Blo 219811 266797 := bbase (se 3 (by rfl) ⟨50024, by rfl⟩ : syracuseStep 266797 = 100049) (by norm_num)
theorem B561725 : Blo 219811 561725 := bbase (se 3 (by rfl) ⟨105323, by rfl⟩ : syracuseStep 561725 = 210647) (by norm_num)
theorem B332357 : Blo 219811 332357 := bbase (se 4 (by rfl) ⟨31158, by rfl⟩ : syracuseStep 332357 = 62317) (by norm_num)
theorem B496205 : Blo 219811 496205 := bbase (se 3 (by rfl) ⟨93038, by rfl⟩ : syracuseStep 496205 = 186077) (by norm_num)
theorem B332381 : Blo 219811 332381 := bbase (se 3 (by rfl) ⟨62321, by rfl⟩ : syracuseStep 332381 = 124643) (by norm_num)
theorem B332405 : Blo 219811 332405 := bbase (se 5 (by rfl) ⟨15581, by rfl⟩ : syracuseStep 332405 = 31163) (by norm_num)
theorem B332429 : Blo 219811 332429 := bbase (se 3 (by rfl) ⟨62330, by rfl⟩ : syracuseStep 332429 = 124661) (by norm_num)
theorem B496277 : Blo 219811 496277 := bbase (se 6 (by rfl) ⟨11631, by rfl⟩ : syracuseStep 496277 = 23263) (by norm_num)
theorem B332453 : Blo 219811 332453 := bbase (se 4 (by rfl) ⟨31167, by rfl⟩ : syracuseStep 332453 = 62335) (by norm_num)
theorem B332477 : Blo 219811 332477 := bbase (se 3 (by rfl) ⟨62339, by rfl⟩ : syracuseStep 332477 = 124679) (by norm_num)
theorem B1118933 : Blo 219811 1118933 := bbase (se 7 (by rfl) ⟨13112, by rfl⟩ : syracuseStep 1118933 = 26225) (by norm_num)
theorem B332501 : Blo 219811 332501 := bbase (se 7 (by rfl) ⟨3896, by rfl⟩ : syracuseStep 332501 = 7793) (by norm_num)
theorem B496349 : Blo 219811 496349 := bbase (se 3 (by rfl) ⟨93065, by rfl⟩ : syracuseStep 496349 = 186131) (by norm_num)
theorem B332525 : Blo 219811 332525 := bbase (se 3 (by rfl) ⟨62348, by rfl⟩ : syracuseStep 332525 = 124697) (by norm_num)
theorem B561917 : Blo 219811 561917 := bbase (se 3 (by rfl) ⟨105359, by rfl⟩ : syracuseStep 561917 = 210719) (by norm_num)
theorem B332549 : Blo 219811 332549 := bbase (se 4 (by rfl) ⟨31176, by rfl⟩ : syracuseStep 332549 = 62353) (by norm_num)
theorem B332573 : Blo 219811 332573 := bbase (se 3 (by rfl) ⟨62357, by rfl⟩ : syracuseStep 332573 = 124715) (by norm_num)
theorem B496421 : Blo 219811 496421 := bbase (se 4 (by rfl) ⟨46539, by rfl⟩ : syracuseStep 496421 = 93079) (by norm_num)
theorem B332597 : Blo 219811 332597 := bbase (se 5 (by rfl) ⟨15590, by rfl⟩ : syracuseStep 332597 = 31181) (by norm_num)
theorem B332621 : Blo 219811 332621 := bbase (se 3 (by rfl) ⟨62366, by rfl⟩ : syracuseStep 332621 = 124733) (by norm_num)
theorem B332645 : Blo 219811 332645 := bbase (se 4 (by rfl) ⟨31185, by rfl⟩ : syracuseStep 332645 = 62371) (by norm_num)
theorem B496493 : Blo 219811 496493 := bbase (se 3 (by rfl) ⟨93092, by rfl⟩ : syracuseStep 496493 = 186185) (by norm_num)
theorem B332669 : Blo 219811 332669 := bbase (se 3 (by rfl) ⟨62375, by rfl⟩ : syracuseStep 332669 = 124751) (by norm_num)
theorem B332693 : Blo 219811 332693 := bbase (se 6 (by rfl) ⟨7797, by rfl⟩ : syracuseStep 332693 = 15595) (by norm_num)
theorem B332717 : Blo 219811 332717 := bbase (se 3 (by rfl) ⟨62384, by rfl⟩ : syracuseStep 332717 = 124769) (by norm_num)
theorem B496565 : Blo 219811 496565 := bbase (se 5 (by rfl) ⟨23276, by rfl⟩ : syracuseStep 496565 = 46553) (by norm_num)
theorem B1676213 : Blo 219811 1676213 := bbase (se 5 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 1676213 = 157145) (by norm_num)
theorem B332741 : Blo 219811 332741 := bbase (se 4 (by rfl) ⟨31194, by rfl⟩ : syracuseStep 332741 = 62389) (by norm_num)
theorem B529357 : Blo 219811 529357 := bbase (se 3 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 529357 = 198509) (by norm_num)
theorem B332765 : Blo 219811 332765 := bbase (se 3 (by rfl) ⟨62393, by rfl⟩ : syracuseStep 332765 = 124787) (by norm_num)
theorem B332789 : Blo 219811 332789 := bbase (se 5 (by rfl) ⟨15599, by rfl⟩ : syracuseStep 332789 = 31199) (by norm_num)
theorem B496637 : Blo 219811 496637 := bbase (se 3 (by rfl) ⟨93119, by rfl⟩ : syracuseStep 496637 = 186239) (by norm_num)
theorem B332813 : Blo 219811 332813 := bbase (se 3 (by rfl) ⟨62402, by rfl⟩ : syracuseStep 332813 = 124805) (by norm_num)
theorem B300061 : Blo 219811 300061 := bbase (se 3 (by rfl) ⟨56261, by rfl⟩ : syracuseStep 300061 = 112523) (by norm_num)
theorem B332837 : Blo 219811 332837 := bbase (se 4 (by rfl) ⟨31203, by rfl⟩ : syracuseStep 332837 = 62407) (by norm_num)
theorem B332861 : Blo 219811 332861 := bbase (se 3 (by rfl) ⟨62411, by rfl⟩ : syracuseStep 332861 = 124823) (by norm_num)
theorem B496709 : Blo 219811 496709 := bbase (se 4 (by rfl) ⟨46566, by rfl⟩ : syracuseStep 496709 = 93133) (by norm_num)
theorem B332885 : Blo 219811 332885 := bbase (se 8 (by rfl) ⟨1950, by rfl⟩ : syracuseStep 332885 = 3901) (by norm_num)
theorem B562261 : Blo 219811 562261 := bbase (se 8 (by rfl) ⟨3294, by rfl⟩ : syracuseStep 562261 = 6589) (by norm_num)
theorem B332909 : Blo 219811 332909 := bbase (se 3 (by rfl) ⟨62420, by rfl⟩ : syracuseStep 332909 = 124841) (by norm_num)
theorem B332933 : Blo 219811 332933 := bbase (se 4 (by rfl) ⟨31212, by rfl⟩ : syracuseStep 332933 = 62425) (by norm_num)
theorem B496781 : Blo 219811 496781 := bbase (se 3 (by rfl) ⟨93146, by rfl⟩ : syracuseStep 496781 = 186293) (by norm_num)
theorem B332957 : Blo 219811 332957 := bbase (se 3 (by rfl) ⟨62429, by rfl⟩ : syracuseStep 332957 = 124859) (by norm_num)
theorem B332981 : Blo 219811 332981 := bbase (se 5 (by rfl) ⟨15608, by rfl⟩ : syracuseStep 332981 = 31217) (by norm_num)
theorem B562373 : Blo 219811 562373 := bbase (se 4 (by rfl) ⟨52722, by rfl⟩ : syracuseStep 562373 = 105445) (by norm_num)
theorem B333005 : Blo 219811 333005 := bbase (se 3 (by rfl) ⟨62438, by rfl⟩ : syracuseStep 333005 = 124877) (by norm_num)
theorem B496853 : Blo 219811 496853 := bbase (se 7 (by rfl) ⟨5822, by rfl⟩ : syracuseStep 496853 = 11645) (by norm_num)
theorem B333029 : Blo 219811 333029 := bbase (se 4 (by rfl) ⟨31221, by rfl⟩ : syracuseStep 333029 = 62443) (by norm_num)
theorem B300277 : Blo 219811 300277 := bbase (se 5 (by rfl) ⟨14075, by rfl⟩ : syracuseStep 300277 = 28151) (by norm_num)
theorem B267509 : Blo 219811 267509 := bbase (se 5 (by rfl) ⟨12539, by rfl⟩ : syracuseStep 267509 = 25079) (by norm_num)
theorem B333053 : Blo 219811 333053 := bbase (se 3 (by rfl) ⟨62447, by rfl⟩ : syracuseStep 333053 = 124895) (by norm_num)
theorem B333077 : Blo 219811 333077 := bbase (se 6 (by rfl) ⟨7806, by rfl⟩ : syracuseStep 333077 = 15613) (by norm_num)
theorem B496925 : Blo 219811 496925 := bbase (se 3 (by rfl) ⟨93173, by rfl⟩ : syracuseStep 496925 = 186347) (by norm_num)
theorem B333101 : Blo 219811 333101 := bbase (se 3 (by rfl) ⟨62456, by rfl⟩ : syracuseStep 333101 = 124913) (by norm_num)
theorem B333125 : Blo 219811 333125 := bbase (se 4 (by rfl) ⟨31230, by rfl⟩ : syracuseStep 333125 = 62461) (by norm_num)
theorem B333149 : Blo 219811 333149 := bbase (se 3 (by rfl) ⟨62465, by rfl⟩ : syracuseStep 333149 = 124931) (by norm_num)
theorem B496997 : Blo 219811 496997 := bbase (se 4 (by rfl) ⟨46593, by rfl⟩ : syracuseStep 496997 = 93187) (by norm_num)
theorem B333173 : Blo 219811 333173 := bbase (se 5 (by rfl) ⟨15617, by rfl⟩ : syracuseStep 333173 = 31235) (by norm_num)
theorem B562565 : Blo 219811 562565 := bbase (se 4 (by rfl) ⟨52740, by rfl⟩ : syracuseStep 562565 = 105481) (by norm_num)
theorem B333197 : Blo 219811 333197 := bbase (se 3 (by rfl) ⟨62474, by rfl⟩ : syracuseStep 333197 = 124949) (by norm_num)
theorem B333221 : Blo 219811 333221 := bbase (se 4 (by rfl) ⟨31239, by rfl⟩ : syracuseStep 333221 = 62479) (by norm_num)
theorem B497069 : Blo 219811 497069 := bbase (se 3 (by rfl) ⟨93200, by rfl⟩ : syracuseStep 497069 = 186401) (by norm_num)
theorem B333245 : Blo 219811 333245 := bbase (se 3 (by rfl) ⟨62483, by rfl⟩ : syracuseStep 333245 = 124967) (by norm_num)
theorem B234949 : Blo 219811 234949 := bbase (se 4 (by rfl) ⟨22026, by rfl⟩ : syracuseStep 234949 = 44053) (by norm_num)
theorem B300493 : Blo 219811 300493 := bbase (se 3 (by rfl) ⟨56342, by rfl⟩ : syracuseStep 300493 = 112685) (by norm_num)
theorem B333269 : Blo 219811 333269 := bbase (se 7 (by rfl) ⟨3905, by rfl⟩ : syracuseStep 333269 = 7811) (by norm_num)
theorem B333293 : Blo 219811 333293 := bbase (se 3 (by rfl) ⟨62492, by rfl⟩ : syracuseStep 333293 = 124985) (by norm_num)
theorem B497141 : Blo 219811 497141 := bbase (se 5 (by rfl) ⟨23303, by rfl⟩ : syracuseStep 497141 = 46607) (by norm_num)
theorem B267769 : Blo 219811 267769 := bbase (se 2 (by rfl) ⟨100413, by rfl⟩ : syracuseStep 267769 = 200827) (by norm_num)
theorem B235009 : Blo 219811 235009 := bbase (se 2 (by rfl) ⟨88128, by rfl⟩ : syracuseStep 235009 = 176257) (by norm_num)
theorem B333317 : Blo 219811 333317 := bbase (se 4 (by rfl) ⟨31248, by rfl⟩ : syracuseStep 333317 = 62497) (by norm_num)
theorem B955925 : Blo 219811 955925 := bbase (se 6 (by rfl) ⟨22404, by rfl⟩ : syracuseStep 955925 = 44809) (by norm_num)
theorem B333341 : Blo 219811 333341 := bbase (se 3 (by rfl) ⟨62501, by rfl⟩ : syracuseStep 333341 = 125003) (by norm_num)
theorem B529973 : Blo 219811 529973 := bbase (se 5 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 529973 = 49685) (by norm_num)
theorem B333365 : Blo 219811 333365 := bbase (se 5 (by rfl) ⟨15626, by rfl⟩ : syracuseStep 333365 = 31253) (by norm_num)
theorem B497213 : Blo 219811 497213 := bbase (se 3 (by rfl) ⟨93227, by rfl⟩ : syracuseStep 497213 = 186455) (by norm_num)
theorem B267845 : Blo 219811 267845 := bbase (se 4 (by rfl) ⟨25110, by rfl⟩ : syracuseStep 267845 = 50221) (by norm_num)
theorem B333389 : Blo 219811 333389 := bbase (se 3 (by rfl) ⟨62510, by rfl⟩ : syracuseStep 333389 = 125021) (by norm_num)
theorem B333413 : Blo 219811 333413 := bbase (se 4 (by rfl) ⟨31257, by rfl⟩ : syracuseStep 333413 = 62515) (by norm_num)
theorem B333437 : Blo 219811 333437 := bbase (se 3 (by rfl) ⟨62519, by rfl⟩ : syracuseStep 333437 = 125039) (by norm_num)
theorem B497285 : Blo 219811 497285 := bbase (se 4 (by rfl) ⟨46620, by rfl⟩ : syracuseStep 497285 = 93241) (by norm_num)
theorem B333461 : Blo 219811 333461 := bbase (se 6 (by rfl) ⟨7815, by rfl⟩ : syracuseStep 333461 = 15631) (by norm_num)
theorem B333485 : Blo 219811 333485 := bbase (se 3 (by rfl) ⟨62528, by rfl⟩ : syracuseStep 333485 = 125057) (by norm_num)
theorem B267961 : Blo 219811 267961 := bbase (se 2 (by rfl) ⟨100485, by rfl⟩ : syracuseStep 267961 = 200971) (by norm_num)
theorem B333509 : Blo 219811 333509 := bbase (se 4 (by rfl) ⟨31266, by rfl⟩ : syracuseStep 333509 = 62533) (by norm_num)
theorem B497357 : Blo 219811 497357 := bbase (se 3 (by rfl) ⟨93254, by rfl⟩ : syracuseStep 497357 = 186509) (by norm_num)
theorem B267985 : Blo 219811 267985 := bbase (se 2 (by rfl) ⟨100494, by rfl⟩ : syracuseStep 267985 = 200989) (by norm_num)
theorem B333533 : Blo 219811 333533 := bbase (se 3 (by rfl) ⟨62537, by rfl⟩ : syracuseStep 333533 = 125075) (by norm_num)
theorem B562909 : Blo 219811 562909 := bbase (se 3 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 562909 = 211091) (by norm_num)
theorem B333557 : Blo 219811 333557 := bbase (se 5 (by rfl) ⟨15635, by rfl⟩ : syracuseStep 333557 = 31271) (by norm_num)
theorem B530173 : Blo 219811 530173 := bbase (se 3 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 530173 = 198815) (by norm_num)
theorem B333581 : Blo 219811 333581 := bbase (se 3 (by rfl) ⟨62546, by rfl⟩ : syracuseStep 333581 = 125093) (by norm_num)
theorem B497429 : Blo 219811 497429 := bbase (se 6 (by rfl) ⟨11658, by rfl⟩ : syracuseStep 497429 = 23317) (by norm_num)
theorem B333605 : Blo 219811 333605 := bbase (se 4 (by rfl) ⟨31275, by rfl⟩ : syracuseStep 333605 = 62551) (by norm_num)
theorem B235325 : Blo 219811 235325 := bbase (se 3 (by rfl) ⟨44123, by rfl⟩ : syracuseStep 235325 = 88247) (by norm_num)
theorem B333629 : Blo 219811 333629 := bbase (se 3 (by rfl) ⟨62555, by rfl⟩ : syracuseStep 333629 = 125111) (by norm_num)
theorem B399173 : Blo 219811 399173 := bbase (se 4 (by rfl) ⟨37422, by rfl⟩ : syracuseStep 399173 = 74845) (by norm_num)
theorem B563021 : Blo 219811 563021 := bbase (se 3 (by rfl) ⟨105566, by rfl⟩ : syracuseStep 563021 = 211133) (by norm_num)
theorem B333653 : Blo 219811 333653 := bbase (se 9 (by rfl) ⟨977, by rfl⟩ : syracuseStep 333653 = 1955) (by norm_num)
theorem B1906517 : Blo 219811 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B497501 : Blo 219811 497501 := bbase (se 3 (by rfl) ⟨93281, by rfl⟩ : syracuseStep 497501 = 186563) (by norm_num)
theorem B333677 : Blo 219811 333677 := bbase (se 3 (by rfl) ⟨62564, by rfl⟩ : syracuseStep 333677 = 125129) (by norm_num)
theorem B333701 : Blo 219811 333701 := bbase (se 4 (by rfl) ⟨31284, by rfl⟩ : syracuseStep 333701 = 62569) (by norm_num)
theorem B333725 : Blo 219811 333725 := bbase (se 3 (by rfl) ⟨62573, by rfl⟩ : syracuseStep 333725 = 125147) (by norm_num)
theorem B497573 : Blo 219811 497573 := bbase (se 4 (by rfl) ⟨46647, by rfl⟩ : syracuseStep 497573 = 93295) (by norm_num)
theorem B628661 : Blo 219811 628661 := bbase (se 5 (by rfl) ⟨29468, by rfl⟩ : syracuseStep 628661 = 58937) (by norm_num)
theorem B333749 : Blo 219811 333749 := bbase (se 5 (by rfl) ⟨15644, by rfl⟩ : syracuseStep 333749 = 31289) (by norm_num)
theorem B333773 : Blo 219811 333773 := bbase (se 3 (by rfl) ⟨62582, by rfl⟩ : syracuseStep 333773 = 125165) (by norm_num)
theorem B399325 : Blo 219811 399325 := bbase (se 3 (by rfl) ⟨74873, by rfl⟩ : syracuseStep 399325 = 149747) (by norm_num)
theorem B366557 : Blo 219811 366557 := bbase (se 3 (by rfl) ⟨68729, by rfl⟩ : syracuseStep 366557 = 137459) (by norm_num)
theorem B1120229 : Blo 219811 1120229 := bbase (se 4 (by rfl) ⟨105021, by rfl⟩ : syracuseStep 1120229 = 210043) (by norm_num)
theorem B333797 : Blo 219811 333797 := bbase (se 4 (by rfl) ⟨31293, by rfl⟩ : syracuseStep 333797 = 62587) (by norm_num)
theorem B497645 : Blo 219811 497645 := bbase (se 3 (by rfl) ⟨93308, by rfl⟩ : syracuseStep 497645 = 186617) (by norm_num)
theorem B333821 : Blo 219811 333821 := bbase (se 3 (by rfl) ⟨62591, by rfl⟩ : syracuseStep 333821 = 125183) (by norm_num)
theorem B563213 : Blo 219811 563213 := bbase (se 3 (by rfl) ⟨105602, by rfl⟩ : syracuseStep 563213 = 211205) (by norm_num)
theorem B333845 : Blo 219811 333845 := bbase (se 6 (by rfl) ⟨7824, by rfl⟩ : syracuseStep 333845 = 15649) (by norm_num)
theorem B333869 : Blo 219811 333869 := bbase (se 3 (by rfl) ⟨62600, by rfl⟩ : syracuseStep 333869 = 125201) (by norm_num)
theorem B497717 : Blo 219811 497717 := bbase (se 5 (by rfl) ⟨23330, by rfl⟩ : syracuseStep 497717 = 46661) (by norm_num)
theorem B333893 : Blo 219811 333893 := bbase (se 4 (by rfl) ⟨31302, by rfl⟩ : syracuseStep 333893 = 62605) (by norm_num)
theorem B333917 : Blo 219811 333917 := bbase (se 3 (by rfl) ⟨62609, by rfl⟩ : syracuseStep 333917 = 125219) (by norm_num)
theorem B333941 : Blo 219811 333941 := bbase (se 5 (by rfl) ⟨15653, by rfl⟩ : syracuseStep 333941 = 31307) (by norm_num)
theorem B497789 : Blo 219811 497789 := bbase (se 3 (by rfl) ⟨93335, by rfl⟩ : syracuseStep 497789 = 186671) (by norm_num)
theorem B333965 : Blo 219811 333965 := bbase (se 3 (by rfl) ⟨62618, by rfl⟩ : syracuseStep 333965 = 125237) (by norm_num)
theorem B333989 : Blo 219811 333989 := bbase (se 4 (by rfl) ⟨31311, by rfl⟩ : syracuseStep 333989 = 62623) (by norm_num)
theorem B334013 : Blo 219811 334013 := bbase (se 3 (by rfl) ⟨62627, by rfl⟩ : syracuseStep 334013 = 125255) (by norm_num)
theorem B497861 : Blo 219811 497861 := bbase (se 4 (by rfl) ⟨46674, by rfl⟩ : syracuseStep 497861 = 93349) (by norm_num)
theorem B334037 : Blo 219811 334037 := bbase (se 7 (by rfl) ⟨3914, by rfl⟩ : syracuseStep 334037 = 7829) (by norm_num)
theorem B334061 : Blo 219811 334061 := bbase (se 3 (by rfl) ⟨62636, by rfl⟩ : syracuseStep 334061 = 125273) (by norm_num)
theorem B235769 : Blo 219811 235769 := bbase (se 2 (by rfl) ⟨88413, by rfl⟩ : syracuseStep 235769 = 176827) (by norm_num)
theorem B334085 : Blo 219811 334085 := bbase (se 4 (by rfl) ⟨31320, by rfl⟩ : syracuseStep 334085 = 62641) (by norm_num)
theorem B497933 : Blo 219811 497933 := bbase (se 3 (by rfl) ⟨93362, by rfl⟩ : syracuseStep 497933 = 186725) (by norm_num)
theorem B334109 : Blo 219811 334109 := bbase (se 3 (by rfl) ⟨62645, by rfl⟩ : syracuseStep 334109 = 125291) (by norm_num)
theorem B235829 : Blo 219811 235829 := bbase (se 5 (by rfl) ⟨11054, by rfl⟩ : syracuseStep 235829 = 22109) (by norm_num)
theorem B334133 : Blo 219811 334133 := bbase (se 5 (by rfl) ⟨15662, by rfl⟩ : syracuseStep 334133 = 31325) (by norm_num)
theorem B334157 : Blo 219811 334157 := bbase (se 3 (by rfl) ⟨62654, by rfl⟩ : syracuseStep 334157 = 125309) (by norm_num)
theorem B498005 : Blo 219811 498005 := bbase (se 10 (by rfl) ⟨729, by rfl⟩ : syracuseStep 498005 = 1459) (by norm_num)
theorem B563557 : Blo 219811 563557 := bbase (se 4 (by rfl) ⟨52833, by rfl⟩ : syracuseStep 563557 = 105667) (by norm_num)
theorem B334181 : Blo 219811 334181 := bbase (se 4 (by rfl) ⟨31329, by rfl⟩ : syracuseStep 334181 = 62659) (by norm_num)
theorem B334205 : Blo 219811 334205 := bbase (se 3 (by rfl) ⟨62663, by rfl⟩ : syracuseStep 334205 = 125327) (by norm_num)
theorem B268681 : Blo 219811 268681 := bbase (se 2 (by rfl) ⟨100755, by rfl⟩ : syracuseStep 268681 = 201511) (by norm_num)
theorem B334229 : Blo 219811 334229 := bbase (se 6 (by rfl) ⟨7833, by rfl⟩ : syracuseStep 334229 = 15667) (by norm_num)
theorem B498077 : Blo 219811 498077 := bbase (se 3 (by rfl) ⟨93389, by rfl⟩ : syracuseStep 498077 = 186779) (by norm_num)
theorem B334253 : Blo 219811 334253 := bbase (se 3 (by rfl) ⟨62672, by rfl⟩ : syracuseStep 334253 = 125345) (by norm_num)
theorem B235957 : Blo 219811 235957 := bbase (se 5 (by rfl) ⟨11060, by rfl⟩ : syracuseStep 235957 = 22121) (by norm_num)
theorem B334277 : Blo 219811 334277 := bbase (se 4 (by rfl) ⟨31338, by rfl⟩ : syracuseStep 334277 = 62677) (by norm_num)
theorem B563669 : Blo 219811 563669 := bbase (se 7 (by rfl) ⟨6605, by rfl⟩ : syracuseStep 563669 = 13211) (by norm_num)
theorem B334301 : Blo 219811 334301 := bbase (se 3 (by rfl) ⟨62681, by rfl⟩ : syracuseStep 334301 = 125363) (by norm_num)
theorem B498149 : Blo 219811 498149 := bbase (se 4 (by rfl) ⟨46701, by rfl⟩ : syracuseStep 498149 = 93403) (by norm_num)
theorem B268777 : Blo 219811 268777 := bbase (se 2 (by rfl) ⟨100791, by rfl⟩ : syracuseStep 268777 = 201583) (by norm_num)
theorem B334325 : Blo 219811 334325 := bbase (se 5 (by rfl) ⟨15671, by rfl⟩ : syracuseStep 334325 = 31343) (by norm_num)
theorem B334349 : Blo 219811 334349 := bbase (se 3 (by rfl) ⟨62690, by rfl⟩ : syracuseStep 334349 = 125381) (by norm_num)
theorem B530981 : Blo 219811 530981 := bbase (se 4 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 530981 = 99559) (by norm_num)
theorem B334373 : Blo 219811 334373 := bbase (se 4 (by rfl) ⟨31347, by rfl⟩ : syracuseStep 334373 = 62695) (by norm_num)
theorem B498221 : Blo 219811 498221 := bbase (se 3 (by rfl) ⟨93416, by rfl⟩ : syracuseStep 498221 = 186833) (by norm_num)
theorem B334397 : Blo 219811 334397 := bbase (se 3 (by rfl) ⟨62699, by rfl⟩ : syracuseStep 334397 = 125399) (by norm_num)
theorem B629333 : Blo 219811 629333 := bbase (se 8 (by rfl) ⟨3687, by rfl⟩ : syracuseStep 629333 = 7375) (by norm_num)
theorem B334421 : Blo 219811 334421 := bbase (se 8 (by rfl) ⟨1959, by rfl⟩ : syracuseStep 334421 = 3919) (by norm_num)
theorem B334445 : Blo 219811 334445 := bbase (se 3 (by rfl) ⟨62708, by rfl⟩ : syracuseStep 334445 = 125417) (by norm_num)
theorem B498293 : Blo 219811 498293 := bbase (se 5 (by rfl) ⟨23357, by rfl⟩ : syracuseStep 498293 = 46715) (by norm_num)
theorem B334469 : Blo 219811 334469 := bbase (se 4 (by rfl) ⟨31356, by rfl⟩ : syracuseStep 334469 = 62713) (by norm_num)
theorem B563861 : Blo 219811 563861 := bbase (se 6 (by rfl) ⟨13215, by rfl⟩ : syracuseStep 563861 = 26431) (by norm_num)
theorem B334493 : Blo 219811 334493 := bbase (se 3 (by rfl) ⟨62717, by rfl⟩ : syracuseStep 334493 = 125435) (by norm_num)
theorem B334517 : Blo 219811 334517 := bbase (se 5 (by rfl) ⟨15680, by rfl⟩ : syracuseStep 334517 = 31361) (by norm_num)
theorem B498365 : Blo 219811 498365 := bbase (se 3 (by rfl) ⟨93443, by rfl⟩ : syracuseStep 498365 = 186887) (by norm_num)
theorem B334541 : Blo 219811 334541 := bbase (se 3 (by rfl) ⟨62726, by rfl⟩ : syracuseStep 334541 = 125453) (by norm_num)
theorem B3185365 : Blo 219811 3185365 := bbase (se 7 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 3185365 = 74657) (by norm_num)
theorem B334565 : Blo 219811 334565 := bbase (se 4 (by rfl) ⟨31365, by rfl⟩ : syracuseStep 334565 = 62731) (by norm_num)
theorem B334589 : Blo 219811 334589 := bbase (se 3 (by rfl) ⟨62735, by rfl⟩ : syracuseStep 334589 = 125471) (by norm_num)
theorem B498437 : Blo 219811 498437 := bbase (se 4 (by rfl) ⟨46728, by rfl⟩ : syracuseStep 498437 = 93457) (by norm_num)
theorem B400133 : Blo 219811 400133 := bbase (se 4 (by rfl) ⟨37512, by rfl⟩ : syracuseStep 400133 = 75025) (by norm_num)
theorem B334613 : Blo 219811 334613 := bbase (se 6 (by rfl) ⟨7842, by rfl⟩ : syracuseStep 334613 = 15685) (by norm_num)
theorem B334637 : Blo 219811 334637 := bbase (se 3 (by rfl) ⟨62744, by rfl⟩ : syracuseStep 334637 = 125489) (by norm_num)
theorem B334661 : Blo 219811 334661 := bbase (se 4 (by rfl) ⟨31374, by rfl⟩ : syracuseStep 334661 = 62749) (by norm_num)
theorem B498509 : Blo 219811 498509 := bbase (se 3 (by rfl) ⟨93470, by rfl⟩ : syracuseStep 498509 = 186941) (by norm_num)
theorem B334685 : Blo 219811 334685 := bbase (se 3 (by rfl) ⟨62753, by rfl⟩ : syracuseStep 334685 = 125507) (by norm_num)
theorem B891749 : Blo 219811 891749 := bbase (se 4 (by rfl) ⟨83601, by rfl⟩ : syracuseStep 891749 = 167203) (by norm_num)
theorem B236401 : Blo 219811 236401 := bbase (se 2 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 236401 = 177301) (by norm_num)
theorem B334709 : Blo 219811 334709 := bbase (se 5 (by rfl) ⟨15689, by rfl⟩ : syracuseStep 334709 = 31379) (by norm_num)
theorem B334733 : Blo 219811 334733 := bbase (se 3 (by rfl) ⟨62762, by rfl⟩ : syracuseStep 334733 = 125525) (by norm_num)
theorem B498581 : Blo 219811 498581 := bbase (se 6 (by rfl) ⟨11685, by rfl⟩ : syracuseStep 498581 = 23371) (by norm_num)
theorem B334757 : Blo 219811 334757 := bbase (se 4 (by rfl) ⟨31383, by rfl⟩ : syracuseStep 334757 = 62767) (by norm_num)
theorem B334781 : Blo 219811 334781 := bbase (se 3 (by rfl) ⟨62771, by rfl⟩ : syracuseStep 334781 = 125543) (by norm_num)
theorem B334805 : Blo 219811 334805 := bbase (se 7 (by rfl) ⟨3923, by rfl⟩ : syracuseStep 334805 = 7847) (by norm_num)
theorem B498653 : Blo 219811 498653 := bbase (se 3 (by rfl) ⟨93497, by rfl⟩ : syracuseStep 498653 = 186995) (by norm_num)
theorem B236521 : Blo 219811 236521 := bbase (se 2 (by rfl) ⟨88695, by rfl⟩ : syracuseStep 236521 = 177391) (by norm_num)
theorem B564205 : Blo 219811 564205 := bbase (se 3 (by rfl) ⟨105788, by rfl⟩ : syracuseStep 564205 = 211577) (by norm_num)
theorem B334829 : Blo 219811 334829 := bbase (se 3 (by rfl) ⟨62780, by rfl⟩ : syracuseStep 334829 = 125561) (by norm_num)
theorem B629765 : Blo 219811 629765 := bbase (se 4 (by rfl) ⟨59040, by rfl⟩ : syracuseStep 629765 = 118081) (by norm_num)
theorem B334853 : Blo 219811 334853 := bbase (se 4 (by rfl) ⟨31392, by rfl⟩ : syracuseStep 334853 = 62785) (by norm_num)
theorem B334877 : Blo 219811 334877 := bbase (se 3 (by rfl) ⟨62789, by rfl⟩ : syracuseStep 334877 = 125579) (by norm_num)
theorem B498725 : Blo 219811 498725 := bbase (se 4 (by rfl) ⟨46755, by rfl⟩ : syracuseStep 498725 = 93511) (by norm_num)
theorem B334901 : Blo 219811 334901 := bbase (se 5 (by rfl) ⟨15698, by rfl⟩ : syracuseStep 334901 = 31397) (by norm_num)
theorem B334925 : Blo 219811 334925 := bbase (se 3 (by rfl) ⟨62798, by rfl⟩ : syracuseStep 334925 = 125597) (by norm_num)
theorem B564317 : Blo 219811 564317 := bbase (se 3 (by rfl) ⟨105809, by rfl⟩ : syracuseStep 564317 = 211619) (by norm_num)
theorem B334949 : Blo 219811 334949 := bbase (se 4 (by rfl) ⟨31401, by rfl⟩ : syracuseStep 334949 = 62803) (by norm_num)
theorem B498797 : Blo 219811 498797 := bbase (se 3 (by rfl) ⟨93524, by rfl⟩ : syracuseStep 498797 = 187049) (by norm_num)
theorem B334973 : Blo 219811 334973 := bbase (se 3 (by rfl) ⟨62807, by rfl⟩ : syracuseStep 334973 = 125615) (by norm_num)
theorem B334997 : Blo 219811 334997 := bbase (se 6 (by rfl) ⟨7851, by rfl⟩ : syracuseStep 334997 = 15703) (by norm_num)
theorem B335021 : Blo 219811 335021 := bbase (se 3 (by rfl) ⟨62816, by rfl⟩ : syracuseStep 335021 = 125633) (by norm_num)
theorem B498869 : Blo 219811 498869 := bbase (se 5 (by rfl) ⟨23384, by rfl⟩ : syracuseStep 498869 = 46769) (by norm_num)
theorem B335045 : Blo 219811 335045 := bbase (se 4 (by rfl) ⟨31410, by rfl⟩ : syracuseStep 335045 = 62821) (by norm_num)
theorem B335069 : Blo 219811 335069 := bbase (se 3 (by rfl) ⟨62825, by rfl⟩ : syracuseStep 335069 = 125651) (by norm_num)
theorem B236773 : Blo 219811 236773 := bbase (se 4 (by rfl) ⟨22197, by rfl⟩ : syracuseStep 236773 = 44395) (by norm_num)
theorem B236777 : Blo 219811 236777 := bbase (se 2 (by rfl) ⟨88791, by rfl⟩ : syracuseStep 236777 = 177583) (by norm_num)
theorem B1121525 : Blo 219811 1121525 := bbase (se 5 (by rfl) ⟨52571, by rfl⟩ : syracuseStep 1121525 = 105143) (by norm_num)
theorem B335093 : Blo 219811 335093 := bbase (se 5 (by rfl) ⟨15707, by rfl⟩ : syracuseStep 335093 = 31415) (by norm_num)
theorem B498941 : Blo 219811 498941 := bbase (se 3 (by rfl) ⟨93551, by rfl⟩ : syracuseStep 498941 = 187103) (by norm_num)
theorem B335117 : Blo 219811 335117 := bbase (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) (by norm_num)
theorem B564509 : Blo 219811 564509 := bbase (se 3 (by rfl) ⟨105845, by rfl⟩ : syracuseStep 564509 = 211691) (by norm_num)
theorem B531749 : Blo 219811 531749 := bbase (se 4 (by rfl) ⟨49851, by rfl⟩ : syracuseStep 531749 = 99703) (by norm_num)
theorem B335141 : Blo 219811 335141 := bbase (se 4 (by rfl) ⟨31419, by rfl⟩ : syracuseStep 335141 = 62839) (by norm_num)
theorem B335165 : Blo 219811 335165 := bbase (se 3 (by rfl) ⟨62843, by rfl⟩ : syracuseStep 335165 = 125687) (by norm_num)
theorem B499013 : Blo 219811 499013 := bbase (se 4 (by rfl) ⟨46782, by rfl⟩ : syracuseStep 499013 = 93565) (by norm_num)
theorem B400709 : Blo 219811 400709 := bbase (se 4 (by rfl) ⟨37566, by rfl⟩ : syracuseStep 400709 = 75133) (by norm_num)
theorem B335189 : Blo 219811 335189 := bbase (se 11 (by rfl) ⟨245, by rfl⟩ : syracuseStep 335189 = 491) (by norm_num)
theorem B335213 : Blo 219811 335213 := bbase (se 3 (by rfl) ⟨62852, by rfl⟩ : syracuseStep 335213 = 125705) (by norm_num)
theorem B269693 : Blo 219811 269693 := bbase (se 3 (by rfl) ⟨50567, by rfl⟩ : syracuseStep 269693 = 101135) (by norm_num)
theorem B335237 : Blo 219811 335237 := bbase (se 4 (by rfl) ⟨31428, by rfl⟩ : syracuseStep 335237 = 62857) (by norm_num)
theorem B499085 : Blo 219811 499085 := bbase (se 3 (by rfl) ⟨93578, by rfl⟩ : syracuseStep 499085 = 187157) (by norm_num)
theorem B335261 : Blo 219811 335261 := bbase (se 3 (by rfl) ⟨62861, by rfl⟩ : syracuseStep 335261 = 125723) (by norm_num)
theorem B335285 : Blo 219811 335285 := bbase (se 5 (by rfl) ⟨15716, by rfl⟩ : syracuseStep 335285 = 31433) (by norm_num)
theorem B335309 : Blo 219811 335309 := bbase (se 3 (by rfl) ⟨62870, by rfl⟩ : syracuseStep 335309 = 125741) (by norm_num)
theorem B597461 : Blo 219811 597461 := bbase (se 7 (by rfl) ⟨7001, by rfl⟩ : syracuseStep 597461 = 14003) (by norm_num)
theorem B499157 : Blo 219811 499157 := bbase (se 7 (by rfl) ⟨5849, by rfl⟩ : syracuseStep 499157 = 11699) (by norm_num)
theorem B335333 : Blo 219811 335333 := bbase (se 4 (by rfl) ⟨31437, by rfl⟩ : syracuseStep 335333 = 62875) (by norm_num)
theorem B335357 : Blo 219811 335357 := bbase (se 3 (by rfl) ⟨62879, by rfl⟩ : syracuseStep 335357 = 125759) (by norm_num)
theorem B335381 : Blo 219811 335381 := bbase (se 6 (by rfl) ⟨7860, by rfl⟩ : syracuseStep 335381 = 15721) (by norm_num)
theorem B499229 : Blo 219811 499229 := bbase (se 3 (by rfl) ⟨93605, by rfl⟩ : syracuseStep 499229 = 187211) (by norm_num)
theorem B335405 : Blo 219811 335405 := bbase (se 3 (by rfl) ⟨62888, by rfl⟩ : syracuseStep 335405 = 125777) (by norm_num)
theorem B335429 : Blo 219811 335429 := bbase (se 4 (by rfl) ⟨31446, by rfl⟩ : syracuseStep 335429 = 62893) (by norm_num)
theorem B335453 : Blo 219811 335453 := bbase (se 3 (by rfl) ⟨62897, by rfl⟩ : syracuseStep 335453 = 125795) (by norm_num)
theorem B499301 : Blo 219811 499301 := bbase (se 4 (by rfl) ⟨46809, by rfl⟩ : syracuseStep 499301 = 93619) (by norm_num)
theorem B335477 : Blo 219811 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B564853 : Blo 219811 564853 := bbase (se 5 (by rfl) ⟨26477, by rfl⟩ : syracuseStep 564853 = 52955) (by norm_num)
theorem B335501 : Blo 219811 335501 := bbase (se 3 (by rfl) ⟨62906, by rfl⟩ : syracuseStep 335501 = 125813) (by norm_num)
theorem B335525 : Blo 219811 335525 := bbase (se 4 (by rfl) ⟨31455, by rfl⟩ : syracuseStep 335525 = 62911) (by norm_num)
theorem B499373 : Blo 219811 499373 := bbase (se 3 (by rfl) ⟨93632, by rfl⟩ : syracuseStep 499373 = 187265) (by norm_num)
theorem B335549 : Blo 219811 335549 := bbase (se 3 (by rfl) ⟨62915, by rfl⟩ : syracuseStep 335549 = 125831) (by norm_num)
theorem B335573 : Blo 219811 335573 := bbase (se 7 (by rfl) ⟨3932, by rfl⟩ : syracuseStep 335573 = 7865) (by norm_num)
theorem B564965 : Blo 219811 564965 := bbase (se 4 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 564965 = 105931) (by norm_num)
theorem B335597 : Blo 219811 335597 := bbase (se 3 (by rfl) ⟨62924, by rfl⟩ : syracuseStep 335597 = 125849) (by norm_num)
theorem B630517 : Blo 219811 630517 := bbase (se 5 (by rfl) ⟨29555, by rfl⟩ : syracuseStep 630517 = 59111) (by norm_num)
theorem B499445 : Blo 219811 499445 := bbase (se 5 (by rfl) ⟨23411, by rfl⟩ : syracuseStep 499445 = 46823) (by norm_num)
theorem B335621 : Blo 219811 335621 := bbase (se 4 (by rfl) ⟨31464, by rfl⟩ : syracuseStep 335621 = 62929) (by norm_num)
theorem B237341 : Blo 219811 237341 := bbase (se 3 (by rfl) ⟨44501, by rfl⟩ : syracuseStep 237341 = 89003) (by norm_num)
theorem B335645 : Blo 219811 335645 := bbase (se 3 (by rfl) ⟨62933, by rfl⟩ : syracuseStep 335645 = 125867) (by norm_num)
theorem B335669 : Blo 219811 335669 := bbase (se 5 (by rfl) ⟨15734, by rfl⟩ : syracuseStep 335669 = 31469) (by norm_num)
theorem B499517 : Blo 219811 499517 := bbase (se 3 (by rfl) ⟨93659, by rfl⟩ : syracuseStep 499517 = 187319) (by norm_num)
theorem B335693 : Blo 219811 335693 := bbase (se 3 (by rfl) ⟨62942, by rfl⟩ : syracuseStep 335693 = 125885) (by norm_num)
theorem B335717 : Blo 219811 335717 := bbase (se 4 (by rfl) ⟨31473, by rfl⟩ : syracuseStep 335717 = 62947) (by norm_num)
theorem B761717 : Blo 219811 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B499589 : Blo 219811 499589 := bbase (se 4 (by rfl) ⟨46836, by rfl⟩ : syracuseStep 499589 = 93673) (by norm_num)
theorem B565157 : Blo 219811 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B499661 : Blo 219811 499661 := bbase (se 3 (by rfl) ⟨93686, by rfl⟩ : syracuseStep 499661 = 187373) (by norm_num)
theorem B1253333 : Blo 219811 1253333 := bbase (se 7 (by rfl) ⟨14687, by rfl⟩ : syracuseStep 1253333 = 29375) (by norm_num)
theorem B237529 : Blo 219811 237529 := bbase (se 2 (by rfl) ⟨89073, by rfl⟩ : syracuseStep 237529 = 178147) (by norm_num)
theorem B565213 : Blo 219811 565213 := bbase (se 3 (by rfl) ⟨105977, by rfl⟩ : syracuseStep 565213 = 211955) (by norm_num)
theorem B499733 : Blo 219811 499733 := bbase (se 6 (by rfl) ⟨11712, by rfl⟩ : syracuseStep 499733 = 23425) (by norm_num)
theorem B499805 : Blo 219811 499805 := bbase (se 3 (by rfl) ⟨93713, by rfl⟩ : syracuseStep 499805 = 187427) (by norm_num)
theorem B499877 : Blo 219811 499877 := bbase (se 4 (by rfl) ⟨46863, by rfl⟩ : syracuseStep 499877 = 93727) (by norm_num)
theorem B499949 : Blo 219811 499949 := bbase (se 3 (by rfl) ⟨93740, by rfl⟩ : syracuseStep 499949 = 187481) (by norm_num)
theorem B565501 : Blo 219811 565501 := bbase (se 3 (by rfl) ⟨106031, by rfl⟩ : syracuseStep 565501 = 212063) (by norm_num)
theorem B500021 : Blo 219811 500021 := bbase (se 5 (by rfl) ⟨23438, by rfl⟩ : syracuseStep 500021 = 46877) (by norm_num)
theorem B565613 : Blo 219811 565613 := bbase (se 3 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 565613 = 212105) (by norm_num)
theorem B500093 : Blo 219811 500093 := bbase (se 3 (by rfl) ⟨93767, by rfl⟩ : syracuseStep 500093 = 187535) (by norm_num)
theorem B500165 : Blo 219811 500165 := bbase (se 4 (by rfl) ⟨46890, by rfl⟩ : syracuseStep 500165 = 93781) (by norm_num)
theorem B1122821 : Blo 219811 1122821 := bbase (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) (by norm_num)
theorem B500237 : Blo 219811 500237 := bbase (se 3 (by rfl) ⟨93794, by rfl⟩ : syracuseStep 500237 = 187589) (by norm_num)
theorem B565805 : Blo 219811 565805 := bbase (se 3 (by rfl) ⟨106088, by rfl⟩ : syracuseStep 565805 = 212177) (by norm_num)
theorem B500309 : Blo 219811 500309 := bbase (se 8 (by rfl) ⟨2931, by rfl⟩ : syracuseStep 500309 = 5863) (by norm_num)
theorem B402013 : Blo 219811 402013 := bbase (se 3 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 402013 = 150755) (by norm_num)
theorem B500381 : Blo 219811 500381 := bbase (se 3 (by rfl) ⟨93821, by rfl⟩ : syracuseStep 500381 = 187643) (by norm_num)
theorem B303845 : Blo 219811 303845 := bbase (se 4 (by rfl) ⟨28485, by rfl⟩ : syracuseStep 303845 = 56971) (by norm_num)
theorem B500453 : Blo 219811 500453 := bbase (se 4 (by rfl) ⟨46917, by rfl⟩ : syracuseStep 500453 = 93835) (by norm_num)
theorem B1909493 : Blo 219811 1909493 := bbase (se 5 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 1909493 = 179015) (by norm_num)
theorem B238349 : Blo 219811 238349 := bbase (se 3 (by rfl) ⟨44690, by rfl⟩ : syracuseStep 238349 = 89381) (by norm_num)
theorem B2564885 : Blo 219811 2564885 := bbase (se 6 (by rfl) ⟨60114, by rfl⟩ : syracuseStep 2564885 = 120229) (by norm_num)
theorem B500525 : Blo 219811 500525 := bbase (se 3 (by rfl) ⟨93848, by rfl⟩ : syracuseStep 500525 = 187697) (by norm_num)
theorem B500597 : Blo 219811 500597 := bbase (se 5 (by rfl) ⟨23465, by rfl⟩ : syracuseStep 500597 = 46931) (by norm_num)
theorem B566149 : Blo 219811 566149 := bbase (se 4 (by rfl) ⟨53076, by rfl⟩ : syracuseStep 566149 = 106153) (by norm_num)
theorem B500669 : Blo 219811 500669 := bbase (se 3 (by rfl) ⟨93875, by rfl⟩ : syracuseStep 500669 = 187751) (by norm_num)
theorem B304069 : Blo 219811 304069 := bbase (se 4 (by rfl) ⟨28506, by rfl⟩ : syracuseStep 304069 = 57013) (by norm_num)
theorem B598997 : Blo 219811 598997 := bbase (se 7 (by rfl) ⟨7019, by rfl⟩ : syracuseStep 598997 = 14039) (by norm_num)
theorem B533461 : Blo 219811 533461 := bbase (se 7 (by rfl) ⟨6251, by rfl⟩ : syracuseStep 533461 = 12503) (by norm_num)
theorem B566261 : Blo 219811 566261 := bbase (se 5 (by rfl) ⟨26543, by rfl⟩ : syracuseStep 566261 = 53087) (by norm_num)
theorem B500741 : Blo 219811 500741 := bbase (se 4 (by rfl) ⟨46944, by rfl⟩ : syracuseStep 500741 = 93889) (by norm_num)
theorem B500813 : Blo 219811 500813 := bbase (se 3 (by rfl) ⟨93902, by rfl⟩ : syracuseStep 500813 = 187805) (by norm_num)
theorem B500885 : Blo 219811 500885 := bbase (se 6 (by rfl) ⟨11739, by rfl⟩ : syracuseStep 500885 = 23479) (by norm_num)
theorem B566453 : Blo 219811 566453 := bbase (se 5 (by rfl) ⟨26552, by rfl⟩ : syracuseStep 566453 = 53105) (by norm_num)
theorem B238793 : Blo 219811 238793 := bbase (se 2 (by rfl) ⟨89547, by rfl⟩ : syracuseStep 238793 = 179095) (by norm_num)
theorem B500957 : Blo 219811 500957 := bbase (se 3 (by rfl) ⟨93929, by rfl⟩ : syracuseStep 500957 = 187859) (by norm_num)
theorem B501029 : Blo 219811 501029 := bbase (se 4 (by rfl) ⟨46971, by rfl⟩ : syracuseStep 501029 = 93943) (by norm_num)
theorem B402733 : Blo 219811 402733 := bbase (se 3 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 402733 = 151025) (by norm_num)
theorem B501101 : Blo 219811 501101 := bbase (se 3 (by rfl) ⟨93956, by rfl⟩ : syracuseStep 501101 = 187913) (by norm_num)
theorem B763253 : Blo 219811 763253 := bbase (se 5 (by rfl) ⟨35777, by rfl⟩ : syracuseStep 763253 = 71555) (by norm_num)
theorem B501173 : Blo 219811 501173 := bbase (se 5 (by rfl) ⟨23492, by rfl⟩ : syracuseStep 501173 = 46985) (by norm_num)
theorem B2139605 : Blo 219811 2139605 := bbase (se 7 (by rfl) ⟨25073, by rfl⟩ : syracuseStep 2139605 = 50147) (by norm_num)
theorem B501245 : Blo 219811 501245 := bbase (se 3 (by rfl) ⟨93983, by rfl⟩ : syracuseStep 501245 = 187967) (by norm_num)
theorem B534077 : Blo 219811 534077 := bbase (se 3 (by rfl) ⟨100139, by rfl⟩ : syracuseStep 534077 = 200279) (by norm_num)
theorem B796229 : Blo 219811 796229 := bbase (se 4 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 796229 = 149293) (by norm_num)
theorem B501317 : Blo 219811 501317 := bbase (se 4 (by rfl) ⟨46998, by rfl⟩ : syracuseStep 501317 = 93997) (by norm_num)
theorem B501389 : Blo 219811 501389 := bbase (se 3 (by rfl) ⟨94010, by rfl⟩ : syracuseStep 501389 = 188021) (by norm_num)
theorem B1058501 : Blo 219811 1058501 := bbase (se 4 (by rfl) ⟨99234, by rfl⟩ : syracuseStep 1058501 = 198469) (by norm_num)
theorem B501461 : Blo 219811 501461 := bbase (se 7 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 501461 = 11753) (by norm_num)
theorem B1124117 : Blo 219811 1124117 := bbase (se 6 (by rfl) ⟨26346, by rfl⟩ : syracuseStep 1124117 = 52693) (by norm_num)
theorem B501533 : Blo 219811 501533 := bbase (se 3 (by rfl) ⟨94037, by rfl⟩ : syracuseStep 501533 = 188075) (by norm_num)
theorem B501605 : Blo 219811 501605 := bbase (se 4 (by rfl) ⟨47025, by rfl⟩ : syracuseStep 501605 = 94051) (by norm_num)
theorem B239473 : Blo 219811 239473 := bbase (se 2 (by rfl) ⟨89802, by rfl⟩ : syracuseStep 239473 = 179605) (by norm_num)
theorem B501677 : Blo 219811 501677 := bbase (se 3 (by rfl) ⟨94064, by rfl⟩ : syracuseStep 501677 = 188129) (by norm_num)
theorem B534509 : Blo 219811 534509 := bbase (se 3 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 534509 = 200441) (by norm_num)
theorem B501749 : Blo 219811 501749 := bbase (se 5 (by rfl) ⟨23519, by rfl⟩ : syracuseStep 501749 = 47039) (by norm_num)
theorem B501821 : Blo 219811 501821 := bbase (se 3 (by rfl) ⟨94091, by rfl⟩ : syracuseStep 501821 = 188183) (by norm_num)
theorem B1058885 : Blo 219811 1058885 := bbase (se 4 (by rfl) ⟨99270, by rfl⟩ : syracuseStep 1058885 = 198541) (by norm_num)
theorem B764005 : Blo 219811 764005 := bbase (se 4 (by rfl) ⟨71625, by rfl⟩ : syracuseStep 764005 = 143251) (by norm_num)
theorem B501893 : Blo 219811 501893 := bbase (se 4 (by rfl) ⟨47052, by rfl⟩ : syracuseStep 501893 = 94105) (by norm_num)
theorem B600229 : Blo 219811 600229 := bbase (se 4 (by rfl) ⟨56271, by rfl⟩ : syracuseStep 600229 = 112543) (by norm_num)
theorem B895157 : Blo 219811 895157 := bbase (se 5 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 895157 = 83921) (by norm_num)
theorem B501965 : Blo 219811 501965 := bbase (se 3 (by rfl) ⟨94118, by rfl⟩ : syracuseStep 501965 = 188237) (by norm_num)
theorem B502037 : Blo 219811 502037 := bbase (se 6 (by rfl) ⟨11766, by rfl⟩ : syracuseStep 502037 = 23533) (by norm_num)
theorem B370973 : Blo 219811 370973 := bbase (se 3 (by rfl) ⟨69557, by rfl⟩ : syracuseStep 370973 = 139115) (by norm_num)
theorem B502109 : Blo 219811 502109 := bbase (se 3 (by rfl) ⟨94145, by rfl⟩ : syracuseStep 502109 = 188291) (by norm_num)
theorem B371101 : Blo 219811 371101 := bbase (se 3 (by rfl) ⟨69581, by rfl⟩ : syracuseStep 371101 = 139163) (by norm_num)
theorem B502181 : Blo 219811 502181 := bbase (se 4 (by rfl) ⟨47079, by rfl⟩ : syracuseStep 502181 = 94159) (by norm_num)
theorem B502253 : Blo 219811 502253 := bbase (se 3 (by rfl) ⟨94172, by rfl⟩ : syracuseStep 502253 = 188345) (by norm_num)
theorem B371189 : Blo 219811 371189 := bbase (se 5 (by rfl) ⟨17399, by rfl⟩ : syracuseStep 371189 = 34799) (by norm_num)
theorem B633365 : Blo 219811 633365 := bbase (se 6 (by rfl) ⟨14844, by rfl⟩ : syracuseStep 633365 = 29689) (by norm_num)
theorem B502325 : Blo 219811 502325 := bbase (se 5 (by rfl) ⟨23546, by rfl⟩ : syracuseStep 502325 = 47093) (by norm_num)
theorem B502357 : Blo 219811 502357 := bbase (se 8 (by rfl) ⟨2943, by rfl⟩ : syracuseStep 502357 = 5887) (by norm_num)
theorem B371317 : Blo 219811 371317 := bbase (se 5 (by rfl) ⟨17405, by rfl⟩ : syracuseStep 371317 = 34811) (by norm_num)
theorem B502397 : Blo 219811 502397 := bbase (se 3 (by rfl) ⟨94199, by rfl⟩ : syracuseStep 502397 = 188399) (by norm_num)
theorem B1452725 : Blo 219811 1452725 := bbase (se 5 (by rfl) ⟨68096, by rfl⟩ : syracuseStep 1452725 = 136193) (by norm_num)
theorem B502469 : Blo 219811 502469 := bbase (se 4 (by rfl) ⟨47106, by rfl⟩ : syracuseStep 502469 = 94213) (by norm_num)
theorem B371405 : Blo 219811 371405 := bbase (se 3 (by rfl) ⟨69638, by rfl⟩ : syracuseStep 371405 = 139277) (by norm_num)
theorem B502541 : Blo 219811 502541 := bbase (se 3 (by rfl) ⟨94226, by rfl⟩ : syracuseStep 502541 = 188453) (by norm_num)
theorem B469813 : Blo 219811 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B371533 : Blo 219811 371533 := bbase (se 3 (by rfl) ⟨69662, by rfl⟩ : syracuseStep 371533 = 139325) (by norm_num)
theorem B502613 : Blo 219811 502613 := bbase (se 9 (by rfl) ⟨1472, by rfl⟩ : syracuseStep 502613 = 2945) (by norm_num)
theorem B502685 : Blo 219811 502685 := bbase (se 3 (by rfl) ⟨94253, by rfl⟩ : syracuseStep 502685 = 188507) (by norm_num)
theorem B371621 : Blo 219811 371621 := bbase (se 4 (by rfl) ⟨34839, by rfl⟩ : syracuseStep 371621 = 69679) (by norm_num)
theorem B502757 : Blo 219811 502757 := bbase (se 4 (by rfl) ⟨47133, by rfl⟩ : syracuseStep 502757 = 94267) (by norm_num)
theorem B568333 : Blo 219811 568333 := bbase (se 3 (by rfl) ⟨106562, by rfl⟩ : syracuseStep 568333 = 213125) (by norm_num)
theorem B371749 : Blo 219811 371749 := bbase (se 4 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 371749 = 69703) (by norm_num)
theorem B1125413 : Blo 219811 1125413 := bbase (se 4 (by rfl) ⟨105507, by rfl⟩ : syracuseStep 1125413 = 211015) (by norm_num)
theorem B502829 : Blo 219811 502829 := bbase (se 3 (by rfl) ⟨94280, by rfl⟩ : syracuseStep 502829 = 188561) (by norm_num)
theorem B502901 : Blo 219811 502901 := bbase (se 5 (by rfl) ⟨23573, by rfl⟩ : syracuseStep 502901 = 47147) (by norm_num)
theorem B371837 : Blo 219811 371837 := bbase (se 3 (by rfl) ⟨69719, by rfl⟩ : syracuseStep 371837 = 139439) (by norm_num)
theorem B535709 : Blo 219811 535709 := bbase (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) (by norm_num)
theorem B502973 : Blo 219811 502973 := bbase (se 3 (by rfl) ⟨94307, by rfl⟩ : syracuseStep 502973 = 188615) (by norm_num)
theorem B371965 : Blo 219811 371965 := bbase (se 3 (by rfl) ⟨69743, by rfl⟩ : syracuseStep 371965 = 139487) (by norm_num)
theorem B503045 : Blo 219811 503045 := bbase (se 4 (by rfl) ⟨47160, by rfl⟩ : syracuseStep 503045 = 94321) (by norm_num)
theorem B503117 : Blo 219811 503117 := bbase (se 3 (by rfl) ⟨94334, by rfl⟩ : syracuseStep 503117 = 188669) (by norm_num)
theorem B372053 : Blo 219811 372053 := bbase (se 11 (by rfl) ⟨272, by rfl⟩ : syracuseStep 372053 = 545) (by norm_num)
theorem B503189 : Blo 219811 503189 := bbase (se 6 (by rfl) ⟨11793, by rfl⟩ : syracuseStep 503189 = 23587) (by norm_num)
theorem B372181 : Blo 219811 372181 := bbase (se 7 (by rfl) ⟨4361, by rfl⟩ : syracuseStep 372181 = 8723) (by norm_num)
theorem B503261 : Blo 219811 503261 := bbase (se 3 (by rfl) ⟨94361, by rfl⟩ : syracuseStep 503261 = 188723) (by norm_num)
theorem B503333 : Blo 219811 503333 := bbase (se 4 (by rfl) ⟨47187, by rfl⟩ : syracuseStep 503333 = 94375) (by norm_num)
theorem B372269 : Blo 219811 372269 := bbase (se 3 (by rfl) ⟨69800, by rfl⟩ : syracuseStep 372269 = 139601) (by norm_num)
theorem B503405 : Blo 219811 503405 := bbase (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) (by norm_num)
theorem B568949 : Blo 219811 568949 := bbase (se 5 (by rfl) ⟨26669, by rfl⟩ : syracuseStep 568949 = 53339) (by norm_num)
theorem B470701 : Blo 219811 470701 := bbase (se 3 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 470701 = 176513) (by norm_num)
theorem B372397 : Blo 219811 372397 := bbase (se 3 (by rfl) ⟨69824, by rfl⟩ : syracuseStep 372397 = 139649) (by norm_num)
theorem B634549 : Blo 219811 634549 := bbase (se 5 (by rfl) ⟨29744, by rfl⟩ : syracuseStep 634549 = 59489) (by norm_num)
theorem B503477 : Blo 219811 503477 := bbase (se 5 (by rfl) ⟨23600, by rfl⟩ : syracuseStep 503477 = 47201) (by norm_num)
theorem B503549 : Blo 219811 503549 := bbase (se 3 (by rfl) ⟨94415, by rfl⟩ : syracuseStep 503549 = 188831) (by norm_num)
theorem B372485 : Blo 219811 372485 := bbase (se 4 (by rfl) ⟨34920, by rfl⟩ : syracuseStep 372485 = 69841) (by norm_num)
theorem B634709 : Blo 219811 634709 := bbase (se 9 (by rfl) ⟨1859, by rfl⟩ : syracuseStep 634709 = 3719) (by norm_num)
theorem B372613 : Blo 219811 372613 := bbase (se 4 (by rfl) ⟨34932, by rfl⟩ : syracuseStep 372613 = 69865) (by norm_num)
theorem B372701 : Blo 219811 372701 := bbase (se 3 (by rfl) ⟨69881, by rfl⟩ : syracuseStep 372701 = 139763) (by norm_num)
theorem B339965 : Blo 219811 339965 := bbase (se 3 (by rfl) ⟨63743, by rfl⟩ : syracuseStep 339965 = 127487) (by norm_num)
theorem B634949 : Blo 219811 634949 := bbase (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) (by norm_num)
theorem B372829 : Blo 219811 372829 := bbase (se 3 (by rfl) ⟨69905, by rfl⟩ : syracuseStep 372829 = 139811) (by norm_num)
theorem B471197 : Blo 219811 471197 := bbase (se 3 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 471197 = 176699) (by norm_num)
theorem B372917 : Blo 219811 372917 := bbase (se 5 (by rfl) ⟨17480, by rfl⟩ : syracuseStep 372917 = 34961) (by norm_num)
theorem B2699477 : Blo 219811 2699477 := bbase (se 7 (by rfl) ⟨31634, by rfl⟩ : syracuseStep 2699477 = 63269) (by norm_num)
theorem B635141 : Blo 219811 635141 := bbase (se 4 (by rfl) ⟨59544, by rfl⟩ : syracuseStep 635141 = 119089) (by norm_num)
theorem B373045 : Blo 219811 373045 := bbase (se 5 (by rfl) ⟨17486, by rfl⟩ : syracuseStep 373045 = 34973) (by norm_num)
theorem B1126709 : Blo 219811 1126709 := bbase (se 5 (by rfl) ⟨52814, by rfl⟩ : syracuseStep 1126709 = 105629) (by norm_num)
theorem B373133 : Blo 219811 373133 := bbase (se 3 (by rfl) ⟨69962, by rfl⟩ : syracuseStep 373133 = 139925) (by norm_num)
theorem B373261 : Blo 219811 373261 := bbase (se 3 (by rfl) ⟨69986, by rfl⟩ : syracuseStep 373261 = 139973) (by norm_num)
theorem B1683989 : Blo 219811 1683989 := bbase (se 6 (by rfl) ⟨39468, by rfl⟩ : syracuseStep 1683989 = 78937) (by norm_num)
theorem B373349 : Blo 219811 373349 := bbase (se 4 (by rfl) ⟨35001, by rfl⟩ : syracuseStep 373349 = 70003) (by norm_num)
theorem B373477 : Blo 219811 373477 := bbase (se 4 (by rfl) ⟨35013, by rfl⟩ : syracuseStep 373477 = 70027) (by norm_num)
theorem B373565 : Blo 219811 373565 := bbase (se 3 (by rfl) ⟨70043, by rfl⟩ : syracuseStep 373565 = 140087) (by norm_num)
theorem B373693 : Blo 219811 373693 := bbase (se 3 (by rfl) ⟨70067, by rfl⟩ : syracuseStep 373693 = 140135) (by norm_num)
theorem B1029077 : Blo 219811 1029077 := bbase (se 7 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 1029077 = 24119) (by norm_num)
theorem B472085 : Blo 219811 472085 := bbase (se 6 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 472085 = 22129) (by norm_num)
theorem B373781 : Blo 219811 373781 := bbase (se 6 (by rfl) ⟨8760, by rfl⟩ : syracuseStep 373781 = 17521) (by norm_num)
theorem B472205 : Blo 219811 472205 := bbase (se 3 (by rfl) ⟨88538, by rfl⟩ : syracuseStep 472205 = 177077) (by norm_num)
theorem B373909 : Blo 219811 373909 := bbase (se 6 (by rfl) ⟨8763, by rfl⟩ : syracuseStep 373909 = 17527) (by norm_num)
theorem B636133 : Blo 219811 636133 := bbase (se 4 (by rfl) ⟨59637, by rfl⟩ : syracuseStep 636133 = 119275) (by norm_num)
theorem B373997 : Blo 219811 373997 := bbase (se 3 (by rfl) ⟨70124, by rfl⟩ : syracuseStep 373997 = 140249) (by norm_num)
theorem B1193237 : Blo 219811 1193237 := bbase (se 6 (by rfl) ⟨27966, by rfl⟩ : syracuseStep 1193237 = 55933) (by norm_num)
theorem B374125 : Blo 219811 374125 := bbase (se 3 (by rfl) ⟨70148, by rfl⟩ : syracuseStep 374125 = 140297) (by norm_num)
theorem B374213 : Blo 219811 374213 := bbase (se 4 (by rfl) ⟨35082, by rfl⟩ : syracuseStep 374213 = 70165) (by norm_num)
theorem B603605 : Blo 219811 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B374341 : Blo 219811 374341 := bbase (se 4 (by rfl) ⟨35094, by rfl⟩ : syracuseStep 374341 = 70189) (by norm_num)
theorem B1128005 : Blo 219811 1128005 := bbase (se 4 (by rfl) ⟨105750, by rfl⟩ : syracuseStep 1128005 = 211501) (by norm_num)
theorem B374429 : Blo 219811 374429 := bbase (se 3 (by rfl) ⟨70205, by rfl⟩ : syracuseStep 374429 = 140411) (by norm_num)
theorem B669397 : Blo 219811 669397 := bbase (se 7 (by rfl) ⟨7844, by rfl⟩ : syracuseStep 669397 = 15689) (by norm_num)
theorem B898789 : Blo 219811 898789 := bbase (se 4 (by rfl) ⟨84261, by rfl⟩ : syracuseStep 898789 = 168523) (by norm_num)
theorem B472837 : Blo 219811 472837 := bbase (se 4 (by rfl) ⟨44328, by rfl⟩ : syracuseStep 472837 = 88657) (by norm_num)
theorem B374557 : Blo 219811 374557 := bbase (se 3 (by rfl) ⟨70229, by rfl⟩ : syracuseStep 374557 = 140459) (by norm_num)
theorem B374645 : Blo 219811 374645 := bbase (se 5 (by rfl) ⟨17561, by rfl⟩ : syracuseStep 374645 = 35123) (by norm_num)
theorem B604037 : Blo 219811 604037 := bbase (se 4 (by rfl) ⟨56628, by rfl⟩ : syracuseStep 604037 = 113257) (by norm_num)
theorem B374773 : Blo 219811 374773 := bbase (se 5 (by rfl) ⟨17567, by rfl⟩ : syracuseStep 374773 = 35135) (by norm_num)
theorem B374861 : Blo 219811 374861 := bbase (se 3 (by rfl) ⟨70286, by rfl⟩ : syracuseStep 374861 = 140573) (by norm_num)
theorem B374989 : Blo 219811 374989 := bbase (se 3 (by rfl) ⟨70310, by rfl⟩ : syracuseStep 374989 = 140621) (by norm_num)
theorem B375077 : Blo 219811 375077 := bbase (se 4 (by rfl) ⟨35163, by rfl⟩ : syracuseStep 375077 = 70327) (by norm_num)
theorem B637237 : Blo 219811 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B375205 : Blo 219811 375205 := bbase (se 4 (by rfl) ⟨35175, by rfl⟩ : syracuseStep 375205 = 70351) (by norm_num)
theorem B375293 : Blo 219811 375293 := bbase (se 3 (by rfl) ⟨70367, by rfl⟩ : syracuseStep 375293 = 140735) (by norm_num)
theorem B473725 : Blo 219811 473725 := bbase (se 3 (by rfl) ⟨88823, by rfl⟩ : syracuseStep 473725 = 177647) (by norm_num)
theorem B375421 : Blo 219811 375421 := bbase (se 3 (by rfl) ⟨70391, by rfl⟩ : syracuseStep 375421 = 140783) (by norm_num)
theorem B375509 : Blo 219811 375509 := bbase (se 7 (by rfl) ⟨4400, by rfl⟩ : syracuseStep 375509 = 8801) (by norm_num)
theorem B473845 : Blo 219811 473845 := bbase (se 5 (by rfl) ⟨22211, by rfl⟩ : syracuseStep 473845 = 44423) (by norm_num)
theorem B3783509 : Blo 219811 3783509 := bbase (se 9 (by rfl) ⟨11084, by rfl⟩ : syracuseStep 3783509 = 22169) (by norm_num)
theorem B375637 : Blo 219811 375637 := bbase (se 9 (by rfl) ⟨1100, by rfl⟩ : syracuseStep 375637 = 2201) (by norm_num)
theorem B1129301 : Blo 219811 1129301 := bbase (se 9 (by rfl) ⟨3308, by rfl⟩ : syracuseStep 1129301 = 6617) (by norm_num)
theorem B375725 : Blo 219811 375725 := bbase (se 3 (by rfl) ⟨70448, by rfl⟩ : syracuseStep 375725 = 140897) (by norm_num)
theorem B1391573 : Blo 219811 1391573 := bbase (se 7 (by rfl) ⟨16307, by rfl⟩ : syracuseStep 1391573 = 32615) (by norm_num)
theorem B474101 : Blo 219811 474101 := bbase (se 5 (by rfl) ⟨22223, by rfl⟩ : syracuseStep 474101 = 44447) (by norm_num)
theorem B1424405 : Blo 219811 1424405 := bbase (se 6 (by rfl) ⟨33384, by rfl⟩ : syracuseStep 1424405 = 66769) (by norm_num)
theorem B375853 : Blo 219811 375853 := bbase (se 3 (by rfl) ⟨70472, by rfl⟩ : syracuseStep 375853 = 140945) (by norm_num)
theorem B375941 : Blo 219811 375941 := bbase (se 4 (by rfl) ⟨35244, by rfl⟩ : syracuseStep 375941 = 70489) (by norm_num)
theorem B802037 : Blo 219811 802037 := bbase (se 5 (by rfl) ⟨37595, by rfl⟩ : syracuseStep 802037 = 75191) (by norm_num)
theorem B376069 : Blo 219811 376069 := bbase (se 4 (by rfl) ⟨35256, by rfl⟩ : syracuseStep 376069 = 70513) (by norm_num)
theorem B376157 : Blo 219811 376157 := bbase (se 3 (by rfl) ⟨70529, by rfl⟩ : syracuseStep 376157 = 141059) (by norm_num)
theorem B4078997 : Blo 219811 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B376285 : Blo 219811 376285 := bbase (se 3 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 376285 = 141107) (by norm_num)
theorem B376373 : Blo 219811 376373 := bbase (se 5 (by rfl) ⟨17642, by rfl⟩ : syracuseStep 376373 = 35285) (by norm_num)
theorem B638533 : Blo 219811 638533 := bbase (se 4 (by rfl) ⟨59862, by rfl⟩ : syracuseStep 638533 = 119725) (by norm_num)
theorem B2014901 : Blo 219811 2014901 := bbase (se 5 (by rfl) ⟨94448, by rfl⟩ : syracuseStep 2014901 = 188897) (by norm_num)
theorem B376501 : Blo 219811 376501 := bbase (se 5 (by rfl) ⟨17648, by rfl⟩ : syracuseStep 376501 = 35297) (by norm_num)
theorem B278245 : Blo 219811 278245 := bbase (se 4 (by rfl) ⟨26085, by rfl⟩ : syracuseStep 278245 = 52171) (by norm_num)
theorem B376589 : Blo 219811 376589 := bbase (se 3 (by rfl) ⟨70610, by rfl⟩ : syracuseStep 376589 = 141221) (by norm_num)
theorem B474989 : Blo 219811 474989 := bbase (se 3 (by rfl) ⟨89060, by rfl⟩ : syracuseStep 474989 = 178121) (by norm_num)
theorem B376717 : Blo 219811 376717 := bbase (se 3 (by rfl) ⟨70634, by rfl⟩ : syracuseStep 376717 = 141269) (by norm_num)
theorem B278417 : Blo 219811 278417 := bbase (se 2 (by rfl) ⟨104406, by rfl⟩ : syracuseStep 278417 = 208813) (by norm_num)
theorem B278473 : Blo 219811 278473 := bbase (se 2 (by rfl) ⟨104427, by rfl⟩ : syracuseStep 278473 = 208855) (by norm_num)
theorem B835541 : Blo 219811 835541 := bbase (se 7 (by rfl) ⟨9791, by rfl⟩ : syracuseStep 835541 = 19583) (by norm_num)
theorem B376805 : Blo 219811 376805 := bbase (se 4 (by rfl) ⟨35325, by rfl⟩ : syracuseStep 376805 = 70651) (by norm_num)
theorem B278569 : Blo 219811 278569 := bbase (se 2 (by rfl) ⟨104463, by rfl⟩ : syracuseStep 278569 = 208927) (by norm_num)
theorem B475229 : Blo 219811 475229 := bbase (se 3 (by rfl) ⟨89105, by rfl⟩ : syracuseStep 475229 = 178211) (by norm_num)
theorem B1130597 : Blo 219811 1130597 := bbase (se 4 (by rfl) ⟨105993, by rfl⟩ : syracuseStep 1130597 = 211987) (by norm_num)
theorem B376933 : Blo 219811 376933 := bbase (se 4 (by rfl) ⟨35337, by rfl⟩ : syracuseStep 376933 = 70675) (by norm_num)
theorem B704693 : Blo 219811 704693 := bbase (se 5 (by rfl) ⟨33032, by rfl⟩ : syracuseStep 704693 = 66065) (by norm_num)
theorem B377021 : Blo 219811 377021 := bbase (se 3 (by rfl) ⟨70691, by rfl⟩ : syracuseStep 377021 = 141383) (by norm_num)
theorem B278741 : Blo 219811 278741 := bbase (se 7 (by rfl) ⟨3266, by rfl⟩ : syracuseStep 278741 = 6533) (by norm_num)
theorem B835829 : Blo 219811 835829 := bbase (se 5 (by rfl) ⟨39179, by rfl⟩ : syracuseStep 835829 = 78359) (by norm_num)
theorem B278797 : Blo 219811 278797 := bbase (se 3 (by rfl) ⟨52274, by rfl⟩ : syracuseStep 278797 = 104549) (by norm_num)
theorem B377149 : Blo 219811 377149 := bbase (se 3 (by rfl) ⟨70715, by rfl⟩ : syracuseStep 377149 = 141431) (by norm_num)
theorem B278893 : Blo 219811 278893 := bbase (se 3 (by rfl) ⟨52292, by rfl⟩ : syracuseStep 278893 = 104585) (by norm_num)
theorem B377237 : Blo 219811 377237 := bbase (se 6 (by rfl) ⟨8841, by rfl⟩ : syracuseStep 377237 = 17683) (by norm_num)
theorem B377365 : Blo 219811 377365 := bbase (se 6 (by rfl) ⟨8844, by rfl⟩ : syracuseStep 377365 = 17689) (by norm_num)
theorem B279065 : Blo 219811 279065 := bbase (se 2 (by rfl) ⟨104649, by rfl⟩ : syracuseStep 279065 = 209299) (by norm_num)
theorem B279121 : Blo 219811 279121 := bbase (se 2 (by rfl) ⟨104670, by rfl⟩ : syracuseStep 279121 = 209341) (by norm_num)
theorem B475733 : Blo 219811 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B475741 : Blo 219811 475741 := bbase (se 3 (by rfl) ⟨89201, by rfl⟩ : syracuseStep 475741 = 178403) (by norm_num)
theorem B377453 : Blo 219811 377453 := bbase (se 3 (by rfl) ⟨70772, by rfl⟩ : syracuseStep 377453 = 141545) (by norm_num)
theorem B279217 : Blo 219811 279217 := bbase (se 2 (by rfl) ⟨104706, by rfl⟩ : syracuseStep 279217 = 209413) (by norm_num)
theorem B377581 : Blo 219811 377581 := bbase (se 3 (by rfl) ⟨70796, by rfl⟩ : syracuseStep 377581 = 141593) (by norm_num)
theorem B377669 : Blo 219811 377669 := bbase (se 4 (by rfl) ⟨35406, by rfl⟩ : syracuseStep 377669 = 70813) (by norm_num)
theorem B279389 : Blo 219811 279389 := bbase (se 3 (by rfl) ⟨52385, by rfl⟩ : syracuseStep 279389 = 104771) (by norm_num)
theorem B279445 : Blo 219811 279445 := bbase (se 6 (by rfl) ⟨6549, by rfl⟩ : syracuseStep 279445 = 13099) (by norm_num)
theorem B279541 : Blo 219811 279541 := bbase (se 5 (by rfl) ⟨13103, by rfl⟩ : syracuseStep 279541 = 26207) (by norm_num)
theorem B1197109 : Blo 219811 1197109 := bbase (se 5 (by rfl) ⟨56114, by rfl⟩ : syracuseStep 1197109 = 112229) (by norm_num)
theorem B279713 : Blo 219811 279713 := bbase (se 2 (by rfl) ⟨104892, by rfl⟩ : syracuseStep 279713 = 209785) (by norm_num)
theorem B279769 : Blo 219811 279769 := bbase (se 2 (by rfl) ⟨104913, by rfl⟩ : syracuseStep 279769 = 209827) (by norm_num)
theorem B279865 : Blo 219811 279865 := bbase (se 2 (by rfl) ⟨104949, by rfl⟩ : syracuseStep 279865 = 209899) (by norm_num)
theorem B1131893 : Blo 219811 1131893 := bbase (se 5 (by rfl) ⟨53057, by rfl⟩ : syracuseStep 1131893 = 106115) (by norm_num)
theorem B837013 : Blo 219811 837013 := bbase (se 6 (by rfl) ⟨19617, by rfl⟩ : syracuseStep 837013 = 39235) (by norm_num)
theorem B476621 : Blo 219811 476621 := bbase (se 3 (by rfl) ⟨89366, by rfl⟩ : syracuseStep 476621 = 178733) (by norm_num)
theorem B378341 : Blo 219811 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B280037 : Blo 219811 280037 := bbase (se 4 (by rfl) ⟨26253, by rfl⟩ : syracuseStep 280037 = 52507) (by norm_num)
theorem B247297 : Blo 219811 247297 := bbase (se 2 (by rfl) ⟨92736, by rfl⟩ : syracuseStep 247297 = 185473) (by norm_num)
theorem B280093 : Blo 219811 280093 := bbase (se 3 (by rfl) ⟨52517, by rfl⟩ : syracuseStep 280093 = 105035) (by norm_num)
theorem B247333 : Blo 219811 247333 := bbase (se 4 (by rfl) ⟨23187, by rfl⟩ : syracuseStep 247333 = 46375) (by norm_num)
theorem B1525301 : Blo 219811 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B706117 : Blo 219811 706117 := bbase (se 4 (by rfl) ⟨66198, by rfl⟩ : syracuseStep 706117 = 132397) (by norm_num)
theorem B247369 : Blo 219811 247369 := bbase (se 2 (by rfl) ⟨92763, by rfl⟩ : syracuseStep 247369 = 185527) (by norm_num)
theorem B247405 : Blo 219811 247405 := bbase (se 3 (by rfl) ⟨46388, by rfl⟩ : syracuseStep 247405 = 92777) (by norm_num)
theorem B1263221 : Blo 219811 1263221 := bbase (se 5 (by rfl) ⟨59213, by rfl⟩ : syracuseStep 1263221 = 118427) (by norm_num)
theorem B280189 : Blo 219811 280189 := bbase (se 3 (by rfl) ⟨52535, by rfl⟩ : syracuseStep 280189 = 105071) (by norm_num)
theorem B247441 : Blo 219811 247441 := bbase (se 2 (by rfl) ⟨92790, by rfl⟩ : syracuseStep 247441 = 185581) (by norm_num)
theorem B247477 : Blo 219811 247477 := bbase (se 5 (by rfl) ⟨11600, by rfl⟩ : syracuseStep 247477 = 23201) (by norm_num)
theorem B837317 : Blo 219811 837317 := bbase (se 4 (by rfl) ⟨78498, by rfl⟩ : syracuseStep 837317 = 156997) (by norm_num)
theorem B476869 : Blo 219811 476869 := bbase (se 4 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 476869 = 89413) (by norm_num)
theorem B1066709 : Blo 219811 1066709 := bbase (se 7 (by rfl) ⟨12500, by rfl⟩ : syracuseStep 1066709 = 25001) (by norm_num)
theorem B247513 : Blo 219811 247513 := bbase (se 2 (by rfl) ⟨92817, by rfl⟩ : syracuseStep 247513 = 185635) (by norm_num)
theorem B1623797 : Blo 219811 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B247549 : Blo 219811 247549 := bbase (se 3 (by rfl) ⟨46415, by rfl⟩ : syracuseStep 247549 = 92831) (by norm_num)
theorem B247585 : Blo 219811 247585 := bbase (se 2 (by rfl) ⟨92844, by rfl⟩ : syracuseStep 247585 = 185689) (by norm_num)
theorem B280361 : Blo 219811 280361 := bbase (se 2 (by rfl) ⟨105135, by rfl⟩ : syracuseStep 280361 = 210271) (by norm_num)
theorem B247621 : Blo 219811 247621 := bbase (se 4 (by rfl) ⟨23214, by rfl⟩ : syracuseStep 247621 = 46429) (by norm_num)
theorem B280417 : Blo 219811 280417 := bbase (se 2 (by rfl) ⟨105156, by rfl⟩ : syracuseStep 280417 = 210313) (by norm_num)
theorem B247657 : Blo 219811 247657 := bbase (se 2 (by rfl) ⟨92871, by rfl⟩ : syracuseStep 247657 = 185743) (by norm_num)
theorem B247693 : Blo 219811 247693 := bbase (se 3 (by rfl) ⟨46442, by rfl⟩ : syracuseStep 247693 = 92885) (by norm_num)
theorem B313237 : Blo 219811 313237 := bbase (se 6 (by rfl) ⟨7341, by rfl⟩ : syracuseStep 313237 = 14683) (by norm_num)
theorem B247729 : Blo 219811 247729 := bbase (se 2 (by rfl) ⟨92898, by rfl⟩ : syracuseStep 247729 = 185797) (by norm_num)
theorem B280513 : Blo 219811 280513 := bbase (se 2 (by rfl) ⟨105192, by rfl⟩ : syracuseStep 280513 = 210385) (by norm_num)
theorem B247765 : Blo 219811 247765 := bbase (se 7 (by rfl) ⟨2903, by rfl⟩ : syracuseStep 247765 = 5807) (by norm_num)
theorem B247801 : Blo 219811 247801 := bbase (se 2 (by rfl) ⟨92925, by rfl⟩ : syracuseStep 247801 = 185851) (by norm_num)
theorem B247837 : Blo 219811 247837 := bbase (se 3 (by rfl) ⟨46469, by rfl⟩ : syracuseStep 247837 = 92939) (by norm_num)
theorem B477245 : Blo 219811 477245 := bbase (se 3 (by rfl) ⟨89483, by rfl⟩ : syracuseStep 477245 = 178967) (by norm_num)
theorem B247873 : Blo 219811 247873 := bbase (se 2 (by rfl) ⟨92952, by rfl⟩ : syracuseStep 247873 = 185905) (by norm_num)
theorem B1198165 : Blo 219811 1198165 := bbase (se 8 (by rfl) ⟨7020, by rfl⟩ : syracuseStep 1198165 = 14041) (by norm_num)
theorem B247909 : Blo 219811 247909 := bbase (se 4 (by rfl) ⟨23241, by rfl⟩ : syracuseStep 247909 = 46483) (by norm_num)
theorem B280685 : Blo 219811 280685 := bbase (se 3 (by rfl) ⟨52628, by rfl⟩ : syracuseStep 280685 = 105257) (by norm_num)
theorem B247945 : Blo 219811 247945 := bbase (se 2 (by rfl) ⟨92979, by rfl⟩ : syracuseStep 247945 = 185959) (by norm_num)
theorem B280741 : Blo 219811 280741 := bbase (se 4 (by rfl) ⟨26319, by rfl⟩ : syracuseStep 280741 = 52639) (by norm_num)
theorem B247981 : Blo 219811 247981 := bbase (se 3 (by rfl) ⟨46496, by rfl⟩ : syracuseStep 247981 = 92993) (by norm_num)
theorem B248017 : Blo 219811 248017 := bbase (se 2 (by rfl) ⟨93006, by rfl⟩ : syracuseStep 248017 = 186013) (by norm_num)
theorem B313573 : Blo 219811 313573 := bbase (se 4 (by rfl) ⟨29397, by rfl⟩ : syracuseStep 313573 = 58795) (by norm_num)
theorem B248053 : Blo 219811 248053 := bbase (se 5 (by rfl) ⟨11627, by rfl⟩ : syracuseStep 248053 = 23255) (by norm_num)
theorem B903413 : Blo 219811 903413 := bbase (se 5 (by rfl) ⟨42347, by rfl⟩ : syracuseStep 903413 = 84695) (by norm_num)
theorem B280837 : Blo 219811 280837 := bbase (se 4 (by rfl) ⟨26328, by rfl⟩ : syracuseStep 280837 = 52657) (by norm_num)
theorem B248089 : Blo 219811 248089 := bbase (se 2 (by rfl) ⟨93033, by rfl⟩ : syracuseStep 248089 = 186067) (by norm_num)
theorem B248125 : Blo 219811 248125 := bbase (se 3 (by rfl) ⟨46523, by rfl⟩ : syracuseStep 248125 = 93047) (by norm_num)
theorem B248161 : Blo 219811 248161 := bbase (se 2 (by rfl) ⟨93060, by rfl⟩ : syracuseStep 248161 = 186121) (by norm_num)
theorem B248197 : Blo 219811 248197 := bbase (se 4 (by rfl) ⟨23268, by rfl⟩ : syracuseStep 248197 = 46537) (by norm_num)
theorem B248233 : Blo 219811 248233 := bbase (se 2 (by rfl) ⟨93087, by rfl⟩ : syracuseStep 248233 = 186175) (by norm_num)
theorem B281009 : Blo 219811 281009 := bbase (se 2 (by rfl) ⟨105378, by rfl⟩ : syracuseStep 281009 = 210757) (by norm_num)
theorem B313789 : Blo 219811 313789 := bbase (se 3 (by rfl) ⟨58835, by rfl⟩ : syracuseStep 313789 = 117671) (by norm_num)
theorem B248269 : Blo 219811 248269 := bbase (se 3 (by rfl) ⟨46550, by rfl⟩ : syracuseStep 248269 = 93101) (by norm_num)
theorem B281065 : Blo 219811 281065 := bbase (se 2 (by rfl) ⟨105399, by rfl⟩ : syracuseStep 281065 = 210799) (by norm_num)
theorem B248305 : Blo 219811 248305 := bbase (se 2 (by rfl) ⟨93114, by rfl⟩ : syracuseStep 248305 = 186229) (by norm_num)
theorem B248341 : Blo 219811 248341 := bbase (se 6 (by rfl) ⟨5820, by rfl⟩ : syracuseStep 248341 = 11641) (by norm_num)
theorem B248377 : Blo 219811 248377 := bbase (se 2 (by rfl) ⟨93141, by rfl⟩ : syracuseStep 248377 = 186283) (by norm_num)
theorem B281161 : Blo 219811 281161 := bbase (se 2 (by rfl) ⟨105435, by rfl⟩ : syracuseStep 281161 = 210871) (by norm_num)
theorem B248413 : Blo 219811 248413 := bbase (se 3 (by rfl) ⟨46577, by rfl⟩ : syracuseStep 248413 = 93155) (by norm_num)
theorem B248449 : Blo 219811 248449 := bbase (se 2 (by rfl) ⟨93168, by rfl⟩ : syracuseStep 248449 = 186337) (by norm_num)
theorem B248485 : Blo 219811 248485 := bbase (se 4 (by rfl) ⟨23295, by rfl⟩ : syracuseStep 248485 = 46591) (by norm_num)
theorem B510637 : Blo 219811 510637 := bbase (se 3 (by rfl) ⟨95744, by rfl⟩ : syracuseStep 510637 = 191489) (by norm_num)
theorem B248521 : Blo 219811 248521 := bbase (se 2 (by rfl) ⟨93195, by rfl⟩ : syracuseStep 248521 = 186391) (by norm_num)
theorem B248557 : Blo 219811 248557 := bbase (se 3 (by rfl) ⟨46604, by rfl⟩ : syracuseStep 248557 = 93209) (by norm_num)
theorem B281333 : Blo 219811 281333 := bbase (se 5 (by rfl) ⟨13187, by rfl⟩ : syracuseStep 281333 = 26375) (by norm_num)
theorem B248593 : Blo 219811 248593 := bbase (se 2 (by rfl) ⟨93222, by rfl⟩ : syracuseStep 248593 = 186445) (by norm_num)
theorem B510749 : Blo 219811 510749 := bbase (se 3 (by rfl) ⟨95765, by rfl⟩ : syracuseStep 510749 = 191531) (by norm_num)
theorem B281389 : Blo 219811 281389 := bbase (se 3 (by rfl) ⟨52760, by rfl⟩ : syracuseStep 281389 = 105521) (by norm_num)
theorem B314165 : Blo 219811 314165 := bbase (se 5 (by rfl) ⟨14726, by rfl⟩ : syracuseStep 314165 = 29453) (by norm_num)
theorem B248629 : Blo 219811 248629 := bbase (se 5 (by rfl) ⟨11654, by rfl⟩ : syracuseStep 248629 = 23309) (by norm_num)
theorem B248665 : Blo 219811 248665 := bbase (se 2 (by rfl) ⟨93249, by rfl⟩ : syracuseStep 248665 = 186499) (by norm_num)
theorem B248701 : Blo 219811 248701 := bbase (se 3 (by rfl) ⟨46631, by rfl⟩ : syracuseStep 248701 = 93263) (by norm_num)
theorem B281485 : Blo 219811 281485 := bbase (se 3 (by rfl) ⟨52778, by rfl⟩ : syracuseStep 281485 = 105557) (by norm_num)
theorem B248737 : Blo 219811 248737 := bbase (se 2 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 248737 = 186553) (by norm_num)
theorem B248773 : Blo 219811 248773 := bbase (se 4 (by rfl) ⟨23322, by rfl⟩ : syracuseStep 248773 = 46645) (by norm_num)
theorem B248809 : Blo 219811 248809 := bbase (se 2 (by rfl) ⟨93303, by rfl⟩ : syracuseStep 248809 = 186607) (by norm_num)
theorem B248845 : Blo 219811 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B248881 : Blo 219811 248881 := bbase (se 2 (by rfl) ⟨93330, by rfl⟩ : syracuseStep 248881 = 186661) (by norm_num)
theorem B281657 : Blo 219811 281657 := bbase (se 2 (by rfl) ⟨105621, by rfl⟩ : syracuseStep 281657 = 211243) (by norm_num)
theorem B248917 : Blo 219811 248917 := bbase (se 8 (by rfl) ⟨1458, by rfl⟩ : syracuseStep 248917 = 2917) (by norm_num)
theorem B281713 : Blo 219811 281713 := bbase (se 2 (by rfl) ⟨105642, by rfl⟩ : syracuseStep 281713 = 211285) (by norm_num)
theorem B248953 : Blo 219811 248953 := bbase (se 2 (by rfl) ⟨93357, by rfl⟩ : syracuseStep 248953 = 186715) (by norm_num)
theorem B707717 : Blo 219811 707717 := bbase (se 4 (by rfl) ⟨66348, by rfl⟩ : syracuseStep 707717 = 132697) (by norm_num)
theorem B248989 : Blo 219811 248989 := bbase (se 3 (by rfl) ⟨46685, by rfl⟩ : syracuseStep 248989 = 93371) (by norm_num)
theorem B249025 : Blo 219811 249025 := bbase (se 2 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 249025 = 186769) (by norm_num)
theorem B281809 : Blo 219811 281809 := bbase (se 2 (by rfl) ⟨105678, by rfl⟩ : syracuseStep 281809 = 211357) (by norm_num)
theorem B249061 : Blo 219811 249061 := bbase (se 4 (by rfl) ⟨23349, by rfl⟩ : syracuseStep 249061 = 46699) (by norm_num)
theorem B249097 : Blo 219811 249097 := bbase (se 2 (by rfl) ⟨93411, by rfl⟩ : syracuseStep 249097 = 186823) (by norm_num)
theorem B249133 : Blo 219811 249133 := bbase (se 3 (by rfl) ⟨46712, by rfl⟩ : syracuseStep 249133 = 93425) (by norm_num)
theorem B249169 : Blo 219811 249169 := bbase (se 2 (by rfl) ⟨93438, by rfl⟩ : syracuseStep 249169 = 186877) (by norm_num)
theorem B249205 : Blo 219811 249205 := bbase (se 5 (by rfl) ⟨11681, by rfl⟩ : syracuseStep 249205 = 23363) (by norm_num)
theorem B281981 : Blo 219811 281981 := bbase (se 3 (by rfl) ⟨52871, by rfl⟩ : syracuseStep 281981 = 105743) (by norm_num)
theorem B249241 : Blo 219811 249241 := bbase (se 2 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 249241 = 186931) (by norm_num)
theorem B282037 : Blo 219811 282037 := bbase (se 5 (by rfl) ⟨13220, by rfl⟩ : syracuseStep 282037 = 26441) (by norm_num)
theorem B249277 : Blo 219811 249277 := bbase (se 3 (by rfl) ⟨46739, by rfl⟩ : syracuseStep 249277 = 93479) (by norm_num)
theorem B282053 : Blo 219811 282053 := bbase (se 4 (by rfl) ⟨26442, by rfl⟩ : syracuseStep 282053 = 52885) (by norm_num)
theorem B249313 : Blo 219811 249313 := bbase (se 2 (by rfl) ⟨93492, by rfl⟩ : syracuseStep 249313 = 186985) (by norm_num)
theorem B249349 : Blo 219811 249349 := bbase (se 4 (by rfl) ⟨23376, by rfl⟩ : syracuseStep 249349 = 46753) (by norm_num)
theorem B282133 : Blo 219811 282133 := bbase (se 6 (by rfl) ⟨6612, by rfl⟩ : syracuseStep 282133 = 13225) (by norm_num)
theorem B249385 : Blo 219811 249385 := bbase (se 2 (by rfl) ⟨93519, by rfl⟩ : syracuseStep 249385 = 187039) (by norm_num)
theorem B249421 : Blo 219811 249421 := bbase (se 3 (by rfl) ⟨46766, by rfl⟩ : syracuseStep 249421 = 93533) (by norm_num)
theorem B609893 : Blo 219811 609893 := bbase (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) (by norm_num)
theorem B249457 : Blo 219811 249457 := bbase (se 2 (by rfl) ⟨93546, by rfl⟩ : syracuseStep 249457 = 187093) (by norm_num)
theorem B446069 : Blo 219811 446069 := bbase (se 5 (by rfl) ⟨20909, by rfl⟩ : syracuseStep 446069 = 41819) (by norm_num)
theorem B249493 : Blo 219811 249493 := bbase (se 6 (by rfl) ⟨5847, by rfl⟩ : syracuseStep 249493 = 11695) (by norm_num)
theorem B249529 : Blo 219811 249529 := bbase (se 2 (by rfl) ⟨93573, by rfl⟩ : syracuseStep 249529 = 187147) (by norm_num)
theorem B478909 : Blo 219811 478909 := bbase (se 3 (by rfl) ⟨89795, by rfl⟩ : syracuseStep 478909 = 179591) (by norm_num)
theorem B282305 : Blo 219811 282305 := bbase (se 2 (by rfl) ⟨105864, by rfl⟩ : syracuseStep 282305 = 211729) (by norm_num)
theorem B249565 : Blo 219811 249565 := bbase (se 3 (by rfl) ⟨46793, by rfl⟩ : syracuseStep 249565 = 93587) (by norm_num)
theorem B282361 : Blo 219811 282361 := bbase (se 2 (by rfl) ⟨105885, by rfl⟩ : syracuseStep 282361 = 211771) (by norm_num)
theorem B249601 : Blo 219811 249601 := bbase (se 2 (by rfl) ⟨93600, by rfl⟩ : syracuseStep 249601 = 187201) (by norm_num)
theorem B839429 : Blo 219811 839429 := bbase (se 4 (by rfl) ⟨78696, by rfl⟩ : syracuseStep 839429 = 157393) (by norm_num)
theorem B249637 : Blo 219811 249637 := bbase (se 4 (by rfl) ⟨23403, by rfl⟩ : syracuseStep 249637 = 46807) (by norm_num)
theorem B249673 : Blo 219811 249673 := bbase (se 2 (by rfl) ⟨93627, by rfl⟩ : syracuseStep 249673 = 187255) (by norm_num)
theorem B2117461 : Blo 219811 2117461 := bbase (se 9 (by rfl) ⟨6203, by rfl⟩ : syracuseStep 2117461 = 12407) (by norm_num)
theorem B282457 : Blo 219811 282457 := bbase (se 2 (by rfl) ⟨105921, by rfl⟩ : syracuseStep 282457 = 211843) (by norm_num)
theorem B249709 : Blo 219811 249709 := bbase (se 3 (by rfl) ⟨46820, by rfl⟩ : syracuseStep 249709 = 93641) (by norm_num)
theorem B249745 : Blo 219811 249745 := bbase (se 2 (by rfl) ⟨93654, by rfl⟩ : syracuseStep 249745 = 187309) (by norm_num)
theorem B249781 : Blo 219811 249781 := bbase (se 5 (by rfl) ⟨11708, by rfl⟩ : syracuseStep 249781 = 23417) (by norm_num)
theorem B249817 : Blo 219811 249817 := bbase (se 2 (by rfl) ⟨93681, by rfl⟩ : syracuseStep 249817 = 187363) (by norm_num)
theorem B249853 : Blo 219811 249853 := bbase (se 3 (by rfl) ⟨46847, by rfl⟩ : syracuseStep 249853 = 93695) (by norm_num)
theorem B282629 : Blo 219811 282629 := bbase (se 4 (by rfl) ⟨26496, by rfl⟩ : syracuseStep 282629 = 52993) (by norm_num)
theorem B249889 : Blo 219811 249889 := bbase (se 2 (by rfl) ⟨93708, by rfl⟩ : syracuseStep 249889 = 187417) (by norm_num)
theorem B839717 : Blo 219811 839717 := bbase (se 4 (by rfl) ⟨78723, by rfl⟩ : syracuseStep 839717 = 157447) (by norm_num)
theorem B282685 : Blo 219811 282685 := bbase (se 3 (by rfl) ⟨53003, by rfl⟩ : syracuseStep 282685 = 106007) (by norm_num)
theorem B249925 : Blo 219811 249925 := bbase (se 4 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 249925 = 46861) (by norm_num)
theorem B249961 : Blo 219811 249961 := bbase (se 2 (by rfl) ⟨93735, by rfl⟩ : syracuseStep 249961 = 187471) (by norm_num)
theorem B1691765 : Blo 219811 1691765 := bbase (se 5 (by rfl) ⟨79301, by rfl⟩ : syracuseStep 1691765 = 158603) (by norm_num)
theorem B249997 : Blo 219811 249997 := bbase (se 3 (by rfl) ⟨46874, by rfl⟩ : syracuseStep 249997 = 93749) (by norm_num)
theorem B282781 : Blo 219811 282781 := bbase (se 3 (by rfl) ⟨53021, by rfl⟩ : syracuseStep 282781 = 106043) (by norm_num)
theorem B512173 : Blo 219811 512173 := bbase (se 3 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 512173 = 192065) (by norm_num)
theorem B250033 : Blo 219811 250033 := bbase (se 2 (by rfl) ⟨93762, by rfl⟩ : syracuseStep 250033 = 187525) (by norm_num)
theorem B643253 : Blo 219811 643253 := bbase (se 5 (by rfl) ⟨30152, by rfl⟩ : syracuseStep 643253 = 60305) (by norm_num)
theorem B315589 : Blo 219811 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B708821 : Blo 219811 708821 := bbase (se 7 (by rfl) ⟨8306, by rfl⟩ : syracuseStep 708821 = 16613) (by norm_num)
theorem B250069 : Blo 219811 250069 := bbase (se 7 (by rfl) ⟨2930, by rfl⟩ : syracuseStep 250069 = 5861) (by norm_num)
theorem B250105 : Blo 219811 250105 := bbase (se 2 (by rfl) ⟨93789, by rfl⟩ : syracuseStep 250105 = 187579) (by norm_num)
theorem B250141 : Blo 219811 250141 := bbase (se 3 (by rfl) ⟨46901, by rfl⟩ : syracuseStep 250141 = 93803) (by norm_num)
theorem B250177 : Blo 219811 250177 := bbase (se 2 (by rfl) ⟨93816, by rfl⟩ : syracuseStep 250177 = 187633) (by norm_num)
theorem B282953 : Blo 219811 282953 := bbase (se 2 (by rfl) ⟨106107, by rfl⟩ : syracuseStep 282953 = 212215) (by norm_num)
theorem B250213 : Blo 219811 250213 := bbase (se 4 (by rfl) ⟨23457, by rfl⟩ : syracuseStep 250213 = 46915) (by norm_num)
theorem B283009 : Blo 219811 283009 := bbase (se 2 (by rfl) ⟨106128, by rfl⟩ : syracuseStep 283009 = 212257) (by norm_num)
theorem B250249 : Blo 219811 250249 := bbase (se 2 (by rfl) ⟨93843, by rfl⟩ : syracuseStep 250249 = 187687) (by norm_num)
theorem B250285 : Blo 219811 250285 := bbase (se 3 (by rfl) ⟨46928, by rfl⟩ : syracuseStep 250285 = 93857) (by norm_num)
theorem B250321 : Blo 219811 250321 := bbase (se 2 (by rfl) ⟨93870, by rfl⟩ : syracuseStep 250321 = 187741) (by norm_num)
theorem B283105 : Blo 219811 283105 := bbase (se 2 (by rfl) ⟨106164, by rfl⟩ : syracuseStep 283105 = 212329) (by norm_num)
theorem B250357 : Blo 219811 250357 := bbase (se 5 (by rfl) ⟨11735, by rfl⟩ : syracuseStep 250357 = 23471) (by norm_num)
theorem B250393 : Blo 219811 250393 := bbase (se 2 (by rfl) ⟨93897, by rfl⟩ : syracuseStep 250393 = 187795) (by norm_num)
theorem B250429 : Blo 219811 250429 := bbase (se 3 (by rfl) ⟨46955, by rfl⟩ : syracuseStep 250429 = 93911) (by norm_num)
theorem B250465 : Blo 219811 250465 := bbase (se 2 (by rfl) ⟨93924, by rfl⟩ : syracuseStep 250465 = 187849) (by norm_num)
theorem B250501 : Blo 219811 250501 := bbase (se 4 (by rfl) ⟨23484, by rfl⟩ : syracuseStep 250501 = 46969) (by norm_num)
theorem B250537 : Blo 219811 250537 := bbase (se 2 (by rfl) ⟨93951, by rfl⟩ : syracuseStep 250537 = 187903) (by norm_num)
theorem B348845 : Blo 219811 348845 := bbase (se 3 (by rfl) ⟨65408, by rfl⟩ : syracuseStep 348845 = 130817) (by norm_num)
theorem B250573 : Blo 219811 250573 := bbase (se 3 (by rfl) ⟨46982, by rfl⟩ : syracuseStep 250573 = 93965) (by norm_num)
theorem B250609 : Blo 219811 250609 := bbase (se 2 (by rfl) ⟨93978, by rfl⟩ : syracuseStep 250609 = 187957) (by norm_num)
theorem B316181 : Blo 219811 316181 := bbase (se 6 (by rfl) ⟨7410, by rfl⟩ : syracuseStep 316181 = 14821) (by norm_num)
theorem B250645 : Blo 219811 250645 := bbase (se 6 (by rfl) ⟨5874, by rfl⟩ : syracuseStep 250645 = 11749) (by norm_num)
theorem B250681 : Blo 219811 250681 := bbase (se 2 (by rfl) ⟨94005, by rfl⟩ : syracuseStep 250681 = 188011) (by norm_num)
theorem B742229 : Blo 219811 742229 := bbase (se 9 (by rfl) ⟨2174, by rfl⟩ : syracuseStep 742229 = 4349) (by norm_num)
theorem B250717 : Blo 219811 250717 := bbase (se 3 (by rfl) ⟨47009, by rfl⟩ : syracuseStep 250717 = 94019) (by norm_num)
theorem B316261 : Blo 219811 316261 := bbase (se 4 (by rfl) ⟨29649, by rfl⟩ : syracuseStep 316261 = 59299) (by norm_num)
theorem B250753 : Blo 219811 250753 := bbase (se 2 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 250753 = 188065) (by norm_num)
theorem B250789 : Blo 219811 250789 := bbase (se 4 (by rfl) ⟨23511, by rfl⟩ : syracuseStep 250789 = 47023) (by norm_num)
theorem B250825 : Blo 219811 250825 := bbase (se 2 (by rfl) ⟨94059, by rfl⟩ : syracuseStep 250825 = 188119) (by norm_num)
theorem B316381 : Blo 219811 316381 := bbase (se 3 (by rfl) ⟨59321, by rfl⟩ : syracuseStep 316381 = 118643) (by norm_num)
theorem B250861 : Blo 219811 250861 := bbase (se 3 (by rfl) ⟨47036, by rfl⟩ : syracuseStep 250861 = 94073) (by norm_num)
theorem B250897 : Blo 219811 250897 := bbase (se 2 (by rfl) ⟨94086, by rfl⟩ : syracuseStep 250897 = 188173) (by norm_num)
theorem B250933 : Blo 219811 250933 := bbase (se 5 (by rfl) ⟨11762, by rfl⟩ : syracuseStep 250933 = 23525) (by norm_num)
theorem B316477 : Blo 219811 316477 := bbase (se 3 (by rfl) ⟨59339, by rfl⟩ : syracuseStep 316477 = 118679) (by norm_num)
theorem B250969 : Blo 219811 250969 := bbase (se 2 (by rfl) ⟨94113, by rfl⟩ : syracuseStep 250969 = 188227) (by norm_num)
theorem B251005 : Blo 219811 251005 := bbase (se 3 (by rfl) ⟨47063, by rfl⟩ : syracuseStep 251005 = 94127) (by norm_num)
theorem B251041 : Blo 219811 251041 := bbase (se 2 (by rfl) ⟨94140, by rfl⟩ : syracuseStep 251041 = 188281) (by norm_num)
theorem B251057 : Blo 219811 251057 := bbase (se 2 (by rfl) ⟨94146, by rfl⟩ : syracuseStep 251057 = 188293) (by norm_num)
theorem B382133 : Blo 219811 382133 := bbase (se 5 (by rfl) ⟨17912, by rfl⟩ : syracuseStep 382133 = 35825) (by norm_num)
theorem B840901 : Blo 219811 840901 := bbase (se 4 (by rfl) ⟨78834, by rfl⟩ : syracuseStep 840901 = 157669) (by norm_num)
theorem B251077 : Blo 219811 251077 := bbase (se 4 (by rfl) ⟨23538, by rfl⟩ : syracuseStep 251077 = 47077) (by norm_num)
theorem B251113 : Blo 219811 251113 := bbase (se 2 (by rfl) ⟨94167, by rfl⟩ : syracuseStep 251113 = 188335) (by norm_num)
theorem B742661 : Blo 219811 742661 := bbase (se 4 (by rfl) ⟨69624, by rfl⟩ : syracuseStep 742661 = 139249) (by norm_num)
theorem B251149 : Blo 219811 251149 := bbase (se 3 (by rfl) ⟨47090, by rfl⟩ : syracuseStep 251149 = 94181) (by norm_num)
theorem B251185 : Blo 219811 251185 := bbase (se 2 (by rfl) ⟨94194, by rfl⟩ : syracuseStep 251185 = 188389) (by norm_num)
theorem B382277 : Blo 219811 382277 := bbase (se 4 (by rfl) ⟨35838, by rfl⟩ : syracuseStep 382277 = 71677) (by norm_num)
theorem B251221 : Blo 219811 251221 := bbase (se 15 (by rfl) ⟨11, by rfl⟩ : syracuseStep 251221 = 23) (by norm_num)
theorem B251257 : Blo 219811 251257 := bbase (se 2 (by rfl) ⟨94221, by rfl⟩ : syracuseStep 251257 = 188443) (by norm_num)
theorem B251293 : Blo 219811 251293 := bbase (se 3 (by rfl) ⟨47117, by rfl⟩ : syracuseStep 251293 = 94235) (by norm_num)
theorem B251329 : Blo 219811 251329 := bbase (se 2 (by rfl) ⟨94248, by rfl⟩ : syracuseStep 251329 = 188497) (by norm_num)
theorem B251365 : Blo 219811 251365 := bbase (se 4 (by rfl) ⟨23565, by rfl⟩ : syracuseStep 251365 = 47131) (by norm_num)
theorem B841205 : Blo 219811 841205 := bbase (se 5 (by rfl) ⟨39431, by rfl⟩ : syracuseStep 841205 = 78863) (by norm_num)
theorem B251401 : Blo 219811 251401 := bbase (se 2 (by rfl) ⟨94275, by rfl⟩ : syracuseStep 251401 = 188551) (by norm_num)
theorem B316973 : Blo 219811 316973 := bbase (se 3 (by rfl) ⟨59432, by rfl⟩ : syracuseStep 316973 = 118865) (by norm_num)
theorem B251437 : Blo 219811 251437 := bbase (se 3 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 251437 = 94289) (by norm_num)
theorem B251473 : Blo 219811 251473 := bbase (se 2 (by rfl) ⟨94302, by rfl⟩ : syracuseStep 251473 = 188605) (by norm_num)
theorem B251509 : Blo 219811 251509 := bbase (se 5 (by rfl) ⟨11789, by rfl⟩ : syracuseStep 251509 = 23579) (by norm_num)
theorem B1070725 : Blo 219811 1070725 := bbase (se 4 (by rfl) ⟨100380, by rfl⟩ : syracuseStep 1070725 = 200761) (by norm_num)
theorem B251545 : Blo 219811 251545 := bbase (se 2 (by rfl) ⟨94329, by rfl⟩ : syracuseStep 251545 = 188659) (by norm_num)
theorem B743093 : Blo 219811 743093 := bbase (se 5 (by rfl) ⟨34832, by rfl⟩ : syracuseStep 743093 = 69665) (by norm_num)
theorem B251581 : Blo 219811 251581 := bbase (se 3 (by rfl) ⟨47171, by rfl⟩ : syracuseStep 251581 = 94343) (by norm_num)
theorem B251617 : Blo 219811 251617 := bbase (se 2 (by rfl) ⟨94356, by rfl⟩ : syracuseStep 251617 = 188713) (by norm_num)
theorem B906997 : Blo 219811 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B251653 : Blo 219811 251653 := bbase (se 4 (by rfl) ⟨23592, by rfl⟩ : syracuseStep 251653 = 47185) (by norm_num)
theorem B251689 : Blo 219811 251689 := bbase (se 2 (by rfl) ⟨94383, by rfl⟩ : syracuseStep 251689 = 188767) (by norm_num)
theorem B251725 : Blo 219811 251725 := bbase (se 3 (by rfl) ⟨47198, by rfl⟩ : syracuseStep 251725 = 94397) (by norm_num)
theorem B251761 : Blo 219811 251761 := bbase (se 2 (by rfl) ⟨94410, by rfl⟩ : syracuseStep 251761 = 188821) (by norm_num)
theorem B1595477 : Blo 219811 1595477 := bbase (se 8 (by rfl) ⟨9348, by rfl⟩ : syracuseStep 1595477 = 18697) (by norm_num)
theorem B710741 : Blo 219811 710741 := bbase (se 8 (by rfl) ⟨4164, by rfl⟩ : syracuseStep 710741 = 8329) (by norm_num)
theorem B317525 : Blo 219811 317525 := bbase (se 8 (by rfl) ⟨1860, by rfl⟩ : syracuseStep 317525 = 3721) (by norm_num)
theorem B743525 : Blo 219811 743525 := bbase (se 4 (by rfl) ⟨69705, by rfl⟩ : syracuseStep 743525 = 139411) (by norm_num)
theorem B8542421 : Blo 219811 8542421 := bbase (se 7 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 8542421 = 200213) (by norm_num)
theorem B317725 : Blo 219811 317725 := bbase (se 3 (by rfl) ⟨59573, by rfl⟩ : syracuseStep 317725 = 119147) (by norm_num)
theorem B743957 : Blo 219811 743957 := bbase (se 6 (by rfl) ⟨17436, by rfl⟩ : syracuseStep 743957 = 34873) (by norm_num)
theorem B645749 : Blo 219811 645749 := bbase (se 5 (by rfl) ⟨30269, by rfl⟩ : syracuseStep 645749 = 60539) (by norm_num)
theorem B940709 : Blo 219811 940709 := bbase (se 4 (by rfl) ⟨88191, by rfl⟩ : syracuseStep 940709 = 176383) (by norm_num)
theorem B940805 : Blo 219811 940805 := bbase (se 4 (by rfl) ⟨88200, by rfl⟩ : syracuseStep 940805 = 176401) (by norm_num)
theorem B285481 : Blo 219811 285481 := bbase (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) (by norm_num)
theorem B318277 : Blo 219811 318277 := bbase (se 4 (by rfl) ⟨29838, by rfl⟩ : syracuseStep 318277 = 59677) (by norm_num)
theorem B744389 : Blo 219811 744389 := bbase (se 4 (by rfl) ⟨69786, by rfl⟩ : syracuseStep 744389 = 139573) (by norm_num)
theorem B253085 : Blo 219811 253085 := bbase (se 3 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 253085 = 94907) (by norm_num)
theorem B449701 : Blo 219811 449701 := bbase (se 4 (by rfl) ⟨42159, by rfl⟩ : syracuseStep 449701 = 84319) (by norm_num)
theorem B580853 : Blo 219811 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B744821 : Blo 219811 744821 := bbase (se 5 (by rfl) ⟨34913, by rfl⟩ : syracuseStep 744821 = 69827) (by norm_num)
theorem B712165 : Blo 219811 712165 := bbase (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) (by norm_num)
theorem B810485 : Blo 219811 810485 := bbase (se 5 (by rfl) ⟨37991, by rfl⟩ : syracuseStep 810485 = 75983) (by norm_num)
theorem B843317 : Blo 219811 843317 := bbase (se 5 (by rfl) ⟨39530, by rfl⟩ : syracuseStep 843317 = 79061) (by norm_num)
theorem B1072709 : Blo 219811 1072709 := bbase (se 4 (by rfl) ⟨100566, by rfl⟩ : syracuseStep 1072709 = 201133) (by norm_num)
theorem B417413 : Blo 219811 417413 := bbase (se 4 (by rfl) ⟨39132, by rfl⟩ : syracuseStep 417413 = 78265) (by norm_num)
theorem B941813 : Blo 219811 941813 := bbase (se 5 (by rfl) ⟨44147, by rfl⟩ : syracuseStep 941813 = 88295) (by norm_num)
theorem B417565 : Blo 219811 417565 := bbase (se 3 (by rfl) ⟨78293, by rfl⟩ : syracuseStep 417565 = 156587) (by norm_num)
theorem B745253 : Blo 219811 745253 := bbase (se 4 (by rfl) ⟨69867, by rfl⟩ : syracuseStep 745253 = 139735) (by norm_num)
theorem B843605 : Blo 219811 843605 := bbase (se 9 (by rfl) ⟨2471, by rfl⟩ : syracuseStep 843605 = 4943) (by norm_num)
theorem B712613 : Blo 219811 712613 := bbase (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) (by norm_num)
theorem B319469 : Blo 219811 319469 := bbase (se 3 (by rfl) ⟨59900, by rfl⟩ : syracuseStep 319469 = 119801) (by norm_num)
theorem B417869 : Blo 219811 417869 := bbase (se 3 (by rfl) ⟨78350, by rfl⟩ : syracuseStep 417869 = 156701) (by norm_num)
theorem B286913 : Blo 219811 286913 := bbase (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) (by norm_num)
theorem B745685 : Blo 219811 745685 := bbase (se 7 (by rfl) ⟨8738, by rfl⟩ : syracuseStep 745685 = 17477) (by norm_num)
theorem B450805 : Blo 219811 450805 := bbase (se 5 (by rfl) ⟨21131, by rfl⟩ : syracuseStep 450805 = 42263) (by norm_num)
theorem B1138949 : Blo 219811 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B483685 : Blo 219811 483685 := bbase (se 4 (by rfl) ⟨45345, by rfl⟩ : syracuseStep 483685 = 90691) (by norm_num)
theorem B680293 : Blo 219811 680293 := bbase (se 4 (by rfl) ⟨63777, by rfl⟩ : syracuseStep 680293 = 127555) (by norm_num)
theorem B680309 : Blo 219811 680309 := bbase (se 5 (by rfl) ⟨31889, by rfl⟩ : syracuseStep 680309 = 63779) (by norm_num)
theorem B483725 : Blo 219811 483725 := bbase (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) (by norm_num)
theorem B287129 : Blo 219811 287129 := bbase (se 2 (by rfl) ⟨107673, by rfl⟩ : syracuseStep 287129 = 215347) (by norm_num)
theorem B352757 : Blo 219811 352757 := bbase (se 5 (by rfl) ⟨16535, by rfl⟩ : syracuseStep 352757 = 33071) (by norm_num)
theorem B746117 : Blo 219811 746117 := bbase (se 4 (by rfl) ⟨69948, by rfl⟩ : syracuseStep 746117 = 139897) (by norm_num)
theorem B287545 : Blo 219811 287545 := bbase (se 2 (by rfl) ⟨107829, by rfl⟩ : syracuseStep 287545 = 215659) (by norm_num)
theorem B418621 : Blo 219811 418621 := bbase (se 3 (by rfl) ⟨78491, by rfl⟩ : syracuseStep 418621 = 156983) (by norm_num)
theorem B418765 : Blo 219811 418765 := bbase (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) (by norm_num)
theorem B353269 : Blo 219811 353269 := bbase (se 5 (by rfl) ⟨16559, by rfl⟩ : syracuseStep 353269 = 33119) (by norm_num)
theorem B844789 : Blo 219811 844789 := bbase (se 5 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 844789 = 79199) (by norm_num)
theorem B746549 : Blo 219811 746549 := bbase (se 5 (by rfl) ⟨34994, by rfl⟩ : syracuseStep 746549 = 69989) (by norm_num)
theorem B418925 : Blo 219811 418925 := bbase (se 3 (by rfl) ⟨78548, by rfl⟩ : syracuseStep 418925 = 157097) (by norm_num)
theorem B419069 : Blo 219811 419069 := bbase (se 3 (by rfl) ⟨78575, by rfl⟩ : syracuseStep 419069 = 157151) (by norm_num)
theorem B845093 : Blo 219811 845093 := bbase (se 4 (by rfl) ⟨79227, by rfl⟩ : syracuseStep 845093 = 158455) (by norm_num)
theorem B714101 : Blo 219811 714101 := bbase (se 5 (by rfl) ⟨33473, by rfl⟩ : syracuseStep 714101 = 66947) (by norm_num)
theorem B943589 : Blo 219811 943589 := bbase (se 4 (by rfl) ⟨88461, by rfl⟩ : syracuseStep 943589 = 176923) (by norm_num)
theorem B746981 : Blo 219811 746981 := bbase (se 4 (by rfl) ⟨70029, by rfl⟩ : syracuseStep 746981 = 140059) (by norm_num)
theorem B1271285 : Blo 219811 1271285 := bbase (se 5 (by rfl) ⟨59591, by rfl⟩ : syracuseStep 1271285 = 119183) (by norm_num)
theorem B4285973 : Blo 219811 4285973 := bbase (se 6 (by rfl) ⟨100452, by rfl⟩ : syracuseStep 4285973 = 200905) (by norm_num)
theorem B419357 : Blo 219811 419357 := bbase (se 3 (by rfl) ⟨78629, by rfl⟩ : syracuseStep 419357 = 157259) (by norm_num)
theorem B419509 : Blo 219811 419509 := bbase (se 5 (by rfl) ⟨19664, by rfl⟩ : syracuseStep 419509 = 39329) (by norm_num)
theorem B747413 : Blo 219811 747413 := bbase (se 6 (by rfl) ⟨17517, by rfl⟩ : syracuseStep 747413 = 35035) (by norm_num)
theorem B223193 : Blo 219811 223193 := bbase (se 2 (by rfl) ⟨83697, by rfl⟩ : syracuseStep 223193 = 167395) (by norm_num)
theorem B354269 : Blo 219811 354269 := bbase (se 3 (by rfl) ⟨66425, by rfl⟩ : syracuseStep 354269 = 132851) (by norm_num)
theorem B419813 : Blo 219811 419813 := bbase (se 4 (by rfl) ⟨39357, by rfl⟩ : syracuseStep 419813 = 78715) (by norm_num)
theorem B682069 : Blo 219811 682069 := bbase (se 8 (by rfl) ⟨3996, by rfl⟩ : syracuseStep 682069 = 7993) (by norm_num)
theorem B354397 : Blo 219811 354397 := bbase (se 3 (by rfl) ⟨66449, by rfl⟩ : syracuseStep 354397 = 132899) (by norm_num)
theorem B714869 : Blo 219811 714869 := bbase (se 5 (by rfl) ⟨33509, by rfl⟩ : syracuseStep 714869 = 67019) (by norm_num)
theorem B354461 : Blo 219811 354461 := bbase (se 3 (by rfl) ⟨66461, by rfl⟩ : syracuseStep 354461 = 132923) (by norm_num)
theorem B223489 : Blo 219811 223489 := bbase (se 2 (by rfl) ⟨83808, by rfl⟩ : syracuseStep 223489 = 167617) (by norm_num)
theorem B223529 : Blo 219811 223529 := bbase (se 2 (by rfl) ⟨83823, by rfl⟩ : syracuseStep 223529 = 167647) (by norm_num)
theorem B747845 : Blo 219811 747845 := bbase (se 4 (by rfl) ⟨70110, by rfl⟩ : syracuseStep 747845 = 140221) (by norm_num)
theorem B453205 : Blo 219811 453205 := bbase (se 8 (by rfl) ⟨2655, by rfl⟩ : syracuseStep 453205 = 5311) (by norm_num)
theorem B1272469 : Blo 219811 1272469 := bbase (se 6 (by rfl) ⟨29823, by rfl⟩ : syracuseStep 1272469 = 59647) (by norm_num)
theorem B420565 : Blo 219811 420565 := bbase (se 7 (by rfl) ⟨4928, by rfl⟩ : syracuseStep 420565 = 9857) (by norm_num)
theorem B748277 : Blo 219811 748277 := bbase (se 5 (by rfl) ⟨35075, by rfl⟩ : syracuseStep 748277 = 70151) (by norm_num)
theorem B420709 : Blo 219811 420709 := bbase (se 4 (by rfl) ⟨39441, by rfl⟩ : syracuseStep 420709 = 78883) (by norm_num)
theorem B387941 : Blo 219811 387941 := bbase (se 4 (by rfl) ⟨36369, by rfl⟩ : syracuseStep 387941 = 72739) (by norm_num)
theorem B224105 : Blo 219811 224105 := bbase (se 2 (by rfl) ⟨84039, by rfl⟩ : syracuseStep 224105 = 168079) (by norm_num)
theorem B420869 : Blo 219811 420869 := bbase (se 4 (by rfl) ⟨39456, by rfl⟩ : syracuseStep 420869 = 78913) (by norm_num)
theorem B421013 : Blo 219811 421013 := bbase (se 6 (by rfl) ⟨9867, by rfl⟩ : syracuseStep 421013 = 19735) (by norm_num)
theorem B748709 : Blo 219811 748709 := bbase (se 4 (by rfl) ⟨70191, by rfl⟩ : syracuseStep 748709 = 140383) (by norm_num)
theorem B290093 : Blo 219811 290093 := bbase (se 3 (by rfl) ⟨54392, by rfl⟩ : syracuseStep 290093 = 108785) (by norm_num)
theorem B847205 : Blo 219811 847205 := bbase (se 4 (by rfl) ⟨79425, by rfl⟩ : syracuseStep 847205 = 158851) (by norm_num)
theorem B1076597 : Blo 219811 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B224689 : Blo 219811 224689 := bbase (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) (by norm_num)
theorem B421301 : Blo 219811 421301 := bbase (se 5 (by rfl) ⟨19748, by rfl⟩ : syracuseStep 421301 = 39497) (by norm_num)
theorem B224705 : Blo 219811 224705 := bbase (se 2 (by rfl) ⟨84264, by rfl⟩ : syracuseStep 224705 = 168529) (by norm_num)
theorem B355781 : Blo 219811 355781 := bbase (se 4 (by rfl) ⟨33354, by rfl⟩ : syracuseStep 355781 = 66709) (by norm_num)
theorem B355909 : Blo 219811 355909 := bbase (se 4 (by rfl) ⟨33366, by rfl⟩ : syracuseStep 355909 = 66733) (by norm_num)
theorem B421453 : Blo 219811 421453 := bbase (se 3 (by rfl) ⟨79022, by rfl⟩ : syracuseStep 421453 = 158045) (by norm_num)
theorem B749141 : Blo 219811 749141 := bbase (se 8 (by rfl) ⟨4389, by rfl⟩ : syracuseStep 749141 = 8779) (by norm_num)
theorem B847493 : Blo 219811 847493 := bbase (se 4 (by rfl) ⟨79452, by rfl⟩ : syracuseStep 847493 = 158905) (by norm_num)
theorem B1699541 : Blo 219811 1699541 := bbase (se 7 (by rfl) ⟨19916, by rfl⟩ : syracuseStep 1699541 = 39833) (by norm_num)
theorem B257773 : Blo 219811 257773 := bbase (se 3 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 257773 = 96665) (by norm_num)
theorem B716597 : Blo 219811 716597 := bbase (se 5 (by rfl) ⟨33590, by rfl⟩ : syracuseStep 716597 = 67181) (by norm_num)
theorem B421757 : Blo 219811 421757 := bbase (se 3 (by rfl) ⟨79079, by rfl⟩ : syracuseStep 421757 = 158159) (by norm_num)
theorem B749573 : Blo 219811 749573 := bbase (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) (by norm_num)
theorem B258185 : Blo 219811 258185 := bbase (se 2 (by rfl) ⟨96819, by rfl⟩ : syracuseStep 258185 = 193639) (by norm_num)
theorem B258221 : Blo 219811 258221 := bbase (se 3 (by rfl) ⟨48416, by rfl⟩ : syracuseStep 258221 = 96833) (by norm_num)
theorem B3207509 : Blo 219811 3207509 := bbase (se 10 (by rfl) ⟨4698, by rfl⟩ : syracuseStep 3207509 = 9397) (by norm_num)
theorem B356717 : Blo 219811 356717 := bbase (se 3 (by rfl) ⟨66884, by rfl⟩ : syracuseStep 356717 = 133769) (by norm_num)
theorem B750005 : Blo 219811 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B225865 : Blo 219811 225865 := bbase (se 2 (by rfl) ⟨84699, by rfl⟩ : syracuseStep 225865 = 169399) (by norm_num)
theorem B1274453 : Blo 219811 1274453 := bbase (se 8 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 1274453 = 14935) (by norm_num)
theorem B422509 : Blo 219811 422509 := bbase (se 3 (by rfl) ⟨79220, by rfl⟩ : syracuseStep 422509 = 158441) (by norm_num)
theorem B848501 : Blo 219811 848501 := bbase (se 5 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 848501 = 79547) (by norm_num)
theorem B357005 : Blo 219811 357005 := bbase (se 3 (by rfl) ⟨66938, by rfl⟩ : syracuseStep 357005 = 133877) (by norm_num)
theorem B422653 : Blo 219811 422653 := bbase (se 3 (by rfl) ⟨79247, by rfl⟩ : syracuseStep 422653 = 158495) (by norm_num)
theorem B1372949 : Blo 219811 1372949 := bbase (se 6 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 1372949 = 64357) (by norm_num)
theorem B848677 : Blo 219811 848677 := bbase (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) (by norm_num)
theorem B750437 : Blo 219811 750437 := bbase (se 4 (by rfl) ⟨70353, by rfl⟩ : syracuseStep 750437 = 140707) (by norm_num)
theorem B422813 : Blo 219811 422813 := bbase (se 3 (by rfl) ⟨79277, by rfl⟩ : syracuseStep 422813 = 158555) (by norm_num)
theorem B1143733 : Blo 219811 1143733 := bbase (se 5 (by rfl) ⟨53612, by rfl⟩ : syracuseStep 1143733 = 107225) (by norm_num)
theorem B1274869 : Blo 219811 1274869 := bbase (se 5 (by rfl) ⟨59759, by rfl⟩ : syracuseStep 1274869 = 119519) (by norm_num)
theorem B422957 : Blo 219811 422957 := bbase (se 3 (by rfl) ⟨79304, by rfl⟩ : syracuseStep 422957 = 158609) (by norm_num)
theorem B357421 : Blo 219811 357421 := bbase (se 3 (by rfl) ⟨67016, by rfl⟩ : syracuseStep 357421 = 134033) (by norm_num)
theorem B848981 : Blo 219811 848981 := bbase (se 8 (by rfl) ⟨4974, by rfl⟩ : syracuseStep 848981 = 9949) (by norm_num)
theorem B750869 : Blo 219811 750869 := bbase (se 6 (by rfl) ⟨17598, by rfl⟩ : syracuseStep 750869 = 35197) (by norm_num)
theorem B423245 : Blo 219811 423245 := bbase (se 3 (by rfl) ⟨79358, by rfl⟩ : syracuseStep 423245 = 158717) (by norm_num)
theorem B423397 : Blo 219811 423397 := bbase (se 4 (by rfl) ⟨39693, by rfl⟩ : syracuseStep 423397 = 79387) (by norm_num)
theorem B947861 : Blo 219811 947861 := bbase (se 6 (by rfl) ⟨22215, by rfl⟩ : syracuseStep 947861 = 44431) (by norm_num)
theorem B751301 : Blo 219811 751301 := bbase (se 4 (by rfl) ⟨70434, by rfl⟩ : syracuseStep 751301 = 140869) (by norm_num)
theorem B423701 : Blo 219811 423701 := bbase (se 6 (by rfl) ⟨9930, by rfl⟩ : syracuseStep 423701 = 19861) (by norm_num)
theorem B358357 : Blo 219811 358357 := bbase (se 7 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 358357 = 8399) (by norm_num)
theorem B227377 : Blo 219811 227377 := bbase (se 2 (by rfl) ⟨85266, by rfl⟩ : syracuseStep 227377 = 170533) (by norm_num)
theorem B751733 : Blo 219811 751733 := bbase (se 5 (by rfl) ⟨35237, by rfl⟩ : syracuseStep 751733 = 70475) (by norm_num)
theorem B424453 : Blo 219811 424453 := bbase (se 4 (by rfl) ⟨39792, by rfl⟩ : syracuseStep 424453 = 79585) (by norm_num)
theorem B752165 : Blo 219811 752165 := bbase (se 4 (by rfl) ⟨70515, by rfl⟩ : syracuseStep 752165 = 141031) (by norm_num)
theorem B424525 : Blo 219811 424525 := bbase (se 3 (by rfl) ⟨79598, by rfl⟩ : syracuseStep 424525 = 159197) (by norm_num)
theorem B490093 : Blo 219811 490093 := bbase (se 3 (by rfl) ⟨91892, by rfl⟩ : syracuseStep 490093 = 183785) (by norm_num)
theorem B424597 : Blo 219811 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B424757 : Blo 219811 424757 := bbase (se 5 (by rfl) ⟨19910, by rfl⟩ : syracuseStep 424757 = 39821) (by norm_num)
theorem B752597 : Blo 219811 752597 := bbase (se 7 (by rfl) ⟨8819, by rfl⟩ : syracuseStep 752597 = 17639) (by norm_num)
theorem B326741 : Blo 219811 326741 := bbase (se 8 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 326741 = 3829) (by norm_num)
theorem B228577 : Blo 219811 228577 := bbase (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) (by norm_num)
theorem B458117 : Blo 219811 458117 := bbase (se 4 (by rfl) ⟨42948, by rfl⟩ : syracuseStep 458117 = 85897) (by norm_num)
theorem B949637 : Blo 219811 949637 := bbase (se 4 (by rfl) ⟨89028, by rfl⟩ : syracuseStep 949637 = 178057) (by norm_num)
theorem B753029 : Blo 219811 753029 := bbase (se 4 (by rfl) ⟨70596, by rfl⟩ : syracuseStep 753029 = 141193) (by norm_num)
theorem B556429 : Blo 219811 556429 := bbase (se 3 (by rfl) ⟨104330, by rfl⟩ : syracuseStep 556429 = 208661) (by norm_num)
theorem B556541 : Blo 219811 556541 := bbase (se 3 (by rfl) ⟨104351, by rfl⟩ : syracuseStep 556541 = 208703) (by norm_num)
theorem B1408565 : Blo 219811 1408565 := bbase (se 5 (by rfl) ⟨66026, by rfl⟩ : syracuseStep 1408565 = 132053) (by norm_num)
theorem B949877 : Blo 219811 949877 := bbase (se 5 (by rfl) ⟨44525, by rfl⟩ : syracuseStep 949877 = 89051) (by norm_num)
theorem B1113749 : Blo 219811 1113749 := bbase (se 6 (by rfl) ⟨26103, by rfl⟩ : syracuseStep 1113749 = 52207) (by norm_num)
theorem B556733 : Blo 219811 556733 := bbase (se 3 (by rfl) ⟨104387, by rfl⟩ : syracuseStep 556733 = 208775) (by norm_num)
theorem B753461 : Blo 219811 753461 := bbase (se 5 (by rfl) ⟨35318, by rfl⟩ : syracuseStep 753461 = 70637) (by norm_num)
theorem B753677 : Blo 219811 753677 := bstep (se 3 (by rfl) ⟨141314, by rfl⟩ : syracuseStep 753677 = 282629) B282629
theorem B753731 : Blo 219811 753731 := bstep (se 1 (by rfl) ⟨565298, by rfl⟩ : syracuseStep 753731 = 1130597) B1130597
theorem B557219 : Blo 219811 557219 := bstep (se 1 (by rfl) ⟨417914, by rfl⟩ : syracuseStep 557219 = 835829) B835829
theorem B1212677 : Blo 219811 1212677 := bstep (se 4 (by rfl) ⟨113688, by rfl⟩ : syracuseStep 1212677 = 227377) B227377
theorem B754001 : Blo 219811 754001 := bstep (se 2 (by rfl) ⟨282750, by rfl⟩ : syracuseStep 754001 = 565501) B565501
theorem B688493 : Blo 219811 688493 := bstep (se 3 (by rfl) ⟨129092, by rfl⟩ : syracuseStep 688493 = 258185) B258185
theorem B688589 : Blo 219811 688589 := bstep (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) B258221
theorem B754541 : Blo 219811 754541 := bstep (se 3 (by rfl) ⟨141476, by rfl⟩ : syracuseStep 754541 = 282953) B282953
theorem B754595 : Blo 219811 754595 := bstep (se 1 (by rfl) ⟨565946, by rfl⟩ : syracuseStep 754595 = 1131893) B1131893
theorem B1016867 : Blo 219811 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B558161 : Blo 219811 558161 := bstep (se 2 (by rfl) ⟨209310, by rfl⟩ : syracuseStep 558161 = 418621) B418621
theorem B558211 : Blo 219811 558211 := bstep (se 1 (by rfl) ⟨418658, by rfl⟩ : syracuseStep 558211 = 837317) B837317
theorem B1082531 : Blo 219811 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B754865 : Blo 219811 754865 := bstep (se 2 (by rfl) ⟨283074, by rfl⟩ : syracuseStep 754865 = 566149) B566149
theorem B558353 : Blo 219811 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B952013 : Blo 219811 952013 := bstep (se 3 (by rfl) ⟨178502, by rfl⟩ : syracuseStep 952013 = 357005) B357005
theorem B1410821 : Blo 219811 1410821 := bstep (se 4 (by rfl) ⟨132264, by rfl⟩ : syracuseStep 1410821 = 264529) B264529
theorem B1116017 : Blo 219811 1116017 := bstep (se 2 (by rfl) ⟨418506, by rfl⟩ : syracuseStep 1116017 = 837013) B837013
theorem B264179 : Blo 219811 264179 := bstep (se 1 (by rfl) ⟨198134, by rfl⟩ : syracuseStep 264179 = 396269) B396269
theorem B329729 : Blo 219811 329729 := bstep (se 2 (by rfl) ⟨123648, by rfl⟩ : syracuseStep 329729 = 247297) B247297
theorem B329747 : Blo 219811 329747 := bstep (se 1 (by rfl) ⟨247310, by rfl⟩ : syracuseStep 329747 = 494621) B494621
theorem B329777 : Blo 219811 329777 := bstep (se 2 (by rfl) ⟨123666, by rfl⟩ : syracuseStep 329777 = 247333) B247333
theorem B329795 : Blo 219811 329795 := bstep (se 1 (by rfl) ⟨247346, by rfl⟩ : syracuseStep 329795 = 494693) B494693
theorem B329825 : Blo 219811 329825 := bstep (se 2 (by rfl) ⟨123684, by rfl⟩ : syracuseStep 329825 = 247369) B247369
theorem B329843 : Blo 219811 329843 := bstep (se 1 (by rfl) ⟨247382, by rfl⟩ : syracuseStep 329843 = 494765) B494765
theorem B329873 : Blo 219811 329873 := bstep (se 2 (by rfl) ⟨123702, by rfl⟩ : syracuseStep 329873 = 247405) B247405
theorem B329891 : Blo 219811 329891 := bstep (se 1 (by rfl) ⟨247418, by rfl⟩ : syracuseStep 329891 = 494837) B494837
theorem B329921 : Blo 219811 329921 := bstep (se 2 (by rfl) ⟨123720, by rfl⟩ : syracuseStep 329921 = 247441) B247441
theorem B329939 : Blo 219811 329939 := bstep (se 1 (by rfl) ⟨247454, by rfl⟩ : syracuseStep 329939 = 494909) B494909
theorem B329969 : Blo 219811 329969 := bstep (se 2 (by rfl) ⟨123738, by rfl⟩ : syracuseStep 329969 = 247477) B247477
theorem B559345 : Blo 219811 559345 := bstep (se 2 (by rfl) ⟨209754, by rfl⟩ : syracuseStep 559345 = 419509) B419509
theorem B329987 : Blo 219811 329987 := bstep (se 1 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 329987 = 494981) B494981
theorem B10455317 : Blo 219811 10455317 := bstep (se 6 (by rfl) ⟨245046, by rfl⟩ : syracuseStep 10455317 = 490093) B490093
theorem B330017 : Blo 219811 330017 := bstep (se 2 (by rfl) ⟨123756, by rfl⟩ : syracuseStep 330017 = 247513) B247513
theorem B330035 : Blo 219811 330035 := bstep (se 1 (by rfl) ⟨247526, by rfl⟩ : syracuseStep 330035 = 495053) B495053
theorem B330065 : Blo 219811 330065 := bstep (se 2 (by rfl) ⟨123774, by rfl⟩ : syracuseStep 330065 = 247549) B247549
theorem B330083 : Blo 219811 330083 := bstep (se 1 (by rfl) ⟨247562, by rfl⟩ : syracuseStep 330083 = 495125) B495125
theorem B330113 : Blo 219811 330113 := bstep (se 2 (by rfl) ⟨123792, by rfl⟩ : syracuseStep 330113 = 247585) B247585
theorem B330131 : Blo 219811 330131 := bstep (se 1 (by rfl) ⟨247598, by rfl⟩ : syracuseStep 330131 = 495197) B495197
theorem B297379 : Blo 219811 297379 := bstep (se 1 (by rfl) ⟨223034, by rfl⟩ : syracuseStep 297379 = 446069) B446069
theorem B330161 : Blo 219811 330161 := bstep (se 2 (by rfl) ⟨123810, by rfl⟩ : syracuseStep 330161 = 247621) B247621
theorem B330179 : Blo 219811 330179 := bstep (se 1 (by rfl) ⟨247634, by rfl⟩ : syracuseStep 330179 = 495269) B495269
theorem B330209 : Blo 219811 330209 := bstep (se 2 (by rfl) ⟨123828, by rfl⟩ : syracuseStep 330209 = 247657) B247657
theorem B330227 : Blo 219811 330227 := bstep (se 1 (by rfl) ⟨247670, by rfl⟩ : syracuseStep 330227 = 495341) B495341
theorem B559619 : Blo 219811 559619 := bstep (se 1 (by rfl) ⟨419714, by rfl⟩ : syracuseStep 559619 = 839429) B839429
theorem B330257 : Blo 219811 330257 := bstep (se 2 (by rfl) ⟨123846, by rfl⟩ : syracuseStep 330257 = 247693) B247693
theorem B330275 : Blo 219811 330275 := bstep (se 1 (by rfl) ⟨247706, by rfl⟩ : syracuseStep 330275 = 495413) B495413
theorem B330305 : Blo 219811 330305 := bstep (se 2 (by rfl) ⟨123864, by rfl⟩ : syracuseStep 330305 = 247729) B247729
theorem B330323 : Blo 219811 330323 := bstep (se 1 (by rfl) ⟨247742, by rfl⟩ : syracuseStep 330323 = 495485) B495485
theorem B330353 : Blo 219811 330353 := bstep (se 2 (by rfl) ⟨123882, by rfl⟩ : syracuseStep 330353 = 247765) B247765
theorem B330371 : Blo 219811 330371 := bstep (se 1 (by rfl) ⟨247778, by rfl⟩ : syracuseStep 330371 = 495557) B495557
theorem B330401 : Blo 219811 330401 := bstep (se 2 (by rfl) ⟨123900, by rfl⟩ : syracuseStep 330401 = 247801) B247801
theorem B330419 : Blo 219811 330419 := bstep (se 1 (by rfl) ⟨247814, by rfl⟩ : syracuseStep 330419 = 495629) B495629
theorem B559811 : Blo 219811 559811 := bstep (se 1 (by rfl) ⟨419858, by rfl⟩ : syracuseStep 559811 = 839717) B839717
theorem B330449 : Blo 219811 330449 := bstep (se 2 (by rfl) ⟨123918, by rfl⟩ : syracuseStep 330449 = 247837) B247837
theorem B330467 : Blo 219811 330467 := bstep (se 1 (by rfl) ⟨247850, by rfl⟩ : syracuseStep 330467 = 495701) B495701
theorem B330497 : Blo 219811 330497 := bstep (se 2 (by rfl) ⟨123936, by rfl⟩ : syracuseStep 330497 = 247873) B247873
theorem B330515 : Blo 219811 330515 := bstep (se 1 (by rfl) ⟨247886, by rfl⟩ : syracuseStep 330515 = 495773) B495773
theorem B330545 : Blo 219811 330545 := bstep (se 2 (by rfl) ⟨123954, by rfl⟩ : syracuseStep 330545 = 247909) B247909
theorem B1018673 : Blo 219811 1018673 := bstep (se 2 (by rfl) ⟨382002, by rfl⟩ : syracuseStep 1018673 = 764005) B764005
theorem B330563 : Blo 219811 330563 := bstep (se 1 (by rfl) ⟨247922, by rfl⟩ : syracuseStep 330563 = 495845) B495845
theorem B330593 : Blo 219811 330593 := bstep (se 2 (by rfl) ⟨123972, by rfl⟩ : syracuseStep 330593 = 247945) B247945
theorem B330611 : Blo 219811 330611 := bstep (se 1 (by rfl) ⟨247958, by rfl⟩ : syracuseStep 330611 = 495917) B495917
theorem B330641 : Blo 219811 330641 := bstep (se 2 (by rfl) ⟨123990, by rfl⟩ : syracuseStep 330641 = 247981) B247981
theorem B330659 : Blo 219811 330659 := bstep (se 1 (by rfl) ⟨247994, by rfl⟩ : syracuseStep 330659 = 495989) B495989
theorem B330689 : Blo 219811 330689 := bstep (se 2 (by rfl) ⟨124008, by rfl⟩ : syracuseStep 330689 = 248017) B248017
theorem B330707 : Blo 219811 330707 := bstep (se 1 (by rfl) ⟨248030, by rfl⟩ : syracuseStep 330707 = 496061) B496061
theorem B330737 : Blo 219811 330737 := bstep (se 2 (by rfl) ⟨124026, by rfl⟩ : syracuseStep 330737 = 248053) B248053
theorem B297985 : Blo 219811 297985 := bstep (se 2 (by rfl) ⟨111744, by rfl⟩ : syracuseStep 297985 = 223489) B223489
theorem B330755 : Blo 219811 330755 := bstep (se 1 (by rfl) ⟨248066, by rfl⟩ : syracuseStep 330755 = 496133) B496133
theorem B330785 : Blo 219811 330785 := bstep (se 2 (by rfl) ⟨124044, by rfl⟩ : syracuseStep 330785 = 248089) B248089
theorem B330803 : Blo 219811 330803 := bstep (se 1 (by rfl) ⟨248102, by rfl⟩ : syracuseStep 330803 = 496205) B496205
theorem B330833 : Blo 219811 330833 := bstep (se 2 (by rfl) ⟨124062, by rfl⟩ : syracuseStep 330833 = 248125) B248125
theorem B330851 : Blo 219811 330851 := bstep (se 1 (by rfl) ⟨248138, by rfl⟩ : syracuseStep 330851 = 496277) B496277
theorem B330881 : Blo 219811 330881 := bstep (se 2 (by rfl) ⟨124080, by rfl⟩ : syracuseStep 330881 = 248161) B248161
theorem B330899 : Blo 219811 330899 := bstep (se 1 (by rfl) ⟨248174, by rfl⟩ : syracuseStep 330899 = 496349) B496349
theorem B330929 : Blo 219811 330929 := bstep (se 2 (by rfl) ⟨124098, by rfl⟩ : syracuseStep 330929 = 248197) B248197
theorem B330947 : Blo 219811 330947 := bstep (se 1 (by rfl) ⟨248210, by rfl⟩ : syracuseStep 330947 = 496421) B496421
theorem B494801 : Blo 219811 494801 := bstep (se 2 (by rfl) ⟨185550, by rfl⟩ : syracuseStep 494801 = 371101) B371101
theorem B330977 : Blo 219811 330977 := bstep (se 2 (by rfl) ⟨124116, by rfl⟩ : syracuseStep 330977 = 248233) B248233
theorem B494819 : Blo 219811 494819 := bstep (se 1 (by rfl) ⟨371114, by rfl⟩ : syracuseStep 494819 = 742229) B742229
theorem B330995 : Blo 219811 330995 := bstep (se 1 (by rfl) ⟨248246, by rfl⟩ : syracuseStep 330995 = 496493) B496493
theorem B331025 : Blo 219811 331025 := bstep (se 2 (by rfl) ⟨124134, by rfl⟩ : syracuseStep 331025 = 248269) B248269
theorem B331043 : Blo 219811 331043 := bstep (se 1 (by rfl) ⟨248282, by rfl⟩ : syracuseStep 331043 = 496565) B496565
theorem B1117475 : Blo 219811 1117475 := bstep (se 1 (by rfl) ⟨838106, by rfl⟩ : syracuseStep 1117475 = 1676213) B1676213
theorem B331073 : Blo 219811 331073 := bstep (se 2 (by rfl) ⟨124152, by rfl⟩ : syracuseStep 331073 = 248305) B248305
theorem B331091 : Blo 219811 331091 := bstep (se 1 (by rfl) ⟨248318, by rfl⟩ : syracuseStep 331091 = 496637) B496637
theorem B331121 : Blo 219811 331121 := bstep (se 2 (by rfl) ⟨124170, by rfl⟩ : syracuseStep 331121 = 248341) B248341
theorem B331139 : Blo 219811 331139 := bstep (se 1 (by rfl) ⟨248354, by rfl⟩ : syracuseStep 331139 = 496709) B496709
theorem B331169 : Blo 219811 331169 := bstep (se 2 (by rfl) ⟨124188, by rfl⟩ : syracuseStep 331169 = 248377) B248377
theorem B331187 : Blo 219811 331187 := bstep (se 1 (by rfl) ⟨248390, by rfl⟩ : syracuseStep 331187 = 496781) B496781
theorem B331217 : Blo 219811 331217 := bstep (se 2 (by rfl) ⟨124206, by rfl⟩ : syracuseStep 331217 = 248413) B248413
theorem B331235 : Blo 219811 331235 := bstep (se 1 (by rfl) ⟨248426, by rfl⟩ : syracuseStep 331235 = 496853) B496853
theorem B495089 : Blo 219811 495089 := bstep (se 2 (by rfl) ⟨185658, by rfl⟩ : syracuseStep 495089 = 371317) B371317
theorem B331265 : Blo 219811 331265 := bstep (se 2 (by rfl) ⟨124224, by rfl⟩ : syracuseStep 331265 = 248449) B248449
theorem B495107 : Blo 219811 495107 := bstep (se 1 (by rfl) ⟨371330, by rfl⟩ : syracuseStep 495107 = 742661) B742661
theorem B1019405 : Blo 219811 1019405 := bstep (se 3 (by rfl) ⟨191138, by rfl⟩ : syracuseStep 1019405 = 382277) B382277
theorem B331283 : Blo 219811 331283 := bstep (se 1 (by rfl) ⟨248462, by rfl⟩ : syracuseStep 331283 = 496925) B496925
theorem B331313 : Blo 219811 331313 := bstep (se 2 (by rfl) ⟨124242, by rfl⟩ : syracuseStep 331313 = 248485) B248485
theorem B331331 : Blo 219811 331331 := bstep (se 1 (by rfl) ⟨248498, by rfl⟩ : syracuseStep 331331 = 496997) B496997
theorem B331361 : Blo 219811 331361 := bstep (se 2 (by rfl) ⟨124260, by rfl⟩ : syracuseStep 331361 = 248521) B248521
theorem B560753 : Blo 219811 560753 := bstep (se 2 (by rfl) ⟨210282, by rfl⟩ : syracuseStep 560753 = 420565) B420565
theorem B331379 : Blo 219811 331379 := bstep (se 1 (by rfl) ⟨248534, by rfl⟩ : syracuseStep 331379 = 497069) B497069
theorem B1904269 : Blo 219811 1904269 := bstep (se 3 (by rfl) ⟨357050, by rfl⟩ : syracuseStep 1904269 = 714101) B714101
theorem B331409 : Blo 219811 331409 := bstep (se 2 (by rfl) ⟨124278, by rfl⟩ : syracuseStep 331409 = 248557) B248557
theorem B331427 : Blo 219811 331427 := bstep (se 1 (by rfl) ⟨248570, by rfl⟩ : syracuseStep 331427 = 497141) B497141
theorem B560803 : Blo 219811 560803 := bstep (se 1 (by rfl) ⟨420602, by rfl⟩ : syracuseStep 560803 = 841205) B841205
theorem B331457 : Blo 219811 331457 := bstep (se 2 (by rfl) ⟨124296, by rfl⟩ : syracuseStep 331457 = 248593) B248593
theorem B331475 : Blo 219811 331475 := bstep (se 1 (by rfl) ⟨248606, by rfl⟩ : syracuseStep 331475 = 497213) B497213
theorem B626417 : Blo 219811 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B331505 : Blo 219811 331505 := bstep (se 2 (by rfl) ⟨124314, by rfl⟩ : syracuseStep 331505 = 248629) B248629
theorem B331523 : Blo 219811 331523 := bstep (se 1 (by rfl) ⟨248642, by rfl⟩ : syracuseStep 331523 = 497285) B497285
theorem B495377 : Blo 219811 495377 := bstep (se 2 (by rfl) ⟨185766, by rfl⟩ : syracuseStep 495377 = 371533) B371533
theorem B331553 : Blo 219811 331553 := bstep (se 2 (by rfl) ⟨124332, by rfl⟩ : syracuseStep 331553 = 248665) B248665
theorem B495395 : Blo 219811 495395 := bstep (se 1 (by rfl) ⟨371546, by rfl⟩ : syracuseStep 495395 = 743093) B743093
theorem B560945 : Blo 219811 560945 := bstep (se 2 (by rfl) ⟨210354, by rfl⟩ : syracuseStep 560945 = 420709) B420709
theorem B331571 : Blo 219811 331571 := bstep (se 1 (by rfl) ⟨248678, by rfl⟩ : syracuseStep 331571 = 497357) B497357
theorem B331601 : Blo 219811 331601 := bstep (se 2 (by rfl) ⟨124350, by rfl⟩ : syracuseStep 331601 = 248701) B248701
theorem B331619 : Blo 219811 331619 := bstep (se 1 (by rfl) ⟨248714, by rfl⟩ : syracuseStep 331619 = 497429) B497429
theorem B331649 : Blo 219811 331649 := bstep (se 2 (by rfl) ⟨124368, by rfl⟩ : syracuseStep 331649 = 248737) B248737
theorem B331667 : Blo 219811 331667 := bstep (se 1 (by rfl) ⟨248750, by rfl⟩ : syracuseStep 331667 = 497501) B497501
theorem B331697 : Blo 219811 331697 := bstep (se 2 (by rfl) ⟨124386, by rfl⟩ : syracuseStep 331697 = 248773) B248773
theorem B331715 : Blo 219811 331715 := bstep (se 1 (by rfl) ⟨248786, by rfl⟩ : syracuseStep 331715 = 497573) B497573
theorem B331745 : Blo 219811 331745 := bstep (se 2 (by rfl) ⟨124404, by rfl⟩ : syracuseStep 331745 = 248809) B248809
theorem B331763 : Blo 219811 331763 := bstep (se 1 (by rfl) ⟨248822, by rfl⟩ : syracuseStep 331763 = 497645) B497645
theorem B331793 : Blo 219811 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B757777 : Blo 219811 757777 := bstep (se 2 (by rfl) ⟨284166, by rfl⟩ : syracuseStep 757777 = 568333) B568333
theorem B331811 : Blo 219811 331811 := bstep (se 1 (by rfl) ⟨248858, by rfl⟩ : syracuseStep 331811 = 497717) B497717
theorem B495665 : Blo 219811 495665 := bstep (se 2 (by rfl) ⟨185874, by rfl⟩ : syracuseStep 495665 = 371749) B371749
theorem B331841 : Blo 219811 331841 := bstep (se 2 (by rfl) ⟨124440, by rfl⟩ : syracuseStep 331841 = 248881) B248881
theorem B495683 : Blo 219811 495683 := bstep (se 1 (by rfl) ⟨371762, by rfl⟩ : syracuseStep 495683 = 743525) B743525
theorem B1118285 : Blo 219811 1118285 := bstep (se 3 (by rfl) ⟨209678, by rfl⟩ : syracuseStep 1118285 = 419357) B419357
theorem B331859 : Blo 219811 331859 := bstep (se 1 (by rfl) ⟨248894, by rfl⟩ : syracuseStep 331859 = 497789) B497789
theorem B331889 : Blo 219811 331889 := bstep (se 2 (by rfl) ⟨124458, by rfl⟩ : syracuseStep 331889 = 248917) B248917
theorem B331907 : Blo 219811 331907 := bstep (se 1 (by rfl) ⟨248930, by rfl⟩ : syracuseStep 331907 = 497861) B497861
theorem B331937 : Blo 219811 331937 := bstep (se 2 (by rfl) ⟨124476, by rfl⟩ : syracuseStep 331937 = 248953) B248953
theorem B331955 : Blo 219811 331955 := bstep (se 1 (by rfl) ⟨248966, by rfl⟩ : syracuseStep 331955 = 497933) B497933
theorem B331985 : Blo 219811 331985 := bstep (se 2 (by rfl) ⟨124494, by rfl⟩ : syracuseStep 331985 = 248989) B248989
theorem B332003 : Blo 219811 332003 := bstep (se 1 (by rfl) ⟨249002, by rfl⟩ : syracuseStep 332003 = 498005) B498005
theorem B332033 : Blo 219811 332033 := bstep (se 2 (by rfl) ⟨124512, by rfl⟩ : syracuseStep 332033 = 249025) B249025
theorem B332051 : Blo 219811 332051 := bstep (se 1 (by rfl) ⟨249038, by rfl⟩ : syracuseStep 332051 = 498077) B498077
theorem B332081 : Blo 219811 332081 := bstep (se 2 (by rfl) ⟨124530, by rfl⟩ : syracuseStep 332081 = 249061) B249061
theorem B332099 : Blo 219811 332099 := bstep (se 1 (by rfl) ⟨249074, by rfl⟩ : syracuseStep 332099 = 498149) B498149
theorem B495953 : Blo 219811 495953 := bstep (se 2 (by rfl) ⟨185982, by rfl⟩ : syracuseStep 495953 = 371965) B371965
theorem B332129 : Blo 219811 332129 := bstep (se 2 (by rfl) ⟨124548, by rfl⟩ : syracuseStep 332129 = 249097) B249097
theorem B495971 : Blo 219811 495971 := bstep (se 1 (by rfl) ⟨371978, by rfl⟩ : syracuseStep 495971 = 743957) B743957
theorem B332147 : Blo 219811 332147 := bstep (se 1 (by rfl) ⟨249110, by rfl⟩ : syracuseStep 332147 = 498221) B498221
theorem B332177 : Blo 219811 332177 := bstep (se 2 (by rfl) ⟨124566, by rfl⟩ : syracuseStep 332177 = 249133) B249133
theorem B332195 : Blo 219811 332195 := bstep (se 1 (by rfl) ⟨249146, by rfl⟩ : syracuseStep 332195 = 498293) B498293
theorem B430499 : Blo 219811 430499 := bstep (se 1 (by rfl) ⟨322874, by rfl⟩ : syracuseStep 430499 = 645749) B645749
theorem B332225 : Blo 219811 332225 := bstep (se 2 (by rfl) ⟨124584, by rfl⟩ : syracuseStep 332225 = 249169) B249169
theorem B627139 : Blo 219811 627139 := bstep (se 1 (by rfl) ⟨470354, by rfl⟩ : syracuseStep 627139 = 940709) B940709
theorem B332243 : Blo 219811 332243 := bstep (se 1 (by rfl) ⟨249182, by rfl⟩ : syracuseStep 332243 = 498365) B498365
theorem B332273 : Blo 219811 332273 := bstep (se 2 (by rfl) ⟨124602, by rfl⟩ : syracuseStep 332273 = 249205) B249205
theorem B627203 : Blo 219811 627203 := bstep (se 1 (by rfl) ⟨470402, by rfl⟩ : syracuseStep 627203 = 940805) B940805
theorem B332291 : Blo 219811 332291 := bstep (se 1 (by rfl) ⟨249218, by rfl⟩ : syracuseStep 332291 = 498437) B498437
theorem B266755 : Blo 219811 266755 := bstep (se 1 (by rfl) ⟨200066, by rfl⟩ : syracuseStep 266755 = 400133) B400133
theorem B332321 : Blo 219811 332321 := bstep (se 2 (by rfl) ⟨124620, by rfl⟩ : syracuseStep 332321 = 249241) B249241
theorem B332339 : Blo 219811 332339 := bstep (se 1 (by rfl) ⟨249254, by rfl⟩ : syracuseStep 332339 = 498509) B498509
theorem B299585 : Blo 219811 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B332369 : Blo 219811 332369 := bstep (se 2 (by rfl) ⟨124638, by rfl⟩ : syracuseStep 332369 = 249277) B249277
theorem B332387 : Blo 219811 332387 := bstep (se 1 (by rfl) ⟨249290, by rfl⟩ : syracuseStep 332387 = 498581) B498581
theorem B496241 : Blo 219811 496241 := bstep (se 2 (by rfl) ⟨186090, by rfl⟩ : syracuseStep 496241 = 372181) B372181
theorem B332417 : Blo 219811 332417 := bstep (se 2 (by rfl) ⟨124656, by rfl⟩ : syracuseStep 332417 = 249313) B249313
theorem B496259 : Blo 219811 496259 := bstep (se 1 (by rfl) ⟨372194, by rfl⟩ : syracuseStep 496259 = 744389) B744389
theorem B332435 : Blo 219811 332435 := bstep (se 1 (by rfl) ⟨249326, by rfl⟩ : syracuseStep 332435 = 498653) B498653
theorem B332465 : Blo 219811 332465 := bstep (se 2 (by rfl) ⟨124674, by rfl⟩ : syracuseStep 332465 = 249349) B249349
theorem B332483 : Blo 219811 332483 := bstep (se 1 (by rfl) ⟨249362, by rfl⟩ : syracuseStep 332483 = 498725) B498725
theorem B332513 : Blo 219811 332513 := bstep (se 2 (by rfl) ⟨124692, by rfl⟩ : syracuseStep 332513 = 249385) B249385
theorem B332531 : Blo 219811 332531 := bstep (se 1 (by rfl) ⟨249398, by rfl⟩ : syracuseStep 332531 = 498797) B498797
theorem B332561 : Blo 219811 332561 := bstep (se 2 (by rfl) ⟨124710, by rfl⟩ : syracuseStep 332561 = 249421) B249421
theorem B561937 : Blo 219811 561937 := bstep (se 2 (by rfl) ⟨210726, by rfl⟩ : syracuseStep 561937 = 421453) B421453
theorem B332579 : Blo 219811 332579 := bstep (se 1 (by rfl) ⟨249434, by rfl⟩ : syracuseStep 332579 = 498869) B498869
theorem B332609 : Blo 219811 332609 := bstep (se 2 (by rfl) ⟨124728, by rfl⟩ : syracuseStep 332609 = 249457) B249457
theorem B627533 : Blo 219811 627533 := bstep (se 3 (by rfl) ⟨117662, by rfl⟩ : syracuseStep 627533 = 235325) B235325
theorem B332627 : Blo 219811 332627 := bstep (se 1 (by rfl) ⟨249470, by rfl⟩ : syracuseStep 332627 = 498941) B498941
theorem B332657 : Blo 219811 332657 := bstep (se 2 (by rfl) ⟨124746, by rfl⟩ : syracuseStep 332657 = 249493) B249493
theorem B332675 : Blo 219811 332675 := bstep (se 1 (by rfl) ⟨249506, by rfl⟩ : syracuseStep 332675 = 499013) B499013
theorem B267139 : Blo 219811 267139 := bstep (se 1 (by rfl) ⟨200354, by rfl⟩ : syracuseStep 267139 = 400709) B400709
theorem B627601 : Blo 219811 627601 := bstep (se 2 (by rfl) ⟨235350, by rfl⟩ : syracuseStep 627601 = 470701) B470701
theorem B496529 : Blo 219811 496529 := bstep (se 2 (by rfl) ⟨186198, by rfl⟩ : syracuseStep 496529 = 372397) B372397
theorem B332705 : Blo 219811 332705 := bstep (se 2 (by rfl) ⟨124764, by rfl⟩ : syracuseStep 332705 = 249529) B249529
theorem B496547 : Blo 219811 496547 := bstep (se 1 (by rfl) ⟨372410, by rfl⟩ : syracuseStep 496547 = 744821) B744821
theorem B332723 : Blo 219811 332723 := bstep (se 1 (by rfl) ⟨249542, by rfl⟩ : syracuseStep 332723 = 499085) B499085
theorem B332753 : Blo 219811 332753 := bstep (se 2 (by rfl) ⟨124782, by rfl⟩ : syracuseStep 332753 = 249565) B249565
theorem B332771 : Blo 219811 332771 := bstep (se 1 (by rfl) ⟨249578, by rfl⟩ : syracuseStep 332771 = 499157) B499157
theorem B332801 : Blo 219811 332801 := bstep (se 2 (by rfl) ⟨124800, by rfl⟩ : syracuseStep 332801 = 249601) B249601
theorem B332819 : Blo 219811 332819 := bstep (se 1 (by rfl) ⟨249614, by rfl⟩ : syracuseStep 332819 = 499229) B499229
theorem B562211 : Blo 219811 562211 := bstep (se 1 (by rfl) ⟨421658, by rfl⟩ : syracuseStep 562211 = 843317) B843317
theorem B332849 : Blo 219811 332849 := bstep (se 2 (by rfl) ⟨124818, by rfl⟩ : syracuseStep 332849 = 249637) B249637
theorem B332867 : Blo 219811 332867 := bstep (se 1 (by rfl) ⟨249650, by rfl⟩ : syracuseStep 332867 = 499301) B499301
theorem B332897 : Blo 219811 332897 := bstep (se 2 (by rfl) ⟨124836, by rfl⟩ : syracuseStep 332897 = 249673) B249673
theorem B2823281 : Blo 219811 2823281 := bstep (se 2 (by rfl) ⟨1058730, by rfl⟩ : syracuseStep 2823281 = 2117461) B2117461
theorem B332915 : Blo 219811 332915 := bstep (se 1 (by rfl) ⟨249686, by rfl⟩ : syracuseStep 332915 = 499373) B499373
theorem B332945 : Blo 219811 332945 := bstep (se 2 (by rfl) ⟨124854, by rfl⟩ : syracuseStep 332945 = 249709) B249709
theorem B627875 : Blo 219811 627875 := bstep (se 1 (by rfl) ⟨470906, by rfl⟩ : syracuseStep 627875 = 941813) B941813
theorem B332963 : Blo 219811 332963 := bstep (se 1 (by rfl) ⟨249722, by rfl⟩ : syracuseStep 332963 = 499445) B499445
theorem B496817 : Blo 219811 496817 := bstep (se 2 (by rfl) ⟨186306, by rfl⟩ : syracuseStep 496817 = 372613) B372613
theorem B332993 : Blo 219811 332993 := bstep (se 2 (by rfl) ⟨124872, by rfl⟩ : syracuseStep 332993 = 249745) B249745
theorem B496835 : Blo 219811 496835 := bstep (se 1 (by rfl) ⟨372626, by rfl⟩ : syracuseStep 496835 = 745253) B745253
theorem B333011 : Blo 219811 333011 := bstep (se 1 (by rfl) ⟨249758, by rfl⟩ : syracuseStep 333011 = 499517) B499517
theorem B562403 : Blo 219811 562403 := bstep (se 1 (by rfl) ⟨421802, by rfl⟩ : syracuseStep 562403 = 843605) B843605
theorem B595181 : Blo 219811 595181 := bstep (se 3 (by rfl) ⟨111596, by rfl⟩ : syracuseStep 595181 = 223193) B223193
theorem B333041 : Blo 219811 333041 := bstep (se 2 (by rfl) ⟨124890, by rfl⟩ : syracuseStep 333041 = 249781) B249781
theorem B333059 : Blo 219811 333059 := bstep (se 1 (by rfl) ⟨249794, by rfl⟩ : syracuseStep 333059 = 499589) B499589
theorem B333089 : Blo 219811 333089 := bstep (se 2 (by rfl) ⟨124908, by rfl⟩ : syracuseStep 333089 = 249817) B249817
theorem B333107 : Blo 219811 333107 := bstep (se 1 (by rfl) ⟨249830, by rfl⟩ : syracuseStep 333107 = 499661) B499661
theorem B333137 : Blo 219811 333137 := bstep (se 2 (by rfl) ⟨124926, by rfl⟩ : syracuseStep 333137 = 249853) B249853
theorem B333155 : Blo 219811 333155 := bstep (se 1 (by rfl) ⟨249866, by rfl⟩ : syracuseStep 333155 = 499733) B499733
theorem B333185 : Blo 219811 333185 := bstep (se 2 (by rfl) ⟨124944, by rfl⟩ : syracuseStep 333185 = 249889) B249889
theorem B333203 : Blo 219811 333203 := bstep (se 1 (by rfl) ⟨249902, by rfl⟩ : syracuseStep 333203 = 499805) B499805
theorem B333233 : Blo 219811 333233 := bstep (se 2 (by rfl) ⟨124962, by rfl⟩ : syracuseStep 333233 = 249925) B249925
theorem B333251 : Blo 219811 333251 := bstep (se 1 (by rfl) ⟨249938, by rfl⟩ : syracuseStep 333251 = 499877) B499877
theorem B497105 : Blo 219811 497105 := bstep (se 2 (by rfl) ⟨186414, by rfl⟩ : syracuseStep 497105 = 372829) B372829
theorem B333281 : Blo 219811 333281 := bstep (se 2 (by rfl) ⟨124980, by rfl⟩ : syracuseStep 333281 = 249961) B249961
theorem B497123 : Blo 219811 497123 := bstep (se 1 (by rfl) ⟨372842, by rfl⟩ : syracuseStep 497123 = 745685) B745685
theorem B333299 : Blo 219811 333299 := bstep (se 1 (by rfl) ⟨249974, by rfl⟩ : syracuseStep 333299 = 499949) B499949
theorem B759299 : Blo 219811 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B333329 : Blo 219811 333329 := bstep (se 2 (by rfl) ⟨124998, by rfl⟩ : syracuseStep 333329 = 249997) B249997
theorem B333347 : Blo 219811 333347 := bstep (se 1 (by rfl) ⟨250010, by rfl⟩ : syracuseStep 333347 = 500021) B500021
theorem B333377 : Blo 219811 333377 := bstep (se 2 (by rfl) ⟨125016, by rfl⟩ : syracuseStep 333377 = 250033) B250033
theorem B333395 : Blo 219811 333395 := bstep (se 1 (by rfl) ⟨250046, by rfl⟩ : syracuseStep 333395 = 500093) B500093
theorem B333425 : Blo 219811 333425 := bstep (se 2 (by rfl) ⟨125034, by rfl⟩ : syracuseStep 333425 = 250069) B250069
theorem B333443 : Blo 219811 333443 := bstep (se 1 (by rfl) ⟨250082, by rfl⟩ : syracuseStep 333443 = 500165) B500165
theorem B333473 : Blo 219811 333473 := bstep (se 2 (by rfl) ⟨125052, by rfl⟩ : syracuseStep 333473 = 250105) B250105
theorem B235171 : Blo 219811 235171 := bstep (se 1 (by rfl) ⟨176378, by rfl⟩ : syracuseStep 235171 = 352757) B352757
theorem B333491 : Blo 219811 333491 := bstep (se 1 (by rfl) ⟨250118, by rfl⟩ : syracuseStep 333491 = 500237) B500237
theorem B333521 : Blo 219811 333521 := bstep (se 2 (by rfl) ⟨125070, by rfl⟩ : syracuseStep 333521 = 250141) B250141
theorem B333539 : Blo 219811 333539 := bstep (se 1 (by rfl) ⟨250154, by rfl⟩ : syracuseStep 333539 = 500309) B500309
theorem B497393 : Blo 219811 497393 := bstep (se 2 (by rfl) ⟨186522, by rfl⟩ : syracuseStep 497393 = 373045) B373045
theorem B333569 : Blo 219811 333569 := bstep (se 2 (by rfl) ⟨125088, by rfl⟩ : syracuseStep 333569 = 250177) B250177
theorem B497411 : Blo 219811 497411 := bstep (se 1 (by rfl) ⟨373058, by rfl⟩ : syracuseStep 497411 = 746117) B746117
theorem B333587 : Blo 219811 333587 := bstep (se 1 (by rfl) ⟨250190, by rfl⟩ : syracuseStep 333587 = 500381) B500381
theorem B333617 : Blo 219811 333617 := bstep (se 2 (by rfl) ⟨125106, by rfl⟩ : syracuseStep 333617 = 250213) B250213
theorem B333635 : Blo 219811 333635 := bstep (se 1 (by rfl) ⟨250226, by rfl⟩ : syracuseStep 333635 = 500453) B500453
theorem B333665 : Blo 219811 333665 := bstep (se 2 (by rfl) ⟨125124, by rfl⟩ : syracuseStep 333665 = 250249) B250249
theorem B1709923 : Blo 219811 1709923 := bstep (se 1 (by rfl) ⟨1282442, by rfl⟩ : syracuseStep 1709923 = 2564885) B2564885
theorem B333683 : Blo 219811 333683 := bstep (se 1 (by rfl) ⟨250262, by rfl⟩ : syracuseStep 333683 = 500525) B500525
theorem B333713 : Blo 219811 333713 := bstep (se 2 (by rfl) ⟨125142, by rfl⟩ : syracuseStep 333713 = 250285) B250285
theorem B333731 : Blo 219811 333731 := bstep (se 1 (by rfl) ⟨250298, by rfl⟩ : syracuseStep 333731 = 500597) B500597
theorem B333761 : Blo 219811 333761 := bstep (se 2 (by rfl) ⟨125160, by rfl⟩ : syracuseStep 333761 = 250321) B250321
theorem B333779 : Blo 219811 333779 := bstep (se 1 (by rfl) ⟨250334, by rfl⟩ : syracuseStep 333779 = 500669) B500669
theorem B399331 : Blo 219811 399331 := bstep (se 1 (by rfl) ⟨299498, by rfl⟩ : syracuseStep 399331 = 598997) B598997
theorem B628717 : Blo 219811 628717 := bstep (se 3 (by rfl) ⟨117884, by rfl⟩ : syracuseStep 628717 = 235769) B235769
theorem B333809 : Blo 219811 333809 := bstep (se 2 (by rfl) ⟨125178, by rfl⟩ : syracuseStep 333809 = 250357) B250357
theorem B333827 : Blo 219811 333827 := bstep (se 1 (by rfl) ⟨250370, by rfl⟩ : syracuseStep 333827 = 500741) B500741
theorem B497681 : Blo 219811 497681 := bstep (se 2 (by rfl) ⟨186630, by rfl⟩ : syracuseStep 497681 = 373261) B373261
theorem B333857 : Blo 219811 333857 := bstep (se 2 (by rfl) ⟨125196, by rfl⟩ : syracuseStep 333857 = 250393) B250393
theorem B497699 : Blo 219811 497699 := bstep (se 1 (by rfl) ⟨373274, by rfl⟩ : syracuseStep 497699 = 746549) B746549
theorem B333875 : Blo 219811 333875 := bstep (se 1 (by rfl) ⟨250406, by rfl⟩ : syracuseStep 333875 = 500813) B500813
theorem B333905 : Blo 219811 333905 := bstep (se 2 (by rfl) ⟨125214, by rfl⟩ : syracuseStep 333905 = 250429) B250429
theorem B301153 : Blo 219811 301153 := bstep (se 2 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 301153 = 225865) B225865
theorem B333923 : Blo 219811 333923 := bstep (se 1 (by rfl) ⟨250442, by rfl⟩ : syracuseStep 333923 = 500885) B500885
theorem B333953 : Blo 219811 333953 := bstep (se 2 (by rfl) ⟨125232, by rfl⟩ : syracuseStep 333953 = 250465) B250465
theorem B628877 : Blo 219811 628877 := bstep (se 3 (by rfl) ⟨117914, by rfl⟩ : syracuseStep 628877 = 235829) B235829
theorem B563345 : Blo 219811 563345 := bstep (se 2 (by rfl) ⟨211254, by rfl⟩ : syracuseStep 563345 = 422509) B422509
theorem B333971 : Blo 219811 333971 := bstep (se 1 (by rfl) ⟨250478, by rfl⟩ : syracuseStep 333971 = 500957) B500957
theorem B334001 : Blo 219811 334001 := bstep (se 2 (by rfl) ⟨125250, by rfl⟩ : syracuseStep 334001 = 250501) B250501
theorem B563395 : Blo 219811 563395 := bstep (se 1 (by rfl) ⟨422546, by rfl⟩ : syracuseStep 563395 = 845093) B845093
theorem B334019 : Blo 219811 334019 := bstep (se 1 (by rfl) ⟨250514, by rfl⟩ : syracuseStep 334019 = 501029) B501029
theorem B2398405 : Blo 219811 2398405 := bstep (se 4 (by rfl) ⟨224850, by rfl⟩ : syracuseStep 2398405 = 449701) B449701
theorem B334049 : Blo 219811 334049 := bstep (se 2 (by rfl) ⟨125268, by rfl⟩ : syracuseStep 334049 = 250537) B250537
theorem B334067 : Blo 219811 334067 := bstep (se 1 (by rfl) ⟨250550, by rfl⟩ : syracuseStep 334067 = 501101) B501101
theorem B334097 : Blo 219811 334097 := bstep (se 2 (by rfl) ⟨125286, by rfl⟩ : syracuseStep 334097 = 250573) B250573
theorem B334115 : Blo 219811 334115 := bstep (se 1 (by rfl) ⟨250586, by rfl⟩ : syracuseStep 334115 = 501173) B501173
theorem B497969 : Blo 219811 497969 := bstep (se 2 (by rfl) ⟨186738, by rfl⟩ : syracuseStep 497969 = 373477) B373477
theorem B334145 : Blo 219811 334145 := bstep (se 2 (by rfl) ⟨125304, by rfl⟩ : syracuseStep 334145 = 250609) B250609
theorem B629059 : Blo 219811 629059 := bstep (se 1 (by rfl) ⟨471794, by rfl⟩ : syracuseStep 629059 = 943589) B943589
theorem B497987 : Blo 219811 497987 := bstep (se 1 (by rfl) ⟨373490, by rfl⟩ : syracuseStep 497987 = 746981) B746981
theorem B563537 : Blo 219811 563537 := bstep (se 2 (by rfl) ⟨211326, by rfl⟩ : syracuseStep 563537 = 422653) B422653
theorem B334163 : Blo 219811 334163 := bstep (se 1 (by rfl) ⟨250622, by rfl⟩ : syracuseStep 334163 = 501245) B501245
theorem B2857315 : Blo 219811 2857315 := bstep (se 1 (by rfl) ⟨2142986, by rfl⟩ : syracuseStep 2857315 = 4285973) B4285973
theorem B334193 : Blo 219811 334193 := bstep (se 2 (by rfl) ⟨125322, by rfl⟩ : syracuseStep 334193 = 250645) B250645
theorem B530819 : Blo 219811 530819 := bstep (se 1 (by rfl) ⟨398114, by rfl⟩ : syracuseStep 530819 = 796229) B796229
theorem B334211 : Blo 219811 334211 := bstep (se 1 (by rfl) ⟨250658, by rfl⟩ : syracuseStep 334211 = 501317) B501317
theorem B334241 : Blo 219811 334241 := bstep (se 2 (by rfl) ⟨125340, by rfl⟩ : syracuseStep 334241 = 250681) B250681
theorem B334259 : Blo 219811 334259 := bstep (se 1 (by rfl) ⟨250694, by rfl⟩ : syracuseStep 334259 = 501389) B501389
theorem B334289 : Blo 219811 334289 := bstep (se 2 (by rfl) ⟨125358, by rfl⟩ : syracuseStep 334289 = 250717) B250717
theorem B334307 : Blo 219811 334307 := bstep (se 1 (by rfl) ⟨250730, by rfl⟩ : syracuseStep 334307 = 501461) B501461
theorem B334337 : Blo 219811 334337 := bstep (se 2 (by rfl) ⟨125376, by rfl⟩ : syracuseStep 334337 = 250753) B250753
theorem B334355 : Blo 219811 334355 := bstep (se 1 (by rfl) ⟨250766, by rfl⟩ : syracuseStep 334355 = 501533) B501533
theorem B334385 : Blo 219811 334385 := bstep (se 2 (by rfl) ⟨125394, by rfl⟩ : syracuseStep 334385 = 250789) B250789
theorem B6068789 : Blo 219811 6068789 := bstep (se 5 (by rfl) ⟨284474, by rfl⟩ : syracuseStep 6068789 = 568949) B568949
theorem B334403 : Blo 219811 334403 := bstep (se 1 (by rfl) ⟨250802, by rfl⟩ : syracuseStep 334403 = 501605) B501605
theorem B498257 : Blo 219811 498257 := bstep (se 2 (by rfl) ⟨186846, by rfl⟩ : syracuseStep 498257 = 373693) B373693
theorem B334433 : Blo 219811 334433 := bstep (se 2 (by rfl) ⟨125412, by rfl⟩ : syracuseStep 334433 = 250825) B250825
theorem B498275 : Blo 219811 498275 := bstep (se 1 (by rfl) ⟨373706, by rfl⟩ : syracuseStep 498275 = 747413) B747413
theorem B334451 : Blo 219811 334451 := bstep (se 1 (by rfl) ⟨250838, by rfl⟩ : syracuseStep 334451 = 501677) B501677
theorem B334481 : Blo 219811 334481 := bstep (se 2 (by rfl) ⟨125430, by rfl⟩ : syracuseStep 334481 = 250861) B250861
theorem B236179 : Blo 219811 236179 := bstep (se 1 (by rfl) ⟨177134, by rfl⟩ : syracuseStep 236179 = 354269) B354269
theorem B334499 : Blo 219811 334499 := bstep (se 1 (by rfl) ⟨250874, by rfl⟩ : syracuseStep 334499 = 501749) B501749
theorem B334529 : Blo 219811 334529 := bstep (se 2 (by rfl) ⟨125448, by rfl⟩ : syracuseStep 334529 = 250897) B250897
theorem B400081 : Blo 219811 400081 := bstep (se 2 (by rfl) ⟨150030, by rfl⟩ : syracuseStep 400081 = 300061) B300061
theorem B334547 : Blo 219811 334547 := bstep (se 1 (by rfl) ⟨250910, by rfl⟩ : syracuseStep 334547 = 501821) B501821
theorem B334577 : Blo 219811 334577 := bstep (se 2 (by rfl) ⟨125466, by rfl⟩ : syracuseStep 334577 = 250933) B250933
theorem B334595 : Blo 219811 334595 := bstep (se 1 (by rfl) ⟨250946, by rfl⟩ : syracuseStep 334595 = 501893) B501893
theorem B334625 : Blo 219811 334625 := bstep (se 2 (by rfl) ⟨125484, by rfl⟩ : syracuseStep 334625 = 250969) B250969
theorem B596771 : Blo 219811 596771 := bstep (se 1 (by rfl) ⟨447578, by rfl⟩ : syracuseStep 596771 = 895157) B895157
theorem B334643 : Blo 219811 334643 := bstep (se 1 (by rfl) ⟨250982, by rfl⟩ : syracuseStep 334643 = 501965) B501965
theorem B334673 : Blo 219811 334673 := bstep (se 2 (by rfl) ⟨125502, by rfl⟩ : syracuseStep 334673 = 251005) B251005
theorem B334691 : Blo 219811 334691 := bstep (se 1 (by rfl) ⟨251018, by rfl⟩ : syracuseStep 334691 = 502037) B502037
theorem B498545 : Blo 219811 498545 := bstep (se 2 (by rfl) ⟨186954, by rfl⟩ : syracuseStep 498545 = 373909) B373909
theorem B334721 : Blo 219811 334721 := bstep (se 2 (by rfl) ⟨125520, by rfl⟩ : syracuseStep 334721 = 251041) B251041
theorem B498563 : Blo 219811 498563 := bstep (se 1 (by rfl) ⟨373922, by rfl⟩ : syracuseStep 498563 = 747845) B747845
theorem B334739 : Blo 219811 334739 := bstep (se 1 (by rfl) ⟨251054, by rfl⟩ : syracuseStep 334739 = 502109) B502109
theorem B1121201 : Blo 219811 1121201 := bstep (se 2 (by rfl) ⟨420450, by rfl⟩ : syracuseStep 1121201 = 840901) B840901
theorem B334769 : Blo 219811 334769 := bstep (se 2 (by rfl) ⟨125538, by rfl⟩ : syracuseStep 334769 = 251077) B251077
theorem B334787 : Blo 219811 334787 := bstep (se 1 (by rfl) ⟨251090, by rfl⟩ : syracuseStep 334787 = 502181) B502181
theorem B334817 : Blo 219811 334817 := bstep (se 2 (by rfl) ⟨125556, by rfl⟩ : syracuseStep 334817 = 251113) B251113
theorem B334835 : Blo 219811 334835 := bstep (se 1 (by rfl) ⟨251126, by rfl⟩ : syracuseStep 334835 = 502253) B502253
theorem B334865 : Blo 219811 334865 := bstep (se 2 (by rfl) ⟨125574, by rfl⟩ : syracuseStep 334865 = 251149) B251149
theorem B334883 : Blo 219811 334883 := bstep (se 1 (by rfl) ⟨251162, by rfl⟩ : syracuseStep 334883 = 502325) B502325
theorem B334913 : Blo 219811 334913 := bstep (se 2 (by rfl) ⟨125592, by rfl⟩ : syracuseStep 334913 = 251185) B251185
theorem B334931 : Blo 219811 334931 := bstep (se 1 (by rfl) ⟨251198, by rfl⟩ : syracuseStep 334931 = 502397) B502397
theorem B334961 : Blo 219811 334961 := bstep (se 2 (by rfl) ⟨125610, by rfl⟩ : syracuseStep 334961 = 251221) B251221
theorem B334979 : Blo 219811 334979 := bstep (se 1 (by rfl) ⟨251234, by rfl⟩ : syracuseStep 334979 = 502469) B502469
theorem B498833 : Blo 219811 498833 := bstep (se 2 (by rfl) ⟨187062, by rfl⟩ : syracuseStep 498833 = 374125) B374125
theorem B335009 : Blo 219811 335009 := bstep (se 2 (by rfl) ⟨125628, by rfl⟩ : syracuseStep 335009 = 251257) B251257
theorem B498851 : Blo 219811 498851 := bstep (se 1 (by rfl) ⟨374138, by rfl⟩ : syracuseStep 498851 = 748277) B748277
theorem B335027 : Blo 219811 335027 := bstep (se 1 (by rfl) ⟨251270, by rfl⟩ : syracuseStep 335027 = 502541) B502541
theorem B335057 : Blo 219811 335057 := bstep (se 2 (by rfl) ⟨125646, by rfl⟩ : syracuseStep 335057 = 251293) B251293
theorem B335075 : Blo 219811 335075 := bstep (se 1 (by rfl) ⟨251306, by rfl⟩ : syracuseStep 335075 = 502613) B502613
theorem B335105 : Blo 219811 335105 := bstep (se 2 (by rfl) ⟨125664, by rfl⟩ : syracuseStep 335105 = 251329) B251329
theorem B400657 : Blo 219811 400657 := bstep (se 2 (by rfl) ⟨150246, by rfl⟩ : syracuseStep 400657 = 300493) B300493
theorem B335123 : Blo 219811 335123 := bstep (se 1 (by rfl) ⟨251342, by rfl⟩ : syracuseStep 335123 = 502685) B502685
theorem B564529 : Blo 219811 564529 := bstep (se 2 (by rfl) ⟨211698, by rfl⟩ : syracuseStep 564529 = 423397) B423397
theorem B335153 : Blo 219811 335153 := bstep (se 2 (by rfl) ⟨125682, by rfl⟩ : syracuseStep 335153 = 251365) B251365
theorem B335171 : Blo 219811 335171 := bstep (se 1 (by rfl) ⟨251378, by rfl⟩ : syracuseStep 335171 = 502757) B502757
theorem B335201 : Blo 219811 335201 := bstep (se 2 (by rfl) ⟨125700, by rfl⟩ : syracuseStep 335201 = 251401) B251401
theorem B335219 : Blo 219811 335219 := bstep (se 1 (by rfl) ⟨251414, by rfl⟩ : syracuseStep 335219 = 502829) B502829
theorem B335249 : Blo 219811 335249 := bstep (se 2 (by rfl) ⟨125718, by rfl⟩ : syracuseStep 335249 = 251437) B251437
theorem B335267 : Blo 219811 335267 := bstep (se 1 (by rfl) ⟨251450, by rfl⟩ : syracuseStep 335267 = 502901) B502901
theorem B499121 : Blo 219811 499121 := bstep (se 2 (by rfl) ⟨187170, by rfl⟩ : syracuseStep 499121 = 374341) B374341
theorem B335297 : Blo 219811 335297 := bstep (se 2 (by rfl) ⟨125736, by rfl⟩ : syracuseStep 335297 = 251473) B251473
theorem B499139 : Blo 219811 499139 := bstep (se 1 (by rfl) ⟨374354, by rfl⟩ : syracuseStep 499139 = 748709) B748709
theorem B335315 : Blo 219811 335315 := bstep (se 1 (by rfl) ⟨251486, by rfl⟩ : syracuseStep 335315 = 502973) B502973
theorem B335345 : Blo 219811 335345 := bstep (se 2 (by rfl) ⟨125754, by rfl⟩ : syracuseStep 335345 = 251509) B251509
theorem B335363 : Blo 219811 335363 := bstep (se 1 (by rfl) ⟨251522, by rfl⟩ : syracuseStep 335363 = 503045) B503045
theorem B335393 : Blo 219811 335393 := bstep (se 2 (by rfl) ⟨125772, by rfl⟩ : syracuseStep 335393 = 251545) B251545
theorem B335411 : Blo 219811 335411 := bstep (se 1 (by rfl) ⟨251558, by rfl⟩ : syracuseStep 335411 = 503117) B503117
theorem B564803 : Blo 219811 564803 := bstep (se 1 (by rfl) ⟨423602, by rfl⟩ : syracuseStep 564803 = 847205) B847205
theorem B335441 : Blo 219811 335441 := bstep (se 2 (by rfl) ⟨125790, by rfl⟩ : syracuseStep 335441 = 251581) B251581
theorem B335459 : Blo 219811 335459 := bstep (se 1 (by rfl) ⟨251594, by rfl⟩ : syracuseStep 335459 = 503189) B503189
theorem B597613 : Blo 219811 597613 := bstep (se 3 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 597613 = 224105) B224105
theorem B892529 : Blo 219811 892529 := bstep (se 2 (by rfl) ⟨334698, by rfl⟩ : syracuseStep 892529 = 669397) B669397
theorem B335489 : Blo 219811 335489 := bstep (se 2 (by rfl) ⟨125808, by rfl⟩ : syracuseStep 335489 = 251617) B251617
theorem B237187 : Blo 219811 237187 := bstep (se 1 (by rfl) ⟨177890, by rfl⟩ : syracuseStep 237187 = 355781) B355781
theorem B335507 : Blo 219811 335507 := bstep (se 1 (by rfl) ⟨251630, by rfl⟩ : syracuseStep 335507 = 503261) B503261
theorem B630449 : Blo 219811 630449 := bstep (se 2 (by rfl) ⟨236418, by rfl⟩ : syracuseStep 630449 = 472837) B472837
theorem B335537 : Blo 219811 335537 := bstep (se 2 (by rfl) ⟨125826, by rfl⟩ : syracuseStep 335537 = 251653) B251653
theorem B335555 : Blo 219811 335555 := bstep (se 1 (by rfl) ⟨251666, by rfl⟩ : syracuseStep 335555 = 503333) B503333
theorem B499409 : Blo 219811 499409 := bstep (se 2 (by rfl) ⟨187278, by rfl⟩ : syracuseStep 499409 = 374557) B374557
theorem B335585 : Blo 219811 335585 := bstep (se 2 (by rfl) ⟨125844, by rfl⟩ : syracuseStep 335585 = 251689) B251689
theorem B499427 : Blo 219811 499427 := bstep (se 1 (by rfl) ⟨374570, by rfl⟩ : syracuseStep 499427 = 749141) B749141
theorem B335603 : Blo 219811 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B564995 : Blo 219811 564995 := bstep (se 1 (by rfl) ⟨423746, by rfl⟩ : syracuseStep 564995 = 847493) B847493
theorem B335633 : Blo 219811 335633 := bstep (se 2 (by rfl) ⟨125862, by rfl⟩ : syracuseStep 335633 = 251725) B251725
theorem B335651 : Blo 219811 335651 := bstep (se 1 (by rfl) ⟨251738, by rfl⟩ : syracuseStep 335651 = 503477) B503477
theorem B335681 : Blo 219811 335681 := bstep (se 2 (by rfl) ⟨125880, by rfl⟩ : syracuseStep 335681 = 251761) B251761
theorem B335699 : Blo 219811 335699 := bstep (se 1 (by rfl) ⟨251774, by rfl⟩ : syracuseStep 335699 = 503549) B503549
theorem B3710861 : Blo 219811 3710861 := bstep (se 3 (by rfl) ⟨695786, by rfl⟩ : syracuseStep 3710861 = 1391573) B1391573
theorem B532433 : Blo 219811 532433 := bstep (se 2 (by rfl) ⟨199662, by rfl⟩ : syracuseStep 532433 = 399325) B399325
theorem B499697 : Blo 219811 499697 := bstep (se 2 (by rfl) ⟨187386, by rfl⟩ : syracuseStep 499697 = 374773) B374773
theorem B499715 : Blo 219811 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B2138339 : Blo 219811 2138339 := bstep (se 1 (by rfl) ⟨1603754, by rfl⟩ : syracuseStep 2138339 = 3207509) B3207509
theorem B237811 : Blo 219811 237811 := bstep (se 1 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 237811 = 356717) B356717
theorem B499985 : Blo 219811 499985 := bstep (se 2 (by rfl) ⟨187494, by rfl⟩ : syracuseStep 499985 = 374989) B374989
theorem B500003 : Blo 219811 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B1122659 : Blo 219811 1122659 := bstep (se 1 (by rfl) ⟨841994, by rfl⟩ : syracuseStep 1122659 = 1683989) B1683989
theorem B565667 : Blo 219811 565667 := bstep (se 1 (by rfl) ⟨424250, by rfl⟩ : syracuseStep 565667 = 848501) B848501
theorem B500273 : Blo 219811 500273 := bstep (se 2 (by rfl) ⟨187602, by rfl⟩ : syracuseStep 500273 = 375205) B375205
theorem B500291 : Blo 219811 500291 := bstep (se 1 (by rfl) ⟨375218, by rfl⟩ : syracuseStep 500291 = 750437) B750437
theorem B631405 : Blo 219811 631405 := bstep (se 3 (by rfl) ⟨118388, by rfl⟩ : syracuseStep 631405 = 236777) B236777
theorem B1548941 : Blo 219811 1548941 := bstep (se 3 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 1548941 = 580853) B580853
theorem B565937 : Blo 219811 565937 := bstep (se 2 (by rfl) ⟨212226, by rfl⟩ : syracuseStep 565937 = 424453) B424453
theorem B565987 : Blo 219811 565987 := bstep (se 1 (by rfl) ⟨424490, by rfl⟩ : syracuseStep 565987 = 848981) B848981
theorem B566033 : Blo 219811 566033 := bstep (se 2 (by rfl) ⟨212262, by rfl⟩ : syracuseStep 566033 = 424525) B424525
theorem B631633 : Blo 219811 631633 := bstep (se 2 (by rfl) ⟨236862, by rfl⟩ : syracuseStep 631633 = 473725) B473725
theorem B500561 : Blo 219811 500561 := bstep (se 2 (by rfl) ⟨187710, by rfl⟩ : syracuseStep 500561 = 375421) B375421
theorem B795491 : Blo 219811 795491 := bstep (se 1 (by rfl) ⟨596618, by rfl⟩ : syracuseStep 795491 = 1193237) B1193237
theorem B500579 : Blo 219811 500579 := bstep (se 1 (by rfl) ⟨375434, by rfl⟩ : syracuseStep 500579 = 750869) B750869
theorem B566129 : Blo 219811 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B402403 : Blo 219811 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B631793 : Blo 219811 631793 := bstep (se 2 (by rfl) ⟨236922, by rfl⟩ : syracuseStep 631793 = 473845) B473845
theorem B4138037 : Blo 219811 4138037 := bstep (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) B387941
theorem B631907 : Blo 219811 631907 := bstep (se 1 (by rfl) ⟨473930, by rfl⟩ : syracuseStep 631907 = 947861) B947861
theorem B500849 : Blo 219811 500849 := bstep (se 2 (by rfl) ⟨187818, by rfl⟩ : syracuseStep 500849 = 375637) B375637
theorem B500867 : Blo 219811 500867 := bstep (se 1 (by rfl) ⟨375650, by rfl⟩ : syracuseStep 500867 = 751301) B751301
theorem B1123469 : Blo 219811 1123469 := bstep (se 3 (by rfl) ⟨210650, by rfl⟩ : syracuseStep 1123469 = 421301) B421301
theorem B599213 : Blo 219811 599213 := bstep (se 3 (by rfl) ⟨112352, by rfl⟩ : syracuseStep 599213 = 224705) B224705
theorem B402691 : Blo 219811 402691 := bstep (se 1 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 402691 = 604037) B604037
theorem B501137 : Blo 219811 501137 := bstep (se 2 (by rfl) ⟨187926, by rfl⟩ : syracuseStep 501137 = 375853) B375853
theorem B501155 : Blo 219811 501155 := bstep (se 1 (by rfl) ⟨375866, by rfl⟩ : syracuseStep 501155 = 751733) B751733
theorem B304769 : Blo 219811 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B501425 : Blo 219811 501425 := bstep (se 2 (by rfl) ⟨188034, by rfl⟩ : syracuseStep 501425 = 376069) B376069
theorem B501443 : Blo 219811 501443 := bstep (se 1 (by rfl) ⟨376082, by rfl⟩ : syracuseStep 501443 = 752165) B752165
theorem B894797 : Blo 219811 894797 := bstep (se 3 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 894797 = 335549) B335549
theorem B501713 : Blo 219811 501713 := bstep (se 2 (by rfl) ⟨188142, by rfl⟩ : syracuseStep 501713 = 376285) B376285
theorem B501731 : Blo 219811 501731 := bstep (se 1 (by rfl) ⟨376298, by rfl⟩ : syracuseStep 501731 = 752597) B752597
theorem B632909 : Blo 219811 632909 := bstep (se 3 (by rfl) ⟨118670, by rfl⟩ : syracuseStep 632909 = 237341) B237341
theorem B534691 : Blo 219811 534691 := bstep (se 1 (by rfl) ⟨401018, by rfl⟩ : syracuseStep 534691 = 802037) B802037
theorem B502001 : Blo 219811 502001 := bstep (se 2 (by rfl) ⟨188250, by rfl⟩ : syracuseStep 502001 = 376501) B376501
theorem B305411 : Blo 219811 305411 := bstep (se 1 (by rfl) ⟨229058, by rfl⟩ : syracuseStep 305411 = 458117) B458117
theorem B633091 : Blo 219811 633091 := bstep (se 1 (by rfl) ⟨474818, by rfl⟩ : syracuseStep 633091 = 949637) B949637
theorem B502019 : Blo 219811 502019 := bstep (se 1 (by rfl) ⟨376514, by rfl⟩ : syracuseStep 502019 = 753029) B753029
theorem B370993 : Blo 219811 370993 := bstep (se 2 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 370993 = 278245) B278245
theorem B3909941 : Blo 219811 3909941 := bstep (se 5 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 3909941 = 366557) B366557
theorem B371027 : Blo 219811 371027 := bstep (se 1 (by rfl) ⟨278270, by rfl⟩ : syracuseStep 371027 = 556541) B556541
theorem B633251 : Blo 219811 633251 := bstep (se 1 (by rfl) ⟨474938, by rfl⟩ : syracuseStep 633251 = 949877) B949877
theorem B371155 : Blo 219811 371155 := bstep (se 1 (by rfl) ⟨278366, by rfl⟩ : syracuseStep 371155 = 556733) B556733
theorem B502289 : Blo 219811 502289 := bstep (se 2 (by rfl) ⟨188358, by rfl⟩ : syracuseStep 502289 = 376717) B376717
theorem B502307 : Blo 219811 502307 := bstep (se 1 (by rfl) ⟨376730, by rfl⟩ : syracuseStep 502307 = 753461) B753461
theorem B371297 : Blo 219811 371297 := bstep (se 2 (by rfl) ⟨139236, by rfl⟩ : syracuseStep 371297 = 278473) B278473
theorem B371425 : Blo 219811 371425 := bstep (se 2 (by rfl) ⟨139284, by rfl⟩ : syracuseStep 371425 = 278569) B278569
theorem B371459 : Blo 219811 371459 := bstep (se 1 (by rfl) ⟨278594, by rfl⟩ : syracuseStep 371459 = 557189) B557189
theorem B469795 : Blo 219811 469795 := bstep (se 1 (by rfl) ⟨352346, by rfl⟩ : syracuseStep 469795 = 704693) B704693
theorem B502577 : Blo 219811 502577 := bstep (se 2 (by rfl) ⟨188466, by rfl⟩ : syracuseStep 502577 = 376933) B376933
theorem B502595 : Blo 219811 502595 := bstep (se 1 (by rfl) ⟨376946, by rfl⟩ : syracuseStep 502595 = 753893) B753893
theorem B371587 : Blo 219811 371587 := bstep (se 1 (by rfl) ⟨278690, by rfl⟩ : syracuseStep 371587 = 557381) B557381
theorem B601073 : Blo 219811 601073 := bstep (se 2 (by rfl) ⟨225402, by rfl⟩ : syracuseStep 601073 = 450805) B450805
theorem B371729 : Blo 219811 371729 := bstep (se 2 (by rfl) ⟨139398, by rfl⟩ : syracuseStep 371729 = 278797) B278797
theorem B502865 : Blo 219811 502865 := bstep (se 2 (by rfl) ⟨188574, by rfl⟩ : syracuseStep 502865 = 377149) B377149
theorem B1682531 : Blo 219811 1682531 := bstep (se 1 (by rfl) ⟨1261898, by rfl⟩ : syracuseStep 1682531 = 2523797) B2523797
theorem B502883 : Blo 219811 502883 := bstep (se 1 (by rfl) ⟨377162, by rfl⟩ : syracuseStep 502883 = 754325) B754325
theorem B1715341 : Blo 219811 1715341 := bstep (se 3 (by rfl) ⟨321626, by rfl⟩ : syracuseStep 1715341 = 643253) B643253
theorem B371857 : Blo 219811 371857 := bstep (se 2 (by rfl) ⟨139446, by rfl⟩ : syracuseStep 371857 = 278893) B278893
theorem B765101 : Blo 219811 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B371891 : Blo 219811 371891 := bstep (se 1 (by rfl) ⟨278918, by rfl⟩ : syracuseStep 371891 = 557837) B557837
theorem B896291 : Blo 219811 896291 := bstep (se 1 (by rfl) ⟨672218, by rfl⟩ : syracuseStep 896291 = 1344437) B1344437
theorem B372019 : Blo 219811 372019 := bstep (se 1 (by rfl) ⟨279014, by rfl⟩ : syracuseStep 372019 = 558029) B558029
theorem B503153 : Blo 219811 503153 := bstep (se 2 (by rfl) ⟨188682, by rfl⟩ : syracuseStep 503153 = 377365) B377365
theorem B503171 : Blo 219811 503171 := bstep (se 1 (by rfl) ⟨377378, by rfl⟩ : syracuseStep 503171 = 754757) B754757
theorem B372161 : Blo 219811 372161 := bstep (se 2 (by rfl) ⟨139560, by rfl⟩ : syracuseStep 372161 = 279121) B279121
theorem B634321 : Blo 219811 634321 := bstep (se 2 (by rfl) ⟨237870, by rfl⟩ : syracuseStep 634321 = 475741) B475741
theorem B536017 : Blo 219811 536017 := bstep (se 2 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 536017 = 402013) B402013
theorem B1879523 : Blo 219811 1879523 := bstep (se 1 (by rfl) ⟨1409642, by rfl⟩ : syracuseStep 1879523 = 2819285) B2819285
theorem B372289 : Blo 219811 372289 := bstep (se 2 (by rfl) ⟨139608, by rfl⟩ : syracuseStep 372289 = 279217) B279217
theorem B372323 : Blo 219811 372323 := bstep (se 1 (by rfl) ⟨279242, by rfl⟩ : syracuseStep 372323 = 558485) B558485
theorem B503441 : Blo 219811 503441 := bstep (se 2 (by rfl) ⟨188790, by rfl⟩ : syracuseStep 503441 = 377581) B377581
theorem B503459 : Blo 219811 503459 := bstep (se 1 (by rfl) ⟨377594, by rfl⟩ : syracuseStep 503459 = 755189) B755189
theorem B372451 : Blo 219811 372451 := bstep (se 1 (by rfl) ⟨279338, by rfl⟩ : syracuseStep 372451 = 558677) B558677
theorem B765677 : Blo 219811 765677 := bstep (se 3 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 765677 = 287129) B287129
theorem B372593 : Blo 219811 372593 := bstep (se 2 (by rfl) ⟨139722, by rfl⟩ : syracuseStep 372593 = 279445) B279445
theorem B2142065 : Blo 219811 2142065 := bstep (se 2 (by rfl) ⟨803274, by rfl⟩ : syracuseStep 2142065 = 1606549) B1606549
theorem B405425 : Blo 219811 405425 := bstep (se 2 (by rfl) ⟨152034, by rfl⟩ : syracuseStep 405425 = 304069) B304069
theorem B471025 : Blo 219811 471025 := bstep (se 2 (by rfl) ⟨176634, by rfl⟩ : syracuseStep 471025 = 353269) B353269
theorem B372721 : Blo 219811 372721 := bstep (se 2 (by rfl) ⟨139770, by rfl⟩ : syracuseStep 372721 = 279541) B279541
theorem B1126385 : Blo 219811 1126385 := bstep (se 2 (by rfl) ⟨422394, by rfl⟩ : syracuseStep 1126385 = 844789) B844789
theorem B372755 : Blo 219811 372755 := bstep (se 1 (by rfl) ⟨279566, by rfl⟩ : syracuseStep 372755 = 559133) B559133
theorem B372883 : Blo 219811 372883 := bstep (se 1 (by rfl) ⟨279662, by rfl⟩ : syracuseStep 372883 = 559325) B559325
theorem B602275 : Blo 219811 602275 := bstep (se 1 (by rfl) ⟨451706, by rfl⟩ : syracuseStep 602275 = 903413) B903413
theorem B373025 : Blo 219811 373025 := bstep (se 2 (by rfl) ⟨139884, by rfl⟩ : syracuseStep 373025 = 279769) B279769
theorem B536977 : Blo 219811 536977 := bstep (se 2 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 536977 = 402733) B402733
theorem B373153 : Blo 219811 373153 := bstep (se 2 (by rfl) ⟨139932, by rfl⟩ : syracuseStep 373153 = 279865) B279865
theorem B373187 : Blo 219811 373187 := bstep (se 1 (by rfl) ⟨279890, by rfl⟩ : syracuseStep 373187 = 559781) B559781
theorem B930253 : Blo 219811 930253 := bstep (se 3 (by rfl) ⟨174422, by rfl⟩ : syracuseStep 930253 = 348845) B348845
theorem B340499 : Blo 219811 340499 := bstep (se 1 (by rfl) ⟨255374, by rfl⟩ : syracuseStep 340499 = 510749) B510749
theorem B373315 : Blo 219811 373315 := bstep (se 1 (by rfl) ⟨279986, by rfl⟩ : syracuseStep 373315 = 559973) B559973
theorem B635597 : Blo 219811 635597 := bstep (se 3 (by rfl) ⟨119174, by rfl⟩ : syracuseStep 635597 = 238349) B238349
theorem B373457 : Blo 219811 373457 := bstep (se 2 (by rfl) ⟨140046, by rfl⟩ : syracuseStep 373457 = 280093) B280093
theorem B373585 : Blo 219811 373585 := bstep (se 2 (by rfl) ⟨140094, by rfl⟩ : syracuseStep 373585 = 280189) B280189
theorem B373619 : Blo 219811 373619 := bstep (se 1 (by rfl) ⟨280214, by rfl⟩ : syracuseStep 373619 = 560429) B560429
theorem B635779 : Blo 219811 635779 := bstep (se 1 (by rfl) ⟨476834, by rfl⟩ : syracuseStep 635779 = 953669) B953669
theorem B635825 : Blo 219811 635825 := bstep (se 2 (by rfl) ⟨238434, by rfl⟩ : syracuseStep 635825 = 476869) B476869
theorem B373747 : Blo 219811 373747 := bstep (se 1 (by rfl) ⟨280310, by rfl⟩ : syracuseStep 373747 = 560621) B560621
theorem B406595 : Blo 219811 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B2012273 : Blo 219811 2012273 := bstep (se 2 (by rfl) ⟨754602, by rfl⟩ : syracuseStep 2012273 = 1509205) B1509205
theorem B373889 : Blo 219811 373889 := bstep (se 2 (by rfl) ⟨140208, by rfl⟩ : syracuseStep 373889 = 280417) B280417
theorem B374017 : Blo 219811 374017 := bstep (se 2 (by rfl) ⟨140256, by rfl⟩ : syracuseStep 374017 = 280513) B280513
theorem B374051 : Blo 219811 374051 := bstep (se 1 (by rfl) ⟨280538, by rfl⟩ : syracuseStep 374051 = 561077) B561077
theorem B570755 : Blo 219811 570755 := bstep (se 1 (by rfl) ⟨428066, by rfl⟩ : syracuseStep 570755 = 856133) B856133
theorem B374179 : Blo 219811 374179 := bstep (se 1 (by rfl) ⟨280634, by rfl⟩ : syracuseStep 374179 = 561269) B561269
theorem B1127843 : Blo 219811 1127843 := bstep (se 1 (by rfl) ⟨845882, by rfl⟩ : syracuseStep 1127843 = 1691765) B1691765
theorem B472529 : Blo 219811 472529 := bstep (se 2 (by rfl) ⟨177198, by rfl⟩ : syracuseStep 472529 = 354397) B354397
theorem B472547 : Blo 219811 472547 := bstep (se 1 (by rfl) ⟨354410, by rfl⟩ : syracuseStep 472547 = 708821) B708821
theorem B374321 : Blo 219811 374321 := bstep (se 2 (by rfl) ⟨140370, by rfl⟩ : syracuseStep 374321 = 280741) B280741
theorem B1422917 : Blo 219811 1422917 := bstep (se 4 (by rfl) ⟨133398, by rfl⟩ : syracuseStep 1422917 = 266797) B266797
theorem B374449 : Blo 219811 374449 := bstep (se 2 (by rfl) ⟨140418, by rfl⟩ : syracuseStep 374449 = 280837) B280837
theorem B374483 : Blo 219811 374483 := bstep (se 1 (by rfl) ⟨280862, by rfl⟩ : syracuseStep 374483 = 561725) B561725
theorem B669485 : Blo 219811 669485 := bstep (se 3 (by rfl) ⟨125528, by rfl⟩ : syracuseStep 669485 = 251057) B251057
theorem B3094325 : Blo 219811 3094325 := bstep (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) B290093
theorem B374611 : Blo 219811 374611 := bstep (se 1 (by rfl) ⟨280958, by rfl⟩ : syracuseStep 374611 = 561917) B561917
theorem B374753 : Blo 219811 374753 := bstep (se 2 (by rfl) ⟨140532, by rfl⟩ : syracuseStep 374753 = 281065) B281065
theorem B374881 : Blo 219811 374881 := bstep (se 2 (by rfl) ⟨140580, by rfl⟩ : syracuseStep 374881 = 281161) B281161
theorem B669809 : Blo 219811 669809 := bstep (se 2 (by rfl) ⟨251178, by rfl⟩ : syracuseStep 669809 = 502357) B502357
theorem B604273 : Blo 219811 604273 := bstep (se 2 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 604273 = 453205) B453205
theorem B374915 : Blo 219811 374915 := bstep (se 1 (by rfl) ⟨281186, by rfl⟩ : syracuseStep 374915 = 562373) B562373
theorem B1128653 : Blo 219811 1128653 := bstep (se 3 (by rfl) ⟨211622, by rfl⟩ : syracuseStep 1128653 = 423245) B423245
theorem B375043 : Blo 219811 375043 := bstep (se 1 (by rfl) ⟨281282, by rfl⟩ : syracuseStep 375043 = 562565) B562565
theorem B637283 : Blo 219811 637283 := bstep (se 1 (by rfl) ⟨477962, by rfl⟩ : syracuseStep 637283 = 955925) B955925
theorem B375185 : Blo 219811 375185 := bstep (se 2 (by rfl) ⟨140694, by rfl⟩ : syracuseStep 375185 = 281389) B281389
theorem B375313 : Blo 219811 375313 := bstep (se 2 (by rfl) ⟨140742, by rfl⟩ : syracuseStep 375313 = 281485) B281485
theorem B375347 : Blo 219811 375347 := bstep (se 1 (by rfl) ⟨281510, by rfl⟩ : syracuseStep 375347 = 563021) B563021
theorem B375475 : Blo 219811 375475 := bstep (se 1 (by rfl) ⟨281606, by rfl⟩ : syracuseStep 375475 = 563213) B563213
theorem B375617 : Blo 219811 375617 := bstep (se 2 (by rfl) ⟨140856, by rfl⟩ : syracuseStep 375617 = 281713) B281713
theorem B375745 : Blo 219811 375745 := bstep (se 2 (by rfl) ⟨140904, by rfl⟩ : syracuseStep 375745 = 281809) B281809
theorem B375779 : Blo 219811 375779 := bstep (se 1 (by rfl) ⟨281834, by rfl⟩ : syracuseStep 375779 = 563669) B563669
theorem B375907 : Blo 219811 375907 := bstep (se 1 (by rfl) ⟨281930, by rfl⟩ : syracuseStep 375907 = 563861) B563861
theorem B1883249 : Blo 219811 1883249 := bstep (se 2 (by rfl) ⟨706218, by rfl⟩ : syracuseStep 1883249 = 1412437) B1412437
theorem B376049 : Blo 219811 376049 := bstep (se 2 (by rfl) ⟨141018, by rfl⟩ : syracuseStep 376049 = 282037) B282037
theorem B1260805 : Blo 219811 1260805 := bstep (se 4 (by rfl) ⟨118200, by rfl⟩ : syracuseStep 1260805 = 236401) B236401
theorem B2014577 : Blo 219811 2014577 := bstep (se 2 (by rfl) ⟨755466, by rfl⟩ : syracuseStep 2014577 = 1510933) B1510933
theorem B376177 : Blo 219811 376177 := bstep (se 2 (by rfl) ⟨141066, by rfl⟩ : syracuseStep 376177 = 282133) B282133
theorem B376211 : Blo 219811 376211 := bstep (se 1 (by rfl) ⟨282158, by rfl⟩ : syracuseStep 376211 = 564317) B564317
theorem B474545 : Blo 219811 474545 := bstep (se 2 (by rfl) ⟨177954, by rfl⟩ : syracuseStep 474545 = 355909) B355909
theorem B1064461 : Blo 219811 1064461 := bstep (se 3 (by rfl) ⟨199586, by rfl⟩ : syracuseStep 1064461 = 399173) B399173
theorem B376339 : Blo 219811 376339 := bstep (se 1 (by rfl) ⟨282254, by rfl⟩ : syracuseStep 376339 = 564509) B564509
theorem B6372917 : Blo 219811 6372917 := bstep (se 5 (by rfl) ⟨298730, by rfl⟩ : syracuseStep 6372917 = 597461) B597461
theorem B638545 : Blo 219811 638545 := bstep (se 2 (by rfl) ⟨239454, by rfl⟩ : syracuseStep 638545 = 478909) B478909
theorem B343697 : Blo 219811 343697 := bstep (se 2 (by rfl) ⟨128886, by rfl⟩ : syracuseStep 343697 = 257773) B257773
theorem B376481 : Blo 219811 376481 := bstep (se 2 (by rfl) ⟨141180, by rfl⟩ : syracuseStep 376481 = 282361) B282361
theorem B540323 : Blo 219811 540323 := bstep (se 1 (by rfl) ⟨405242, by rfl⟩ : syracuseStep 540323 = 810485) B810485
theorem B376609 : Blo 219811 376609 := bstep (se 2 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 376609 = 282457) B282457
theorem B376643 : Blo 219811 376643 := bstep (se 1 (by rfl) ⟨282482, by rfl⟩ : syracuseStep 376643 = 564965) B564965
theorem B475075 : Blo 219811 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B376771 : Blo 219811 376771 := bstep (se 1 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 376771 = 565157) B565157
theorem B6799301 : Blo 219811 6799301 := bstep (se 4 (by rfl) ⟨637434, by rfl⟩ : syracuseStep 6799301 = 1274869) B1274869
theorem B835555 : Blo 219811 835555 := bstep (se 1 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 835555 = 1253333) B1253333
theorem B278579 : Blo 219811 278579 := bstep (se 1 (by rfl) ⟨208934, by rfl⟩ : syracuseStep 278579 = 417869) B417869
theorem B376913 : Blo 219811 376913 := bstep (se 2 (by rfl) ⟨141342, by rfl⟩ : syracuseStep 376913 = 282685) B282685
theorem B377041 : Blo 219811 377041 := bstep (se 2 (by rfl) ⟨141390, by rfl⟩ : syracuseStep 377041 = 282781) B282781
theorem B377075 : Blo 219811 377075 := bstep (se 1 (by rfl) ⟨282806, by rfl⟩ : syracuseStep 377075 = 565613) B565613
theorem B1687877 : Blo 219811 1687877 := bstep (se 4 (by rfl) ⟨158238, by rfl⟩ : syracuseStep 1687877 = 316477) B316477
theorem B377203 : Blo 219811 377203 := bstep (se 1 (by rfl) ⟨282902, by rfl⟩ : syracuseStep 377203 = 565805) B565805
theorem B377345 : Blo 219811 377345 := bstep (se 2 (by rfl) ⟨141504, by rfl⟩ : syracuseStep 377345 = 283009) B283009
theorem B377473 : Blo 219811 377473 := bstep (se 2 (by rfl) ⟨141552, by rfl⟩ : syracuseStep 377473 = 283105) B283105
theorem B377507 : Blo 219811 377507 := bstep (se 1 (by rfl) ⟨283130, by rfl⟩ : syracuseStep 377507 = 566261) B566261
theorem B279283 : Blo 219811 279283 := bstep (se 1 (by rfl) ⟨209462, by rfl⟩ : syracuseStep 279283 = 418925) B418925
theorem B377635 : Blo 219811 377635 := bstep (se 1 (by rfl) ⟨283226, by rfl⟩ : syracuseStep 377635 = 566453) B566453
theorem B279379 : Blo 219811 279379 := bstep (se 1 (by rfl) ⟨209534, by rfl⟩ : syracuseStep 279379 = 419069) B419069
theorem B508835 : Blo 219811 508835 := bstep (se 1 (by rfl) ⟨381626, by rfl⟩ : syracuseStep 508835 = 763253) B763253
theorem B1426403 : Blo 219811 1426403 := bstep (se 1 (by rfl) ⟨1069802, by rfl⟩ : syracuseStep 1426403 = 2139605) B2139605
theorem B1131569 : Blo 219811 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B705667 : Blo 219811 705667 := bstep (se 1 (by rfl) ⟨529250, by rfl⟩ : syracuseStep 705667 = 1058501) B1058501
theorem B1262789 : Blo 219811 1262789 := bstep (se 4 (by rfl) ⟨118386, by rfl⟩ : syracuseStep 1262789 = 236773) B236773
theorem B1524977 : Blo 219811 1524977 := bstep (se 2 (by rfl) ⟨571866, by rfl⟩ : syracuseStep 1524977 = 1143733) B1143733
theorem B705809 : Blo 219811 705809 := bstep (se 2 (by rfl) ⟨264678, by rfl⟩ : syracuseStep 705809 = 529357) B529357
theorem B279875 : Blo 219811 279875 := bstep (se 1 (by rfl) ⟨209906, by rfl⟩ : syracuseStep 279875 = 419813) B419813
theorem B705923 : Blo 219811 705923 := bstep (se 1 (by rfl) ⟨529442, by rfl⟩ : syracuseStep 705923 = 1058885) B1058885
theorem B476561 : Blo 219811 476561 := bstep (se 2 (by rfl) ⟨178710, by rfl⟩ : syracuseStep 476561 = 357421) B357421
theorem B476579 : Blo 219811 476579 := bstep (se 1 (by rfl) ⟨357434, by rfl⟩ : syracuseStep 476579 = 714869) B714869
theorem B247315 : Blo 219811 247315 := bstep (se 1 (by rfl) ⟨185486, by rfl⟩ : syracuseStep 247315 = 370973) B370973
theorem B247459 : Blo 219811 247459 := bstep (se 1 (by rfl) ⟨185594, by rfl⟩ : syracuseStep 247459 = 371189) B371189
theorem B968483 : Blo 219811 968483 := bstep (se 1 (by rfl) ⟨726362, by rfl⟩ : syracuseStep 968483 = 1452725) B1452725
theorem B247603 : Blo 219811 247603 := bstep (se 1 (by rfl) ⟨185702, by rfl⟩ : syracuseStep 247603 = 371405) B371405
theorem B313265 : Blo 219811 313265 := bstep (se 2 (by rfl) ⟨117474, by rfl⟩ : syracuseStep 313265 = 234949) B234949
theorem B247747 : Blo 219811 247747 := bstep (se 1 (by rfl) ⟨185810, by rfl⟩ : syracuseStep 247747 = 371621) B371621
theorem B313345 : Blo 219811 313345 := bstep (se 2 (by rfl) ⟨117504, by rfl⟩ : syracuseStep 313345 = 235009) B235009
theorem B280579 : Blo 219811 280579 := bstep (se 1 (by rfl) ⟨210434, by rfl⟩ : syracuseStep 280579 = 420869) B420869
theorem B247891 : Blo 219811 247891 := bstep (se 1 (by rfl) ⟨185918, by rfl⟩ : syracuseStep 247891 = 371837) B371837
theorem B280675 : Blo 219811 280675 := bstep (se 1 (by rfl) ⟨210506, by rfl⟩ : syracuseStep 280675 = 421013) B421013
theorem B837773 : Blo 219811 837773 := bstep (se 3 (by rfl) ⟨157082, by rfl⟩ : syracuseStep 837773 = 314165) B314165
theorem B1427633 : Blo 219811 1427633 := bstep (se 2 (by rfl) ⟨535362, by rfl⟩ : syracuseStep 1427633 = 1070725) B1070725
theorem B248035 : Blo 219811 248035 := bstep (se 1 (by rfl) ⟨186026, by rfl⟩ : syracuseStep 248035 = 372053) B372053
theorem B2377997 : Blo 219811 2377997 := bstep (se 3 (by rfl) ⟨445874, by rfl⟩ : syracuseStep 2377997 = 891749) B891749
theorem B1198385 : Blo 219811 1198385 := bstep (se 2 (by rfl) ⟨449394, by rfl⟩ : syracuseStep 1198385 = 898789) B898789
theorem B706897 : Blo 219811 706897 := bstep (se 2 (by rfl) ⟨265086, by rfl⟩ : syracuseStep 706897 = 530173) B530173
theorem B248179 : Blo 219811 248179 := bstep (se 1 (by rfl) ⟨186134, by rfl⟩ : syracuseStep 248179 = 372269) B372269
theorem B1133027 : Blo 219811 1133027 := bstep (se 1 (by rfl) ⟨849770, by rfl⟩ : syracuseStep 1133027 = 1699541) B1699541
theorem B248323 : Blo 219811 248323 := bstep (se 1 (by rfl) ⟨186242, by rfl⟩ : syracuseStep 248323 = 372485) B372485
theorem B477731 : Blo 219811 477731 := bstep (se 1 (by rfl) ⟨358298, by rfl⟩ : syracuseStep 477731 = 716597) B716597
theorem B281171 : Blo 219811 281171 := bstep (se 1 (by rfl) ⟨210878, by rfl⟩ : syracuseStep 281171 = 421757) B421757
theorem B477809 : Blo 219811 477809 := bstep (se 2 (by rfl) ⟨179178, by rfl⟩ : syracuseStep 477809 = 358357) B358357
theorem B1428101 : Blo 219811 1428101 := bstep (se 4 (by rfl) ⟨133884, by rfl⟩ : syracuseStep 1428101 = 267769) B267769
theorem B248467 : Blo 219811 248467 := bstep (se 1 (by rfl) ⟨186350, by rfl⟩ : syracuseStep 248467 = 372701) B372701
theorem B314131 : Blo 219811 314131 := bstep (se 1 (by rfl) ⟨235598, by rfl⟩ : syracuseStep 314131 = 471197) B471197
theorem B248611 : Blo 219811 248611 := bstep (se 1 (by rfl) ⟨186458, by rfl⟩ : syracuseStep 248611 = 372917) B372917
theorem B871309 : Blo 219811 871309 := bstep (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) B326741
theorem B248755 : Blo 219811 248755 := bstep (se 1 (by rfl) ⟨186566, by rfl⟩ : syracuseStep 248755 = 373133) B373133
theorem B2837429 : Blo 219811 2837429 := bstep (se 5 (by rfl) ⟨133004, by rfl⟩ : syracuseStep 2837429 = 266009) B266009
theorem B1887245 : Blo 219811 1887245 := bstep (se 3 (by rfl) ⟨353858, by rfl⟩ : syracuseStep 1887245 = 707717) B707717
theorem B248899 : Blo 219811 248899 := bstep (se 1 (by rfl) ⟨186674, by rfl⟩ : syracuseStep 248899 = 373349) B373349
theorem B674893 : Blo 219811 674893 := bstep (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) B253085
theorem B249043 : Blo 219811 249043 := bstep (se 1 (by rfl) ⟨186782, by rfl⟩ : syracuseStep 249043 = 373565) B373565
theorem B314609 : Blo 219811 314609 := bstep (se 2 (by rfl) ⟨117978, by rfl⟩ : syracuseStep 314609 = 235957) B235957
theorem B281875 : Blo 219811 281875 := bstep (se 1 (by rfl) ⟨211406, by rfl⟩ : syracuseStep 281875 = 422813) B422813
theorem B314723 : Blo 219811 314723 := bstep (se 1 (by rfl) ⟨236042, by rfl⟩ : syracuseStep 314723 = 472085) B472085
theorem B249187 : Blo 219811 249187 := bstep (se 1 (by rfl) ⟨186890, by rfl⟩ : syracuseStep 249187 = 373781) B373781
theorem B281971 : Blo 219811 281971 := bstep (se 1 (by rfl) ⟨211478, by rfl⟩ : syracuseStep 281971 = 422957) B422957
theorem B2280845 : Blo 219811 2280845 := bstep (se 3 (by rfl) ⟨427658, by rfl⟩ : syracuseStep 2280845 = 855317) B855317
theorem B314803 : Blo 219811 314803 := bstep (se 1 (by rfl) ⟨236102, by rfl⟩ : syracuseStep 314803 = 472205) B472205
theorem B249331 : Blo 219811 249331 := bstep (se 1 (by rfl) ⟨186998, by rfl⟩ : syracuseStep 249331 = 373997) B373997
theorem B4247153 : Blo 219811 4247153 := bstep (se 2 (by rfl) ⟨1592682, by rfl⟩ : syracuseStep 4247153 = 3185365) B3185365
theorem B249475 : Blo 219811 249475 := bstep (se 1 (by rfl) ⟨187106, by rfl⟩ : syracuseStep 249475 = 374213) B374213
theorem B380641 : Blo 219811 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B249619 : Blo 219811 249619 := bstep (se 1 (by rfl) ⟨187214, by rfl⟩ : syracuseStep 249619 = 374429) B374429
theorem B282467 : Blo 219811 282467 := bstep (se 1 (by rfl) ⟨211850, by rfl⟩ : syracuseStep 282467 = 423701) B423701
theorem B249763 : Blo 219811 249763 := bstep (se 1 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 249763 = 374645) B374645
theorem B315361 : Blo 219811 315361 := bstep (se 2 (by rfl) ⟨118260, by rfl⟩ : syracuseStep 315361 = 236521) B236521
theorem B249907 : Blo 219811 249907 := bstep (se 1 (by rfl) ⟨187430, by rfl⟩ : syracuseStep 249907 = 374861) B374861
theorem B250051 : Blo 219811 250051 := bstep (se 1 (by rfl) ⟨187538, by rfl⟩ : syracuseStep 250051 = 375077) B375077
theorem B250195 : Blo 219811 250195 := bstep (se 1 (by rfl) ⟨187646, by rfl⟩ : syracuseStep 250195 = 375293) B375293
theorem B250339 : Blo 219811 250339 := bstep (se 1 (by rfl) ⟨187754, by rfl⟩ : syracuseStep 250339 = 375509) B375509
theorem B741905 : Blo 219811 741905 := bstep (se 2 (by rfl) ⟨278214, by rfl⟩ : syracuseStep 741905 = 556429) B556429
theorem B283171 : Blo 219811 283171 := bstep (se 1 (by rfl) ⟨212378, by rfl⟩ : syracuseStep 283171 = 424757) B424757
theorem B250483 : Blo 219811 250483 := bstep (se 1 (by rfl) ⟨187862, by rfl⟩ : syracuseStep 250483 = 375725) B375725
theorem B316067 : Blo 219811 316067 := bstep (se 1 (by rfl) ⟨237050, by rfl⟩ : syracuseStep 316067 = 474101) B474101
theorem B250627 : Blo 219811 250627 := bstep (se 1 (by rfl) ⟨187970, by rfl⟩ : syracuseStep 250627 = 375941) B375941
theorem B250771 : Blo 219811 250771 := bstep (se 1 (by rfl) ⟨188078, by rfl⟩ : syracuseStep 250771 = 376157) B376157
theorem B1266637 : Blo 219811 1266637 := bstep (se 3 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 1266637 = 474989) B474989
theorem B840689 : Blo 219811 840689 := bstep (se 2 (by rfl) ⟨315258, by rfl⟩ : syracuseStep 840689 = 630517) B630517
theorem B939043 : Blo 219811 939043 := bstep (se 1 (by rfl) ⟨704282, by rfl⟩ : syracuseStep 939043 = 1408565) B1408565
theorem B250915 : Blo 219811 250915 := bstep (se 1 (by rfl) ⟨188186, by rfl⟩ : syracuseStep 250915 = 376373) B376373
theorem B742445 : Blo 219811 742445 := bstep (se 3 (by rfl) ⟨139208, by rfl⟩ : syracuseStep 742445 = 278417) B278417
theorem B742499 : Blo 219811 742499 := bstep (se 1 (by rfl) ⟨556874, by rfl⟩ : syracuseStep 742499 = 1113749) B1113749
theorem B251059 : Blo 219811 251059 := bstep (se 1 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 251059 = 376589) B376589
theorem B316705 : Blo 219811 316705 := bstep (se 2 (by rfl) ⟨118764, by rfl⟩ : syracuseStep 316705 = 237529) B237529
theorem B251203 : Blo 219811 251203 := bstep (se 1 (by rfl) ⟨188402, by rfl⟩ : syracuseStep 251203 = 376805) B376805
theorem B742769 : Blo 219811 742769 := bstep (se 2 (by rfl) ⟨278538, by rfl⟩ : syracuseStep 742769 = 557077) B557077
theorem B316819 : Blo 219811 316819 := bstep (se 1 (by rfl) ⟨237614, by rfl⟩ : syracuseStep 316819 = 475229) B475229
theorem B251347 : Blo 219811 251347 := bstep (se 1 (by rfl) ⟨188510, by rfl⟩ : syracuseStep 251347 = 377021) B377021
theorem B1136177 : Blo 219811 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B251491 : Blo 219811 251491 := bstep (se 1 (by rfl) ⟨188618, by rfl⟩ : syracuseStep 251491 = 377237) B377237
theorem B251635 : Blo 219811 251635 := bstep (se 1 (by rfl) ⟨188726, by rfl⟩ : syracuseStep 251635 = 377453) B377453
theorem B907057 : Blo 219811 907057 := bstep (se 2 (by rfl) ⟨340146, by rfl⟩ : syracuseStep 907057 = 680293) B680293
theorem B251779 : Blo 219811 251779 := bstep (se 1 (by rfl) ⟨188834, by rfl⟩ : syracuseStep 251779 = 377669) B377669
theorem B743309 : Blo 219811 743309 := bstep (se 3 (by rfl) ⟨139370, by rfl⟩ : syracuseStep 743309 = 278741) B278741
theorem B743363 : Blo 219811 743363 := bstep (se 1 (by rfl) ⟨557522, by rfl⟩ : syracuseStep 743363 = 1115045) B1115045
theorem B1693709 : Blo 219811 1693709 := bstep (se 3 (by rfl) ⟨317570, by rfl⟩ : syracuseStep 1693709 = 635141) B635141
theorem B3201221 : Blo 219811 3201221 := bstep (se 4 (by rfl) ⟨300114, by rfl⟩ : syracuseStep 3201221 = 600229) B600229
theorem B743633 : Blo 219811 743633 := bstep (se 2 (by rfl) ⟨278862, by rfl⟩ : syracuseStep 743633 = 557725) B557725
theorem B317747 : Blo 219811 317747 := bstep (se 1 (by rfl) ⟨238310, by rfl⟩ : syracuseStep 317747 = 476621) B476621
theorem B252227 : Blo 219811 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B383393 : Blo 219811 383393 := bstep (se 2 (by rfl) ⟨143772, by rfl⟩ : syracuseStep 383393 = 287545) B287545
theorem B842147 : Blo 219811 842147 := bstep (se 1 (by rfl) ⟨631610, by rfl⟩ : syracuseStep 842147 = 1263221) B1263221
theorem B711281 : Blo 219811 711281 := bstep (se 2 (by rfl) ⟨266730, by rfl⟩ : syracuseStep 711281 = 533461) B533461
theorem B219811 : Blo 219811 219811 := bstep (se 1 (by rfl) ⟨164858, by rfl⟩ : syracuseStep 219811 = 329717) B329717
theorem B219827 : Blo 219811 219827 := bstep (se 1 (by rfl) ⟨164870, by rfl⟩ : syracuseStep 219827 = 329741) B329741
theorem B219843 : Blo 219811 219843 := bstep (se 1 (by rfl) ⟨164882, by rfl⟩ : syracuseStep 219843 = 329765) B329765
theorem B219859 : Blo 219811 219859 := bstep (se 1 (by rfl) ⟨164894, by rfl⟩ : syracuseStep 219859 = 329789) B329789
theorem B318163 : Blo 219811 318163 := bstep (se 1 (by rfl) ⟨238622, by rfl⟩ : syracuseStep 318163 = 477245) B477245
theorem B219875 : Blo 219811 219875 := bstep (se 1 (by rfl) ⟨164906, by rfl⟩ : syracuseStep 219875 = 329813) B329813
theorem B744173 : Blo 219811 744173 := bstep (se 3 (by rfl) ⟨139532, by rfl⟩ : syracuseStep 744173 = 279065) B279065
theorem B1596145 : Blo 219811 1596145 := bstep (se 2 (by rfl) ⟨598554, by rfl⟩ : syracuseStep 1596145 = 1197109) B1197109
theorem B219891 : Blo 219811 219891 := bstep (se 1 (by rfl) ⟨164918, by rfl⟩ : syracuseStep 219891 = 329837) B329837
theorem B219907 : Blo 219811 219907 := bstep (se 1 (by rfl) ⟨164930, by rfl⟩ : syracuseStep 219907 = 329861) B329861
theorem B219923 : Blo 219811 219923 := bstep (se 1 (by rfl) ⟨164942, by rfl⟩ : syracuseStep 219923 = 329885) B329885
theorem B219939 : Blo 219811 219939 := bstep (se 1 (by rfl) ⟨164954, by rfl⟩ : syracuseStep 219939 = 329909) B329909
theorem B744227 : Blo 219811 744227 := bstep (se 1 (by rfl) ⟨558170, by rfl⟩ : syracuseStep 744227 = 1116341) B1116341
theorem B219955 : Blo 219811 219955 := bstep (se 1 (by rfl) ⟨164966, by rfl⟩ : syracuseStep 219955 = 329933) B329933
theorem B219971 : Blo 219811 219971 := bstep (se 1 (by rfl) ⟨164978, by rfl⟩ : syracuseStep 219971 = 329957) B329957
theorem B1694533 : Blo 219811 1694533 := bstep (se 4 (by rfl) ⟨158862, by rfl⟩ : syracuseStep 1694533 = 317725) B317725
theorem B219987 : Blo 219811 219987 := bstep (se 1 (by rfl) ⟨164990, by rfl⟩ : syracuseStep 219987 = 329981) B329981
theorem B220003 : Blo 219811 220003 := bstep (se 1 (by rfl) ⟨165002, by rfl⟩ : syracuseStep 220003 = 330005) B330005
theorem B220019 : Blo 219811 220019 := bstep (se 1 (by rfl) ⟨165014, by rfl⟩ : syracuseStep 220019 = 330029) B330029
theorem B220035 : Blo 219811 220035 := bstep (se 1 (by rfl) ⟨165026, by rfl⟩ : syracuseStep 220035 = 330053) B330053
theorem B1268621 : Blo 219811 1268621 := bstep (se 3 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 1268621 = 475733) B475733
theorem B220051 : Blo 219811 220051 := bstep (se 1 (by rfl) ⟨165038, by rfl⟩ : syracuseStep 220051 = 330077) B330077
theorem B220067 : Blo 219811 220067 := bstep (se 1 (by rfl) ⟨165050, by rfl⟩ : syracuseStep 220067 = 330101) B330101
theorem B220083 : Blo 219811 220083 := bstep (se 1 (by rfl) ⟨165062, by rfl⟩ : syracuseStep 220083 = 330125) B330125
theorem B220099 : Blo 219811 220099 := bstep (se 1 (by rfl) ⟨165074, by rfl⟩ : syracuseStep 220099 = 330149) B330149
theorem B220115 : Blo 219811 220115 := bstep (se 1 (by rfl) ⟨165086, by rfl⟩ : syracuseStep 220115 = 330173) B330173
theorem B220131 : Blo 219811 220131 := bstep (se 1 (by rfl) ⟨165098, by rfl⟩ : syracuseStep 220131 = 330197) B330197
theorem B1137649 : Blo 219811 1137649 := bstep (se 2 (by rfl) ⟨426618, by rfl⟩ : syracuseStep 1137649 = 853237) B853237
theorem B220147 : Blo 219811 220147 := bstep (se 1 (by rfl) ⟨165110, by rfl⟩ : syracuseStep 220147 = 330221) B330221
theorem B220163 : Blo 219811 220163 := bstep (se 1 (by rfl) ⟨165122, by rfl⟩ : syracuseStep 220163 = 330245) B330245
theorem B220179 : Blo 219811 220179 := bstep (se 1 (by rfl) ⟨165134, by rfl⟩ : syracuseStep 220179 = 330269) B330269
theorem B220195 : Blo 219811 220195 := bstep (se 1 (by rfl) ⟨165146, by rfl⟩ : syracuseStep 220195 = 330293) B330293
theorem B744497 : Blo 219811 744497 := bstep (se 2 (by rfl) ⟨279186, by rfl⟩ : syracuseStep 744497 = 558373) B558373
theorem B220211 : Blo 219811 220211 := bstep (se 1 (by rfl) ⟨165158, by rfl⟩ : syracuseStep 220211 = 330317) B330317
theorem B220227 : Blo 219811 220227 := bstep (se 1 (by rfl) ⟨165170, by rfl⟩ : syracuseStep 220227 = 330341) B330341
theorem B220243 : Blo 219811 220243 := bstep (se 1 (by rfl) ⟨165182, by rfl⟩ : syracuseStep 220243 = 330365) B330365
theorem B220259 : Blo 219811 220259 := bstep (se 1 (by rfl) ⟨165194, by rfl⟩ : syracuseStep 220259 = 330389) B330389
theorem B220275 : Blo 219811 220275 := bstep (se 1 (by rfl) ⟨165206, by rfl⟩ : syracuseStep 220275 = 330413) B330413
theorem B220291 : Blo 219811 220291 := bstep (se 1 (by rfl) ⟨165218, by rfl⟩ : syracuseStep 220291 = 330437) B330437
theorem B220307 : Blo 219811 220307 := bstep (se 1 (by rfl) ⟨165230, by rfl⟩ : syracuseStep 220307 = 330461) B330461
theorem B220323 : Blo 219811 220323 := bstep (se 1 (by rfl) ⟨165242, by rfl⟩ : syracuseStep 220323 = 330485) B330485
theorem B220339 : Blo 219811 220339 := bstep (se 1 (by rfl) ⟨165254, by rfl⟩ : syracuseStep 220339 = 330509) B330509
theorem B220355 : Blo 219811 220355 := bstep (se 1 (by rfl) ⟨165266, by rfl⟩ : syracuseStep 220355 = 330533) B330533
theorem B2579653 : Blo 219811 2579653 := bstep (se 4 (by rfl) ⟨241842, by rfl⟩ : syracuseStep 2579653 = 483685) B483685
theorem B220371 : Blo 219811 220371 := bstep (se 1 (by rfl) ⟨165278, by rfl⟩ : syracuseStep 220371 = 330557) B330557
theorem B220387 : Blo 219811 220387 := bstep (se 1 (by rfl) ⟨165290, by rfl⟩ : syracuseStep 220387 = 330581) B330581
theorem B220403 : Blo 219811 220403 := bstep (se 1 (by rfl) ⟨165302, by rfl⟩ : syracuseStep 220403 = 330605) B330605
theorem B220419 : Blo 219811 220419 := bstep (se 1 (by rfl) ⟨165314, by rfl⟩ : syracuseStep 220419 = 330629) B330629
theorem B810253 : Blo 219811 810253 := bstep (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) B303845
theorem B220435 : Blo 219811 220435 := bstep (se 1 (by rfl) ⟨165326, by rfl⟩ : syracuseStep 220435 = 330653) B330653
theorem B220451 : Blo 219811 220451 := bstep (se 1 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 220451 = 330677) B330677
theorem B220467 : Blo 219811 220467 := bstep (se 1 (by rfl) ⟨165350, by rfl⟩ : syracuseStep 220467 = 330701) B330701
theorem B220483 : Blo 219811 220483 := bstep (se 1 (by rfl) ⟨165362, by rfl⟩ : syracuseStep 220483 = 330725) B330725
theorem B220499 : Blo 219811 220499 := bstep (se 1 (by rfl) ⟨165374, by rfl⟩ : syracuseStep 220499 = 330749) B330749
theorem B220515 : Blo 219811 220515 := bstep (se 1 (by rfl) ⟨165386, by rfl⟩ : syracuseStep 220515 = 330773) B330773
theorem B220531 : Blo 219811 220531 := bstep (se 1 (by rfl) ⟨165398, by rfl⟩ : syracuseStep 220531 = 330797) B330797
theorem B220547 : Blo 219811 220547 := bstep (se 1 (by rfl) ⟨165410, by rfl⟩ : syracuseStep 220547 = 330821) B330821
theorem B843149 : Blo 219811 843149 := bstep (se 3 (by rfl) ⟨158090, by rfl⟩ : syracuseStep 843149 = 316181) B316181
theorem B220563 : Blo 219811 220563 := bstep (se 1 (by rfl) ⟨165422, by rfl⟩ : syracuseStep 220563 = 330845) B330845
theorem B220579 : Blo 219811 220579 := bstep (se 1 (by rfl) ⟨165434, by rfl⟩ : syracuseStep 220579 = 330869) B330869
theorem B941489 : Blo 219811 941489 := bstep (se 2 (by rfl) ⟨353058, by rfl⟩ : syracuseStep 941489 = 706117) B706117
theorem B220595 : Blo 219811 220595 := bstep (se 1 (by rfl) ⟨165446, by rfl⟩ : syracuseStep 220595 = 330893) B330893
theorem B2547125 : Blo 219811 2547125 := bstep (se 5 (by rfl) ⟨119396, by rfl⟩ : syracuseStep 2547125 = 238793) B238793
theorem B220611 : Blo 219811 220611 := bstep (se 1 (by rfl) ⟨165458, by rfl⟩ : syracuseStep 220611 = 330917) B330917
theorem B220627 : Blo 219811 220627 := bstep (se 1 (by rfl) ⟨165470, by rfl⟩ : syracuseStep 220627 = 330941) B330941
theorem B220643 : Blo 219811 220643 := bstep (se 1 (by rfl) ⟨165482, by rfl⟩ : syracuseStep 220643 = 330965) B330965
theorem B220659 : Blo 219811 220659 := bstep (se 1 (by rfl) ⟨165494, by rfl⟩ : syracuseStep 220659 = 330989) B330989
theorem B220675 : Blo 219811 220675 := bstep (se 1 (by rfl) ⟨165506, by rfl⟩ : syracuseStep 220675 = 331013) B331013
theorem B220691 : Blo 219811 220691 := bstep (se 1 (by rfl) ⟨165518, by rfl⟩ : syracuseStep 220691 = 331037) B331037
theorem B220707 : Blo 219811 220707 := bstep (se 1 (by rfl) ⟨165530, by rfl⟩ : syracuseStep 220707 = 331061) B331061
theorem B220723 : Blo 219811 220723 := bstep (se 1 (by rfl) ⟨165542, by rfl⟩ : syracuseStep 220723 = 331085) B331085
theorem B220739 : Blo 219811 220739 := bstep (se 1 (by rfl) ⟨165554, by rfl⟩ : syracuseStep 220739 = 331109) B331109
theorem B745037 : Blo 219811 745037 := bstep (se 3 (by rfl) ⟨139694, by rfl⟩ : syracuseStep 745037 = 279389) B279389
theorem B220755 : Blo 219811 220755 := bstep (se 1 (by rfl) ⟨165566, by rfl⟩ : syracuseStep 220755 = 331133) B331133
theorem B220771 : Blo 219811 220771 := bstep (se 1 (by rfl) ⟨165578, by rfl⟩ : syracuseStep 220771 = 331157) B331157
theorem B220787 : Blo 219811 220787 := bstep (se 1 (by rfl) ⟨165590, by rfl⟩ : syracuseStep 220787 = 331181) B331181
theorem B745091 : Blo 219811 745091 := bstep (se 1 (by rfl) ⟨558818, by rfl⟩ : syracuseStep 745091 = 1117637) B1117637
theorem B220803 : Blo 219811 220803 := bstep (se 1 (by rfl) ⟨165602, by rfl⟩ : syracuseStep 220803 = 331205) B331205
theorem B220819 : Blo 219811 220819 := bstep (se 1 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 220819 = 331229) B331229
theorem B220835 : Blo 219811 220835 := bstep (se 1 (by rfl) ⟨165626, by rfl⟩ : syracuseStep 220835 = 331253) B331253
theorem B220851 : Blo 219811 220851 := bstep (se 1 (by rfl) ⟨165638, by rfl⟩ : syracuseStep 220851 = 331277) B331277
theorem B220867 : Blo 219811 220867 := bstep (se 1 (by rfl) ⟨165650, by rfl⟩ : syracuseStep 220867 = 331301) B331301
theorem B220883 : Blo 219811 220883 := bstep (se 1 (by rfl) ⟨165662, by rfl⟩ : syracuseStep 220883 = 331325) B331325
theorem B220899 : Blo 219811 220899 := bstep (se 1 (by rfl) ⟨165674, by rfl⟩ : syracuseStep 220899 = 331349) B331349
theorem B220915 : Blo 219811 220915 := bstep (se 1 (by rfl) ⟨165686, by rfl⟩ : syracuseStep 220915 = 331373) B331373
theorem B220931 : Blo 219811 220931 := bstep (se 1 (by rfl) ⟨165698, by rfl⟩ : syracuseStep 220931 = 331397) B331397
theorem B220947 : Blo 219811 220947 := bstep (se 1 (by rfl) ⟨165710, by rfl⟩ : syracuseStep 220947 = 331421) B331421
theorem B220963 : Blo 219811 220963 := bstep (se 1 (by rfl) ⟨165722, by rfl⟩ : syracuseStep 220963 = 331445) B331445
theorem B1269553 : Blo 219811 1269553 := bstep (se 2 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 1269553 = 952165) B952165
theorem B220979 : Blo 219811 220979 := bstep (se 1 (by rfl) ⟨165734, by rfl⟩ : syracuseStep 220979 = 331469) B331469
theorem B319297 : Blo 219811 319297 := bstep (se 2 (by rfl) ⟨119736, by rfl⟩ : syracuseStep 319297 = 239473) B239473
theorem B220995 : Blo 219811 220995 := bstep (se 1 (by rfl) ⟨165746, by rfl⟩ : syracuseStep 220995 = 331493) B331493
theorem B221011 : Blo 219811 221011 := bstep (se 1 (by rfl) ⟨165758, by rfl⟩ : syracuseStep 221011 = 331517) B331517
theorem B221027 : Blo 219811 221027 := bstep (se 1 (by rfl) ⟨165770, by rfl⟩ : syracuseStep 221027 = 331541) B331541
theorem B417649 : Blo 219811 417649 := bstep (se 2 (by rfl) ⟨156618, by rfl⟩ : syracuseStep 417649 = 313237) B313237
theorem B221043 : Blo 219811 221043 := bstep (se 1 (by rfl) ⟨165782, by rfl⟩ : syracuseStep 221043 = 331565) B331565
theorem B221059 : Blo 219811 221059 := bstep (se 1 (by rfl) ⟨165794, by rfl⟩ : syracuseStep 221059 = 331589) B331589
theorem B1433477 : Blo 219811 1433477 := bstep (se 4 (by rfl) ⟨134388, by rfl⟩ : syracuseStep 1433477 = 268777) B268777
theorem B745361 : Blo 219811 745361 := bstep (se 2 (by rfl) ⟨279510, by rfl⟩ : syracuseStep 745361 = 559021) B559021
theorem B221075 : Blo 219811 221075 := bstep (se 1 (by rfl) ⟨165806, by rfl⟩ : syracuseStep 221075 = 331613) B331613
theorem B221091 : Blo 219811 221091 := bstep (se 1 (by rfl) ⟨165818, by rfl⟩ : syracuseStep 221091 = 331637) B331637
theorem B221107 : Blo 219811 221107 := bstep (se 1 (by rfl) ⟨165830, by rfl⟩ : syracuseStep 221107 = 331661) B331661
theorem B221123 : Blo 219811 221123 := bstep (se 1 (by rfl) ⟨165842, by rfl⟩ : syracuseStep 221123 = 331685) B331685
theorem B1138637 : Blo 219811 1138637 := bstep (se 3 (by rfl) ⟨213494, by rfl⟩ : syracuseStep 1138637 = 426989) B426989
theorem B221139 : Blo 219811 221139 := bstep (se 1 (by rfl) ⟨165854, by rfl⟩ : syracuseStep 221139 = 331709) B331709
theorem B221155 : Blo 219811 221155 := bstep (se 1 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 221155 = 331733) B331733
theorem B286691 : Blo 219811 286691 := bstep (se 1 (by rfl) ⟨215018, by rfl⟩ : syracuseStep 286691 = 430037) B430037
theorem B221171 : Blo 219811 221171 := bstep (se 1 (by rfl) ⟨165878, by rfl⟩ : syracuseStep 221171 = 331757) B331757
theorem B221187 : Blo 219811 221187 := bstep (se 1 (by rfl) ⟨165890, by rfl⟩ : syracuseStep 221187 = 331781) B331781
theorem B221203 : Blo 219811 221203 := bstep (se 1 (by rfl) ⟨165902, by rfl⟩ : syracuseStep 221203 = 331805) B331805
theorem B221219 : Blo 219811 221219 := bstep (se 1 (by rfl) ⟨165914, by rfl⟩ : syracuseStep 221219 = 331829) B331829
theorem B221235 : Blo 219811 221235 := bstep (se 1 (by rfl) ⟨165926, by rfl⟩ : syracuseStep 221235 = 331853) B331853
theorem B221251 : Blo 219811 221251 := bstep (se 1 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 221251 = 331877) B331877
theorem B221267 : Blo 219811 221267 := bstep (se 1 (by rfl) ⟨165950, by rfl⟩ : syracuseStep 221267 = 331901) B331901
theorem B221283 : Blo 219811 221283 := bstep (se 1 (by rfl) ⟨165962, by rfl⟩ : syracuseStep 221283 = 331925) B331925
theorem B909425 : Blo 219811 909425 := bstep (se 2 (by rfl) ⟨341034, by rfl⟩ : syracuseStep 909425 = 682069) B682069
theorem B1597553 : Blo 219811 1597553 := bstep (se 2 (by rfl) ⟨599082, by rfl⟩ : syracuseStep 1597553 = 1198165) B1198165
theorem B221299 : Blo 219811 221299 := bstep (se 1 (by rfl) ⟨165974, by rfl⟩ : syracuseStep 221299 = 331949) B331949
theorem B221315 : Blo 219811 221315 := bstep (se 1 (by rfl) ⟨165986, by rfl⟩ : syracuseStep 221315 = 331973) B331973
theorem B221331 : Blo 219811 221331 := bstep (se 1 (by rfl) ⟨165998, by rfl⟩ : syracuseStep 221331 = 331997) B331997
theorem B221347 : Blo 219811 221347 := bstep (se 1 (by rfl) ⟨166010, by rfl⟩ : syracuseStep 221347 = 332021) B332021
theorem B221363 : Blo 219811 221363 := bstep (se 1 (by rfl) ⟨166022, by rfl⟩ : syracuseStep 221363 = 332045) B332045
theorem B221379 : Blo 219811 221379 := bstep (se 1 (by rfl) ⟨166034, by rfl⟩ : syracuseStep 221379 = 332069) B332069
theorem B221395 : Blo 219811 221395 := bstep (se 1 (by rfl) ⟨166046, by rfl⟩ : syracuseStep 221395 = 332093) B332093
theorem B221411 : Blo 219811 221411 := bstep (se 1 (by rfl) ⟨166058, by rfl⟩ : syracuseStep 221411 = 332117) B332117
theorem B221427 : Blo 219811 221427 := bstep (se 1 (by rfl) ⟨166070, by rfl⟩ : syracuseStep 221427 = 332141) B332141
theorem B418051 : Blo 219811 418051 := bstep (se 1 (by rfl) ⟨313538, by rfl⟩ : syracuseStep 418051 = 627077) B627077
theorem B221443 : Blo 219811 221443 := bstep (se 1 (by rfl) ⟨166082, by rfl⟩ : syracuseStep 221443 = 332165) B332165
theorem B221459 : Blo 219811 221459 := bstep (se 1 (by rfl) ⟨166094, by rfl⟩ : syracuseStep 221459 = 332189) B332189
theorem B221475 : Blo 219811 221475 := bstep (se 1 (by rfl) ⟨166106, by rfl⟩ : syracuseStep 221475 = 332213) B332213
theorem B418097 : Blo 219811 418097 := bstep (se 2 (by rfl) ⟨156786, by rfl⟩ : syracuseStep 418097 = 313573) B313573
theorem B221491 : Blo 219811 221491 := bstep (se 1 (by rfl) ⟨166118, by rfl⟩ : syracuseStep 221491 = 332237) B332237
theorem B221507 : Blo 219811 221507 := bstep (se 1 (by rfl) ⟨166130, by rfl⟩ : syracuseStep 221507 = 332261) B332261
theorem B221523 : Blo 219811 221523 := bstep (se 1 (by rfl) ⟨166142, by rfl⟩ : syracuseStep 221523 = 332285) B332285
theorem B221539 : Blo 219811 221539 := bstep (se 1 (by rfl) ⟨166154, by rfl⟩ : syracuseStep 221539 = 332309) B332309
theorem B221555 : Blo 219811 221555 := bstep (se 1 (by rfl) ⟨166166, by rfl⟩ : syracuseStep 221555 = 332333) B332333
theorem B221571 : Blo 219811 221571 := bstep (se 1 (by rfl) ⟨166178, by rfl⟩ : syracuseStep 221571 = 332357) B332357
theorem B221587 : Blo 219811 221587 := bstep (se 1 (by rfl) ⟨166190, by rfl⟩ : syracuseStep 221587 = 332381) B332381
theorem B221603 : Blo 219811 221603 := bstep (se 1 (by rfl) ⟨166202, by rfl⟩ : syracuseStep 221603 = 332405) B332405
theorem B745901 : Blo 219811 745901 := bstep (se 3 (by rfl) ⟨139856, by rfl⟩ : syracuseStep 745901 = 279713) B279713
theorem B221619 : Blo 219811 221619 := bstep (se 1 (by rfl) ⟨166214, by rfl⟩ : syracuseStep 221619 = 332429) B332429
theorem B2384309 : Blo 219811 2384309 := bstep (se 5 (by rfl) ⟨111764, by rfl⟩ : syracuseStep 2384309 = 223529) B223529
theorem B221635 : Blo 219811 221635 := bstep (se 1 (by rfl) ⟨166226, by rfl⟩ : syracuseStep 221635 = 332453) B332453
theorem B221651 : Blo 219811 221651 := bstep (se 1 (by rfl) ⟨166238, by rfl⟩ : syracuseStep 221651 = 332477) B332477
theorem B745955 : Blo 219811 745955 := bstep (se 1 (by rfl) ⟨559466, by rfl⟩ : syracuseStep 745955 = 1118933) B1118933
theorem B221667 : Blo 219811 221667 := bstep (se 1 (by rfl) ⟨166250, by rfl⟩ : syracuseStep 221667 = 332501) B332501
theorem B221683 : Blo 219811 221683 := bstep (se 1 (by rfl) ⟨166262, by rfl⟩ : syracuseStep 221683 = 332525) B332525
theorem B221699 : Blo 219811 221699 := bstep (se 1 (by rfl) ⟨166274, by rfl⟩ : syracuseStep 221699 = 332549) B332549
theorem B221715 : Blo 219811 221715 := bstep (se 1 (by rfl) ⟨166286, by rfl⟩ : syracuseStep 221715 = 332573) B332573
theorem B221731 : Blo 219811 221731 := bstep (se 1 (by rfl) ⟨166298, by rfl⟩ : syracuseStep 221731 = 332597) B332597
theorem B221747 : Blo 219811 221747 := bstep (se 1 (by rfl) ⟨166310, by rfl⟩ : syracuseStep 221747 = 332621) B332621
theorem B221763 : Blo 219811 221763 := bstep (se 1 (by rfl) ⟨166322, by rfl⟩ : syracuseStep 221763 = 332645) B332645
theorem B418385 : Blo 219811 418385 := bstep (se 2 (by rfl) ⟨156894, by rfl⟩ : syracuseStep 418385 = 313789) B313789
theorem B221779 : Blo 219811 221779 := bstep (se 1 (by rfl) ⟨166334, by rfl⟩ : syracuseStep 221779 = 332669) B332669
theorem B221795 : Blo 219811 221795 := bstep (se 1 (by rfl) ⟨166346, by rfl⟩ : syracuseStep 221795 = 332693) B332693
theorem B221811 : Blo 219811 221811 := bstep (se 1 (by rfl) ⟨166358, by rfl⟩ : syracuseStep 221811 = 332717) B332717
theorem B221827 : Blo 219811 221827 := bstep (se 1 (by rfl) ⟨166370, by rfl⟩ : syracuseStep 221827 = 332741) B332741
theorem B713357 : Blo 219811 713357 := bstep (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) B267509
theorem B221843 : Blo 219811 221843 := bstep (se 1 (by rfl) ⟨166382, by rfl⟩ : syracuseStep 221843 = 332765) B332765
theorem B221859 : Blo 219811 221859 := bstep (se 1 (by rfl) ⟨166394, by rfl⟩ : syracuseStep 221859 = 332789) B332789
theorem B221875 : Blo 219811 221875 := bstep (se 1 (by rfl) ⟨166406, by rfl⟩ : syracuseStep 221875 = 332813) B332813
theorem B221891 : Blo 219811 221891 := bstep (se 1 (by rfl) ⟨166418, by rfl⟩ : syracuseStep 221891 = 332837) B332837
theorem B221907 : Blo 219811 221907 := bstep (se 1 (by rfl) ⟨166430, by rfl⟩ : syracuseStep 221907 = 332861) B332861
theorem B221923 : Blo 219811 221923 := bstep (se 1 (by rfl) ⟨166442, by rfl⟩ : syracuseStep 221923 = 332885) B332885
theorem B746225 : Blo 219811 746225 := bstep (se 2 (by rfl) ⟨279834, by rfl⟩ : syracuseStep 746225 = 559669) B559669
theorem B221939 : Blo 219811 221939 := bstep (se 1 (by rfl) ⟨166454, by rfl⟩ : syracuseStep 221939 = 332909) B332909
theorem B221955 : Blo 219811 221955 := bstep (se 1 (by rfl) ⟨166466, by rfl⟩ : syracuseStep 221955 = 332933) B332933
theorem B221971 : Blo 219811 221971 := bstep (se 1 (by rfl) ⟨166478, by rfl⟩ : syracuseStep 221971 = 332957) B332957
theorem B221987 : Blo 219811 221987 := bstep (se 1 (by rfl) ⟨166490, by rfl⟩ : syracuseStep 221987 = 332981) B332981
theorem B254755 : Blo 219811 254755 := bstep (se 1 (by rfl) ⟨191066, by rfl⟩ : syracuseStep 254755 = 382133) B382133
theorem B222003 : Blo 219811 222003 := bstep (se 1 (by rfl) ⟨166502, by rfl⟩ : syracuseStep 222003 = 333005) B333005
theorem B222019 : Blo 219811 222019 := bstep (se 1 (by rfl) ⟨166514, by rfl⟩ : syracuseStep 222019 = 333029) B333029
theorem B222035 : Blo 219811 222035 := bstep (se 1 (by rfl) ⟨166526, by rfl⟩ : syracuseStep 222035 = 333053) B333053
theorem B222051 : Blo 219811 222051 := bstep (se 1 (by rfl) ⟨166538, by rfl⟩ : syracuseStep 222051 = 333077) B333077
theorem B1696625 : Blo 219811 1696625 := bstep (se 2 (by rfl) ⟨636234, by rfl⟩ : syracuseStep 1696625 = 1272469) B1272469
theorem B222067 : Blo 219811 222067 := bstep (se 1 (by rfl) ⟨166550, by rfl⟩ : syracuseStep 222067 = 333101) B333101
theorem B222083 : Blo 219811 222083 := bstep (se 1 (by rfl) ⟨166562, by rfl⟩ : syracuseStep 222083 = 333125) B333125
theorem B680849 : Blo 219811 680849 := bstep (se 2 (by rfl) ⟨255318, by rfl⟩ : syracuseStep 680849 = 510637) B510637
theorem B222099 : Blo 219811 222099 := bstep (se 1 (by rfl) ⟨166574, by rfl⟩ : syracuseStep 222099 = 333149) B333149
theorem B222115 : Blo 219811 222115 := bstep (se 1 (by rfl) ⟨166586, by rfl⟩ : syracuseStep 222115 = 333173) B333173
theorem B222131 : Blo 219811 222131 := bstep (se 1 (by rfl) ⟨166598, by rfl⟩ : syracuseStep 222131 = 333197) B333197
theorem B222147 : Blo 219811 222147 := bstep (se 1 (by rfl) ⟨166610, by rfl⟩ : syracuseStep 222147 = 333221) B333221
theorem B222163 : Blo 219811 222163 := bstep (se 1 (by rfl) ⟨166622, by rfl⟩ : syracuseStep 222163 = 333245) B333245
theorem B222179 : Blo 219811 222179 := bstep (se 1 (by rfl) ⟨166634, by rfl⟩ : syracuseStep 222179 = 333269) B333269
theorem B222195 : Blo 219811 222195 := bstep (se 1 (by rfl) ⟨166646, by rfl⟩ : syracuseStep 222195 = 333293) B333293
theorem B222211 : Blo 219811 222211 := bstep (se 1 (by rfl) ⟨166658, by rfl⟩ : syracuseStep 222211 = 333317) B333317
theorem B222227 : Blo 219811 222227 := bstep (se 1 (by rfl) ⟨166670, by rfl⟩ : syracuseStep 222227 = 333341) B333341
theorem B353315 : Blo 219811 353315 := bstep (se 1 (by rfl) ⟨264986, by rfl⟩ : syracuseStep 353315 = 529973) B529973
theorem B222243 : Blo 219811 222243 := bstep (se 1 (by rfl) ⟨166682, by rfl⟩ : syracuseStep 222243 = 333365) B333365
theorem B222259 : Blo 219811 222259 := bstep (se 1 (by rfl) ⟨166694, by rfl⟩ : syracuseStep 222259 = 333389) B333389
theorem B222275 : Blo 219811 222275 := bstep (se 1 (by rfl) ⟨166706, by rfl⟩ : syracuseStep 222275 = 333413) B333413
theorem B222291 : Blo 219811 222291 := bstep (se 1 (by rfl) ⟨166718, by rfl⟩ : syracuseStep 222291 = 333437) B333437
theorem B222307 : Blo 219811 222307 := bstep (se 1 (by rfl) ⟨166730, by rfl⟩ : syracuseStep 222307 = 333461) B333461
theorem B222323 : Blo 219811 222323 := bstep (se 1 (by rfl) ⟨166742, by rfl⟩ : syracuseStep 222323 = 333485) B333485
theorem B222339 : Blo 219811 222339 := bstep (se 1 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 222339 = 333509) B333509
theorem B222355 : Blo 219811 222355 := bstep (se 1 (by rfl) ⟨166766, by rfl⟩ : syracuseStep 222355 = 333533) B333533
theorem B222371 : Blo 219811 222371 := bstep (se 1 (by rfl) ⟨166778, by rfl⟩ : syracuseStep 222371 = 333557) B333557
theorem B222387 : Blo 219811 222387 := bstep (se 1 (by rfl) ⟨166790, by rfl⟩ : syracuseStep 222387 = 333581) B333581
theorem B222403 : Blo 219811 222403 := bstep (se 1 (by rfl) ⟨166802, by rfl⟩ : syracuseStep 222403 = 333605) B333605
theorem B222419 : Blo 219811 222419 := bstep (se 1 (by rfl) ⟨166814, by rfl⟩ : syracuseStep 222419 = 333629) B333629
theorem B222435 : Blo 219811 222435 := bstep (se 1 (by rfl) ⟨166826, by rfl⟩ : syracuseStep 222435 = 333653) B333653
theorem B1271011 : Blo 219811 1271011 := bstep (se 1 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 1271011 = 1906517) B1906517
theorem B222451 : Blo 219811 222451 := bstep (se 1 (by rfl) ⟨166838, by rfl⟩ : syracuseStep 222451 = 333677) B333677
theorem B222467 : Blo 219811 222467 := bstep (se 1 (by rfl) ⟨166850, by rfl⟩ : syracuseStep 222467 = 333701) B333701
theorem B746765 : Blo 219811 746765 := bstep (se 3 (by rfl) ⟨140018, by rfl⟩ : syracuseStep 746765 = 280037) B280037
theorem B222483 : Blo 219811 222483 := bstep (se 1 (by rfl) ⟨166862, by rfl⟩ : syracuseStep 222483 = 333725) B333725
theorem B419107 : Blo 219811 419107 := bstep (se 1 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 419107 = 628661) B628661
theorem B222499 : Blo 219811 222499 := bstep (se 1 (by rfl) ⟨166874, by rfl⟩ : syracuseStep 222499 = 333749) B333749
theorem B222515 : Blo 219811 222515 := bstep (se 1 (by rfl) ⟨166886, by rfl⟩ : syracuseStep 222515 = 333773) B333773
theorem B2876725 : Blo 219811 2876725 := bstep (se 5 (by rfl) ⟨134846, by rfl⟩ : syracuseStep 2876725 = 269693) B269693
theorem B746819 : Blo 219811 746819 := bstep (se 1 (by rfl) ⟨560114, by rfl⟩ : syracuseStep 746819 = 1120229) B1120229
theorem B222531 : Blo 219811 222531 := bstep (se 1 (by rfl) ⟨166898, by rfl⟩ : syracuseStep 222531 = 333797) B333797
theorem B222547 : Blo 219811 222547 := bstep (se 1 (by rfl) ⟨166910, by rfl⟩ : syracuseStep 222547 = 333821) B333821
theorem B222563 : Blo 219811 222563 := bstep (se 1 (by rfl) ⟨166922, by rfl⟩ : syracuseStep 222563 = 333845) B333845
theorem B222579 : Blo 219811 222579 := bstep (se 1 (by rfl) ⟨166934, by rfl⟩ : syracuseStep 222579 = 333869) B333869
theorem B222595 : Blo 219811 222595 := bstep (se 1 (by rfl) ⟨166946, by rfl⟩ : syracuseStep 222595 = 333893) B333893
theorem B222611 : Blo 219811 222611 := bstep (se 1 (by rfl) ⟨166958, by rfl⟩ : syracuseStep 222611 = 333917) B333917
theorem B222627 : Blo 219811 222627 := bstep (se 1 (by rfl) ⟨166970, by rfl⟩ : syracuseStep 222627 = 333941) B333941
theorem B222643 : Blo 219811 222643 := bstep (se 1 (by rfl) ⟨166982, by rfl⟩ : syracuseStep 222643 = 333965) B333965
theorem B222659 : Blo 219811 222659 := bstep (se 1 (by rfl) ⟨166994, by rfl⟩ : syracuseStep 222659 = 333989) B333989
theorem B845261 : Blo 219811 845261 := bstep (se 3 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 845261 = 316973) B316973
theorem B222675 : Blo 219811 222675 := bstep (se 1 (by rfl) ⟨167006, by rfl⟩ : syracuseStep 222675 = 334013) B334013
theorem B5694947 : Blo 219811 5694947 := bstep (se 1 (by rfl) ⟨4271210, by rfl⟩ : syracuseStep 5694947 = 8542421) B8542421
theorem B222691 : Blo 219811 222691 := bstep (se 1 (by rfl) ⟨167018, by rfl⟩ : syracuseStep 222691 = 334037) B334037
theorem B222707 : Blo 219811 222707 := bstep (se 1 (by rfl) ⟨167030, by rfl⟩ : syracuseStep 222707 = 334061) B334061
theorem B222723 : Blo 219811 222723 := bstep (se 1 (by rfl) ⟨167042, by rfl⟩ : syracuseStep 222723 = 334085) B334085
theorem B714253 : Blo 219811 714253 := bstep (se 3 (by rfl) ⟨133922, by rfl⟩ : syracuseStep 714253 = 267845) B267845
theorem B222739 : Blo 219811 222739 := bstep (se 1 (by rfl) ⟨167054, by rfl⟩ : syracuseStep 222739 = 334109) B334109
theorem B222755 : Blo 219811 222755 := bstep (se 1 (by rfl) ⟨167066, by rfl⟩ : syracuseStep 222755 = 334133) B334133
theorem B222771 : Blo 219811 222771 := bstep (se 1 (by rfl) ⟨167078, by rfl⟩ : syracuseStep 222771 = 334157) B334157
theorem B222787 : Blo 219811 222787 := bstep (se 1 (by rfl) ⟨167090, by rfl⟩ : syracuseStep 222787 = 334181) B334181
theorem B747089 : Blo 219811 747089 := bstep (se 2 (by rfl) ⟨280158, by rfl⟩ : syracuseStep 747089 = 560317) B560317
theorem B222803 : Blo 219811 222803 := bstep (se 1 (by rfl) ⟨167102, by rfl⟩ : syracuseStep 222803 = 334205) B334205
theorem B222819 : Blo 219811 222819 := bstep (se 1 (by rfl) ⟨167114, by rfl⟩ : syracuseStep 222819 = 334229) B334229
theorem B222835 : Blo 219811 222835 := bstep (se 1 (by rfl) ⟨167126, by rfl⟩ : syracuseStep 222835 = 334253) B334253
theorem B222851 : Blo 219811 222851 := bstep (se 1 (by rfl) ⟨167138, by rfl⟩ : syracuseStep 222851 = 334277) B334277
theorem B222867 : Blo 219811 222867 := bstep (se 1 (by rfl) ⟨167150, by rfl⟩ : syracuseStep 222867 = 334301) B334301
theorem B222883 : Blo 219811 222883 := bstep (se 1 (by rfl) ⟨167162, by rfl⟩ : syracuseStep 222883 = 334325) B334325
theorem B222899 : Blo 219811 222899 := bstep (se 1 (by rfl) ⟨167174, by rfl⟩ : syracuseStep 222899 = 334349) B334349
theorem B353987 : Blo 219811 353987 := bstep (se 1 (by rfl) ⟨265490, by rfl⟩ : syracuseStep 353987 = 530981) B530981
theorem B222915 : Blo 219811 222915 := bstep (se 1 (by rfl) ⟨167186, by rfl⟩ : syracuseStep 222915 = 334373) B334373
theorem B222931 : Blo 219811 222931 := bstep (se 1 (by rfl) ⟨167198, by rfl⟩ : syracuseStep 222931 = 334397) B334397
theorem B419555 : Blo 219811 419555 := bstep (se 1 (by rfl) ⟨314666, by rfl⟩ : syracuseStep 419555 = 629333) B629333
theorem B222947 : Blo 219811 222947 := bstep (se 1 (by rfl) ⟨167210, by rfl⟩ : syracuseStep 222947 = 334421) B334421
theorem B1271537 : Blo 219811 1271537 := bstep (se 2 (by rfl) ⟨476826, by rfl⟩ : syracuseStep 1271537 = 953653) B953653
theorem B222963 : Blo 219811 222963 := bstep (se 1 (by rfl) ⟨167222, by rfl⟩ : syracuseStep 222963 = 334445) B334445
theorem B222979 : Blo 219811 222979 := bstep (se 1 (by rfl) ⟨167234, by rfl⟩ : syracuseStep 222979 = 334469) B334469
theorem B222995 : Blo 219811 222995 := bstep (se 1 (by rfl) ⟨167246, by rfl⟩ : syracuseStep 222995 = 334493) B334493
theorem B223011 : Blo 219811 223011 := bstep (se 1 (by rfl) ⟨167258, by rfl⟩ : syracuseStep 223011 = 334517) B334517
theorem B223027 : Blo 219811 223027 := bstep (se 1 (by rfl) ⟨167270, by rfl⟩ : syracuseStep 223027 = 334541) B334541
theorem B223043 : Blo 219811 223043 := bstep (se 1 (by rfl) ⟨167282, by rfl⟩ : syracuseStep 223043 = 334565) B334565
theorem B223059 : Blo 219811 223059 := bstep (se 1 (by rfl) ⟨167294, by rfl⟩ : syracuseStep 223059 = 334589) B334589
theorem B223075 : Blo 219811 223075 := bstep (se 1 (by rfl) ⟨167306, by rfl⟩ : syracuseStep 223075 = 334613) B334613
theorem B223091 : Blo 219811 223091 := bstep (se 1 (by rfl) ⟨167318, by rfl⟩ : syracuseStep 223091 = 334637) B334637
theorem B223107 : Blo 219811 223107 := bstep (se 1 (by rfl) ⟨167330, by rfl⟩ : syracuseStep 223107 = 334661) B334661
theorem B2844557 : Blo 219811 2844557 := bstep (se 3 (by rfl) ⟨533354, by rfl⟩ : syracuseStep 2844557 = 1066709) B1066709
theorem B223123 : Blo 219811 223123 := bstep (se 1 (by rfl) ⟨167342, by rfl⟩ : syracuseStep 223123 = 334685) B334685
theorem B223139 : Blo 219811 223139 := bstep (se 1 (by rfl) ⟨167354, by rfl⟩ : syracuseStep 223139 = 334709) B334709
theorem B223155 : Blo 219811 223155 := bstep (se 1 (by rfl) ⟨167366, by rfl⟩ : syracuseStep 223155 = 334733) B334733
theorem B223171 : Blo 219811 223171 := bstep (se 1 (by rfl) ⟨167378, by rfl⟩ : syracuseStep 223171 = 334757) B334757
theorem B223187 : Blo 219811 223187 := bstep (se 1 (by rfl) ⟨167390, by rfl⟩ : syracuseStep 223187 = 334781) B334781
theorem B223203 : Blo 219811 223203 := bstep (se 1 (by rfl) ⟨167402, by rfl⟩ : syracuseStep 223203 = 334805) B334805
theorem B354289 : Blo 219811 354289 := bstep (se 2 (by rfl) ⟨132858, by rfl⟩ : syracuseStep 354289 = 265717) B265717
theorem B223219 : Blo 219811 223219 := bstep (se 1 (by rfl) ⟨167414, by rfl⟩ : syracuseStep 223219 = 334829) B334829
theorem B419843 : Blo 219811 419843 := bstep (se 1 (by rfl) ⟨314882, by rfl⟩ : syracuseStep 419843 = 629765) B629765
theorem B223235 : Blo 219811 223235 := bstep (se 1 (by rfl) ⟨167426, by rfl⟩ : syracuseStep 223235 = 334853) B334853
theorem B223251 : Blo 219811 223251 := bstep (se 1 (by rfl) ⟨167438, by rfl⟩ : syracuseStep 223251 = 334877) B334877
theorem B223267 : Blo 219811 223267 := bstep (se 1 (by rfl) ⟨167450, by rfl⟩ : syracuseStep 223267 = 334901) B334901
theorem B223283 : Blo 219811 223283 := bstep (se 1 (by rfl) ⟨167462, by rfl⟩ : syracuseStep 223283 = 334925) B334925
theorem B223299 : Blo 219811 223299 := bstep (se 1 (by rfl) ⟨167474, by rfl⟩ : syracuseStep 223299 = 334949) B334949
theorem B223315 : Blo 219811 223315 := bstep (se 1 (by rfl) ⟨167486, by rfl⟩ : syracuseStep 223315 = 334973) B334973
theorem B223331 : Blo 219811 223331 := bstep (se 1 (by rfl) ⟨167498, by rfl⟩ : syracuseStep 223331 = 334997) B334997
theorem B747629 : Blo 219811 747629 := bstep (se 3 (by rfl) ⟨140180, by rfl⟩ : syracuseStep 747629 = 280361) B280361
theorem B223347 : Blo 219811 223347 := bstep (se 1 (by rfl) ⟨167510, by rfl⟩ : syracuseStep 223347 = 335021) B335021
theorem B223363 : Blo 219811 223363 := bstep (se 1 (by rfl) ⟨167522, by rfl⟩ : syracuseStep 223363 = 335045) B335045
theorem B223379 : Blo 219811 223379 := bstep (se 1 (by rfl) ⟨167534, by rfl⟩ : syracuseStep 223379 = 335069) B335069
theorem B747683 : Blo 219811 747683 := bstep (se 1 (by rfl) ⟨560762, by rfl⟩ : syracuseStep 747683 = 1121525) B1121525
theorem B223395 : Blo 219811 223395 := bstep (se 1 (by rfl) ⟨167546, by rfl⟩ : syracuseStep 223395 = 335093) B335093
theorem B223411 : Blo 219811 223411 := bstep (se 1 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 223411 = 335117) B335117
theorem B354499 : Blo 219811 354499 := bstep (se 1 (by rfl) ⟨265874, by rfl⟩ : syracuseStep 354499 = 531749) B531749
theorem B223427 : Blo 219811 223427 := bstep (se 1 (by rfl) ⟨167570, by rfl⟩ : syracuseStep 223427 = 335141) B335141
theorem B223443 : Blo 219811 223443 := bstep (se 1 (by rfl) ⟨167582, by rfl⟩ : syracuseStep 223443 = 335165) B335165
theorem B223459 : Blo 219811 223459 := bstep (se 1 (by rfl) ⟨167594, by rfl⟩ : syracuseStep 223459 = 335189) B335189
theorem B354545 : Blo 219811 354545 := bstep (se 2 (by rfl) ⟨132954, by rfl⟩ : syracuseStep 354545 = 265909) B265909
theorem B846065 : Blo 219811 846065 := bstep (se 2 (by rfl) ⟨317274, by rfl⟩ : syracuseStep 846065 = 634549) B634549
theorem B223475 : Blo 219811 223475 := bstep (se 1 (by rfl) ⟨167606, by rfl⟩ : syracuseStep 223475 = 335213) B335213
theorem B223491 : Blo 219811 223491 := bstep (se 1 (by rfl) ⟨167618, by rfl⟩ : syracuseStep 223491 = 335237) B335237
theorem B223507 : Blo 219811 223507 := bstep (se 1 (by rfl) ⟨167630, by rfl⟩ : syracuseStep 223507 = 335261) B335261
theorem B223523 : Blo 219811 223523 := bstep (se 1 (by rfl) ⟨167642, by rfl⟩ : syracuseStep 223523 = 335285) B335285
theorem B223539 : Blo 219811 223539 := bstep (se 1 (by rfl) ⟨167654, by rfl⟩ : syracuseStep 223539 = 335309) B335309
theorem B223555 : Blo 219811 223555 := bstep (se 1 (by rfl) ⟨167666, by rfl⟩ : syracuseStep 223555 = 335333) B335333
theorem B223571 : Blo 219811 223571 := bstep (se 1 (by rfl) ⟨167678, by rfl⟩ : syracuseStep 223571 = 335357) B335357
theorem B223587 : Blo 219811 223587 := bstep (se 1 (by rfl) ⟨167690, by rfl⟩ : syracuseStep 223587 = 335381) B335381
theorem B223603 : Blo 219811 223603 := bstep (se 1 (by rfl) ⟨167702, by rfl⟩ : syracuseStep 223603 = 335405) B335405
theorem B715139 : Blo 219811 715139 := bstep (se 1 (by rfl) ⟨536354, by rfl⟩ : syracuseStep 715139 = 1072709) B1072709
theorem B223619 : Blo 219811 223619 := bstep (se 1 (by rfl) ⟨167714, by rfl⟩ : syracuseStep 223619 = 335429) B335429
theorem B223635 : Blo 219811 223635 := bstep (se 1 (by rfl) ⟨167726, by rfl⟩ : syracuseStep 223635 = 335453) B335453
theorem B223651 : Blo 219811 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B747953 : Blo 219811 747953 := bstep (se 2 (by rfl) ⟨280482, by rfl⟩ : syracuseStep 747953 = 560965) B560965
theorem B223667 : Blo 219811 223667 := bstep (se 1 (by rfl) ⟨167750, by rfl⟩ : syracuseStep 223667 = 335501) B335501
theorem B223683 : Blo 219811 223683 := bstep (se 1 (by rfl) ⟨167762, by rfl⟩ : syracuseStep 223683 = 335525) B335525
theorem B223699 : Blo 219811 223699 := bstep (se 1 (by rfl) ⟨167774, by rfl⟩ : syracuseStep 223699 = 335549) B335549
theorem B223715 : Blo 219811 223715 := bstep (se 1 (by rfl) ⟨167786, by rfl⟩ : syracuseStep 223715 = 335573) B335573
theorem B223731 : Blo 219811 223731 := bstep (se 1 (by rfl) ⟨167798, by rfl⟩ : syracuseStep 223731 = 335597) B335597
theorem B223747 : Blo 219811 223747 := bstep (se 1 (by rfl) ⟨167810, by rfl⟩ : syracuseStep 223747 = 335621) B335621
theorem B223763 : Blo 219811 223763 := bstep (se 1 (by rfl) ⟨167822, by rfl⟩ : syracuseStep 223763 = 335645) B335645
theorem B223779 : Blo 219811 223779 := bstep (se 1 (by rfl) ⟨167834, by rfl⟩ : syracuseStep 223779 = 335669) B335669
theorem B223795 : Blo 219811 223795 := bstep (se 1 (by rfl) ⟨167846, by rfl⟩ : syracuseStep 223795 = 335693) B335693
theorem B223811 : Blo 219811 223811 := bstep (se 1 (by rfl) ⟨167858, by rfl⟩ : syracuseStep 223811 = 335717) B335717
theorem B4254605 : Blo 219811 4254605 := bstep (se 3 (by rfl) ⟨797738, by rfl⟩ : syracuseStep 4254605 = 1595477) B1595477
theorem B1895309 : Blo 219811 1895309 := bstep (se 3 (by rfl) ⟨355370, by rfl⟩ : syracuseStep 1895309 = 710741) B710741
theorem B846733 : Blo 219811 846733 := bstep (se 3 (by rfl) ⟨158762, by rfl⟩ : syracuseStep 846733 = 317525) B317525
theorem B682897 : Blo 219811 682897 := bstep (se 2 (by rfl) ⟨256086, by rfl⟩ : syracuseStep 682897 = 512173) B512173
theorem B453539 : Blo 219811 453539 := bstep (se 1 (by rfl) ⟨340154, by rfl⟩ : syracuseStep 453539 = 680309) B680309
theorem B420785 : Blo 219811 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B322483 : Blo 219811 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B748493 : Blo 219811 748493 := bstep (se 3 (by rfl) ⟨140342, by rfl⟩ : syracuseStep 748493 = 280685) B280685
theorem B748547 : Blo 219811 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B945229 : Blo 219811 945229 := bstep (se 3 (by rfl) ⟨177230, by rfl⟩ : syracuseStep 945229 = 354461) B354461
theorem B1272995 : Blo 219811 1272995 := bstep (se 1 (by rfl) ⟨954746, by rfl⟩ : syracuseStep 1272995 = 1909493) B1909493
theorem B748817 : Blo 219811 748817 := bstep (se 2 (by rfl) ⟨280806, by rfl⟩ : syracuseStep 748817 = 561613) B561613
theorem B847523 : Blo 219811 847523 := bstep (se 1 (by rfl) ⟨635642, by rfl⟩ : syracuseStep 847523 = 1271285) B1271285
theorem B356051 : Blo 219811 356051 := bstep (se 1 (by rfl) ⟨267038, by rfl⟩ : syracuseStep 356051 = 534077) B534077
theorem B749357 : Blo 219811 749357 := bstep (se 3 (by rfl) ⟨140504, by rfl⟩ : syracuseStep 749357 = 281009) B281009
theorem B421681 : Blo 219811 421681 := bstep (se 2 (by rfl) ⟨158130, by rfl⟩ : syracuseStep 421681 = 316261) B316261
theorem B749411 : Blo 219811 749411 := bstep (se 1 (by rfl) ⟨562058, by rfl⟩ : syracuseStep 749411 = 1124117) B1124117
theorem B1601477 : Blo 219811 1601477 := bstep (se 4 (by rfl) ⟨150138, by rfl⟩ : syracuseStep 1601477 = 300277) B300277
theorem B421841 : Blo 219811 421841 := bstep (se 2 (by rfl) ⟨158190, by rfl⟩ : syracuseStep 421841 = 316381) B316381
theorem B356339 : Blo 219811 356339 := bstep (se 1 (by rfl) ⟨267254, by rfl⟩ : syracuseStep 356339 = 534509) B534509
theorem B749681 : Blo 219811 749681 := bstep (se 2 (by rfl) ⟨281130, by rfl⟩ : syracuseStep 749681 = 562261) B562261
theorem B848177 : Blo 219811 848177 := bstep (se 2 (by rfl) ⟨318066, by rfl⟩ : syracuseStep 848177 = 636133) B636133
theorem B422243 : Blo 219811 422243 := bstep (se 1 (by rfl) ⟨316682, by rfl⟩ : syracuseStep 422243 = 633365) B633365
theorem B750221 : Blo 219811 750221 := bstep (se 3 (by rfl) ⟨140666, by rfl⟩ : syracuseStep 750221 = 281333) B281333
theorem B750275 : Blo 219811 750275 := bstep (se 1 (by rfl) ⟨562706, by rfl⟩ : syracuseStep 750275 = 1125413) B1125413
theorem B357139 : Blo 219811 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B357281 : Blo 219811 357281 := bstep (se 2 (by rfl) ⟨133980, by rfl⟩ : syracuseStep 357281 = 267961) B267961
theorem B717731 : Blo 219811 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B357313 : Blo 219811 357313 := bstep (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) B267985
theorem B750545 : Blo 219811 750545 := bstep (se 2 (by rfl) ⟨281454, by rfl⟩ : syracuseStep 750545 = 562909) B562909
theorem B1209329 : Blo 219811 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B423139 : Blo 219811 423139 := bstep (se 1 (by rfl) ⟨317354, by rfl⟩ : syracuseStep 423139 = 634709) B634709
theorem B226643 : Blo 219811 226643 := bstep (se 1 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 226643 = 339965) B339965
theorem B423299 : Blo 219811 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B1799651 : Blo 219811 1799651 := bstep (se 1 (by rfl) ⟨1349738, by rfl⟩ : syracuseStep 1799651 = 2699477) B2699477
theorem B751085 : Blo 219811 751085 := bstep (se 3 (by rfl) ⟨140828, by rfl⟩ : syracuseStep 751085 = 281657) B281657
theorem B751139 : Blo 219811 751139 := bstep (se 1 (by rfl) ⟨563354, by rfl⟩ : syracuseStep 751139 = 1126709) B1126709
theorem B3405509 : Blo 219811 3405509 := bstep (se 4 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 3405509 = 638533) B638533
theorem B849635 : Blo 219811 849635 := bstep (se 1 (by rfl) ⟨637226, by rfl⟩ : syracuseStep 849635 = 1274453) B1274453
theorem B849649 : Blo 219811 849649 := bstep (se 2 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 849649 = 637237) B637237
theorem B751409 : Blo 219811 751409 := bstep (se 2 (by rfl) ⟨281778, by rfl⟩ : syracuseStep 751409 = 563557) B563557
theorem B358241 : Blo 219811 358241 := bstep (se 2 (by rfl) ⟨134340, by rfl⟩ : syracuseStep 358241 = 268681) B268681
theorem B915299 : Blo 219811 915299 := bstep (se 1 (by rfl) ⟨686474, by rfl⟩ : syracuseStep 915299 = 1372949) B1372949
theorem B686051 : Blo 219811 686051 := bstep (se 1 (by rfl) ⟨514538, by rfl⟩ : syracuseStep 686051 = 1029077) B1029077
theorem B751949 : Blo 219811 751949 := bstep (se 3 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 751949 = 281981) B281981
theorem B752003 : Blo 219811 752003 := bstep (se 1 (by rfl) ⟨564002, by rfl⟩ : syracuseStep 752003 = 1128005) B1128005
theorem B424369 : Blo 219811 424369 := bstep (se 2 (by rfl) ⟨159138, by rfl⟩ : syracuseStep 424369 = 318277) B318277
theorem B752141 : Blo 219811 752141 := bstep (se 3 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 752141 = 282053) B282053
theorem B752273 : Blo 219811 752273 := bstep (se 2 (by rfl) ⟨282102, by rfl⟩ : syracuseStep 752273 = 564205) B564205
theorem B1113101 : Blo 219811 1113101 := bstep (se 3 (by rfl) ⟨208706, by rfl⟩ : syracuseStep 1113101 = 417413) B417413
theorem B752813 : Blo 219811 752813 := bstep (se 3 (by rfl) ⟨141152, by rfl⟩ : syracuseStep 752813 = 282305) B282305
theorem B2522339 : Blo 219811 2522339 := bstep (se 1 (by rfl) ⟨1891754, by rfl⟩ : syracuseStep 2522339 = 3783509) B3783509
theorem B752867 : Blo 219811 752867 := bstep (se 1 (by rfl) ⟨564650, by rfl⟩ : syracuseStep 752867 = 1129301) B1129301
theorem B949553 : Blo 219811 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B949603 : Blo 219811 949603 := bstep (se 1 (by rfl) ⟨712202, by rfl⟩ : syracuseStep 949603 = 1424405) B1424405
theorem B753137 : Blo 219811 753137 := bstep (se 2 (by rfl) ⟨282426, by rfl⟩ : syracuseStep 753137 = 564853) B564853
theorem B2719331 : Blo 219811 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B2031245 : Blo 219811 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B556753 : Blo 219811 556753 := bstep (se 2 (by rfl) ⟨208782, by rfl⟩ : syracuseStep 556753 = 417565) B417565
theorem B1343267 : Blo 219811 1343267 := bstep (se 1 (by rfl) ⟨1007450, by rfl⟩ : syracuseStep 1343267 = 2014901) B2014901
theorem B851917 : Blo 219811 851917 := bstep (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) B319469
theorem B753617 : Blo 219811 753617 := bstep (se 2 (by rfl) ⟨282606, by rfl⟩ : syracuseStep 753617 = 565213) B565213
theorem B557027 : Blo 219811 557027 := bstep (se 1 (by rfl) ⟨417770, by rfl⟩ : syracuseStep 557027 = 835541) B835541
theorem B458995 : Blo 219811 458995 := bstep (se 1 (by rfl) ⟨344246, by rfl⟩ : syracuseStep 458995 = 688493) B688493
theorem B2425133 : Blo 219811 2425133 := bstep (se 3 (by rfl) ⟨454712, by rfl⟩ : syracuseStep 2425133 = 909425) B909425
theorem B459059 : Blo 219811 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B557401 : Blo 219811 557401 := bstep (se 2 (by rfl) ⟨209025, by rfl⟩ : syracuseStep 557401 = 418051) B418051
theorem B950935 : Blo 219811 950935 := bstep (se 1 (by rfl) ⟨713201, by rfl⟩ : syracuseStep 950935 = 1426403) B1426403
theorem B754379 : Blo 219811 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B1016651 : Blo 219811 1016651 := bstep (se 1 (by rfl) ⟨762488, by rfl⟩ : syracuseStep 1016651 = 1524977) B1524977
theorem B754649 : Blo 219811 754649 := bstep (se 2 (by rfl) ⟨282993, by rfl⟩ : syracuseStep 754649 = 565987) B565987
theorem B558515 : Blo 219811 558515 := bstep (se 1 (by rfl) ⟨418886, by rfl⟩ : syracuseStep 558515 = 837773) B837773
theorem B951755 : Blo 219811 951755 := bstep (se 1 (by rfl) ⟨713816, by rfl⟩ : syracuseStep 951755 = 1427633) B1427633
theorem B1115693 : Blo 219811 1115693 := bstep (se 3 (by rfl) ⟨209192, by rfl⟩ : syracuseStep 1115693 = 418385) B418385
theorem B755351 : Blo 219811 755351 := bstep (se 1 (by rfl) ⟨566513, by rfl⟩ : syracuseStep 755351 = 1133027) B1133027
theorem B4130509 : Blo 219811 4130509 := bstep (se 3 (by rfl) ⟨774470, by rfl⟩ : syracuseStep 4130509 = 1548941) B1548941
theorem B558809 : Blo 219811 558809 := bstep (se 2 (by rfl) ⟨209553, by rfl⟩ : syracuseStep 558809 = 419107) B419107
theorem B3835633 : Blo 219811 3835633 := bstep (se 2 (by rfl) ⟨1438362, by rfl⟩ : syracuseStep 3835633 = 2876725) B2876725
theorem B952067 : Blo 219811 952067 := bstep (se 1 (by rfl) ⟨714050, by rfl⟩ : syracuseStep 952067 = 1428101) B1428101
theorem B952337 : Blo 219811 952337 := bstep (se 2 (by rfl) ⟨357126, by rfl⟩ : syracuseStep 952337 = 714253) B714253
theorem B329753 : Blo 219811 329753 := bstep (se 2 (by rfl) ⟨123657, by rfl⟩ : syracuseStep 329753 = 247315) B247315
theorem B329867 : Blo 219811 329867 := bstep (se 1 (by rfl) ⟨247400, by rfl⟩ : syracuseStep 329867 = 494801) B494801
theorem B329879 : Blo 219811 329879 := bstep (se 1 (by rfl) ⟨247409, by rfl⟩ : syracuseStep 329879 = 494819) B494819
theorem B329945 : Blo 219811 329945 := bstep (se 2 (by rfl) ⟨123729, by rfl⟩ : syracuseStep 329945 = 247459) B247459
theorem B330059 : Blo 219811 330059 := bstep (se 1 (by rfl) ⟨247544, by rfl⟩ : syracuseStep 330059 = 495089) B495089
theorem B330071 : Blo 219811 330071 := bstep (se 1 (by rfl) ⟨247553, by rfl⟩ : syracuseStep 330071 = 495107) B495107
theorem B330137 : Blo 219811 330137 := bstep (se 2 (by rfl) ⟨123801, by rfl⟩ : syracuseStep 330137 = 247603) B247603
theorem B330251 : Blo 219811 330251 := bstep (se 1 (by rfl) ⟨247688, by rfl⟩ : syracuseStep 330251 = 495377) B495377
theorem B330263 : Blo 219811 330263 := bstep (se 1 (by rfl) ⟨247697, by rfl⟩ : syracuseStep 330263 = 495395) B495395
theorem B330329 : Blo 219811 330329 := bstep (se 2 (by rfl) ⟨123873, by rfl⟩ : syracuseStep 330329 = 247747) B247747
theorem B330443 : Blo 219811 330443 := bstep (se 1 (by rfl) ⟨247832, by rfl⟩ : syracuseStep 330443 = 495665) B495665
theorem B330455 : Blo 219811 330455 := bstep (se 1 (by rfl) ⟨247841, by rfl⟩ : syracuseStep 330455 = 495683) B495683
theorem B330521 : Blo 219811 330521 := bstep (se 2 (by rfl) ⟨123945, by rfl⟩ : syracuseStep 330521 = 247891) B247891
theorem B330635 : Blo 219811 330635 := bstep (se 1 (by rfl) ⟨247976, by rfl⟩ : syracuseStep 330635 = 495953) B495953
theorem B330647 : Blo 219811 330647 := bstep (se 1 (by rfl) ⟨247985, by rfl⟩ : syracuseStep 330647 = 495971) B495971
theorem B330713 : Blo 219811 330713 := bstep (se 2 (by rfl) ⟨124017, by rfl⟩ : syracuseStep 330713 = 248035) B248035
theorem B494603 : Blo 219811 494603 := bstep (se 1 (by rfl) ⟨370952, by rfl⟩ : syracuseStep 494603 = 741905) B741905
theorem B494657 : Blo 219811 494657 := bstep (se 2 (by rfl) ⟨185496, by rfl⟩ : syracuseStep 494657 = 370993) B370993
theorem B330827 : Blo 219811 330827 := bstep (se 1 (by rfl) ⟨248120, by rfl⟩ : syracuseStep 330827 = 496241) B496241
theorem B330839 : Blo 219811 330839 := bstep (se 1 (by rfl) ⟨248129, by rfl⟩ : syracuseStep 330839 = 496259) B496259
theorem B2886749 : Blo 219811 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B330905 : Blo 219811 330905 := bstep (se 2 (by rfl) ⟨124089, by rfl⟩ : syracuseStep 330905 = 248179) B248179
theorem B396505 : Blo 219811 396505 := bstep (se 2 (by rfl) ⟨148689, by rfl⟩ : syracuseStep 396505 = 297379) B297379
theorem B331019 : Blo 219811 331019 := bstep (se 1 (by rfl) ⟨248264, by rfl⟩ : syracuseStep 331019 = 496529) B496529
theorem B331031 : Blo 219811 331031 := bstep (se 1 (by rfl) ⟨248273, by rfl⟩ : syracuseStep 331031 = 496547) B496547
theorem B494873 : Blo 219811 494873 := bstep (se 2 (by rfl) ⟨185577, by rfl⟩ : syracuseStep 494873 = 371155) B371155
theorem B560459 : Blo 219811 560459 := bstep (se 1 (by rfl) ⟨420344, by rfl⟩ : syracuseStep 560459 = 840689) B840689
theorem B331097 : Blo 219811 331097 := bstep (se 2 (by rfl) ⟨124161, by rfl⟩ : syracuseStep 331097 = 248323) B248323
theorem B494963 : Blo 219811 494963 := bstep (se 1 (by rfl) ⟨371222, by rfl⟩ : syracuseStep 494963 = 742445) B742445
theorem B494999 : Blo 219811 494999 := bstep (se 1 (by rfl) ⟨371249, by rfl⟩ : syracuseStep 494999 = 742499) B742499
theorem B331211 : Blo 219811 331211 := bstep (se 1 (by rfl) ⟨248408, by rfl⟩ : syracuseStep 331211 = 496817) B496817
theorem B331223 : Blo 219811 331223 := bstep (se 1 (by rfl) ⟨248417, by rfl⟩ : syracuseStep 331223 = 496835) B496835
theorem B396787 : Blo 219811 396787 := bstep (se 1 (by rfl) ⟨297590, by rfl⟩ : syracuseStep 396787 = 595181) B595181
theorem B331289 : Blo 219811 331289 := bstep (se 2 (by rfl) ⟨124233, by rfl⟩ : syracuseStep 331289 = 248467) B248467
theorem B495179 : Blo 219811 495179 := bstep (se 1 (by rfl) ⟨371384, by rfl⟩ : syracuseStep 495179 = 742769) B742769
theorem B495233 : Blo 219811 495233 := bstep (se 2 (by rfl) ⟨185712, by rfl⟩ : syracuseStep 495233 = 371425) B371425
theorem B331403 : Blo 219811 331403 := bstep (se 1 (by rfl) ⟨248552, by rfl⟩ : syracuseStep 331403 = 497105) B497105
theorem B331415 : Blo 219811 331415 := bstep (se 1 (by rfl) ⟨248561, by rfl⟩ : syracuseStep 331415 = 497123) B497123
theorem B757451 : Blo 219811 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B626393 : Blo 219811 626393 := bstep (se 2 (by rfl) ⟨234897, by rfl⟩ : syracuseStep 626393 = 469795) B469795
theorem B331481 : Blo 219811 331481 := bstep (se 2 (by rfl) ⟨124305, by rfl⟩ : syracuseStep 331481 = 248611) B248611
theorem B331595 : Blo 219811 331595 := bstep (se 1 (by rfl) ⟨248696, by rfl⟩ : syracuseStep 331595 = 497393) B497393
theorem B331607 : Blo 219811 331607 := bstep (se 1 (by rfl) ⟨248705, by rfl⟩ : syracuseStep 331607 = 497411) B497411
theorem B495449 : Blo 219811 495449 := bstep (se 2 (by rfl) ⟨185793, by rfl⟩ : syracuseStep 495449 = 371587) B371587
theorem B331673 : Blo 219811 331673 := bstep (se 2 (by rfl) ⟨124377, by rfl⟩ : syracuseStep 331673 = 248755) B248755
theorem B429977 : Blo 219811 429977 := bstep (se 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) B322483
theorem B495539 : Blo 219811 495539 := bstep (se 1 (by rfl) ⟨371654, by rfl⟩ : syracuseStep 495539 = 743309) B743309
theorem B495575 : Blo 219811 495575 := bstep (se 1 (by rfl) ⟨371681, by rfl⟩ : syracuseStep 495575 = 743363) B743363
theorem B397313 : Blo 219811 397313 := bstep (se 2 (by rfl) ⟨148992, by rfl⟩ : syracuseStep 397313 = 297985) B297985
theorem B331787 : Blo 219811 331787 := bstep (se 1 (by rfl) ⟨248840, by rfl⟩ : syracuseStep 331787 = 497681) B497681
theorem B331799 : Blo 219811 331799 := bstep (se 1 (by rfl) ⟨248849, by rfl⟩ : syracuseStep 331799 = 497699) B497699
theorem B331865 : Blo 219811 331865 := bstep (se 2 (by rfl) ⟨124449, by rfl⟩ : syracuseStep 331865 = 248899) B248899
theorem B1904741 : Blo 219811 1904741 := bstep (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) B357139
theorem B2134147 : Blo 219811 2134147 := bstep (se 1 (by rfl) ⟨1600610, by rfl⟩ : syracuseStep 2134147 = 3201221) B3201221
theorem B495755 : Blo 219811 495755 := bstep (se 1 (by rfl) ⟨371816, by rfl⟩ : syracuseStep 495755 = 743633) B743633
theorem B495809 : Blo 219811 495809 := bstep (se 2 (by rfl) ⟨185928, by rfl⟩ : syracuseStep 495809 = 371857) B371857
theorem B331979 : Blo 219811 331979 := bstep (se 1 (by rfl) ⟨248984, by rfl⟩ : syracuseStep 331979 = 497969) B497969
theorem B331991 : Blo 219811 331991 := bstep (se 1 (by rfl) ⟨248993, by rfl⟩ : syracuseStep 331991 = 497987) B497987
theorem B561431 : Blo 219811 561431 := bstep (se 1 (by rfl) ⟨421073, by rfl⟩ : syracuseStep 561431 = 842147) B842147
theorem B332057 : Blo 219811 332057 := bstep (se 2 (by rfl) ⟨124521, by rfl⟩ : syracuseStep 332057 = 249043) B249043
theorem B332171 : Blo 219811 332171 := bstep (se 1 (by rfl) ⟨249128, by rfl⟩ : syracuseStep 332171 = 498257) B498257
theorem B332183 : Blo 219811 332183 := bstep (se 1 (by rfl) ⟨249137, by rfl⟩ : syracuseStep 332183 = 498275) B498275
theorem B496025 : Blo 219811 496025 := bstep (se 2 (by rfl) ⟨186009, by rfl⟩ : syracuseStep 496025 = 372019) B372019
theorem B332249 : Blo 219811 332249 := bstep (se 2 (by rfl) ⟨124593, by rfl⟩ : syracuseStep 332249 = 249187) B249187
theorem B496115 : Blo 219811 496115 := bstep (se 1 (by rfl) ⟨372086, by rfl⟩ : syracuseStep 496115 = 744173) B744173
theorem B496151 : Blo 219811 496151 := bstep (se 1 (by rfl) ⟨372113, by rfl⟩ : syracuseStep 496151 = 744227) B744227
theorem B397847 : Blo 219811 397847 := bstep (se 1 (by rfl) ⟨298385, by rfl⟩ : syracuseStep 397847 = 596771) B596771
theorem B332363 : Blo 219811 332363 := bstep (se 1 (by rfl) ⟨249272, by rfl⟩ : syracuseStep 332363 = 498545) B498545
theorem B332375 : Blo 219811 332375 := bstep (se 1 (by rfl) ⟨249281, by rfl⟩ : syracuseStep 332375 = 498563) B498563
theorem B332441 : Blo 219811 332441 := bstep (se 2 (by rfl) ⟨124665, by rfl⟩ : syracuseStep 332441 = 249331) B249331
theorem B496331 : Blo 219811 496331 := bstep (se 1 (by rfl) ⟨372248, by rfl⟩ : syracuseStep 496331 = 744497) B744497
theorem B496385 : Blo 219811 496385 := bstep (se 2 (by rfl) ⟨186144, by rfl⟩ : syracuseStep 496385 = 372289) B372289
theorem B332555 : Blo 219811 332555 := bstep (se 1 (by rfl) ⟨249416, by rfl⟩ : syracuseStep 332555 = 498833) B498833
theorem B332567 : Blo 219811 332567 := bstep (se 1 (by rfl) ⟨249425, by rfl⟩ : syracuseStep 332567 = 498851) B498851
theorem B332633 : Blo 219811 332633 := bstep (se 2 (by rfl) ⟨124737, by rfl⟩ : syracuseStep 332633 = 249475) B249475
theorem B955309 : Blo 219811 955309 := bstep (se 3 (by rfl) ⟨179120, by rfl⟩ : syracuseStep 955309 = 358241) B358241
theorem B562099 : Blo 219811 562099 := bstep (se 1 (by rfl) ⟨421574, by rfl⟩ : syracuseStep 562099 = 843149) B843149
theorem B627659 : Blo 219811 627659 := bstep (se 1 (by rfl) ⟨470744, by rfl⟩ : syracuseStep 627659 = 941489) B941489
theorem B332747 : Blo 219811 332747 := bstep (se 1 (by rfl) ⟨249560, by rfl⟩ : syracuseStep 332747 = 499121) B499121
theorem B332759 : Blo 219811 332759 := bstep (se 1 (by rfl) ⟨249569, by rfl⟩ : syracuseStep 332759 = 499139) B499139
theorem B496601 : Blo 219811 496601 := bstep (se 2 (by rfl) ⟨186225, by rfl⟩ : syracuseStep 496601 = 372451) B372451
theorem B332825 : Blo 219811 332825 := bstep (se 2 (by rfl) ⟨124809, by rfl⟩ : syracuseStep 332825 = 249619) B249619
theorem B496691 : Blo 219811 496691 := bstep (se 1 (by rfl) ⟨372518, by rfl⟩ : syracuseStep 496691 = 745037) B745037
theorem B562241 : Blo 219811 562241 := bstep (se 2 (by rfl) ⟨210840, by rfl⟩ : syracuseStep 562241 = 421681) B421681
theorem B595019 : Blo 219811 595019 := bstep (se 1 (by rfl) ⟨446264, by rfl⟩ : syracuseStep 595019 = 892529) B892529
theorem B496727 : Blo 219811 496727 := bstep (se 1 (by rfl) ⟨372545, by rfl⟩ : syracuseStep 496727 = 745091) B745091
theorem B332939 : Blo 219811 332939 := bstep (se 1 (by rfl) ⟨249704, by rfl⟩ : syracuseStep 332939 = 499409) B499409
theorem B332951 : Blo 219811 332951 := bstep (se 1 (by rfl) ⟨249713, by rfl⟩ : syracuseStep 332951 = 499427) B499427
theorem B333017 : Blo 219811 333017 := bstep (se 2 (by rfl) ⟨124881, by rfl⟩ : syracuseStep 333017 = 249763) B249763
theorem B955651 : Blo 219811 955651 := bstep (se 1 (by rfl) ⟨716738, by rfl⟩ : syracuseStep 955651 = 1433477) B1433477
theorem B496907 : Blo 219811 496907 := bstep (se 1 (by rfl) ⟨372680, by rfl⟩ : syracuseStep 496907 = 745361) B745361
theorem B759091 : Blo 219811 759091 := bstep (se 1 (by rfl) ⟨569318, by rfl⟩ : syracuseStep 759091 = 1138637) B1138637
theorem B496961 : Blo 219811 496961 := bstep (se 2 (by rfl) ⟨186360, by rfl⟩ : syracuseStep 496961 = 372721) B372721
theorem B333131 : Blo 219811 333131 := bstep (se 1 (by rfl) ⟨249848, by rfl⟩ : syracuseStep 333131 = 499697) B499697
theorem B333143 : Blo 219811 333143 := bstep (se 1 (by rfl) ⟨249857, by rfl⟩ : syracuseStep 333143 = 499715) B499715
theorem B1119581 : Blo 219811 1119581 := bstep (se 3 (by rfl) ⟨209921, by rfl⟩ : syracuseStep 1119581 = 419843) B419843
theorem B333209 : Blo 219811 333209 := bstep (se 2 (by rfl) ⟨124953, by rfl⟩ : syracuseStep 333209 = 249907) B249907
theorem B333323 : Blo 219811 333323 := bstep (se 1 (by rfl) ⟨249992, by rfl⟩ : syracuseStep 333323 = 499985) B499985
theorem B333335 : Blo 219811 333335 := bstep (se 1 (by rfl) ⟨250001, by rfl⟩ : syracuseStep 333335 = 500003) B500003
theorem B497177 : Blo 219811 497177 := bstep (se 2 (by rfl) ⟨186441, by rfl⟩ : syracuseStep 497177 = 372883) B372883
theorem B333401 : Blo 219811 333401 := bstep (se 2 (by rfl) ⟨125025, by rfl⟩ : syracuseStep 333401 = 250051) B250051
theorem B497267 : Blo 219811 497267 := bstep (se 1 (by rfl) ⟨372950, by rfl⟩ : syracuseStep 497267 = 745901) B745901
theorem B497303 : Blo 219811 497303 := bstep (se 1 (by rfl) ⟨372977, by rfl⟩ : syracuseStep 497303 = 745955) B745955
theorem B333515 : Blo 219811 333515 := bstep (se 1 (by rfl) ⟨250136, by rfl⟩ : syracuseStep 333515 = 500273) B500273
theorem B333527 : Blo 219811 333527 := bstep (se 1 (by rfl) ⟨250145, by rfl⟩ : syracuseStep 333527 = 500291) B500291
theorem B333593 : Blo 219811 333593 := bstep (se 2 (by rfl) ⟨125097, by rfl⟩ : syracuseStep 333593 = 250195) B250195
theorem B497483 : Blo 219811 497483 := bstep (se 1 (by rfl) ⟨373112, by rfl⟩ : syracuseStep 497483 = 746225) B746225
theorem B497537 : Blo 219811 497537 := bstep (se 2 (by rfl) ⟨186576, by rfl⟩ : syracuseStep 497537 = 373153) B373153
theorem B333707 : Blo 219811 333707 := bstep (se 1 (by rfl) ⟨250280, by rfl⟩ : syracuseStep 333707 = 500561) B500561
theorem B530327 : Blo 219811 530327 := bstep (se 1 (by rfl) ⟨397745, by rfl⟩ : syracuseStep 530327 = 795491) B795491
theorem B333719 : Blo 219811 333719 := bstep (se 1 (by rfl) ⟨250289, by rfl⟩ : syracuseStep 333719 = 500579) B500579
theorem B333785 : Blo 219811 333785 := bstep (se 2 (by rfl) ⟨125169, by rfl⟩ : syracuseStep 333785 = 250339) B250339
theorem B235543 : Blo 219811 235543 := bstep (se 1 (by rfl) ⟨176657, by rfl⟩ : syracuseStep 235543 = 353315) B353315
theorem B2758691 : Blo 219811 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B333899 : Blo 219811 333899 := bstep (se 1 (by rfl) ⟨250424, by rfl⟩ : syracuseStep 333899 = 500849) B500849
theorem B333911 : Blo 219811 333911 := bstep (se 1 (by rfl) ⟨250433, by rfl⟩ : syracuseStep 333911 = 500867) B500867
theorem B497753 : Blo 219811 497753 := bstep (se 2 (by rfl) ⟨186657, by rfl⟩ : syracuseStep 497753 = 373315) B373315
theorem B399475 : Blo 219811 399475 := bstep (se 1 (by rfl) ⟨299606, by rfl⟩ : syracuseStep 399475 = 599213) B599213
theorem B333977 : Blo 219811 333977 := bstep (se 2 (by rfl) ⟨125241, by rfl⟩ : syracuseStep 333977 = 250483) B250483
theorem B497843 : Blo 219811 497843 := bstep (se 1 (by rfl) ⟨373382, by rfl⟩ : syracuseStep 497843 = 746765) B746765
theorem B497879 : Blo 219811 497879 := bstep (se 1 (by rfl) ⟨373409, by rfl⟩ : syracuseStep 497879 = 746819) B746819
theorem B334091 : Blo 219811 334091 := bstep (se 1 (by rfl) ⟨250568, by rfl⟩ : syracuseStep 334091 = 501137) B501137
theorem B334103 : Blo 219811 334103 := bstep (se 1 (by rfl) ⟨250577, by rfl⟩ : syracuseStep 334103 = 501155) B501155
theorem B563507 : Blo 219811 563507 := bstep (se 1 (by rfl) ⟨422630, by rfl⟩ : syracuseStep 563507 = 845261) B845261
theorem B334169 : Blo 219811 334169 := bstep (se 2 (by rfl) ⟨125313, by rfl⟩ : syracuseStep 334169 = 250627) B250627
theorem B498059 : Blo 219811 498059 := bstep (se 1 (by rfl) ⟨373544, by rfl⟩ : syracuseStep 498059 = 747089) B747089
theorem B1022381 : Blo 219811 1022381 := bstep (se 3 (by rfl) ⟨191696, by rfl⟩ : syracuseStep 1022381 = 383393) B383393
theorem B498113 : Blo 219811 498113 := bstep (se 2 (by rfl) ⟨186792, by rfl⟩ : syracuseStep 498113 = 373585) B373585
theorem B334283 : Blo 219811 334283 := bstep (se 1 (by rfl) ⟨250712, by rfl⟩ : syracuseStep 334283 = 501425) B501425
theorem B235991 : Blo 219811 235991 := bstep (se 1 (by rfl) ⟨176993, by rfl⟩ : syracuseStep 235991 = 353987) B353987
theorem B334295 : Blo 219811 334295 := bstep (se 1 (by rfl) ⟨250721, by rfl⟩ : syracuseStep 334295 = 501443) B501443
theorem B334361 : Blo 219811 334361 := bstep (se 2 (by rfl) ⟨125385, by rfl⟩ : syracuseStep 334361 = 250771) B250771
theorem B596531 : Blo 219811 596531 := bstep (se 1 (by rfl) ⟨447398, by rfl⟩ : syracuseStep 596531 = 894797) B894797
theorem B334475 : Blo 219811 334475 := bstep (se 1 (by rfl) ⟨250856, by rfl⟩ : syracuseStep 334475 = 501713) B501713
theorem B334487 : Blo 219811 334487 := bstep (se 1 (by rfl) ⟨250865, by rfl⟩ : syracuseStep 334487 = 501731) B501731
theorem B498329 : Blo 219811 498329 := bstep (se 2 (by rfl) ⟨186873, by rfl⟩ : syracuseStep 498329 = 373747) B373747
theorem B1252057 : Blo 219811 1252057 := bstep (se 2 (by rfl) ⟨469521, by rfl⟩ : syracuseStep 1252057 = 939043) B939043
theorem B334553 : Blo 219811 334553 := bstep (se 2 (by rfl) ⟨125457, by rfl⟩ : syracuseStep 334553 = 250915) B250915
theorem B498419 : Blo 219811 498419 := bstep (se 1 (by rfl) ⟨373814, by rfl⟩ : syracuseStep 498419 = 747629) B747629
theorem B498455 : Blo 219811 498455 := bstep (se 1 (by rfl) ⟨373841, by rfl⟩ : syracuseStep 498455 = 747683) B747683
theorem B236363 : Blo 219811 236363 := bstep (se 1 (by rfl) ⟨177272, by rfl⟩ : syracuseStep 236363 = 354545) B354545
theorem B564043 : Blo 219811 564043 := bstep (se 1 (by rfl) ⟨423032, by rfl⟩ : syracuseStep 564043 = 846065) B846065
theorem B334667 : Blo 219811 334667 := bstep (se 1 (by rfl) ⟨251000, by rfl⟩ : syracuseStep 334667 = 502001) B502001
theorem B334679 : Blo 219811 334679 := bstep (se 1 (by rfl) ⟨251009, by rfl⟩ : syracuseStep 334679 = 502019) B502019
theorem B334745 : Blo 219811 334745 := bstep (se 2 (by rfl) ⟨125529, by rfl⟩ : syracuseStep 334745 = 251059) B251059
theorem B498635 : Blo 219811 498635 := bstep (se 1 (by rfl) ⟨373976, by rfl⟩ : syracuseStep 498635 = 747953) B747953
theorem B564185 : Blo 219811 564185 := bstep (se 2 (by rfl) ⟨211569, by rfl⟩ : syracuseStep 564185 = 423139) B423139
theorem B498689 : Blo 219811 498689 := bstep (se 2 (by rfl) ⟨187008, by rfl⟩ : syracuseStep 498689 = 374017) B374017
theorem B334859 : Blo 219811 334859 := bstep (se 1 (by rfl) ⟨251144, by rfl⟩ : syracuseStep 334859 = 502289) B502289
theorem B334871 : Blo 219811 334871 := bstep (se 1 (by rfl) ⟨251153, by rfl⟩ : syracuseStep 334871 = 502307) B502307
theorem B334937 : Blo 219811 334937 := bstep (se 2 (by rfl) ⟨125601, by rfl⟩ : syracuseStep 334937 = 251203) B251203
theorem B335051 : Blo 219811 335051 := bstep (se 1 (by rfl) ⟨251288, by rfl⟩ : syracuseStep 335051 = 502577) B502577
theorem B335063 : Blo 219811 335063 := bstep (se 1 (by rfl) ⟨251297, by rfl⟩ : syracuseStep 335063 = 502595) B502595
theorem B498905 : Blo 219811 498905 := bstep (se 2 (by rfl) ⟨187089, by rfl⟩ : syracuseStep 498905 = 374179) B374179
theorem B302359 : Blo 219811 302359 := bstep (se 1 (by rfl) ⟨226769, by rfl⟩ : syracuseStep 302359 = 453539) B453539
theorem B335129 : Blo 219811 335129 := bstep (se 2 (by rfl) ⟨125673, by rfl⟩ : syracuseStep 335129 = 251347) B251347
theorem B498995 : Blo 219811 498995 := bstep (se 1 (by rfl) ⟨374246, by rfl⟩ : syracuseStep 498995 = 748493) B748493
theorem B400715 : Blo 219811 400715 := bstep (se 1 (by rfl) ⟨300536, by rfl⟩ : syracuseStep 400715 = 601073) B601073
theorem B499031 : Blo 219811 499031 := bstep (se 1 (by rfl) ⟨374273, by rfl⟩ : syracuseStep 499031 = 748547) B748547
theorem B335243 : Blo 219811 335243 := bstep (se 1 (by rfl) ⟨251432, by rfl⟩ : syracuseStep 335243 = 502865) B502865
theorem B1121687 : Blo 219811 1121687 := bstep (se 1 (by rfl) ⟨841265, by rfl⟩ : syracuseStep 1121687 = 1682531) B1682531
theorem B335255 : Blo 219811 335255 := bstep (se 1 (by rfl) ⟨251441, by rfl⟩ : syracuseStep 335255 = 502883) B502883
theorem B335321 : Blo 219811 335321 := bstep (se 2 (by rfl) ⟨125745, by rfl⟩ : syracuseStep 335321 = 251491) B251491
theorem B499211 : Blo 219811 499211 := bstep (se 1 (by rfl) ⟨374408, by rfl⟩ : syracuseStep 499211 = 748817) B748817
theorem B597527 : Blo 219811 597527 := bstep (se 1 (by rfl) ⟨448145, by rfl⟩ : syracuseStep 597527 = 896291) B896291
theorem B499265 : Blo 219811 499265 := bstep (se 2 (by rfl) ⟨187224, by rfl⟩ : syracuseStep 499265 = 374449) B374449
theorem B335435 : Blo 219811 335435 := bstep (se 1 (by rfl) ⟨251576, by rfl⟩ : syracuseStep 335435 = 503153) B503153
theorem B335447 : Blo 219811 335447 := bstep (se 1 (by rfl) ⟨251585, by rfl⟩ : syracuseStep 335447 = 503171) B503171
theorem B1253015 : Blo 219811 1253015 := bstep (se 1 (by rfl) ⟨939761, by rfl⟩ : syracuseStep 1253015 = 1879523) B1879523
theorem B335513 : Blo 219811 335513 := bstep (se 2 (by rfl) ⟨125817, by rfl⟩ : syracuseStep 335513 = 251635) B251635
theorem B335627 : Blo 219811 335627 := bstep (se 1 (by rfl) ⟨251720, by rfl⟩ : syracuseStep 335627 = 503441) B503441
theorem B565015 : Blo 219811 565015 := bstep (se 1 (by rfl) ⟨423761, by rfl⟩ : syracuseStep 565015 = 847523) B847523
theorem B335639 : Blo 219811 335639 := bstep (se 1 (by rfl) ⟨251729, by rfl⟩ : syracuseStep 335639 = 503459) B503459
theorem B499481 : Blo 219811 499481 := bstep (se 2 (by rfl) ⟨187305, by rfl⟩ : syracuseStep 499481 = 374611) B374611
theorem B237367 : Blo 219811 237367 := bstep (se 1 (by rfl) ⟨178025, by rfl⟩ : syracuseStep 237367 = 356051) B356051
theorem B335705 : Blo 219811 335705 := bstep (se 2 (by rfl) ⟨125889, by rfl⟩ : syracuseStep 335705 = 251779) B251779
theorem B499571 : Blo 219811 499571 := bstep (se 1 (by rfl) ⟨374678, by rfl⟩ : syracuseStep 499571 = 749357) B749357
theorem B499607 : Blo 219811 499607 := bstep (se 1 (by rfl) ⟨374705, by rfl⟩ : syracuseStep 499607 = 749411) B749411
theorem B270283 : Blo 219811 270283 := bstep (se 1 (by rfl) ⟨202712, by rfl⟩ : syracuseStep 270283 = 405425) B405425
theorem B532441 : Blo 219811 532441 := bstep (se 2 (by rfl) ⟨199665, by rfl⟩ : syracuseStep 532441 = 399331) B399331
theorem B499787 : Blo 219811 499787 := bstep (se 1 (by rfl) ⟨374840, by rfl⟩ : syracuseStep 499787 = 749681) B749681
theorem B499841 : Blo 219811 499841 := bstep (se 2 (by rfl) ⟨187440, by rfl⟩ : syracuseStep 499841 = 374881) B374881
theorem B401537 : Blo 219811 401537 := bstep (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) B301153
theorem B6037685 : Blo 219811 6037685 := bstep (se 5 (by rfl) ⟨283016, by rfl⟩ : syracuseStep 6037685 = 566033) B566033
theorem B565451 : Blo 219811 565451 := bstep (se 1 (by rfl) ⟨424088, by rfl⟩ : syracuseStep 565451 = 848177) B848177
theorem B500057 : Blo 219811 500057 := bstep (se 2 (by rfl) ⟨187521, by rfl⟩ : syracuseStep 500057 = 375043) B375043
theorem B500147 : Blo 219811 500147 := bstep (se 1 (by rfl) ⟨375110, by rfl⟩ : syracuseStep 500147 = 750221) B750221
theorem B500183 : Blo 219811 500183 := bstep (se 1 (by rfl) ⟨375137, by rfl⟩ : syracuseStep 500183 = 750275) B750275
theorem B3809753 : Blo 219811 3809753 := bstep (se 2 (by rfl) ⟨1428657, by rfl⟩ : syracuseStep 3809753 = 2857315) B2857315
theorem B565825 : Blo 219811 565825 := bstep (se 2 (by rfl) ⟨212184, by rfl⟩ : syracuseStep 565825 = 424369) B424369
theorem B238187 : Blo 219811 238187 := bstep (se 1 (by rfl) ⟨178640, by rfl⟩ : syracuseStep 238187 = 357281) B357281
theorem B500363 : Blo 219811 500363 := bstep (se 1 (by rfl) ⟨375272, by rfl⟩ : syracuseStep 500363 = 750545) B750545
theorem B500417 : Blo 219811 500417 := bstep (se 2 (by rfl) ⟨187656, by rfl⟩ : syracuseStep 500417 = 375313) B375313
theorem B271063 : Blo 219811 271063 := bstep (se 1 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 271063 = 406595) B406595
theorem B500633 : Blo 219811 500633 := bstep (se 2 (by rfl) ⟨187737, by rfl⟩ : syracuseStep 500633 = 375475) B375475
theorem B533441 : Blo 219811 533441 := bstep (se 2 (by rfl) ⟨200040, by rfl⟩ : syracuseStep 533441 = 400081) B400081
theorem B500723 : Blo 219811 500723 := bstep (se 1 (by rfl) ⟨375542, by rfl⟩ : syracuseStep 500723 = 751085) B751085
theorem B500759 : Blo 219811 500759 := bstep (se 1 (by rfl) ⟨375569, by rfl⟩ : syracuseStep 500759 = 751139) B751139
theorem B2270339 : Blo 219811 2270339 := bstep (se 1 (by rfl) ⟨1702754, by rfl⟩ : syracuseStep 2270339 = 3405509) B3405509
theorem B566423 : Blo 219811 566423 := bstep (se 1 (by rfl) ⟨424817, by rfl⟩ : syracuseStep 566423 = 849635) B849635
theorem B500939 : Blo 219811 500939 := bstep (se 1 (by rfl) ⟨375704, by rfl⟩ : syracuseStep 500939 = 751409) B751409
theorem B500993 : Blo 219811 500993 := bstep (se 2 (by rfl) ⟨187872, by rfl⟩ : syracuseStep 500993 = 375745) B375745
theorem B1516865 : Blo 219811 1516865 := bstep (se 2 (by rfl) ⟨568824, by rfl⟩ : syracuseStep 1516865 = 1137649) B1137649
theorem B501209 : Blo 219811 501209 := bstep (se 2 (by rfl) ⟨187953, by rfl⟩ : syracuseStep 501209 = 375907) B375907
theorem B501299 : Blo 219811 501299 := bstep (se 1 (by rfl) ⟨375974, by rfl⟩ : syracuseStep 501299 = 751949) B751949
theorem B501335 : Blo 219811 501335 := bstep (se 1 (by rfl) ⟨376001, by rfl⟩ : syracuseStep 501335 = 752003) B752003
theorem B1681073 : Blo 219811 1681073 := bstep (se 2 (by rfl) ⟨630402, by rfl⟩ : syracuseStep 1681073 = 1260805) B1260805
theorem B501427 : Blo 219811 501427 := bstep (se 1 (by rfl) ⟨376070, by rfl⟩ : syracuseStep 501427 = 752141) B752141
theorem B534209 : Blo 219811 534209 := bstep (se 2 (by rfl) ⟨200328, by rfl⟩ : syracuseStep 534209 = 400657) B400657
theorem B501515 : Blo 219811 501515 := bstep (se 1 (by rfl) ⟨376136, by rfl⟩ : syracuseStep 501515 = 752273) B752273
theorem B501569 : Blo 219811 501569 := bstep (se 2 (by rfl) ⟨188088, by rfl⟩ : syracuseStep 501569 = 376177) B376177
theorem B1419281 : Blo 219811 1419281 := bstep (se 2 (by rfl) ⟨532230, by rfl⟩ : syracuseStep 1419281 = 1064461) B1064461
theorem B501785 : Blo 219811 501785 := bstep (se 2 (by rfl) ⟨188169, by rfl⟩ : syracuseStep 501785 = 376339) B376339
theorem B1255499 : Blo 219811 1255499 := bstep (se 1 (by rfl) ⟨941624, by rfl⟩ : syracuseStep 1255499 = 1883249) B1883249
theorem B501875 : Blo 219811 501875 := bstep (se 1 (by rfl) ⟨376406, by rfl⟩ : syracuseStep 501875 = 752813) B752813
theorem B796817 : Blo 219811 796817 := bstep (se 2 (by rfl) ⟨298806, by rfl⟩ : syracuseStep 796817 = 597613) B597613
theorem B1681559 : Blo 219811 1681559 := bstep (se 1 (by rfl) ⟨1261169, by rfl⟩ : syracuseStep 1681559 = 2522339) B2522339
theorem B501911 : Blo 219811 501911 := bstep (se 1 (by rfl) ⟨376433, by rfl⟩ : syracuseStep 501911 = 752867) B752867
theorem B633035 : Blo 219811 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B502091 : Blo 219811 502091 := bstep (se 1 (by rfl) ⟨376568, by rfl⟩ : syracuseStep 502091 = 753137) B753137
theorem B3058037 : Blo 219811 3058037 := bstep (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) B286691
theorem B502145 : Blo 219811 502145 := bstep (se 2 (by rfl) ⟨188304, by rfl⟩ : syracuseStep 502145 = 376609) B376609
theorem B1812887 : Blo 219811 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B1354163 : Blo 219811 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B895511 : Blo 219811 895511 := bstep (se 1 (by rfl) ⟨671633, by rfl⟩ : syracuseStep 895511 = 1343267) B1343267
theorem B633433 : Blo 219811 633433 := bstep (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) B475075
theorem B502361 : Blo 219811 502361 := bstep (se 2 (by rfl) ⟨188385, by rfl⟩ : syracuseStep 502361 = 376771) B376771
theorem B4532867 : Blo 219811 4532867 := bstep (se 1 (by rfl) ⟨3399650, by rfl⟩ : syracuseStep 4532867 = 6799301) B6799301
theorem B502411 : Blo 219811 502411 := bstep (se 1 (by rfl) ⟨376808, by rfl⟩ : syracuseStep 502411 = 753617) B753617
theorem B371351 : Blo 219811 371351 := bstep (se 1 (by rfl) ⟨278513, by rfl⟩ : syracuseStep 371351 = 557027) B557027
theorem B502451 : Blo 219811 502451 := bstep (se 1 (by rfl) ⟨376838, by rfl⟩ : syracuseStep 502451 = 753677) B753677
theorem B502487 : Blo 219811 502487 := bstep (se 1 (by rfl) ⟨376865, by rfl⟩ : syracuseStep 502487 = 753731) B753731
theorem B371479 : Blo 219811 371479 := bstep (se 1 (by rfl) ⟨278609, by rfl⟩ : syracuseStep 371479 = 557219) B557219
theorem B1125251 : Blo 219811 1125251 := bstep (se 1 (by rfl) ⟨843938, by rfl⟩ : syracuseStep 1125251 = 1687877) B1687877
theorem B502667 : Blo 219811 502667 := bstep (se 1 (by rfl) ⟨377000, by rfl⟩ : syracuseStep 502667 = 754001) B754001
theorem B502721 : Blo 219811 502721 := bstep (se 2 (by rfl) ⟨188520, by rfl⟩ : syracuseStep 502721 = 377041) B377041
theorem B502937 : Blo 219811 502937 := bstep (se 2 (by rfl) ⟨188601, by rfl⟩ : syracuseStep 502937 = 377203) B377203
theorem B503027 : Blo 219811 503027 := bstep (se 1 (by rfl) ⟨377270, by rfl⟩ : syracuseStep 503027 = 754541) B754541
theorem B339223 : Blo 219811 339223 := bstep (se 1 (by rfl) ⟨254417, by rfl⟩ : syracuseStep 339223 = 508835) B508835
theorem B503063 : Blo 219811 503063 := bstep (se 1 (by rfl) ⟨377297, by rfl⟩ : syracuseStep 503063 = 754595) B754595
theorem B372107 : Blo 219811 372107 := bstep (se 1 (by rfl) ⟨279080, by rfl⟩ : syracuseStep 372107 = 558161) B558161
theorem B503243 : Blo 219811 503243 := bstep (se 1 (by rfl) ⟨377432, by rfl⟩ : syracuseStep 503243 = 754865) B754865
theorem B503297 : Blo 219811 503297 := bstep (se 2 (by rfl) ⟨188736, by rfl⟩ : syracuseStep 503297 = 377473) B377473
theorem B470539 : Blo 219811 470539 := bstep (se 1 (by rfl) ⟨352904, by rfl⟩ : syracuseStep 470539 = 705809) B705809
theorem B372235 : Blo 219811 372235 := bstep (se 1 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 372235 = 558353) B558353
theorem B470615 : Blo 219811 470615 := bstep (se 1 (by rfl) ⟨352961, by rfl⟩ : syracuseStep 470615 = 705923) B705923
theorem B372377 : Blo 219811 372377 := bstep (se 2 (by rfl) ⟨139641, by rfl⟩ : syracuseStep 372377 = 279283) B279283
theorem B503513 : Blo 219811 503513 := bstep (se 2 (by rfl) ⟨188817, by rfl⟩ : syracuseStep 503513 = 377635) B377635
theorem B372505 : Blo 219811 372505 := bstep (se 2 (by rfl) ⟨139689, by rfl⟩ : syracuseStep 372505 = 279379) B279379
theorem B634675 : Blo 219811 634675 := bstep (se 1 (by rfl) ⟨476006, by rfl⟩ : syracuseStep 634675 = 952013) B952013
theorem B536537 : Blo 219811 536537 := bstep (se 2 (by rfl) ⟨201201, by rfl⟩ : syracuseStep 536537 = 402403) B402403
theorem B798893 : Blo 219811 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B1585331 : Blo 219811 1585331 := bstep (se 1 (by rfl) ⟨1188998, by rfl⟩ : syracuseStep 1585331 = 2377997) B2377997
theorem B798923 : Blo 219811 798923 := bstep (se 1 (by rfl) ⟨599192, by rfl⟩ : syracuseStep 798923 = 1198385) B1198385
theorem B373079 : Blo 219811 373079 := bstep (se 1 (by rfl) ⟨279809, by rfl⟩ : syracuseStep 373079 = 559619) B559619
theorem B536921 : Blo 219811 536921 := bstep (se 2 (by rfl) ⟨201345, by rfl⟩ : syracuseStep 536921 = 402691) B402691
theorem B373207 : Blo 219811 373207 := bstep (se 1 (by rfl) ⟨279905, by rfl⟩ : syracuseStep 373207 = 559811) B559811
theorem B1258163 : Blo 219811 1258163 := bstep (se 1 (by rfl) ⟨943622, by rfl⟩ : syracuseStep 1258163 = 1887245) B1887245
theorem B1192805 : Blo 219811 1192805 := bstep (se 4 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 1192805 = 223651) B223651
theorem B2831435 : Blo 219811 2831435 := bstep (se 1 (by rfl) ⟨2123576, by rfl⟩ : syracuseStep 2831435 = 4247153) B4247153
theorem B373835 : Blo 219811 373835 := bstep (se 1 (by rfl) ⟨280376, by rfl⟩ : syracuseStep 373835 = 560753) B560753
theorem B373963 : Blo 219811 373963 := bstep (se 1 (by rfl) ⟨280472, by rfl⟩ : syracuseStep 373963 = 560945) B560945
theorem B472385 : Blo 219811 472385 := bstep (se 2 (by rfl) ⟨177144, by rfl⟩ : syracuseStep 472385 = 354289) B354289
theorem B374105 : Blo 219811 374105 := bstep (se 2 (by rfl) ⟨140289, by rfl⟩ : syracuseStep 374105 = 280579) B280579
theorem B374233 : Blo 219811 374233 := bstep (se 2 (by rfl) ⟨140337, by rfl⟩ : syracuseStep 374233 = 280675) B280675
theorem B374807 : Blo 219811 374807 := bstep (se 1 (by rfl) ⟨281105, by rfl⟩ : syracuseStep 374807 = 562211) B562211
theorem B1882187 : Blo 219811 1882187 := bstep (se 1 (by rfl) ⟨1411640, by rfl⟩ : syracuseStep 1882187 = 2823281) B2823281
theorem B1259621 : Blo 219811 1259621 := bstep (se 4 (by rfl) ⟨118089, by rfl⟩ : syracuseStep 1259621 = 236179) B236179
theorem B374935 : Blo 219811 374935 := bstep (se 1 (by rfl) ⟨281201, by rfl⟩ : syracuseStep 374935 = 562403) B562403
theorem B1128977 : Blo 219811 1128977 := bstep (se 2 (by rfl) ⟨423366, by rfl⟩ : syracuseStep 1128977 = 846733) B846733
theorem B1161745 : Blo 219811 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B1129139 : Blo 219811 1129139 := bstep (se 1 (by rfl) ⟨846854, by rfl⟩ : syracuseStep 1129139 = 1693709) B1693709
theorem B375563 : Blo 219811 375563 := bstep (se 1 (by rfl) ⟨281672, by rfl⟩ : syracuseStep 375563 = 563345) B563345
theorem B1260305 : Blo 219811 1260305 := bstep (se 2 (by rfl) ⟨472614, by rfl⟩ : syracuseStep 1260305 = 945229) B945229
theorem B899857 : Blo 219811 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B1358693 : Blo 219811 1358693 := bstep (se 4 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 1358693 = 254755) B254755
theorem B375691 : Blo 219811 375691 := bstep (se 1 (by rfl) ⟨281768, by rfl⟩ : syracuseStep 375691 = 563537) B563537
theorem B375833 : Blo 219811 375833 := bstep (se 2 (by rfl) ⟨140937, by rfl⟩ : syracuseStep 375833 = 281875) B281875
theorem B4045859 : Blo 219811 4045859 := bstep (se 1 (by rfl) ⟨3034394, by rfl⟩ : syracuseStep 4045859 = 6068789) B6068789
theorem B474187 : Blo 219811 474187 := bstep (se 1 (by rfl) ⟨355640, by rfl⟩ : syracuseStep 474187 = 711281) B711281
theorem B375961 : Blo 219811 375961 := bstep (se 2 (by rfl) ⟨140985, by rfl⟩ : syracuseStep 375961 = 281971) B281971
theorem B2539025 : Blo 219811 2539025 := bstep (se 2 (by rfl) ⟨952134, by rfl⟩ : syracuseStep 2539025 = 1904269) B1904269
theorem B507521 : Blo 219811 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B376535 : Blo 219811 376535 := bstep (se 1 (by rfl) ⟨282401, by rfl⟩ : syracuseStep 376535 = 564803) B564803
theorem B835373 : Blo 219811 835373 := bstep (se 3 (by rfl) ⟨156632, by rfl⟩ : syracuseStep 835373 = 313265) B313265
theorem B376663 : Blo 219811 376663 := bstep (se 1 (by rfl) ⟨282497, by rfl⟩ : syracuseStep 376663 = 564995) B564995
theorem B2473907 : Blo 219811 2473907 := bstep (se 1 (by rfl) ⟨1855430, by rfl⟩ : syracuseStep 2473907 = 3710861) B3710861
theorem B704477 : Blo 219811 704477 := bstep (se 3 (by rfl) ⟨132089, by rfl⟩ : syracuseStep 704477 = 264179) B264179
theorem B1065035 : Blo 219811 1065035 := bstep (se 1 (by rfl) ⟨798776, by rfl⟩ : syracuseStep 1065035 = 1597553) B1597553
theorem B1425559 : Blo 219811 1425559 := bstep (se 1 (by rfl) ⟨1069169, by rfl⟩ : syracuseStep 1425559 = 2138339) B2138339
theorem B278731 : Blo 219811 278731 := bstep (se 1 (by rfl) ⟨209048, by rfl⟩ : syracuseStep 278731 = 418097) B418097
theorem B803033 : Blo 219811 803033 := bstep (se 2 (by rfl) ⟨301137, by rfl⟩ : syracuseStep 803033 = 602275) B602275
theorem B377111 : Blo 219811 377111 := bstep (se 1 (by rfl) ⟨282833, by rfl⟩ : syracuseStep 377111 = 565667) B565667
theorem B1589539 : Blo 219811 1589539 := bstep (se 1 (by rfl) ⟨1192154, by rfl⟩ : syracuseStep 1589539 = 2384309) B2384309
theorem B1786157 : Blo 219811 1786157 := bstep (se 3 (by rfl) ⟨334904, by rfl⟩ : syracuseStep 1786157 = 669809) B669809
theorem B475571 : Blo 219811 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B377291 : Blo 219811 377291 := bstep (se 1 (by rfl) ⟨282968, by rfl⟩ : syracuseStep 377291 = 565937) B565937
theorem B1131083 : Blo 219811 1131083 := bstep (se 1 (by rfl) ⟨848312, by rfl⟩ : syracuseStep 1131083 = 1696625) B1696625
theorem B377419 : Blo 219811 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B836185 : Blo 219811 836185 := bstep (se 2 (by rfl) ⟨313569, by rfl⟩ : syracuseStep 836185 = 627139) B627139
theorem B377561 : Blo 219811 377561 := bstep (se 2 (by rfl) ⟨141585, by rfl⟩ : syracuseStep 377561 = 283171) B283171
theorem B672605 : Blo 219811 672605 := bstep (se 3 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 672605 = 252227) B252227
theorem B279703 : Blo 219811 279703 := bstep (se 1 (by rfl) ⟨209777, by rfl⟩ : syracuseStep 279703 = 419555) B419555
theorem B836801 : Blo 219811 836801 := bstep (se 2 (by rfl) ⟨313800, by rfl⟩ : syracuseStep 836801 = 627601) B627601
theorem B476417 : Blo 219811 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B1688849 : Blo 219811 1688849 := bstep (se 2 (by rfl) ⟨633318, by rfl⟩ : syracuseStep 1688849 = 1266637) B1266637
theorem B2606627 : Blo 219811 2606627 := bstep (se 1 (by rfl) ⟨1954970, by rfl⟩ : syracuseStep 2606627 = 3909941) B3909941
theorem B247351 : Blo 219811 247351 := bstep (se 1 (by rfl) ⟨185513, by rfl⟩ : syracuseStep 247351 = 371027) B371027
theorem B476759 : Blo 219811 476759 := bstep (se 1 (by rfl) ⟨357569, by rfl⟩ : syracuseStep 476759 = 715139) B715139
theorem B247531 : Blo 219811 247531 := bstep (se 1 (by rfl) ⟨185648, by rfl⟩ : syracuseStep 247531 = 371297) B371297
theorem B247639 : Blo 219811 247639 := bstep (se 1 (by rfl) ⟨185729, by rfl⟩ : syracuseStep 247639 = 371459) B371459
theorem B2836403 : Blo 219811 2836403 := bstep (se 1 (by rfl) ⟨2127302, by rfl⟩ : syracuseStep 2836403 = 4254605) B4254605
theorem B1263539 : Blo 219811 1263539 := bstep (se 1 (by rfl) ⟨947654, by rfl⟩ : syracuseStep 1263539 = 1895309) B1895309
theorem B280523 : Blo 219811 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B247819 : Blo 219811 247819 := bstep (se 1 (by rfl) ⟨185864, by rfl⟩ : syracuseStep 247819 = 371729) B371729
theorem B510067 : Blo 219811 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B247927 : Blo 219811 247927 := bstep (se 1 (by rfl) ⟨185945, by rfl⟩ : syracuseStep 247927 = 371891) B371891
theorem B313561 : Blo 219811 313561 := bstep (se 2 (by rfl) ⟨117585, by rfl⟩ : syracuseStep 313561 = 235171) B235171
theorem B248107 : Blo 219811 248107 := bstep (se 1 (by rfl) ⟨186080, by rfl⟩ : syracuseStep 248107 = 372161) B372161
theorem B1132865 : Blo 219811 1132865 := bstep (se 2 (by rfl) ⟨424824, by rfl⟩ : syracuseStep 1132865 = 849649) B849649
theorem B248215 : Blo 219811 248215 := bstep (se 1 (by rfl) ⟨186161, by rfl⟩ : syracuseStep 248215 = 372323) B372323
theorem B2279897 : Blo 219811 2279897 := bstep (se 2 (by rfl) ⟨854961, by rfl⟩ : syracuseStep 2279897 = 1709923) B1709923
theorem B510451 : Blo 219811 510451 := bstep (se 1 (by rfl) ⟨382838, by rfl⟩ : syracuseStep 510451 = 765677) B765677
theorem B248395 : Blo 219811 248395 := bstep (se 1 (by rfl) ⟨186296, by rfl⟩ : syracuseStep 248395 = 372593) B372593
theorem B1428043 : Blo 219811 1428043 := bstep (se 1 (by rfl) ⟨1071032, by rfl⟩ : syracuseStep 1428043 = 2142065) B2142065
theorem B1067651 : Blo 219811 1067651 := bstep (se 1 (by rfl) ⟨800738, by rfl⟩ : syracuseStep 1067651 = 1601477) B1601477
theorem B281227 : Blo 219811 281227 := bstep (se 1 (by rfl) ⟨210920, by rfl⟩ : syracuseStep 281227 = 421841) B421841
theorem B838289 : Blo 219811 838289 := bstep (se 2 (by rfl) ⟨314358, by rfl⟩ : syracuseStep 838289 = 628717) B628717
theorem B248503 : Blo 219811 248503 := bstep (se 1 (by rfl) ⟨186377, by rfl⟩ : syracuseStep 248503 = 372755) B372755
theorem B805697 : Blo 219811 805697 := bstep (se 2 (by rfl) ⟨302136, by rfl⟩ : syracuseStep 805697 = 604273) B604273
theorem B248683 : Blo 219811 248683 := bstep (se 1 (by rfl) ⟨186512, by rfl⟩ : syracuseStep 248683 = 373025) B373025
theorem B281495 : Blo 219811 281495 := bstep (se 1 (by rfl) ⟨211121, by rfl⟩ : syracuseStep 281495 = 422243) B422243
theorem B3197873 : Blo 219811 3197873 := bstep (se 2 (by rfl) ⟨1199202, by rfl⟩ : syracuseStep 3197873 = 2398405) B2398405
theorem B248791 : Blo 219811 248791 := bstep (se 1 (by rfl) ⟨186593, by rfl⟩ : syracuseStep 248791 = 373187) B373187
theorem B838745 : Blo 219811 838745 := bstep (se 2 (by rfl) ⟨314529, by rfl⟩ : syracuseStep 838745 = 629059) B629059
theorem B248971 : Blo 219811 248971 := bstep (se 1 (by rfl) ⟨186728, by rfl⟩ : syracuseStep 248971 = 373457) B373457
theorem B249079 : Blo 219811 249079 := bstep (se 1 (by rfl) ⟨186809, by rfl⟩ : syracuseStep 249079 = 373619) B373619
theorem B478487 : Blo 219811 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B838957 : Blo 219811 838957 := bstep (se 3 (by rfl) ⟨157304, by rfl⟩ : syracuseStep 838957 = 314609) B314609
theorem B806219 : Blo 219811 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B1264997 : Blo 219811 1264997 := bstep (se 4 (by rfl) ⟨118593, by rfl⟩ : syracuseStep 1264997 = 237187) B237187
theorem B249259 : Blo 219811 249259 := bstep (se 1 (by rfl) ⟨186944, by rfl⟩ : syracuseStep 249259 = 373889) B373889
theorem B249367 : Blo 219811 249367 := bstep (se 1 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 249367 = 374051) B374051
theorem B380503 : Blo 219811 380503 := bstep (se 1 (by rfl) ⟨285377, by rfl⟩ : syracuseStep 380503 = 570755) B570755
theorem B282199 : Blo 219811 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B839261 : Blo 219811 839261 := bstep (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) B314723
theorem B315019 : Blo 219811 315019 := bstep (se 1 (by rfl) ⟨236264, by rfl⟩ : syracuseStep 315019 = 472529) B472529
theorem B315031 : Blo 219811 315031 := bstep (se 1 (by rfl) ⟨236273, by rfl⟩ : syracuseStep 315031 = 472547) B472547
theorem B1199767 : Blo 219811 1199767 := bstep (se 1 (by rfl) ⟨899825, by rfl⟩ : syracuseStep 1199767 = 1799651) B1799651
theorem B249547 : Blo 219811 249547 := bstep (se 1 (by rfl) ⟨187160, by rfl⟩ : syracuseStep 249547 = 374321) B374321
theorem B6082253 : Blo 219811 6082253 := bstep (se 3 (by rfl) ⟨1140422, by rfl⟩ : syracuseStep 6082253 = 2280845) B2280845
theorem B1265453 : Blo 219811 1265453 := bstep (se 3 (by rfl) ⟨237272, by rfl⟩ : syracuseStep 1265453 = 474545) B474545
theorem B249655 : Blo 219811 249655 := bstep (se 1 (by rfl) ⟨187241, by rfl⟩ : syracuseStep 249655 = 374483) B374483
theorem B446323 : Blo 219811 446323 := bstep (se 1 (by rfl) ⟨334742, by rfl⟩ : syracuseStep 446323 = 669485) B669485
theorem B610199 : Blo 219811 610199 := bstep (se 1 (by rfl) ⟨457649, by rfl⟩ : syracuseStep 610199 = 915299) B915299
theorem B249835 : Blo 219811 249835 := bstep (se 1 (by rfl) ⟨187376, by rfl⟩ : syracuseStep 249835 = 374753) B374753
theorem B249943 : Blo 219811 249943 := bstep (se 1 (by rfl) ⟨187457, by rfl⟩ : syracuseStep 249943 = 374915) B374915
theorem B4837637 : Blo 219811 4837637 := bstep (se 4 (by rfl) ⟨453528, by rfl⟩ : syracuseStep 4837637 = 907057) B907057
theorem B250123 : Blo 219811 250123 := bstep (se 1 (by rfl) ⟨187592, by rfl⟩ : syracuseStep 250123 = 375185) B375185
theorem B250231 : Blo 219811 250231 := bstep (se 1 (by rfl) ⟨187673, by rfl⟩ : syracuseStep 250231 = 375347) B375347
theorem B1266137 : Blo 219811 1266137 := bstep (se 2 (by rfl) ⟨474801, by rfl⟩ : syracuseStep 1266137 = 949603) B949603
theorem B250411 : Blo 219811 250411 := bstep (se 1 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 250411 = 375617) B375617
theorem B250519 : Blo 219811 250519 := bstep (se 1 (by rfl) ⟨187889, by rfl⟩ : syracuseStep 250519 = 375779) B375779
theorem B742067 : Blo 219811 742067 := bstep (se 1 (by rfl) ⟨556550, by rfl⟩ : syracuseStep 742067 = 1113101) B1113101
theorem B250699 : Blo 219811 250699 := bstep (se 1 (by rfl) ⟨188024, by rfl⟩ : syracuseStep 250699 = 376049) B376049
theorem B250807 : Blo 219811 250807 := bstep (se 1 (by rfl) ⟨188105, by rfl⟩ : syracuseStep 250807 = 376211) B376211
theorem B742337 : Blo 219811 742337 := bstep (se 2 (by rfl) ⟨278376, by rfl⟩ : syracuseStep 742337 = 556753) B556753
theorem B4248611 : Blo 219811 4248611 := bstep (se 1 (by rfl) ⟨3186458, by rfl⟩ : syracuseStep 4248611 = 6372917) B6372917
theorem B1692737 : Blo 219811 1692737 := bstep (se 2 (by rfl) ⟨634776, by rfl⟩ : syracuseStep 1692737 = 1269553) B1269553
theorem B250987 : Blo 219811 250987 := bstep (se 1 (by rfl) ⟨188240, by rfl⟩ : syracuseStep 250987 = 376481) B376481
theorem B251095 : Blo 219811 251095 := bstep (se 1 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 251095 = 376643) B376643
theorem B2512133 : Blo 219811 2512133 := bstep (se 4 (by rfl) ⟨235512, by rfl⟩ : syracuseStep 2512133 = 471025) B471025
theorem B1135889 : Blo 219811 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B251275 : Blo 219811 251275 := bstep (se 1 (by rfl) ⟨188456, by rfl⟩ : syracuseStep 251275 = 376913) B376913
theorem B742877 : Blo 219811 742877 := bstep (se 3 (by rfl) ⟨139289, by rfl⟩ : syracuseStep 742877 = 278579) B278579
theorem B251383 : Blo 219811 251383 := bstep (se 1 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 251383 = 377075) B377075
theorem B808451 : Blo 219811 808451 := bstep (se 1 (by rfl) ⟨606338, by rfl⟩ : syracuseStep 808451 = 1212677) B1212677
theorem B317081 : Blo 219811 317081 := bstep (se 2 (by rfl) ⟨118905, by rfl⟩ : syracuseStep 317081 = 237811) B237811
theorem B251563 : Blo 219811 251563 := bstep (se 1 (by rfl) ⟨188672, by rfl⟩ : syracuseStep 251563 = 377345) B377345
theorem B251671 : Blo 219811 251671 := bstep (se 1 (by rfl) ⟨188753, by rfl⟩ : syracuseStep 251671 = 377507) B377507
theorem B677911 : Blo 219811 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B841859 : Blo 219811 841859 := bstep (se 1 (by rfl) ⟨631394, by rfl⟩ : syracuseStep 841859 = 1262789) B1262789
theorem B841873 : Blo 219811 841873 := bstep (se 2 (by rfl) ⟨315702, by rfl⟩ : syracuseStep 841873 = 631405) B631405
theorem B317719 : Blo 219811 317719 := bstep (se 1 (by rfl) ⟨238289, by rfl⟩ : syracuseStep 317719 = 476579) B476579
theorem B1890661 : Blo 219811 1890661 := bstep (se 4 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 1890661 = 354499) B354499
theorem B842177 : Blo 219811 842177 := bstep (se 2 (by rfl) ⟨315816, by rfl⟩ : syracuseStep 842177 = 631633) B631633
theorem B940547 : Blo 219811 940547 := bstep (se 1 (by rfl) ⟨705410, by rfl⟩ : syracuseStep 940547 = 1410821) B1410821
theorem B645655 : Blo 219811 645655 := bstep (se 1 (by rfl) ⟨484241, by rfl⟩ : syracuseStep 645655 = 968483) B968483
theorem B744011 : Blo 219811 744011 := bstep (se 1 (by rfl) ⟨558008, by rfl⟩ : syracuseStep 744011 = 1116017) B1116017
theorem B219819 : Blo 219811 219819 := bstep (se 1 (by rfl) ⟨164864, by rfl⟩ : syracuseStep 219819 = 329729) B329729
theorem B219831 : Blo 219811 219831 := bstep (se 1 (by rfl) ⟨164873, by rfl⟩ : syracuseStep 219831 = 329747) B329747
theorem B219851 : Blo 219811 219851 := bstep (se 1 (by rfl) ⟨164888, by rfl⟩ : syracuseStep 219851 = 329777) B329777
theorem B219863 : Blo 219811 219863 := bstep (se 1 (by rfl) ⟨164897, by rfl⟩ : syracuseStep 219863 = 329795) B329795
theorem B219883 : Blo 219811 219883 := bstep (se 1 (by rfl) ⟨164912, by rfl⟩ : syracuseStep 219883 = 329825) B329825
theorem B219895 : Blo 219811 219895 := bstep (se 1 (by rfl) ⟨164921, by rfl⟩ : syracuseStep 219895 = 329843) B329843
theorem B219915 : Blo 219811 219915 := bstep (se 1 (by rfl) ⟨164936, by rfl⟩ : syracuseStep 219915 = 329873) B329873
theorem B219927 : Blo 219811 219927 := bstep (se 1 (by rfl) ⟨164945, by rfl⟩ : syracuseStep 219927 = 329891) B329891
theorem B219947 : Blo 219811 219947 := bstep (se 1 (by rfl) ⟨164960, by rfl⟩ : syracuseStep 219947 = 329921) B329921
theorem B219959 : Blo 219811 219959 := bstep (se 1 (by rfl) ⟨164969, by rfl⟩ : syracuseStep 219959 = 329939) B329939
theorem B219979 : Blo 219811 219979 := bstep (se 1 (by rfl) ⟨164984, by rfl⟩ : syracuseStep 219979 = 329969) B329969
theorem B219991 : Blo 219811 219991 := bstep (se 1 (by rfl) ⟨164993, by rfl⟩ : syracuseStep 219991 = 329987) B329987
theorem B940889 : Blo 219811 940889 := bstep (se 2 (by rfl) ⟨352833, by rfl⟩ : syracuseStep 940889 = 705667) B705667
theorem B744281 : Blo 219811 744281 := bstep (se 2 (by rfl) ⟨279105, by rfl⟩ : syracuseStep 744281 = 558211) B558211
theorem B6970211 : Blo 219811 6970211 := bstep (se 1 (by rfl) ⟨5227658, by rfl⟩ : syracuseStep 6970211 = 10455317) B10455317
theorem B220011 : Blo 219811 220011 := bstep (se 1 (by rfl) ⟨165008, by rfl⟩ : syracuseStep 220011 = 330017) B330017
theorem B220023 : Blo 219811 220023 := bstep (se 1 (by rfl) ⟨165017, by rfl⟩ : syracuseStep 220023 = 330035) B330035
theorem B220043 : Blo 219811 220043 := bstep (se 1 (by rfl) ⟨165032, by rfl⟩ : syracuseStep 220043 = 330065) B330065
theorem B220055 : Blo 219811 220055 := bstep (se 1 (by rfl) ⟨165041, by rfl⟩ : syracuseStep 220055 = 330083) B330083
theorem B220075 : Blo 219811 220075 := bstep (se 1 (by rfl) ⟨165056, by rfl⟩ : syracuseStep 220075 = 330113) B330113
theorem B220087 : Blo 219811 220087 := bstep (se 1 (by rfl) ⟨165065, by rfl⟩ : syracuseStep 220087 = 330131) B330131
theorem B220107 : Blo 219811 220107 := bstep (se 1 (by rfl) ⟨165080, by rfl⟩ : syracuseStep 220107 = 330161) B330161
theorem B220119 : Blo 219811 220119 := bstep (se 1 (by rfl) ⟨165089, by rfl⟩ : syracuseStep 220119 = 330179) B330179
theorem B1694681 : Blo 219811 1694681 := bstep (se 2 (by rfl) ⟨635505, by rfl⟩ : syracuseStep 1694681 = 1271011) B1271011
theorem B220139 : Blo 219811 220139 := bstep (se 1 (by rfl) ⟨165104, by rfl⟩ : syracuseStep 220139 = 330209) B330209
theorem B220151 : Blo 219811 220151 := bstep (se 1 (by rfl) ⟨165113, by rfl⟩ : syracuseStep 220151 = 330227) B330227
theorem B220171 : Blo 219811 220171 := bstep (se 1 (by rfl) ⟨165128, by rfl⟩ : syracuseStep 220171 = 330257) B330257
theorem B220183 : Blo 219811 220183 := bstep (se 1 (by rfl) ⟨165137, by rfl⟩ : syracuseStep 220183 = 330275) B330275
theorem B318487 : Blo 219811 318487 := bstep (se 1 (by rfl) ⟨238865, by rfl⟩ : syracuseStep 318487 = 477731) B477731
theorem B220203 : Blo 219811 220203 := bstep (se 1 (by rfl) ⟨165152, by rfl⟩ : syracuseStep 220203 = 330305) B330305
theorem B220215 : Blo 219811 220215 := bstep (se 1 (by rfl) ⟨165161, by rfl⟩ : syracuseStep 220215 = 330323) B330323
theorem B220235 : Blo 219811 220235 := bstep (se 1 (by rfl) ⟨165176, by rfl⟩ : syracuseStep 220235 = 330353) B330353
theorem B318539 : Blo 219811 318539 := bstep (se 1 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 318539 = 477809) B477809
theorem B220247 : Blo 219811 220247 := bstep (se 1 (by rfl) ⟨165185, by rfl⟩ : syracuseStep 220247 = 330371) B330371
theorem B842845 : Blo 219811 842845 := bstep (se 3 (by rfl) ⟨158033, by rfl⟩ : syracuseStep 842845 = 316067) B316067
theorem B220267 : Blo 219811 220267 := bstep (se 1 (by rfl) ⟨165200, by rfl⟩ : syracuseStep 220267 = 330401) B330401
theorem B220279 : Blo 219811 220279 := bstep (se 1 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 220279 = 330419) B330419
theorem B220299 : Blo 219811 220299 := bstep (se 1 (by rfl) ⟨165224, by rfl⟩ : syracuseStep 220299 = 330449) B330449
theorem B220311 : Blo 219811 220311 := bstep (se 1 (by rfl) ⟨165233, by rfl⟩ : syracuseStep 220311 = 330467) B330467
theorem B220331 : Blo 219811 220331 := bstep (se 1 (by rfl) ⟨165248, by rfl⟩ : syracuseStep 220331 = 330497) B330497
theorem B220343 : Blo 219811 220343 := bstep (se 1 (by rfl) ⟨165257, by rfl⟩ : syracuseStep 220343 = 330515) B330515
theorem B220363 : Blo 219811 220363 := bstep (se 1 (by rfl) ⟨165272, by rfl⟩ : syracuseStep 220363 = 330545) B330545
theorem B679115 : Blo 219811 679115 := bstep (se 1 (by rfl) ⟨509336, by rfl⟩ : syracuseStep 679115 = 1018673) B1018673
theorem B220375 : Blo 219811 220375 := bstep (se 1 (by rfl) ⟨165281, by rfl⟩ : syracuseStep 220375 = 330563) B330563
theorem B220395 : Blo 219811 220395 := bstep (se 1 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 220395 = 330593) B330593
theorem B220407 : Blo 219811 220407 := bstep (se 1 (by rfl) ⟨165305, by rfl⟩ : syracuseStep 220407 = 330611) B330611
theorem B220427 : Blo 219811 220427 := bstep (se 1 (by rfl) ⟨165320, by rfl⟩ : syracuseStep 220427 = 330641) B330641
theorem B220439 : Blo 219811 220439 := bstep (se 1 (by rfl) ⟨165329, by rfl⟩ : syracuseStep 220439 = 330659) B330659
theorem B1891619 : Blo 219811 1891619 := bstep (se 1 (by rfl) ⟨1418714, by rfl⟩ : syracuseStep 1891619 = 2837429) B2837429
theorem B220459 : Blo 219811 220459 := bstep (se 1 (by rfl) ⟨165344, by rfl⟩ : syracuseStep 220459 = 330689) B330689
theorem B220471 : Blo 219811 220471 := bstep (se 1 (by rfl) ⟨165353, by rfl⟩ : syracuseStep 220471 = 330707) B330707
theorem B220491 : Blo 219811 220491 := bstep (se 1 (by rfl) ⟨165368, by rfl⟩ : syracuseStep 220491 = 330737) B330737
theorem B220503 : Blo 219811 220503 := bstep (se 1 (by rfl) ⟨165377, by rfl⟩ : syracuseStep 220503 = 330755) B330755
theorem B220523 : Blo 219811 220523 := bstep (se 1 (by rfl) ⟨165392, by rfl⟩ : syracuseStep 220523 = 330785) B330785
theorem B220535 : Blo 219811 220535 := bstep (se 1 (by rfl) ⟨165401, by rfl⟩ : syracuseStep 220535 = 330803) B330803
theorem B220555 : Blo 219811 220555 := bstep (se 1 (by rfl) ⟨165416, by rfl⟩ : syracuseStep 220555 = 330833) B330833
theorem B220567 : Blo 219811 220567 := bstep (se 1 (by rfl) ⟨165425, by rfl⟩ : syracuseStep 220567 = 330851) B330851
theorem B220587 : Blo 219811 220587 := bstep (se 1 (by rfl) ⟨165440, by rfl⟩ : syracuseStep 220587 = 330881) B330881
theorem B220599 : Blo 219811 220599 := bstep (se 1 (by rfl) ⟨165449, by rfl⟩ : syracuseStep 220599 = 330899) B330899
theorem B220619 : Blo 219811 220619 := bstep (se 1 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 220619 = 330929) B330929
theorem B220631 : Blo 219811 220631 := bstep (se 1 (by rfl) ⟨165473, by rfl⟩ : syracuseStep 220631 = 330947) B330947
theorem B220651 : Blo 219811 220651 := bstep (se 1 (by rfl) ⟨165488, by rfl⟩ : syracuseStep 220651 = 330977) B330977
theorem B220663 : Blo 219811 220663 := bstep (se 1 (by rfl) ⟨165497, by rfl⟩ : syracuseStep 220663 = 330995) B330995
theorem B220683 : Blo 219811 220683 := bstep (se 1 (by rfl) ⟨165512, by rfl⟩ : syracuseStep 220683 = 331025) B331025
theorem B220695 : Blo 219811 220695 := bstep (se 1 (by rfl) ⟨165521, by rfl⟩ : syracuseStep 220695 = 331043) B331043
theorem B744983 : Blo 219811 744983 := bstep (se 1 (by rfl) ⟨558737, by rfl⟩ : syracuseStep 744983 = 1117475) B1117475
theorem B220715 : Blo 219811 220715 := bstep (se 1 (by rfl) ⟨165536, by rfl⟩ : syracuseStep 220715 = 331073) B331073
theorem B220727 : Blo 219811 220727 := bstep (se 1 (by rfl) ⟨165545, by rfl⟩ : syracuseStep 220727 = 331091) B331091
theorem B220747 : Blo 219811 220747 := bstep (se 1 (by rfl) ⟨165560, by rfl⟩ : syracuseStep 220747 = 331121) B331121
theorem B220759 : Blo 219811 220759 := bstep (se 1 (by rfl) ⟨165569, by rfl⟩ : syracuseStep 220759 = 331139) B331139
theorem B220779 : Blo 219811 220779 := bstep (se 1 (by rfl) ⟨165584, by rfl⟩ : syracuseStep 220779 = 331169) B331169
theorem B220791 : Blo 219811 220791 := bstep (se 1 (by rfl) ⟨165593, by rfl⟩ : syracuseStep 220791 = 331187) B331187
theorem B220811 : Blo 219811 220811 := bstep (se 1 (by rfl) ⟨165608, by rfl⟩ : syracuseStep 220811 = 331217) B331217
theorem B220823 : Blo 219811 220823 := bstep (se 1 (by rfl) ⟨165617, by rfl⟩ : syracuseStep 220823 = 331235) B331235
theorem B220843 : Blo 219811 220843 := bstep (se 1 (by rfl) ⟨165632, by rfl⟩ : syracuseStep 220843 = 331265) B331265
theorem B679603 : Blo 219811 679603 := bstep (se 1 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 679603 = 1019405) B1019405
theorem B220855 : Blo 219811 220855 := bstep (se 1 (by rfl) ⟨165641, by rfl⟩ : syracuseStep 220855 = 331283) B331283
theorem B220875 : Blo 219811 220875 := bstep (se 1 (by rfl) ⟨165656, by rfl⟩ : syracuseStep 220875 = 331313) B331313
theorem B220887 : Blo 219811 220887 := bstep (se 1 (by rfl) ⟨165665, by rfl⟩ : syracuseStep 220887 = 331331) B331331
theorem B220907 : Blo 219811 220907 := bstep (se 1 (by rfl) ⟨165680, by rfl⟩ : syracuseStep 220907 = 331361) B331361
theorem B220919 : Blo 219811 220919 := bstep (se 1 (by rfl) ⟨165689, by rfl⟩ : syracuseStep 220919 = 331379) B331379
theorem B220939 : Blo 219811 220939 := bstep (se 1 (by rfl) ⟨165704, by rfl⟩ : syracuseStep 220939 = 331409) B331409
theorem B220951 : Blo 219811 220951 := bstep (se 1 (by rfl) ⟨165713, by rfl⟩ : syracuseStep 220951 = 331427) B331427
theorem B220971 : Blo 219811 220971 := bstep (se 1 (by rfl) ⟨165728, by rfl⟩ : syracuseStep 220971 = 331457) B331457
theorem B220983 : Blo 219811 220983 := bstep (se 1 (by rfl) ⟨165737, by rfl⟩ : syracuseStep 220983 = 331475) B331475
theorem B417611 : Blo 219811 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B221003 : Blo 219811 221003 := bstep (se 1 (by rfl) ⟨165752, by rfl⟩ : syracuseStep 221003 = 331505) B331505
theorem B221015 : Blo 219811 221015 := bstep (se 1 (by rfl) ⟨165761, by rfl⟩ : syracuseStep 221015 = 331523) B331523
theorem B221035 : Blo 219811 221035 := bstep (se 1 (by rfl) ⟨165776, by rfl⟩ : syracuseStep 221035 = 331553) B331553
theorem B221047 : Blo 219811 221047 := bstep (se 1 (by rfl) ⟨165785, by rfl⟩ : syracuseStep 221047 = 331571) B331571
theorem B221067 : Blo 219811 221067 := bstep (se 1 (by rfl) ⟨165800, by rfl⟩ : syracuseStep 221067 = 331601) B331601
theorem B221079 : Blo 219811 221079 := bstep (se 1 (by rfl) ⟨165809, by rfl⟩ : syracuseStep 221079 = 331619) B331619
theorem B221099 : Blo 219811 221099 := bstep (se 1 (by rfl) ⟨165824, by rfl⟩ : syracuseStep 221099 = 331649) B331649
theorem B221111 : Blo 219811 221111 := bstep (se 1 (by rfl) ⟨165833, by rfl⟩ : syracuseStep 221111 = 331667) B331667
theorem B221131 : Blo 219811 221131 := bstep (se 1 (by rfl) ⟨165848, by rfl⟩ : syracuseStep 221131 = 331697) B331697
theorem B221143 : Blo 219811 221143 := bstep (se 1 (by rfl) ⟨165857, by rfl⟩ : syracuseStep 221143 = 331715) B331715
theorem B221163 : Blo 219811 221163 := bstep (se 1 (by rfl) ⟨165872, by rfl⟩ : syracuseStep 221163 = 331745) B331745
theorem B221175 : Blo 219811 221175 := bstep (se 1 (by rfl) ⟨165881, by rfl⟩ : syracuseStep 221175 = 331763) B331763
theorem B417793 : Blo 219811 417793 := bstep (se 2 (by rfl) ⟨156672, by rfl⟩ : syracuseStep 417793 = 313345) B313345
theorem B221195 : Blo 219811 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B221207 : Blo 219811 221207 := bstep (se 1 (by rfl) ⟨165905, by rfl⟩ : syracuseStep 221207 = 331811) B331811
theorem B221227 : Blo 219811 221227 := bstep (se 1 (by rfl) ⟨165920, by rfl⟩ : syracuseStep 221227 = 331841) B331841
theorem B745523 : Blo 219811 745523 := bstep (se 1 (by rfl) ⟨559142, by rfl⟩ : syracuseStep 745523 = 1118285) B1118285
theorem B221239 : Blo 219811 221239 := bstep (se 1 (by rfl) ⟨165929, by rfl⟩ : syracuseStep 221239 = 331859) B331859
theorem B221259 : Blo 219811 221259 := bstep (se 1 (by rfl) ⟨165944, by rfl⟩ : syracuseStep 221259 = 331889) B331889
theorem B221271 : Blo 219811 221271 := bstep (se 1 (by rfl) ⟨165953, by rfl⟩ : syracuseStep 221271 = 331907) B331907
theorem B221291 : Blo 219811 221291 := bstep (se 1 (by rfl) ⟨165968, by rfl⟩ : syracuseStep 221291 = 331937) B331937
theorem B221303 : Blo 219811 221303 := bstep (se 1 (by rfl) ⟨165977, by rfl⟩ : syracuseStep 221303 = 331955) B331955
theorem B221323 : Blo 219811 221323 := bstep (se 1 (by rfl) ⟨165992, by rfl⟩ : syracuseStep 221323 = 331985) B331985
theorem B221335 : Blo 219811 221335 := bstep (se 1 (by rfl) ⟨166001, by rfl⟩ : syracuseStep 221335 = 332003) B332003
theorem B221355 : Blo 219811 221355 := bstep (se 1 (by rfl) ⟨166016, by rfl⟩ : syracuseStep 221355 = 332033) B332033
theorem B221367 : Blo 219811 221367 := bstep (se 1 (by rfl) ⟨166025, by rfl⟩ : syracuseStep 221367 = 332051) B332051
theorem B221387 : Blo 219811 221387 := bstep (se 1 (by rfl) ⟨166040, by rfl⟩ : syracuseStep 221387 = 332081) B332081
theorem B221399 : Blo 219811 221399 := bstep (se 1 (by rfl) ⟨166049, by rfl⟩ : syracuseStep 221399 = 332099) B332099
theorem B712921 : Blo 219811 712921 := bstep (se 2 (by rfl) ⟨267345, by rfl⟩ : syracuseStep 712921 = 534691) B534691
theorem B221419 : Blo 219811 221419 := bstep (se 1 (by rfl) ⟨166064, by rfl⟩ : syracuseStep 221419 = 332129) B332129
theorem B221431 : Blo 219811 221431 := bstep (se 1 (by rfl) ⟨166073, by rfl⟩ : syracuseStep 221431 = 332147) B332147
theorem B221451 : Blo 219811 221451 := bstep (se 1 (by rfl) ⟨166088, by rfl⟩ : syracuseStep 221451 = 332177) B332177
theorem B221463 : Blo 219811 221463 := bstep (se 1 (by rfl) ⟨166097, by rfl⟩ : syracuseStep 221463 = 332195) B332195
theorem B286999 : Blo 219811 286999 := bstep (se 1 (by rfl) ⟨215249, by rfl⟩ : syracuseStep 286999 = 430499) B430499
theorem B221483 : Blo 219811 221483 := bstep (se 1 (by rfl) ⟨166112, by rfl⟩ : syracuseStep 221483 = 332225) B332225
theorem B221495 : Blo 219811 221495 := bstep (se 1 (by rfl) ⟨166121, by rfl⟩ : syracuseStep 221495 = 332243) B332243
theorem B745793 : Blo 219811 745793 := bstep (se 2 (by rfl) ⟨279672, by rfl⟩ : syracuseStep 745793 = 559345) B559345
theorem B221515 : Blo 219811 221515 := bstep (se 1 (by rfl) ⟨166136, by rfl⟩ : syracuseStep 221515 = 332273) B332273
theorem B418135 : Blo 219811 418135 := bstep (se 1 (by rfl) ⟨313601, by rfl⟩ : syracuseStep 418135 = 627203) B627203
theorem B221527 : Blo 219811 221527 := bstep (se 1 (by rfl) ⟨166145, by rfl⟩ : syracuseStep 221527 = 332291) B332291
theorem B844121 : Blo 219811 844121 := bstep (se 2 (by rfl) ⟨316545, by rfl⟩ : syracuseStep 844121 = 633091) B633091
theorem B221547 : Blo 219811 221547 := bstep (se 1 (by rfl) ⟨166160, by rfl⟩ : syracuseStep 221547 = 332321) B332321
theorem B221559 : Blo 219811 221559 := bstep (se 1 (by rfl) ⟨166169, by rfl⟩ : syracuseStep 221559 = 332339) B332339
theorem B221579 : Blo 219811 221579 := bstep (se 1 (by rfl) ⟨166184, by rfl⟩ : syracuseStep 221579 = 332369) B332369
theorem B221591 : Blo 219811 221591 := bstep (se 1 (by rfl) ⟨166193, by rfl⟩ : syracuseStep 221591 = 332387) B332387
theorem B221611 : Blo 219811 221611 := bstep (se 1 (by rfl) ⟨166208, by rfl⟩ : syracuseStep 221611 = 332417) B332417
theorem B221623 : Blo 219811 221623 := bstep (se 1 (by rfl) ⟨166217, by rfl⟩ : syracuseStep 221623 = 332435) B332435
theorem B942529 : Blo 219811 942529 := bstep (se 2 (by rfl) ⟨353448, by rfl⟩ : syracuseStep 942529 = 706897) B706897
theorem B221643 : Blo 219811 221643 := bstep (se 1 (by rfl) ⟨166232, by rfl⟩ : syracuseStep 221643 = 332465) B332465
theorem B221655 : Blo 219811 221655 := bstep (se 1 (by rfl) ⟨166241, by rfl⟩ : syracuseStep 221655 = 332483) B332483
theorem B221675 : Blo 219811 221675 := bstep (se 1 (by rfl) ⟨166256, by rfl⟩ : syracuseStep 221675 = 332513) B332513
theorem B221687 : Blo 219811 221687 := bstep (se 1 (by rfl) ⟨166265, by rfl⟩ : syracuseStep 221687 = 332531) B332531
theorem B221707 : Blo 219811 221707 := bstep (se 1 (by rfl) ⟨166280, by rfl⟩ : syracuseStep 221707 = 332561) B332561
theorem B221719 : Blo 219811 221719 := bstep (se 1 (by rfl) ⟨166289, by rfl⟩ : syracuseStep 221719 = 332579) B332579
theorem B221739 : Blo 219811 221739 := bstep (se 1 (by rfl) ⟨166304, by rfl⟩ : syracuseStep 221739 = 332609) B332609
theorem B418355 : Blo 219811 418355 := bstep (se 1 (by rfl) ⟨313766, by rfl⟩ : syracuseStep 418355 = 627533) B627533
theorem B221751 : Blo 219811 221751 := bstep (se 1 (by rfl) ⟨166313, by rfl⟩ : syracuseStep 221751 = 332627) B332627
theorem B221771 : Blo 219811 221771 := bstep (se 1 (by rfl) ⟨166328, by rfl⟩ : syracuseStep 221771 = 332657) B332657
theorem B221783 : Blo 219811 221783 := bstep (se 1 (by rfl) ⟨166337, by rfl⟩ : syracuseStep 221783 = 332675) B332675
theorem B221803 : Blo 219811 221803 := bstep (se 1 (by rfl) ⟨166352, by rfl⟩ : syracuseStep 221803 = 332705) B332705
theorem B221815 : Blo 219811 221815 := bstep (se 1 (by rfl) ⟨166361, by rfl⟩ : syracuseStep 221815 = 332723) B332723
theorem B221835 : Blo 219811 221835 := bstep (se 1 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 221835 = 332753) B332753
theorem B221847 : Blo 219811 221847 := bstep (se 1 (by rfl) ⟨166385, by rfl⟩ : syracuseStep 221847 = 332771) B332771
theorem B221867 : Blo 219811 221867 := bstep (se 1 (by rfl) ⟨166400, by rfl⟩ : syracuseStep 221867 = 332801) B332801
theorem B221879 : Blo 219811 221879 := bstep (se 1 (by rfl) ⟨166409, by rfl⟩ : syracuseStep 221879 = 332819) B332819
theorem B221899 : Blo 219811 221899 := bstep (se 1 (by rfl) ⟨166424, by rfl⟩ : syracuseStep 221899 = 332849) B332849
theorem B221911 : Blo 219811 221911 := bstep (se 1 (by rfl) ⟨166433, by rfl⟩ : syracuseStep 221911 = 332867) B332867
theorem B221931 : Blo 219811 221931 := bstep (se 1 (by rfl) ⟨166448, by rfl⟩ : syracuseStep 221931 = 332897) B332897
theorem B221943 : Blo 219811 221943 := bstep (se 1 (by rfl) ⟨166457, by rfl⟩ : syracuseStep 221943 = 332915) B332915
theorem B221963 : Blo 219811 221963 := bstep (se 1 (by rfl) ⟨166472, by rfl⟩ : syracuseStep 221963 = 332945) B332945
theorem B418583 : Blo 219811 418583 := bstep (se 1 (by rfl) ⟨313937, by rfl⟩ : syracuseStep 418583 = 627875) B627875
theorem B221975 : Blo 219811 221975 := bstep (se 1 (by rfl) ⟨166481, by rfl⟩ : syracuseStep 221975 = 332963) B332963
theorem B221995 : Blo 219811 221995 := bstep (se 1 (by rfl) ⟨166496, by rfl⟩ : syracuseStep 221995 = 332993) B332993
theorem B222007 : Blo 219811 222007 := bstep (se 1 (by rfl) ⟨166505, by rfl⟩ : syracuseStep 222007 = 333011) B333011
theorem B222027 : Blo 219811 222027 := bstep (se 1 (by rfl) ⟨166520, by rfl⟩ : syracuseStep 222027 = 333041) B333041
theorem B222039 : Blo 219811 222039 := bstep (se 1 (by rfl) ⟨166529, by rfl⟩ : syracuseStep 222039 = 333059) B333059
theorem B746333 : Blo 219811 746333 := bstep (se 3 (by rfl) ⟨139937, by rfl⟩ : syracuseStep 746333 = 279875) B279875
theorem B222059 : Blo 219811 222059 := bstep (se 1 (by rfl) ⟨166544, by rfl⟩ : syracuseStep 222059 = 333089) B333089
theorem B2417525 : Blo 219811 2417525 := bstep (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) B226643
theorem B222071 : Blo 219811 222071 := bstep (se 1 (by rfl) ⟨166553, by rfl⟩ : syracuseStep 222071 = 333107) B333107
theorem B222091 : Blo 219811 222091 := bstep (se 1 (by rfl) ⟨166568, by rfl⟩ : syracuseStep 222091 = 333137) B333137
theorem B222103 : Blo 219811 222103 := bstep (se 1 (by rfl) ⟨166577, by rfl⟩ : syracuseStep 222103 = 333155) B333155
theorem B222123 : Blo 219811 222123 := bstep (se 1 (by rfl) ⟨166592, by rfl⟩ : syracuseStep 222123 = 333185) B333185
theorem B222135 : Blo 219811 222135 := bstep (se 1 (by rfl) ⟨166601, by rfl⟩ : syracuseStep 222135 = 333203) B333203
theorem B222155 : Blo 219811 222155 := bstep (se 1 (by rfl) ⟨166616, by rfl⟩ : syracuseStep 222155 = 333233) B333233
theorem B222167 : Blo 219811 222167 := bstep (se 1 (by rfl) ⟨166625, by rfl⟩ : syracuseStep 222167 = 333251) B333251
theorem B222187 : Blo 219811 222187 := bstep (se 1 (by rfl) ⟨166640, by rfl⟩ : syracuseStep 222187 = 333281) B333281
theorem B222199 : Blo 219811 222199 := bstep (se 1 (by rfl) ⟨166649, by rfl⟩ : syracuseStep 222199 = 333299) B333299
theorem B222219 : Blo 219811 222219 := bstep (se 1 (by rfl) ⟨166664, by rfl⟩ : syracuseStep 222219 = 333329) B333329
theorem B222231 : Blo 219811 222231 := bstep (se 1 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 222231 = 333347) B333347
theorem B418841 : Blo 219811 418841 := bstep (se 2 (by rfl) ⟨157065, by rfl⟩ : syracuseStep 418841 = 314131) B314131
theorem B222251 : Blo 219811 222251 := bstep (se 1 (by rfl) ⟨166688, by rfl⟩ : syracuseStep 222251 = 333377) B333377
theorem B1270829 : Blo 219811 1270829 := bstep (se 3 (by rfl) ⟨238280, by rfl⟩ : syracuseStep 1270829 = 476561) B476561
theorem B222263 : Blo 219811 222263 := bstep (se 1 (by rfl) ⟨166697, by rfl⟩ : syracuseStep 222263 = 333395) B333395
theorem B222283 : Blo 219811 222283 := bstep (se 1 (by rfl) ⟨166712, by rfl⟩ : syracuseStep 222283 = 333425) B333425
theorem B222295 : Blo 219811 222295 := bstep (se 1 (by rfl) ⟨166721, by rfl⟩ : syracuseStep 222295 = 333443) B333443
theorem B222315 : Blo 219811 222315 := bstep (se 1 (by rfl) ⟨166736, by rfl⟩ : syracuseStep 222315 = 333473) B333473
theorem B222327 : Blo 219811 222327 := bstep (se 1 (by rfl) ⟨166745, by rfl⟩ : syracuseStep 222327 = 333491) B333491
theorem B222347 : Blo 219811 222347 := bstep (se 1 (by rfl) ⟨166760, by rfl⟩ : syracuseStep 222347 = 333521) B333521
theorem B222359 : Blo 219811 222359 := bstep (se 1 (by rfl) ⟨166769, by rfl⟩ : syracuseStep 222359 = 333539) B333539
theorem B222379 : Blo 219811 222379 := bstep (se 1 (by rfl) ⟨166784, by rfl⟩ : syracuseStep 222379 = 333569) B333569
theorem B222391 : Blo 219811 222391 := bstep (se 1 (by rfl) ⟨166793, by rfl⟩ : syracuseStep 222391 = 333587) B333587
theorem B910529 : Blo 219811 910529 := bstep (se 2 (by rfl) ⟨341448, by rfl⟩ : syracuseStep 910529 = 682897) B682897
theorem B222411 : Blo 219811 222411 := bstep (se 1 (by rfl) ⟨166808, by rfl⟩ : syracuseStep 222411 = 333617) B333617
theorem B222423 : Blo 219811 222423 := bstep (se 1 (by rfl) ⟨166817, by rfl⟩ : syracuseStep 222423 = 333635) B333635
theorem B222443 : Blo 219811 222443 := bstep (se 1 (by rfl) ⟨166832, by rfl⟩ : syracuseStep 222443 = 333665) B333665
theorem B222455 : Blo 219811 222455 := bstep (se 1 (by rfl) ⟨166841, by rfl⟩ : syracuseStep 222455 = 333683) B333683
theorem B222475 : Blo 219811 222475 := bstep (se 1 (by rfl) ⟨166856, by rfl⟩ : syracuseStep 222475 = 333713) B333713
theorem B222487 : Blo 219811 222487 := bstep (se 1 (by rfl) ⟨166865, by rfl⟩ : syracuseStep 222487 = 333731) B333731
theorem B222507 : Blo 219811 222507 := bstep (se 1 (by rfl) ⟨166880, by rfl⟩ : syracuseStep 222507 = 333761) B333761
theorem B222519 : Blo 219811 222519 := bstep (se 1 (by rfl) ⟨166889, by rfl⟩ : syracuseStep 222519 = 333779) B333779
theorem B222539 : Blo 219811 222539 := bstep (se 1 (by rfl) ⟨166904, by rfl⟩ : syracuseStep 222539 = 333809) B333809
theorem B222551 : Blo 219811 222551 := bstep (se 1 (by rfl) ⟨166913, by rfl⟩ : syracuseStep 222551 = 333827) B333827
theorem B2024797 : Blo 219811 2024797 := bstep (se 3 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 2024797 = 759299) B759299
theorem B222571 : Blo 219811 222571 := bstep (se 1 (by rfl) ⟨166928, by rfl⟩ : syracuseStep 222571 = 333857) B333857
theorem B222583 : Blo 219811 222583 := bstep (se 1 (by rfl) ⟨166937, by rfl⟩ : syracuseStep 222583 = 333875) B333875
theorem B222603 : Blo 219811 222603 := bstep (se 1 (by rfl) ⟨166952, by rfl⟩ : syracuseStep 222603 = 333905) B333905
theorem B222615 : Blo 219811 222615 := bstep (se 1 (by rfl) ⟨166961, by rfl⟩ : syracuseStep 222615 = 333923) B333923
theorem B222635 : Blo 219811 222635 := bstep (se 1 (by rfl) ⟨166976, by rfl⟩ : syracuseStep 222635 = 333953) B333953
theorem B419251 : Blo 219811 419251 := bstep (se 1 (by rfl) ⟨314438, by rfl⟩ : syracuseStep 419251 = 628877) B628877
theorem B222647 : Blo 219811 222647 := bstep (se 1 (by rfl) ⟨166985, by rfl⟩ : syracuseStep 222647 = 333971) B333971
theorem B222667 : Blo 219811 222667 := bstep (se 1 (by rfl) ⟨167000, by rfl⟩ : syracuseStep 222667 = 334001) B334001
theorem B222679 : Blo 219811 222679 := bstep (se 1 (by rfl) ⟨167009, by rfl⟩ : syracuseStep 222679 = 334019) B334019
theorem B222699 : Blo 219811 222699 := bstep (se 1 (by rfl) ⟨167024, by rfl⟩ : syracuseStep 222699 = 334049) B334049
theorem B222711 : Blo 219811 222711 := bstep (se 1 (by rfl) ⟨167033, by rfl⟩ : syracuseStep 222711 = 334067) B334067
theorem B222731 : Blo 219811 222731 := bstep (se 1 (by rfl) ⟨167048, by rfl⟩ : syracuseStep 222731 = 334097) B334097
theorem B2287121 : Blo 219811 2287121 := bstep (se 2 (by rfl) ⟨857670, by rfl⟩ : syracuseStep 2287121 = 1715341) B1715341
theorem B222743 : Blo 219811 222743 := bstep (se 1 (by rfl) ⟨167057, by rfl⟩ : syracuseStep 222743 = 334115) B334115
theorem B222763 : Blo 219811 222763 := bstep (se 1 (by rfl) ⟨167072, by rfl⟩ : syracuseStep 222763 = 334145) B334145
theorem B222775 : Blo 219811 222775 := bstep (se 1 (by rfl) ⟨167081, by rfl⟩ : syracuseStep 222775 = 334163) B334163
theorem B222795 : Blo 219811 222795 := bstep (se 1 (by rfl) ⟨167096, by rfl⟩ : syracuseStep 222795 = 334193) B334193
theorem B353879 : Blo 219811 353879 := bstep (se 1 (by rfl) ⟨265409, by rfl⟩ : syracuseStep 353879 = 530819) B530819
theorem B222807 : Blo 219811 222807 := bstep (se 1 (by rfl) ⟨167105, by rfl⟩ : syracuseStep 222807 = 334211) B334211
theorem B222827 : Blo 219811 222827 := bstep (se 1 (by rfl) ⟨167120, by rfl⟩ : syracuseStep 222827 = 334241) B334241
theorem B222839 : Blo 219811 222839 := bstep (se 1 (by rfl) ⟨167129, by rfl⟩ : syracuseStep 222839 = 334259) B334259
theorem B222859 : Blo 219811 222859 := bstep (se 1 (by rfl) ⟨167144, by rfl⟩ : syracuseStep 222859 = 334289) B334289
theorem B222871 : Blo 219811 222871 := bstep (se 1 (by rfl) ⟨167153, by rfl⟩ : syracuseStep 222871 = 334307) B334307
theorem B222891 : Blo 219811 222891 := bstep (se 1 (by rfl) ⟨167168, by rfl⟩ : syracuseStep 222891 = 334337) B334337
theorem B812717 : Blo 219811 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B222903 : Blo 219811 222903 := bstep (se 1 (by rfl) ⟨167177, by rfl⟩ : syracuseStep 222903 = 334355) B334355
theorem B222923 : Blo 219811 222923 := bstep (se 1 (by rfl) ⟨167192, by rfl⟩ : syracuseStep 222923 = 334385) B334385
theorem B222935 : Blo 219811 222935 := bstep (se 1 (by rfl) ⟨167201, by rfl⟩ : syracuseStep 222935 = 334403) B334403
theorem B222955 : Blo 219811 222955 := bstep (se 1 (by rfl) ⟨167216, by rfl⟩ : syracuseStep 222955 = 334433) B334433
theorem B222967 : Blo 219811 222967 := bstep (se 1 (by rfl) ⟨167225, by rfl⟩ : syracuseStep 222967 = 334451) B334451
theorem B222987 : Blo 219811 222987 := bstep (se 1 (by rfl) ⟨167240, by rfl⟩ : syracuseStep 222987 = 334481) B334481
theorem B222999 : Blo 219811 222999 := bstep (se 1 (by rfl) ⟨167249, by rfl⟩ : syracuseStep 222999 = 334499) B334499
theorem B223019 : Blo 219811 223019 := bstep (se 1 (by rfl) ⟨167264, by rfl⟩ : syracuseStep 223019 = 334529) B334529
theorem B223031 : Blo 219811 223031 := bstep (se 1 (by rfl) ⟨167273, by rfl⟩ : syracuseStep 223031 = 334547) B334547
theorem B223051 : Blo 219811 223051 := bstep (se 1 (by rfl) ⟨167288, by rfl⟩ : syracuseStep 223051 = 334577) B334577
theorem B223063 : Blo 219811 223063 := bstep (se 1 (by rfl) ⟨167297, by rfl⟩ : syracuseStep 223063 = 334595) B334595
theorem B223083 : Blo 219811 223083 := bstep (se 1 (by rfl) ⟨167312, by rfl⟩ : syracuseStep 223083 = 334625) B334625
theorem B223095 : Blo 219811 223095 := bstep (se 1 (by rfl) ⟨167321, by rfl⟩ : syracuseStep 223095 = 334643) B334643
theorem B223115 : Blo 219811 223115 := bstep (se 1 (by rfl) ⟨167336, by rfl⟩ : syracuseStep 223115 = 334673) B334673
theorem B223127 : Blo 219811 223127 := bstep (se 1 (by rfl) ⟨167345, by rfl⟩ : syracuseStep 223127 = 334691) B334691
theorem B419737 : Blo 219811 419737 := bstep (se 2 (by rfl) ⟨157401, by rfl⟩ : syracuseStep 419737 = 314803) B314803
theorem B223147 : Blo 219811 223147 := bstep (se 1 (by rfl) ⟨167360, by rfl⟩ : syracuseStep 223147 = 334721) B334721
theorem B845747 : Blo 219811 845747 := bstep (se 1 (by rfl) ⟨634310, by rfl⟩ : syracuseStep 845747 = 1268621) B1268621
theorem B223159 : Blo 219811 223159 := bstep (se 1 (by rfl) ⟨167369, by rfl⟩ : syracuseStep 223159 = 334739) B334739
theorem B845761 : Blo 219811 845761 := bstep (se 2 (by rfl) ⟨317160, by rfl⟩ : syracuseStep 845761 = 634321) B634321
theorem B714689 : Blo 219811 714689 := bstep (se 2 (by rfl) ⟨268008, by rfl⟩ : syracuseStep 714689 = 536017) B536017
theorem B747467 : Blo 219811 747467 := bstep (se 1 (by rfl) ⟨560600, by rfl⟩ : syracuseStep 747467 = 1121201) B1121201
theorem B223179 : Blo 219811 223179 := bstep (se 1 (by rfl) ⟨167384, by rfl⟩ : syracuseStep 223179 = 334769) B334769
theorem B223191 : Blo 219811 223191 := bstep (se 1 (by rfl) ⟨167393, by rfl⟩ : syracuseStep 223191 = 334787) B334787
theorem B223211 : Blo 219811 223211 := bstep (se 1 (by rfl) ⟨167408, by rfl⟩ : syracuseStep 223211 = 334817) B334817
theorem B223223 : Blo 219811 223223 := bstep (se 1 (by rfl) ⟨167417, by rfl⟩ : syracuseStep 223223 = 334835) B334835
theorem B223243 : Blo 219811 223243 := bstep (se 1 (by rfl) ⟨167432, by rfl⟩ : syracuseStep 223243 = 334865) B334865
theorem B223255 : Blo 219811 223255 := bstep (se 1 (by rfl) ⟨167441, by rfl⟩ : syracuseStep 223255 = 334883) B334883
theorem B223275 : Blo 219811 223275 := bstep (se 1 (by rfl) ⟨167456, by rfl⟩ : syracuseStep 223275 = 334913) B334913
theorem B223287 : Blo 219811 223287 := bstep (se 1 (by rfl) ⟨167465, by rfl⟩ : syracuseStep 223287 = 334931) B334931
theorem B223307 : Blo 219811 223307 := bstep (se 1 (by rfl) ⟨167480, by rfl⟩ : syracuseStep 223307 = 334961) B334961
theorem B223319 : Blo 219811 223319 := bstep (se 1 (by rfl) ⟨167489, by rfl⟩ : syracuseStep 223319 = 334979) B334979
theorem B223339 : Blo 219811 223339 := bstep (se 1 (by rfl) ⟨167504, by rfl⟩ : syracuseStep 223339 = 335009) B335009
theorem B223351 : Blo 219811 223351 := bstep (se 1 (by rfl) ⟨167513, by rfl⟩ : syracuseStep 223351 = 335027) B335027
theorem B223371 : Blo 219811 223371 := bstep (se 1 (by rfl) ⟨167528, by rfl⟩ : syracuseStep 223371 = 335057) B335057
theorem B223383 : Blo 219811 223383 := bstep (se 1 (by rfl) ⟨167537, by rfl⟩ : syracuseStep 223383 = 335075) B335075
theorem B223403 : Blo 219811 223403 := bstep (se 1 (by rfl) ⟨167552, by rfl⟩ : syracuseStep 223403 = 335105) B335105
theorem B223415 : Blo 219811 223415 := bstep (se 1 (by rfl) ⟨167561, by rfl⟩ : syracuseStep 223415 = 335123) B335123
theorem B223435 : Blo 219811 223435 := bstep (se 1 (by rfl) ⟨167576, by rfl⟩ : syracuseStep 223435 = 335153) B335153
theorem B223447 : Blo 219811 223447 := bstep (se 1 (by rfl) ⟨167585, by rfl⟩ : syracuseStep 223447 = 335171) B335171
theorem B747737 : Blo 219811 747737 := bstep (se 2 (by rfl) ⟨280401, by rfl⟩ : syracuseStep 747737 = 560803) B560803
theorem B223467 : Blo 219811 223467 := bstep (se 1 (by rfl) ⟨167600, by rfl⟩ : syracuseStep 223467 = 335201) B335201
theorem B223479 : Blo 219811 223479 := bstep (se 1 (by rfl) ⟨167609, by rfl⟩ : syracuseStep 223479 = 335219) B335219
theorem B223499 : Blo 219811 223499 := bstep (se 1 (by rfl) ⟨167624, by rfl⟩ : syracuseStep 223499 = 335249) B335249
theorem B223511 : Blo 219811 223511 := bstep (se 1 (by rfl) ⟨167633, by rfl⟩ : syracuseStep 223511 = 335267) B335267
theorem B1698083 : Blo 219811 1698083 := bstep (se 1 (by rfl) ⟨1273562, by rfl⟩ : syracuseStep 1698083 = 2547125) B2547125
theorem B223531 : Blo 219811 223531 := bstep (se 1 (by rfl) ⟨167648, by rfl⟩ : syracuseStep 223531 = 335297) B335297
theorem B223543 : Blo 219811 223543 := bstep (se 1 (by rfl) ⟨167657, by rfl⟩ : syracuseStep 223543 = 335315) B335315
theorem B223563 : Blo 219811 223563 := bstep (se 1 (by rfl) ⟨167672, by rfl⟩ : syracuseStep 223563 = 335345) B335345
theorem B223575 : Blo 219811 223575 := bstep (se 1 (by rfl) ⟨167681, by rfl⟩ : syracuseStep 223575 = 335363) B335363
theorem B223595 : Blo 219811 223595 := bstep (se 1 (by rfl) ⟨167696, by rfl⟩ : syracuseStep 223595 = 335393) B335393
theorem B223607 : Blo 219811 223607 := bstep (se 1 (by rfl) ⟨167705, by rfl⟩ : syracuseStep 223607 = 335411) B335411
theorem B223627 : Blo 219811 223627 := bstep (se 1 (by rfl) ⟨167720, by rfl⟩ : syracuseStep 223627 = 335441) B335441
theorem B223639 : Blo 219811 223639 := bstep (se 1 (by rfl) ⟨167729, by rfl⟩ : syracuseStep 223639 = 335459) B335459
theorem B223659 : Blo 219811 223659 := bstep (se 1 (by rfl) ⟨167744, by rfl⟩ : syracuseStep 223659 = 335489) B335489
theorem B223671 : Blo 219811 223671 := bstep (se 1 (by rfl) ⟨167753, by rfl⟩ : syracuseStep 223671 = 335507) B335507
theorem B420299 : Blo 219811 420299 := bstep (se 1 (by rfl) ⟨315224, by rfl⟩ : syracuseStep 420299 = 630449) B630449
theorem B223691 : Blo 219811 223691 := bstep (se 1 (by rfl) ⟨167768, by rfl⟩ : syracuseStep 223691 = 335537) B335537
theorem B223703 : Blo 219811 223703 := bstep (se 1 (by rfl) ⟨167777, by rfl⟩ : syracuseStep 223703 = 335555) B335555
theorem B223723 : Blo 219811 223723 := bstep (se 1 (by rfl) ⟨167792, by rfl⟩ : syracuseStep 223723 = 335585) B335585
theorem B223735 : Blo 219811 223735 := bstep (se 1 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 223735 = 335603) B335603
theorem B223755 : Blo 219811 223755 := bstep (se 1 (by rfl) ⟨167816, by rfl⟩ : syracuseStep 223755 = 335633) B335633
theorem B223767 : Blo 219811 223767 := bstep (se 1 (by rfl) ⟨167825, by rfl⟩ : syracuseStep 223767 = 335651) B335651
theorem B223787 : Blo 219811 223787 := bstep (se 1 (by rfl) ⟨167840, by rfl⟩ : syracuseStep 223787 = 335681) B335681
theorem B223799 : Blo 219811 223799 := bstep (se 1 (by rfl) ⟨167849, by rfl⟩ : syracuseStep 223799 = 335699) B335699
theorem B420481 : Blo 219811 420481 := bstep (se 2 (by rfl) ⟨157680, by rfl⟩ : syracuseStep 420481 = 315361) B315361
theorem B354955 : Blo 219811 354955 := bstep (se 1 (by rfl) ⟨266216, by rfl⟩ : syracuseStep 354955 = 532433) B532433
theorem B1010369 : Blo 219811 1010369 := bstep (se 2 (by rfl) ⟨378888, by rfl⟩ : syracuseStep 1010369 = 757777) B757777
theorem B748439 : Blo 219811 748439 := bstep (se 1 (by rfl) ⟨561329, by rfl⟩ : syracuseStep 748439 = 1122659) B1122659
theorem B715969 : Blo 219811 715969 := bstep (se 2 (by rfl) ⟨268488, by rfl⟩ : syracuseStep 715969 = 536977) B536977
theorem B453899 : Blo 219811 453899 := bstep (se 1 (by rfl) ⟨340424, by rfl⟩ : syracuseStep 453899 = 680849) B680849
theorem B1240337 : Blo 219811 1240337 := bstep (se 2 (by rfl) ⟨465126, by rfl⟩ : syracuseStep 1240337 = 930253) B930253
theorem B421195 : Blo 219811 421195 := bstep (se 1 (by rfl) ⟨315896, by rfl⟩ : syracuseStep 421195 = 631793) B631793
theorem B355673 : Blo 219811 355673 := bstep (se 2 (by rfl) ⟨133377, by rfl⟩ : syracuseStep 355673 = 266755) B266755
theorem B814429 : Blo 219811 814429 := bstep (se 3 (by rfl) ⟨152705, by rfl⟩ : syracuseStep 814429 = 305411) B305411
theorem B421271 : Blo 219811 421271 := bstep (se 1 (by rfl) ⟨315953, by rfl⟩ : syracuseStep 421271 = 631907) B631907
theorem B748979 : Blo 219811 748979 := bstep (se 1 (by rfl) ⟨561734, by rfl⟩ : syracuseStep 748979 = 1123469) B1123469
theorem B847325 : Blo 219811 847325 := bstep (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) B317747
theorem B3796631 : Blo 219811 3796631 := bstep (se 1 (by rfl) ⟨2847473, by rfl⟩ : syracuseStep 3796631 = 5694947) B5694947
theorem B749249 : Blo 219811 749249 := bstep (se 2 (by rfl) ⟨280968, by rfl⟩ : syracuseStep 749249 = 561937) B561937
theorem B13758149 : Blo 219811 13758149 := bstep (se 4 (by rfl) ⟨1289826, by rfl⟩ : syracuseStep 13758149 = 2579653) B2579653
theorem B847691 : Blo 219811 847691 := bstep (se 1 (by rfl) ⟨635768, by rfl⟩ : syracuseStep 847691 = 1271537) B1271537
theorem B356185 : Blo 219811 356185 := bstep (se 2 (by rfl) ⟨133569, by rfl⟩ : syracuseStep 356185 = 267139) B267139
theorem B847705 : Blo 219811 847705 := bstep (se 2 (by rfl) ⟨317889, by rfl⟩ : syracuseStep 847705 = 635779) B635779
theorem B1896371 : Blo 219811 1896371 := bstep (se 1 (by rfl) ⟨1422278, by rfl⟩ : syracuseStep 1896371 = 2844557) B2844557
theorem B421939 : Blo 219811 421939 := bstep (se 1 (by rfl) ⟨316454, by rfl⟩ : syracuseStep 421939 = 632909) B632909
theorem B749789 : Blo 219811 749789 := bstep (se 3 (by rfl) ⟨140585, by rfl⟩ : syracuseStep 749789 = 281171) B281171
theorem B422167 : Blo 219811 422167 := bstep (se 1 (by rfl) ⟨316625, by rfl⟩ : syracuseStep 422167 = 633251) B633251
theorem B422273 : Blo 219811 422273 := bstep (se 2 (by rfl) ⟨158352, by rfl⟩ : syracuseStep 422273 = 316705) B316705
theorem B422425 : Blo 219811 422425 := bstep (se 2 (by rfl) ⟨158409, by rfl⟩ : syracuseStep 422425 = 316819) B316819
theorem B848663 : Blo 219811 848663 := bstep (se 1 (by rfl) ⟨636497, by rfl⟩ : syracuseStep 848663 = 1272995) B1272995
theorem B750923 : Blo 219811 750923 := bstep (se 1 (by rfl) ⟨563192, by rfl⟩ : syracuseStep 750923 = 1126385) B1126385
theorem B751193 : Blo 219811 751193 := bstep (se 2 (by rfl) ⟨281697, by rfl⟩ : syracuseStep 751193 = 563395) B563395
theorem B226999 : Blo 219811 226999 := bstep (se 1 (by rfl) ⟨170249, by rfl⟩ : syracuseStep 226999 = 340499) B340499
theorem B423731 : Blo 219811 423731 := bstep (se 1 (by rfl) ⟨317798, by rfl⟩ : syracuseStep 423731 = 635597) B635597
theorem B423883 : Blo 219811 423883 := bstep (se 1 (by rfl) ⟨317912, by rfl⟩ : syracuseStep 423883 = 635825) B635825
theorem B1341515 : Blo 219811 1341515 := bstep (se 1 (by rfl) ⟨1006136, by rfl⟩ : syracuseStep 1341515 = 2012273) B2012273
theorem B751895 : Blo 219811 751895 := bstep (se 1 (by rfl) ⟨563921, by rfl⟩ : syracuseStep 751895 = 1127843) B1127843
theorem B424217 : Blo 219811 424217 := bstep (se 2 (by rfl) ⟨159081, by rfl⟩ : syracuseStep 424217 = 318163) B318163
theorem B2128193 : Blo 219811 2128193 := bstep (se 2 (by rfl) ⟨798072, by rfl⟩ : syracuseStep 2128193 = 1596145) B1596145
theorem B948611 : Blo 219811 948611 := bstep (se 1 (by rfl) ⟨711458, by rfl⟩ : syracuseStep 948611 = 1422917) B1422917
theorem B2259377 : Blo 219811 2259377 := bstep (se 2 (by rfl) ⟨847266, by rfl⟩ : syracuseStep 2259377 = 1694533) B1694533
theorem B2062883 : Blo 219811 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B457367 : Blo 219811 457367 := bstep (se 1 (by rfl) ⟨343025, by rfl⟩ : syracuseStep 457367 = 686051) B686051
theorem B752435 : Blo 219811 752435 := bstep (se 1 (by rfl) ⟨564326, by rfl⟩ : syracuseStep 752435 = 1128653) B1128653
theorem B424855 : Blo 219811 424855 := bstep (se 1 (by rfl) ⟨318641, by rfl⟩ : syracuseStep 424855 = 637283) B637283
theorem B1080337 : Blo 219811 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B916525 : Blo 219811 916525 := bstep (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) B343697
theorem B752705 : Blo 219811 752705 := bstep (se 2 (by rfl) ⟨282264, by rfl⟩ : syracuseStep 752705 = 564529) B564529
theorem B851393 : Blo 219811 851393 := bstep (se 2 (by rfl) ⟨319272, by rfl⟩ : syracuseStep 851393 = 638545) B638545
theorem B1343051 : Blo 219811 1343051 := bstep (se 1 (by rfl) ⟨1007288, by rfl⟩ : syracuseStep 1343051 = 2014577) B2014577
theorem B753245 : Blo 219811 753245 := bstep (se 3 (by rfl) ⟨141233, by rfl⟩ : syracuseStep 753245 = 282467) B282467
theorem B425729 : Blo 219811 425729 := bstep (se 2 (by rfl) ⟨159648, by rfl⟩ : syracuseStep 425729 = 319297) B319297
theorem B360215 : Blo 219811 360215 := bstep (se 1 (by rfl) ⟨270161, by rfl⟩ : syracuseStep 360215 = 540323) B540323
theorem B556865 : Blo 219811 556865 := bstep (se 2 (by rfl) ⟨208824, by rfl⟩ : syracuseStep 556865 = 417649) B417649
theorem B1114073 : Blo 219811 1114073 := bstep (se 2 (by rfl) ⟨417777, by rfl⟩ : syracuseStep 1114073 = 835555) B835555
theorem B950237 : Blo 219811 950237 := bstep (se 3 (by rfl) ⟨178169, by rfl⟩ : syracuseStep 950237 = 356339) B356339
theorem B557057 : Blo 219811 557057 := bstep (se 2 (by rfl) ⟨208896, by rfl⟩ : syracuseStep 557057 = 417793) B417793
theorem B1900745 : Blo 219811 1900745 := bstep (se 2 (by rfl) ⟨712779, by rfl⟩ : syracuseStep 1900745 = 1425559) B1425559
theorem B950561 : Blo 219811 950561 := bstep (se 2 (by rfl) ⟨356460, by rfl⟩ : syracuseStep 950561 = 712921) B712921
theorem B754055 : Blo 219811 754055 := bstep (se 1 (by rfl) ⟨565541, by rfl⟩ : syracuseStep 754055 = 1131083) B1131083
theorem B557513 : Blo 219811 557513 := bstep (se 2 (by rfl) ⟨209067, by rfl⟩ : syracuseStep 557513 = 418135) B418135
theorem B2130533 : Blo 219811 2130533 := bstep (se 4 (by rfl) ⟨199737, by rfl⟩ : syracuseStep 2130533 = 399475) B399475
theorem B754433 : Blo 219811 754433 := bstep (se 2 (by rfl) ⟨282912, by rfl⟩ : syracuseStep 754433 = 565825) B565825
theorem B1114913 : Blo 219811 1114913 := bstep (se 2 (by rfl) ⟨418092, by rfl⟩ : syracuseStep 1114913 = 836185) B836185
theorem B557867 : Blo 219811 557867 := bstep (se 1 (by rfl) ⟨418400, by rfl⟩ : syracuseStep 557867 = 836801) B836801
theorem B361417 : Blo 219811 361417 := bstep (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) B271063
theorem B1672325 : Blo 219811 1672325 := bstep (se 4 (by rfl) ⟨156780, by rfl⟩ : syracuseStep 1672325 = 313561) B313561
theorem B755243 : Blo 219811 755243 := bstep (se 1 (by rfl) ⟨566432, by rfl⟩ : syracuseStep 755243 = 1132865) B1132865
theorem B558859 : Blo 219811 558859 := bstep (se 1 (by rfl) ⟨419144, by rfl⟩ : syracuseStep 558859 = 838289) B838289
theorem B559001 : Blo 219811 559001 := bstep (se 2 (by rfl) ⟨209625, by rfl⟩ : syracuseStep 559001 = 419251) B419251
theorem B2131915 : Blo 219811 2131915 := bstep (se 1 (by rfl) ⟨1598936, by rfl⟩ : syracuseStep 2131915 = 3197873) B3197873
theorem B329735 : Blo 219811 329735 := bstep (se 1 (by rfl) ⟨247301, by rfl⟩ : syracuseStep 329735 = 494603) B494603
theorem B329771 : Blo 219811 329771 := bstep (se 1 (by rfl) ⟨247328, by rfl⟩ : syracuseStep 329771 = 494657) B494657
theorem B559163 : Blo 219811 559163 := bstep (se 1 (by rfl) ⟨419372, by rfl⟩ : syracuseStep 559163 = 838745) B838745
theorem B329801 : Blo 219811 329801 := bstep (se 2 (by rfl) ⟨123675, by rfl⟩ : syracuseStep 329801 = 247351) B247351
theorem B329915 : Blo 219811 329915 := bstep (se 1 (by rfl) ⟨247436, by rfl⟩ : syracuseStep 329915 = 494873) B494873
theorem B329975 : Blo 219811 329975 := bstep (se 1 (by rfl) ⟨247481, by rfl⟩ : syracuseStep 329975 = 494963) B494963
theorem B329999 : Blo 219811 329999 := bstep (se 1 (by rfl) ⟨247499, by rfl⟩ : syracuseStep 329999 = 494999) B494999
theorem B5507345 : Blo 219811 5507345 := bstep (se 2 (by rfl) ⟨2065254, by rfl⟩ : syracuseStep 5507345 = 4130509) B4130509
theorem B330041 : Blo 219811 330041 := bstep (se 2 (by rfl) ⟨123765, by rfl⟩ : syracuseStep 330041 = 247531) B247531
theorem B5114177 : Blo 219811 5114177 := bstep (se 2 (by rfl) ⟨1917816, by rfl⟩ : syracuseStep 5114177 = 3835633) B3835633
theorem B330119 : Blo 219811 330119 := bstep (se 1 (by rfl) ⟨247589, by rfl⟩ : syracuseStep 330119 = 495179) B495179
theorem B559507 : Blo 219811 559507 := bstep (se 1 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 559507 = 839261) B839261
theorem B330155 : Blo 219811 330155 := bstep (se 1 (by rfl) ⟨247616, by rfl⟩ : syracuseStep 330155 = 495233) B495233
theorem B330185 : Blo 219811 330185 := bstep (se 2 (by rfl) ⟨123819, by rfl⟩ : syracuseStep 330185 = 247639) B247639
theorem B559649 : Blo 219811 559649 := bstep (se 2 (by rfl) ⟨209868, by rfl⟩ : syracuseStep 559649 = 419737) B419737
theorem B330299 : Blo 219811 330299 := bstep (se 1 (by rfl) ⟨247724, by rfl⟩ : syracuseStep 330299 = 495449) B495449
theorem B2722405 : Blo 219811 2722405 := bstep (se 4 (by rfl) ⟨255225, by rfl⟩ : syracuseStep 2722405 = 510451) B510451
theorem B330359 : Blo 219811 330359 := bstep (se 1 (by rfl) ⟨247769, by rfl⟩ : syracuseStep 330359 = 495539) B495539
theorem B330383 : Blo 219811 330383 := bstep (se 1 (by rfl) ⟨247787, by rfl⟩ : syracuseStep 330383 = 495575) B495575
theorem B264875 : Blo 219811 264875 := bstep (se 1 (by rfl) ⟨198656, by rfl⟩ : syracuseStep 264875 = 397313) B397313
theorem B330425 : Blo 219811 330425 := bstep (se 2 (by rfl) ⟨123909, by rfl⟩ : syracuseStep 330425 = 247819) B247819
theorem B6195973 : Blo 219811 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B330503 : Blo 219811 330503 := bstep (se 1 (by rfl) ⟨247877, by rfl⟩ : syracuseStep 330503 = 495755) B495755
theorem B330539 : Blo 219811 330539 := bstep (se 1 (by rfl) ⟨247904, by rfl⟩ : syracuseStep 330539 = 495809) B495809
theorem B330569 : Blo 219811 330569 := bstep (se 2 (by rfl) ⟨123963, by rfl⟩ : syracuseStep 330569 = 247927) B247927
theorem B330683 : Blo 219811 330683 := bstep (se 1 (by rfl) ⟨248012, by rfl⟩ : syracuseStep 330683 = 496025) B496025
theorem B330743 : Blo 219811 330743 := bstep (se 1 (by rfl) ⟨248057, by rfl⟩ : syracuseStep 330743 = 496115) B496115
theorem B330767 : Blo 219811 330767 := bstep (se 1 (by rfl) ⟨248075, by rfl⟩ : syracuseStep 330767 = 496151) B496151
theorem B265231 : Blo 219811 265231 := bstep (se 1 (by rfl) ⟨198923, by rfl⟩ : syracuseStep 265231 = 397847) B397847
theorem B330809 : Blo 219811 330809 := bstep (se 2 (by rfl) ⟨124053, by rfl⟩ : syracuseStep 330809 = 248107) B248107
theorem B494711 : Blo 219811 494711 := bstep (se 1 (by rfl) ⟨371033, by rfl⟩ : syracuseStep 494711 = 742067) B742067
theorem B330887 : Blo 219811 330887 := bstep (se 1 (by rfl) ⟨248165, by rfl⟩ : syracuseStep 330887 = 496331) B496331
theorem B330923 : Blo 219811 330923 := bstep (se 1 (by rfl) ⟨248192, by rfl⟩ : syracuseStep 330923 = 496385) B496385
theorem B330953 : Blo 219811 330953 := bstep (se 2 (by rfl) ⟨124107, by rfl⟩ : syracuseStep 330953 = 248215) B248215
theorem B494891 : Blo 219811 494891 := bstep (se 1 (by rfl) ⟨371168, by rfl⟩ : syracuseStep 494891 = 742337) B742337
theorem B331067 : Blo 219811 331067 := bstep (se 1 (by rfl) ⟨248300, by rfl⟩ : syracuseStep 331067 = 496601) B496601
theorem B331127 : Blo 219811 331127 := bstep (se 1 (by rfl) ⟨248345, by rfl⟩ : syracuseStep 331127 = 496691) B496691
theorem B396679 : Blo 219811 396679 := bstep (se 1 (by rfl) ⟨297509, by rfl⟩ : syracuseStep 396679 = 595019) B595019
theorem B331151 : Blo 219811 331151 := bstep (se 1 (by rfl) ⟨248363, by rfl⟩ : syracuseStep 331151 = 496727) B496727
theorem B331193 : Blo 219811 331193 := bstep (se 2 (by rfl) ⟨124197, by rfl⟩ : syracuseStep 331193 = 248395) B248395
theorem B1904057 : Blo 219811 1904057 := bstep (se 2 (by rfl) ⟨714021, by rfl⟩ : syracuseStep 1904057 = 1428043) B1428043
theorem B560641 : Blo 219811 560641 := bstep (se 2 (by rfl) ⟨210240, by rfl⟩ : syracuseStep 560641 = 420481) B420481
theorem B1674755 : Blo 219811 1674755 := bstep (se 1 (by rfl) ⟨1256066, by rfl⟩ : syracuseStep 1674755 = 2512133) B2512133
theorem B331271 : Blo 219811 331271 := bstep (se 1 (by rfl) ⟨248453, by rfl⟩ : syracuseStep 331271 = 496907) B496907
theorem B757259 : Blo 219811 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B331307 : Blo 219811 331307 := bstep (se 1 (by rfl) ⟨248480, by rfl⟩ : syracuseStep 331307 = 496961) B496961
theorem B331337 : Blo 219811 331337 := bstep (se 2 (by rfl) ⟨124251, by rfl⟩ : syracuseStep 331337 = 248503) B248503
theorem B495251 : Blo 219811 495251 := bstep (se 1 (by rfl) ⟨371438, by rfl⟩ : syracuseStep 495251 = 742877) B742877
theorem B331451 : Blo 219811 331451 := bstep (se 1 (by rfl) ⟨248588, by rfl⟩ : syracuseStep 331451 = 497177) B497177
theorem B495305 : Blo 219811 495305 := bstep (se 2 (by rfl) ⟨185739, by rfl⟩ : syracuseStep 495305 = 371479) B371479
theorem B331511 : Blo 219811 331511 := bstep (se 1 (by rfl) ⟨248633, by rfl⟩ : syracuseStep 331511 = 497267) B497267
theorem B331535 : Blo 219811 331535 := bstep (se 1 (by rfl) ⟨248651, by rfl⟩ : syracuseStep 331535 = 497303) B497303
theorem B331577 : Blo 219811 331577 := bstep (se 2 (by rfl) ⟨124341, by rfl⟩ : syracuseStep 331577 = 248683) B248683
theorem B331655 : Blo 219811 331655 := bstep (se 1 (by rfl) ⟨248741, by rfl⟩ : syracuseStep 331655 = 497483) B497483
theorem B331691 : Blo 219811 331691 := bstep (se 1 (by rfl) ⟨248768, by rfl⟩ : syracuseStep 331691 = 497537) B497537
theorem B331721 : Blo 219811 331721 := bstep (se 2 (by rfl) ⟨124395, by rfl⟩ : syracuseStep 331721 = 248791) B248791
theorem B6098989 : Blo 219811 6098989 := bstep (se 3 (by rfl) ⟨1143560, by rfl⟩ : syracuseStep 6098989 = 2287121) B2287121
theorem B331835 : Blo 219811 331835 := bstep (se 1 (by rfl) ⟨248876, by rfl⟩ : syracuseStep 331835 = 497753) B497753
theorem B561239 : Blo 219811 561239 := bstep (se 1 (by rfl) ⟨420929, by rfl⟩ : syracuseStep 561239 = 841859) B841859
theorem B6951005 : Blo 219811 6951005 := bstep (se 3 (by rfl) ⟨1303313, by rfl⟩ : syracuseStep 6951005 = 2606627) B2606627
theorem B331895 : Blo 219811 331895 := bstep (se 1 (by rfl) ⟨248921, by rfl⟩ : syracuseStep 331895 = 497843) B497843
theorem B331919 : Blo 219811 331919 := bstep (se 1 (by rfl) ⟨248939, by rfl⟩ : syracuseStep 331919 = 497879) B497879
theorem B331961 : Blo 219811 331961 := bstep (se 2 (by rfl) ⟨124485, by rfl⟩ : syracuseStep 331961 = 248971) B248971
theorem B332039 : Blo 219811 332039 := bstep (se 1 (by rfl) ⟨249029, by rfl⟩ : syracuseStep 332039 = 498059) B498059
theorem B332075 : Blo 219811 332075 := bstep (se 1 (by rfl) ⟨249056, by rfl⟩ : syracuseStep 332075 = 498113) B498113
theorem B561451 : Blo 219811 561451 := bstep (se 1 (by rfl) ⟨421088, by rfl⟩ : syracuseStep 561451 = 842177) B842177
theorem B332105 : Blo 219811 332105 := bstep (se 2 (by rfl) ⟨124539, by rfl⟩ : syracuseStep 332105 = 249079) B249079
theorem B627031 : Blo 219811 627031 := bstep (se 1 (by rfl) ⟨470273, by rfl⟩ : syracuseStep 627031 = 940547) B940547
theorem B496007 : Blo 219811 496007 := bstep (se 1 (by rfl) ⟨372005, by rfl⟩ : syracuseStep 496007 = 744011) B744011
theorem B1118609 : Blo 219811 1118609 := bstep (se 2 (by rfl) ⟨419478, by rfl⟩ : syracuseStep 1118609 = 838957) B838957
theorem B561593 : Blo 219811 561593 := bstep (se 2 (by rfl) ⟨210597, by rfl⟩ : syracuseStep 561593 = 421195) B421195
theorem B332219 : Blo 219811 332219 := bstep (se 1 (by rfl) ⟨249164, by rfl⟩ : syracuseStep 332219 = 498329) B498329
theorem B1085905 : Blo 219811 1085905 := bstep (se 2 (by rfl) ⟨407214, by rfl⟩ : syracuseStep 1085905 = 814429) B814429
theorem B332279 : Blo 219811 332279 := bstep (se 1 (by rfl) ⟨249209, by rfl⟩ : syracuseStep 332279 = 498419) B498419
theorem B332303 : Blo 219811 332303 := bstep (se 1 (by rfl) ⟨249227, by rfl⟩ : syracuseStep 332303 = 498455) B498455
theorem B332345 : Blo 219811 332345 := bstep (se 2 (by rfl) ⟨124629, by rfl⟩ : syracuseStep 332345 = 249259) B249259
theorem B627259 : Blo 219811 627259 := bstep (se 1 (by rfl) ⟨470444, by rfl⟩ : syracuseStep 627259 = 940889) B940889
theorem B496187 : Blo 219811 496187 := bstep (se 1 (by rfl) ⟨372140, by rfl⟩ : syracuseStep 496187 = 744281) B744281
theorem B332423 : Blo 219811 332423 := bstep (se 1 (by rfl) ⟨249317, by rfl⟩ : syracuseStep 332423 = 498635) B498635
theorem B529049 : Blo 219811 529049 := bstep (se 2 (by rfl) ⟨198393, by rfl⟩ : syracuseStep 529049 = 396787) B396787
theorem B332459 : Blo 219811 332459 := bstep (se 1 (by rfl) ⟨249344, by rfl⟩ : syracuseStep 332459 = 498689) B498689
theorem B627385 : Blo 219811 627385 := bstep (se 2 (by rfl) ⟨235269, by rfl⟩ : syracuseStep 627385 = 470539) B470539
theorem B496313 : Blo 219811 496313 := bstep (se 2 (by rfl) ⟨186117, by rfl⟩ : syracuseStep 496313 = 372235) B372235
theorem B332489 : Blo 219811 332489 := bstep (se 2 (by rfl) ⟨124683, by rfl⟩ : syracuseStep 332489 = 249367) B249367
theorem B332603 : Blo 219811 332603 := bstep (se 1 (by rfl) ⟨249452, by rfl⟩ : syracuseStep 332603 = 498905) B498905
theorem B332663 : Blo 219811 332663 := bstep (se 1 (by rfl) ⟨249497, by rfl⟩ : syracuseStep 332663 = 498995) B498995
theorem B267143 : Blo 219811 267143 := bstep (se 1 (by rfl) ⟨200357, by rfl⟩ : syracuseStep 267143 = 400715) B400715
theorem B332687 : Blo 219811 332687 := bstep (se 1 (by rfl) ⟨249515, by rfl⟩ : syracuseStep 332687 = 499031) B499031
theorem B332729 : Blo 219811 332729 := bstep (se 2 (by rfl) ⟨124773, by rfl⟩ : syracuseStep 332729 = 249547) B249547
theorem B332807 : Blo 219811 332807 := bstep (se 1 (by rfl) ⟨249605, by rfl⟩ : syracuseStep 332807 = 499211) B499211
theorem B496655 : Blo 219811 496655 := bstep (se 1 (by rfl) ⟨372491, by rfl⟩ : syracuseStep 496655 = 744983) B744983
theorem B398351 : Blo 219811 398351 := bstep (se 1 (by rfl) ⟨298763, by rfl⟩ : syracuseStep 398351 = 597527) B597527
theorem B496673 : Blo 219811 496673 := bstep (se 2 (by rfl) ⟨186252, by rfl⟩ : syracuseStep 496673 = 372505) B372505
theorem B332843 : Blo 219811 332843 := bstep (se 1 (by rfl) ⟨249632, by rfl⟩ : syracuseStep 332843 = 499265) B499265
theorem B1414205 : Blo 219811 1414205 := bstep (se 3 (by rfl) ⟨265163, by rfl⟩ : syracuseStep 1414205 = 530327) B530327
theorem B332873 : Blo 219811 332873 := bstep (se 2 (by rfl) ⟨124827, by rfl⟩ : syracuseStep 332873 = 249655) B249655
theorem B595097 : Blo 219811 595097 := bstep (se 2 (by rfl) ⟨223161, by rfl⟩ : syracuseStep 595097 = 446323) B446323
theorem B332987 : Blo 219811 332987 := bstep (se 1 (by rfl) ⟨249740, by rfl⟩ : syracuseStep 332987 = 499481) B499481
theorem B333047 : Blo 219811 333047 := bstep (se 1 (by rfl) ⟨249785, by rfl⟩ : syracuseStep 333047 = 499571) B499571
theorem B333071 : Blo 219811 333071 := bstep (se 1 (by rfl) ⟨249803, by rfl⟩ : syracuseStep 333071 = 499607) B499607
theorem B333113 : Blo 219811 333113 := bstep (se 2 (by rfl) ⟨124917, by rfl⟩ : syracuseStep 333113 = 249835) B249835
theorem B497015 : Blo 219811 497015 := bstep (se 1 (by rfl) ⟨372761, by rfl⟩ : syracuseStep 497015 = 745523) B745523
theorem B333191 : Blo 219811 333191 := bstep (se 1 (by rfl) ⟨249893, by rfl⟩ : syracuseStep 333191 = 499787) B499787
theorem B562585 : Blo 219811 562585 := bstep (se 2 (by rfl) ⟨210969, by rfl⟩ : syracuseStep 562585 = 421939) B421939
theorem B333227 : Blo 219811 333227 := bstep (se 1 (by rfl) ⟨249920, by rfl⟩ : syracuseStep 333227 = 499841) B499841
theorem B333257 : Blo 219811 333257 := bstep (se 2 (by rfl) ⟨124971, by rfl⟩ : syracuseStep 333257 = 249943) B249943
theorem B497195 : Blo 219811 497195 := bstep (se 1 (by rfl) ⟨372896, by rfl⟩ : syracuseStep 497195 = 745793) B745793
theorem B333371 : Blo 219811 333371 := bstep (se 1 (by rfl) ⟨250028, by rfl⟩ : syracuseStep 333371 = 500057) B500057
theorem B562747 : Blo 219811 562747 := bstep (se 1 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 562747 = 844121) B844121
theorem B333431 : Blo 219811 333431 := bstep (se 1 (by rfl) ⟨250073, by rfl⟩ : syracuseStep 333431 = 500147) B500147
theorem B333455 : Blo 219811 333455 := bstep (se 1 (by rfl) ⟨250091, by rfl⟩ : syracuseStep 333455 = 500183) B500183
theorem B333497 : Blo 219811 333497 := bstep (se 2 (by rfl) ⟨125061, by rfl⟩ : syracuseStep 333497 = 250123) B250123
theorem B562889 : Blo 219811 562889 := bstep (se 2 (by rfl) ⟨211083, by rfl⟩ : syracuseStep 562889 = 422167) B422167
theorem B333575 : Blo 219811 333575 := bstep (se 1 (by rfl) ⟨250181, by rfl⟩ : syracuseStep 333575 = 500363) B500363
theorem B333611 : Blo 219811 333611 := bstep (se 1 (by rfl) ⟨250208, by rfl⟩ : syracuseStep 333611 = 500417) B500417
theorem B333641 : Blo 219811 333641 := bstep (se 2 (by rfl) ⟨125115, by rfl⟩ : syracuseStep 333641 = 250231) B250231
theorem B497555 : Blo 219811 497555 := bstep (se 1 (by rfl) ⟨373166, by rfl⟩ : syracuseStep 497555 = 746333) B746333
theorem B1611683 : Blo 219811 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B333755 : Blo 219811 333755 := bstep (se 1 (by rfl) ⟨250316, by rfl⟩ : syracuseStep 333755 = 500633) B500633
theorem B497609 : Blo 219811 497609 := bstep (se 2 (by rfl) ⟨186603, by rfl⟩ : syracuseStep 497609 = 373207) B373207
theorem B333815 : Blo 219811 333815 := bstep (se 1 (by rfl) ⟨250361, by rfl⟩ : syracuseStep 333815 = 500723) B500723
theorem B333839 : Blo 219811 333839 := bstep (se 1 (by rfl) ⟨250379, by rfl⟩ : syracuseStep 333839 = 500759) B500759
theorem B563233 : Blo 219811 563233 := bstep (se 2 (by rfl) ⟨211212, by rfl⟩ : syracuseStep 563233 = 422425) B422425
theorem B333881 : Blo 219811 333881 := bstep (se 2 (by rfl) ⟨125205, by rfl⟩ : syracuseStep 333881 = 250411) B250411
theorem B1513559 : Blo 219811 1513559 := bstep (se 1 (by rfl) ⟨1135169, by rfl⟩ : syracuseStep 1513559 = 2270339) B2270339
theorem B333959 : Blo 219811 333959 := bstep (se 1 (by rfl) ⟨250469, by rfl⟩ : syracuseStep 333959 = 500939) B500939
theorem B333995 : Blo 219811 333995 := bstep (se 1 (by rfl) ⟨250496, by rfl⟩ : syracuseStep 333995 = 500993) B500993
theorem B334025 : Blo 219811 334025 := bstep (se 2 (by rfl) ⟨125259, by rfl⟩ : syracuseStep 334025 = 250519) B250519
theorem B334139 : Blo 219811 334139 := bstep (se 1 (by rfl) ⟨250604, by rfl⟩ : syracuseStep 334139 = 501209) B501209
theorem B2529629 : Blo 219811 2529629 := bstep (se 3 (by rfl) ⟨474305, by rfl⟩ : syracuseStep 2529629 = 948611) B948611
theorem B334199 : Blo 219811 334199 := bstep (se 1 (by rfl) ⟨250649, by rfl⟩ : syracuseStep 334199 = 501299) B501299
theorem B235919 : Blo 219811 235919 := bstep (se 1 (by rfl) ⟨176939, by rfl⟩ : syracuseStep 235919 = 353879) B353879
theorem B334223 : Blo 219811 334223 := bstep (se 1 (by rfl) ⟨250667, by rfl⟩ : syracuseStep 334223 = 501335) B501335
theorem B334265 : Blo 219811 334265 := bstep (se 2 (by rfl) ⟨125349, by rfl⟩ : syracuseStep 334265 = 250699) B250699
theorem B1120715 : Blo 219811 1120715 := bstep (se 1 (by rfl) ⟨840536, by rfl⟩ : syracuseStep 1120715 = 1681073) B1681073
theorem B334343 : Blo 219811 334343 := bstep (se 1 (by rfl) ⟨250757, by rfl⟩ : syracuseStep 334343 = 501515) B501515
theorem B334379 : Blo 219811 334379 := bstep (se 1 (by rfl) ⟨250784, by rfl⟩ : syracuseStep 334379 = 501569) B501569
theorem B629309 : Blo 219811 629309 := bstep (se 3 (by rfl) ⟨117995, by rfl⟩ : syracuseStep 629309 = 235991) B235991
theorem B334409 : Blo 219811 334409 := bstep (se 2 (by rfl) ⟨125403, by rfl⟩ : syracuseStep 334409 = 250807) B250807
theorem B563831 : Blo 219811 563831 := bstep (se 1 (by rfl) ⟨422873, by rfl⟩ : syracuseStep 563831 = 845747) B845747
theorem B498311 : Blo 219811 498311 := bstep (se 1 (by rfl) ⟨373733, by rfl⟩ : syracuseStep 498311 = 747467) B747467
theorem B334523 : Blo 219811 334523 := bstep (se 1 (by rfl) ⟨250892, by rfl⟩ : syracuseStep 334523 = 501785) B501785
theorem B334583 : Blo 219811 334583 := bstep (se 1 (by rfl) ⟨250937, by rfl⟩ : syracuseStep 334583 = 501875) B501875
theorem B531211 : Blo 219811 531211 := bstep (se 1 (by rfl) ⟨398408, by rfl⟩ : syracuseStep 531211 = 796817) B796817
theorem B1121039 : Blo 219811 1121039 := bstep (se 1 (by rfl) ⟨840779, by rfl⟩ : syracuseStep 1121039 = 1681559) B1681559
theorem B334607 : Blo 219811 334607 := bstep (se 1 (by rfl) ⟨250955, by rfl⟩ : syracuseStep 334607 = 501911) B501911
theorem B334649 : Blo 219811 334649 := bstep (se 2 (by rfl) ⟨125493, by rfl⟩ : syracuseStep 334649 = 250987) B250987
theorem B498491 : Blo 219811 498491 := bstep (se 1 (by rfl) ⟨373868, by rfl⟩ : syracuseStep 498491 = 747737) B747737
theorem B334727 : Blo 219811 334727 := bstep (se 1 (by rfl) ⟨251045, by rfl⟩ : syracuseStep 334727 = 502091) B502091
theorem B2038691 : Blo 219811 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B334763 : Blo 219811 334763 := bstep (se 1 (by rfl) ⟨251072, by rfl⟩ : syracuseStep 334763 = 502145) B502145
theorem B498617 : Blo 219811 498617 := bstep (se 2 (by rfl) ⟨186981, by rfl⟩ : syracuseStep 498617 = 373963) B373963
theorem B334793 : Blo 219811 334793 := bstep (se 2 (by rfl) ⟨125547, by rfl⟩ : syracuseStep 334793 = 251095) B251095
theorem B597007 : Blo 219811 597007 := bstep (se 1 (by rfl) ⟨447755, by rfl⟩ : syracuseStep 597007 = 895511) B895511
theorem B334907 : Blo 219811 334907 := bstep (se 1 (by rfl) ⟨251180, by rfl⟩ : syracuseStep 334907 = 502361) B502361
theorem B1219645 : Blo 219811 1219645 := bstep (se 3 (by rfl) ⟨228683, by rfl⟩ : syracuseStep 1219645 = 457367) B457367
theorem B3021911 : Blo 219811 3021911 := bstep (se 1 (by rfl) ⟨2266433, by rfl⟩ : syracuseStep 3021911 = 4532867) B4532867
theorem B334967 : Blo 219811 334967 := bstep (se 1 (by rfl) ⟨251225, by rfl⟩ : syracuseStep 334967 = 502451) B502451
theorem B334991 : Blo 219811 334991 := bstep (se 1 (by rfl) ⟨251243, by rfl⟩ : syracuseStep 334991 = 502487) B502487
theorem B335033 : Blo 219811 335033 := bstep (se 2 (by rfl) ⟨125637, by rfl⟩ : syracuseStep 335033 = 251275) B251275
theorem B335111 : Blo 219811 335111 := bstep (se 1 (by rfl) ⟨251333, by rfl⟩ : syracuseStep 335111 = 502667) B502667
theorem B498959 : Blo 219811 498959 := bstep (se 1 (by rfl) ⟨374219, by rfl⟩ : syracuseStep 498959 = 748439) B748439
theorem B498977 : Blo 219811 498977 := bstep (se 2 (by rfl) ⟨187116, by rfl⟩ : syracuseStep 498977 = 374233) B374233
theorem B335147 : Blo 219811 335147 := bstep (se 1 (by rfl) ⟨251360, by rfl⟩ : syracuseStep 335147 = 502721) B502721
theorem B335177 : Blo 219811 335177 := bstep (se 2 (by rfl) ⟨125691, by rfl⟩ : syracuseStep 335177 = 251383) B251383
theorem B335291 : Blo 219811 335291 := bstep (se 1 (by rfl) ⟨251468, by rfl⟩ : syracuseStep 335291 = 502937) B502937
theorem B335351 : Blo 219811 335351 := bstep (se 1 (by rfl) ⟨251513, by rfl⟩ : syracuseStep 335351 = 503027) B503027
theorem B302599 : Blo 219811 302599 := bstep (se 1 (by rfl) ⟨226949, by rfl⟩ : syracuseStep 302599 = 453899) B453899
theorem B826891 : Blo 219811 826891 := bstep (se 1 (by rfl) ⟨620168, by rfl⟩ : syracuseStep 826891 = 1240337) B1240337
theorem B335375 : Blo 219811 335375 := bstep (se 1 (by rfl) ⟨251531, by rfl⟩ : syracuseStep 335375 = 503063) B503063
theorem B630301 : Blo 219811 630301 := bstep (se 3 (by rfl) ⟨118181, by rfl⟩ : syracuseStep 630301 = 236363) B236363
theorem B237115 : Blo 219811 237115 := bstep (se 1 (by rfl) ⟨177836, by rfl⟩ : syracuseStep 237115 = 355673) B355673
theorem B335417 : Blo 219811 335417 := bstep (se 2 (by rfl) ⟨125781, by rfl⟩ : syracuseStep 335417 = 251563) B251563
theorem B302665 : Blo 219811 302665 := bstep (se 2 (by rfl) ⟨113499, by rfl⟩ : syracuseStep 302665 = 226999) B226999
theorem B499319 : Blo 219811 499319 := bstep (se 1 (by rfl) ⟨374489, by rfl⟩ : syracuseStep 499319 = 748979) B748979
theorem B335495 : Blo 219811 335495 := bstep (se 1 (by rfl) ⟨251621, by rfl⟩ : syracuseStep 335495 = 503243) B503243
theorem B335531 : Blo 219811 335531 := bstep (se 1 (by rfl) ⟨251648, by rfl⟩ : syracuseStep 335531 = 503297) B503297
theorem B335561 : Blo 219811 335561 := bstep (se 2 (by rfl) ⟨125835, by rfl⟩ : syracuseStep 335561 = 251671) B251671
theorem B2531087 : Blo 219811 2531087 := bstep (se 1 (by rfl) ⟨1898315, by rfl⟩ : syracuseStep 2531087 = 3796631) B3796631
theorem B499499 : Blo 219811 499499 := bstep (se 1 (by rfl) ⟨374624, by rfl⟩ : syracuseStep 499499 = 749249) B749249
theorem B335675 : Blo 219811 335675 := bstep (se 1 (by rfl) ⟨251756, by rfl⟩ : syracuseStep 335675 = 503513) B503513
theorem B565127 : Blo 219811 565127 := bstep (se 1 (by rfl) ⟨423845, by rfl⟩ : syracuseStep 565127 = 847691) B847691
theorem B565177 : Blo 219811 565177 := bstep (se 2 (by rfl) ⟨211941, by rfl⟩ : syracuseStep 565177 = 423883) B423883
theorem B532595 : Blo 219811 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B1056887 : Blo 219811 1056887 := bstep (se 1 (by rfl) ⟨792665, by rfl⟩ : syracuseStep 1056887 = 1585331) B1585331
theorem B532615 : Blo 219811 532615 := bstep (se 1 (by rfl) ⟨399461, by rfl⟩ : syracuseStep 532615 = 798923) B798923
theorem B499859 : Blo 219811 499859 := bstep (se 1 (by rfl) ⟨374894, by rfl⟩ : syracuseStep 499859 = 749789) B749789
theorem B1122497 : Blo 219811 1122497 := bstep (se 2 (by rfl) ⟨420936, by rfl⟩ : syracuseStep 1122497 = 841873) B841873
theorem B499913 : Blo 219811 499913 := bstep (se 2 (by rfl) ⟨187467, by rfl⟩ : syracuseStep 499913 = 374935) B374935
theorem B565775 : Blo 219811 565775 := bstep (se 1 (by rfl) ⟨424331, by rfl⟩ : syracuseStep 565775 = 848663) B848663
theorem B1810973 : Blo 219811 1810973 := bstep (se 3 (by rfl) ⟨339557, by rfl⟩ : syracuseStep 1810973 = 679115) B679115
theorem B795203 : Blo 219811 795203 := bstep (se 1 (by rfl) ⟨596402, by rfl⟩ : syracuseStep 795203 = 1192805) B1192805
theorem B860873 : Blo 219811 860873 := bstep (se 2 (by rfl) ⟨322827, by rfl⟩ : syracuseStep 860873 = 645655) B645655
theorem B1680101 : Blo 219811 1680101 := bstep (se 4 (by rfl) ⟨157509, by rfl⟩ : syracuseStep 1680101 = 315019) B315019
theorem B500615 : Blo 219811 500615 := bstep (se 1 (by rfl) ⟨375461, by rfl⟩ : syracuseStep 500615 = 750923) B750923
theorem B500795 : Blo 219811 500795 := bstep (se 1 (by rfl) ⟨375596, by rfl⟩ : syracuseStep 500795 = 751193) B751193
theorem B500921 : Blo 219811 500921 := bstep (se 2 (by rfl) ⟨187845, by rfl⟩ : syracuseStep 500921 = 375691) B375691
theorem B566473 : Blo 219811 566473 := bstep (se 2 (by rfl) ⟨212427, by rfl⟩ : syracuseStep 566473 = 424855) B424855
theorem B1254791 : Blo 219811 1254791 := bstep (se 1 (by rfl) ⟨941093, by rfl⟩ : syracuseStep 1254791 = 1882187) B1882187
theorem B894343 : Blo 219811 894343 := bstep (se 1 (by rfl) ⟨670757, by rfl⟩ : syracuseStep 894343 = 1341515) B1341515
theorem B1222033 : Blo 219811 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B632249 : Blo 219811 632249 := bstep (se 2 (by rfl) ⟨237093, by rfl⟩ : syracuseStep 632249 = 474187) B474187
theorem B1123793 : Blo 219811 1123793 := bstep (se 2 (by rfl) ⟨421422, by rfl⟩ : syracuseStep 1123793 = 842845) B842845
theorem B501263 : Blo 219811 501263 := bstep (se 1 (by rfl) ⟨375947, by rfl⟩ : syracuseStep 501263 = 751895) B751895
theorem B501281 : Blo 219811 501281 := bstep (se 2 (by rfl) ⟨187980, by rfl⟩ : syracuseStep 501281 = 375961) B375961
theorem B1418795 : Blo 219811 1418795 := bstep (se 1 (by rfl) ⟨1064096, by rfl⟩ : syracuseStep 1418795 = 2128193) B2128193
theorem B1254973 : Blo 219811 1254973 := bstep (se 3 (by rfl) ⟨235307, by rfl⟩ : syracuseStep 1254973 = 470615) B470615
theorem B403145 : Blo 219811 403145 := bstep (se 2 (by rfl) ⟨151179, by rfl⟩ : syracuseStep 403145 = 302359) B302359
theorem B26388341 : Blo 219811 26388341 := bstep (se 5 (by rfl) ⟨1236953, by rfl⟩ : syracuseStep 26388341 = 2473907) B2473907
theorem B501623 : Blo 219811 501623 := bstep (se 1 (by rfl) ⟨376217, by rfl⟩ : syracuseStep 501623 = 752435) B752435
theorem B2697239 : Blo 219811 2697239 := bstep (se 1 (by rfl) ⟨2022929, by rfl⟩ : syracuseStep 2697239 = 4045859) B4045859
theorem B501803 : Blo 219811 501803 := bstep (se 1 (by rfl) ⟨376352, by rfl⟩ : syracuseStep 501803 = 752705) B752705
theorem B567595 : Blo 219811 567595 := bstep (se 1 (by rfl) ⟨425696, by rfl⟩ : syracuseStep 567595 = 851393) B851393
theorem B895367 : Blo 219811 895367 := bstep (se 1 (by rfl) ⟨671525, by rfl⟩ : syracuseStep 895367 = 1343051) B1343051
theorem B502163 : Blo 219811 502163 := bstep (se 1 (by rfl) ⟨376622, by rfl⟩ : syracuseStep 502163 = 753245) B753245
theorem B338347 : Blo 219811 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B502217 : Blo 219811 502217 := bstep (se 2 (by rfl) ⟨188331, by rfl⟩ : syracuseStep 502217 = 376663) B376663
theorem B240143 : Blo 219811 240143 := bstep (se 1 (by rfl) ⟨180107, by rfl⟩ : syracuseStep 240143 = 360215) B360215
theorem B371243 : Blo 219811 371243 := bstep (se 1 (by rfl) ⟨278432, by rfl⟩ : syracuseStep 371243 = 556865) B556865
theorem B469651 : Blo 219811 469651 := bstep (se 1 (by rfl) ⟨352238, by rfl⟩ : syracuseStep 469651 = 704477) B704477
theorem B633491 : Blo 219811 633491 := bstep (se 1 (by rfl) ⟨475118, by rfl⟩ : syracuseStep 633491 = 950237) B950237
theorem B535355 : Blo 219811 535355 := bstep (se 1 (by rfl) ⟨401516, by rfl⟩ : syracuseStep 535355 = 803033) B803033
theorem B1190771 : Blo 219811 1190771 := bstep (se 1 (by rfl) ⟨893078, by rfl⟩ : syracuseStep 1190771 = 1786157) B1786157
theorem B1616755 : Blo 219811 1616755 := bstep (se 1 (by rfl) ⟨1212566, by rfl⟩ : syracuseStep 1616755 = 2425133) B2425133
theorem B371641 : Blo 219811 371641 := bstep (se 2 (by rfl) ⟨139365, by rfl⟩ : syracuseStep 371641 = 278731) B278731
theorem B502919 : Blo 219811 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B1256705 : Blo 219811 1256705 := bstep (se 2 (by rfl) ⟨471264, by rfl⟩ : syracuseStep 1256705 = 942529) B942529
theorem B503099 : Blo 219811 503099 := bstep (se 1 (by rfl) ⟨377324, by rfl⟩ : syracuseStep 503099 = 754649) B754649
theorem B503225 : Blo 219811 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B1224157 : Blo 219811 1224157 := bstep (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) B459059
theorem B1125899 : Blo 219811 1125899 := bstep (se 1 (by rfl) ⟨844424, by rfl⟩ : syracuseStep 1125899 = 1688849) B1688849
theorem B372343 : Blo 219811 372343 := bstep (se 1 (by rfl) ⟨279257, by rfl⟩ : syracuseStep 372343 = 558515) B558515
theorem B1126061 : Blo 219811 1126061 := bstep (se 3 (by rfl) ⟨211136, by rfl⟩ : syracuseStep 1126061 = 422273) B422273
theorem B503567 : Blo 219811 503567 := bstep (se 1 (by rfl) ⟨377675, by rfl⟩ : syracuseStep 503567 = 755351) B755351
theorem B372539 : Blo 219811 372539 := bstep (se 1 (by rfl) ⟨279404, by rfl⟩ : syracuseStep 372539 = 558809) B558809
theorem B634711 : Blo 219811 634711 := bstep (se 1 (by rfl) ⟨476033, by rfl⟩ : syracuseStep 634711 = 952067) B952067
theorem B634891 : Blo 219811 634891 := bstep (se 1 (by rfl) ⟨476168, by rfl⟩ : syracuseStep 634891 = 952337) B952337
theorem B372937 : Blo 219811 372937 := bstep (se 2 (by rfl) ⟨139851, by rfl⟩ : syracuseStep 372937 = 279703) B279703
theorem B635165 : Blo 219811 635165 := bstep (se 3 (by rfl) ⟨119093, by rfl⟩ : syracuseStep 635165 = 238187) B238187
theorem B1519931 : Blo 219811 1519931 := bstep (se 1 (by rfl) ⟨1139948, by rfl⟩ : syracuseStep 1519931 = 2279897) B2279897
theorem B2699729 : Blo 219811 2699729 := bstep (se 2 (by rfl) ⟨1012398, by rfl⟩ : syracuseStep 2699729 = 2024797) B2024797
theorem B537131 : Blo 219811 537131 := bstep (se 1 (by rfl) ⟨402848, by rfl⟩ : syracuseStep 537131 = 805697) B805697
theorem B373639 : Blo 219811 373639 := bstep (se 1 (by rfl) ⟨280229, by rfl⟩ : syracuseStep 373639 = 560459) B560459
theorem B537479 : Blo 219811 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B668569 : Blo 219811 668569 := bstep (se 2 (by rfl) ⟨250713, by rfl⟩ : syracuseStep 668569 = 501427) B501427
theorem B504967 : Blo 219811 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B1127681 : Blo 219811 1127681 := bstep (se 2 (by rfl) ⟨422880, by rfl⟩ : syracuseStep 1127681 = 845761) B845761
theorem B406799 : Blo 219811 406799 := bstep (se 1 (by rfl) ⟨305099, by rfl⟩ : syracuseStep 406799 = 610199) B610199
theorem B3225091 : Blo 219811 3225091 := bstep (se 1 (by rfl) ⟨2418818, by rfl⟩ : syracuseStep 3225091 = 4837637) B4837637
theorem B374287 : Blo 219811 374287 := bstep (se 1 (by rfl) ⟨280715, by rfl⟩ : syracuseStep 374287 = 561431) B561431
theorem B2832407 : Blo 219811 2832407 := bstep (se 1 (by rfl) ⟨2124305, by rfl⟩ : syracuseStep 2832407 = 4248611) B4248611
theorem B374827 : Blo 219811 374827 := bstep (se 1 (by rfl) ⟨281120, by rfl⟩ : syracuseStep 374827 = 562241) B562241
theorem B1128491 : Blo 219811 1128491 := bstep (se 1 (by rfl) ⟨846368, by rfl⟩ : syracuseStep 1128491 = 1692737) B1692737
theorem B4044973 : Blo 219811 4044973 := bstep (se 3 (by rfl) ⟨758432, by rfl⟩ : syracuseStep 4044973 = 1516865) B1516865
theorem B669881 : Blo 219811 669881 := bstep (se 2 (by rfl) ⟨251205, by rfl⟩ : syracuseStep 669881 = 502411) B502411
theorem B473273 : Blo 219811 473273 := bstep (se 2 (by rfl) ⟨177477, by rfl⟩ : syracuseStep 473273 = 354955) B354955
theorem B374969 : Blo 219811 374969 := bstep (se 2 (by rfl) ⟨140613, by rfl⟩ : syracuseStep 374969 = 281227) B281227
theorem B538967 : Blo 219811 538967 := bstep (se 1 (by rfl) ⟨404225, by rfl⟩ : syracuseStep 538967 = 808451) B808451
theorem B375671 : Blo 219811 375671 := bstep (se 1 (by rfl) ⟨281753, by rfl⟩ : syracuseStep 375671 = 563507) B563507
theorem B1424557 : Blo 219811 1424557 := bstep (se 3 (by rfl) ⟨267104, by rfl⟩ : syracuseStep 1424557 = 534209) B534209
theorem B376123 : Blo 219811 376123 := bstep (se 1 (by rfl) ⟨282092, by rfl⟩ : syracuseStep 376123 = 564185) B564185
theorem B1129787 : Blo 219811 1129787 := bstep (se 1 (by rfl) ⟨847340, by rfl⟩ : syracuseStep 1129787 = 1694681) B1694681
theorem B376265 : Blo 219811 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B1129949 : Blo 219811 1129949 := bstep (se 3 (by rfl) ⟨211865, by rfl⟩ : syracuseStep 1129949 = 423731) B423731
theorem B1261079 : Blo 219811 1261079 := bstep (se 1 (by rfl) ⟨945809, by rfl⟩ : syracuseStep 1261079 = 1891619) B1891619
theorem B835343 : Blo 219811 835343 := bstep (se 1 (by rfl) ⟨626507, by rfl⟩ : syracuseStep 835343 = 1253015) B1253015
theorem B474913 : Blo 219811 474913 := bstep (se 2 (by rfl) ⟨178092, by rfl⟩ : syracuseStep 474913 = 356185) B356185
theorem B1130273 : Blo 219811 1130273 := bstep (se 2 (by rfl) ⟨423852, by rfl⟩ : syracuseStep 1130273 = 847705) B847705
theorem B278407 : Blo 219811 278407 := bstep (se 1 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 278407 = 417611) B417611
theorem B7356509 : Blo 219811 7356509 := bstep (se 3 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 7356509 = 2758691) B2758691
theorem B376967 : Blo 219811 376967 := bstep (se 1 (by rfl) ⟨282725, by rfl⟩ : syracuseStep 376967 = 565451) B565451
theorem B2539835 : Blo 219811 2539835 := bstep (se 1 (by rfl) ⟨1904876, by rfl⟩ : syracuseStep 2539835 = 3809753) B3809753
theorem B278903 : Blo 219811 278903 := bstep (se 1 (by rfl) ⟨209177, by rfl⟩ : syracuseStep 278903 = 418355) B418355
theorem B279055 : Blo 219811 279055 := bstep (se 1 (by rfl) ⟨209291, by rfl⟩ : syracuseStep 279055 = 418583) B418583
theorem B279227 : Blo 219811 279227 := bstep (se 1 (by rfl) ⟨209420, by rfl⟩ : syracuseStep 279227 = 418841) B418841
theorem B1131245 : Blo 219811 1131245 := bstep (se 3 (by rfl) ⟨212108, by rfl⟩ : syracuseStep 1131245 = 424217) B424217
theorem B377615 : Blo 219811 377615 := bstep (se 1 (by rfl) ⟨283211, by rfl⟩ : syracuseStep 377615 = 566423) B566423
theorem B607019 : Blo 219811 607019 := bstep (se 1 (by rfl) ⟨455264, by rfl⟩ : syracuseStep 607019 = 910529) B910529
theorem B3818501 : Blo 219811 3818501 := bstep (se 4 (by rfl) ⟨357984, by rfl⟩ : syracuseStep 3818501 = 715969) B715969
theorem B541811 : Blo 219811 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B2114693 : Blo 219811 2114693 := bstep (se 4 (by rfl) ⟨198252, by rfl⟩ : syracuseStep 2114693 = 396505) B396505
theorem B476459 : Blo 219811 476459 := bstep (se 1 (by rfl) ⟨357344, by rfl⟩ : syracuseStep 476459 = 714689) B714689
theorem B836999 : Blo 219811 836999 := bstep (se 1 (by rfl) ⟨627749, by rfl⟩ : syracuseStep 836999 = 1255499) B1255499
theorem B1590749 : Blo 219811 1590749 := bstep (se 3 (by rfl) ⟨298265, by rfl⟩ : syracuseStep 1590749 = 596531) B596531
theorem B1132055 : Blo 219811 1132055 := bstep (se 1 (by rfl) ⟨849041, by rfl⟩ : syracuseStep 1132055 = 1698083) B1698083
theorem B280199 : Blo 219811 280199 := bstep (se 1 (by rfl) ⟨210149, by rfl⟩ : syracuseStep 280199 = 420299) B420299
theorem B247567 : Blo 219811 247567 := bstep (se 1 (by rfl) ⟨185675, by rfl⟩ : syracuseStep 247567 = 371351) B371351
theorem B673579 : Blo 219811 673579 := bstep (se 1 (by rfl) ⟨505184, by rfl⟩ : syracuseStep 673579 = 1010369) B1010369
theorem B248071 : Blo 219811 248071 := bstep (se 1 (by rfl) ⟨186053, by rfl⟩ : syracuseStep 248071 = 372107) B372107
theorem B280847 : Blo 219811 280847 := bstep (se 1 (by rfl) ⟨210635, by rfl⟩ : syracuseStep 280847 = 421271) B421271
theorem B248251 : Blo 219811 248251 := bstep (se 1 (by rfl) ⟨186188, by rfl⟩ : syracuseStep 248251 = 372377) B372377
theorem B1264247 : Blo 219811 1264247 := bstep (se 1 (by rfl) ⟨948185, by rfl⟩ : syracuseStep 1264247 = 1896371) B1896371
theorem B314057 : Blo 219811 314057 := bstep (se 2 (by rfl) ⟨117771, by rfl⟩ : syracuseStep 314057 = 235543) B235543
theorem B903881 : Blo 219811 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B248719 : Blo 219811 248719 := bstep (se 1 (by rfl) ⟨186539, by rfl⟩ : syracuseStep 248719 = 373079) B373079
theorem B838775 : Blo 219811 838775 := bstep (se 1 (by rfl) ⟨629081, by rfl⟩ : syracuseStep 838775 = 1258163) B1258163
theorem B1887623 : Blo 219811 1887623 := bstep (se 1 (by rfl) ⟨1415717, by rfl⟩ : syracuseStep 1887623 = 2831435) B2831435
theorem B249223 : Blo 219811 249223 := bstep (se 1 (by rfl) ⟨186917, by rfl⟩ : syracuseStep 249223 = 373835) B373835
theorem B314923 : Blo 219811 314923 := bstep (se 1 (by rfl) ⟨236192, by rfl⟩ : syracuseStep 314923 = 472385) B472385
theorem B249403 : Blo 219811 249403 := bstep (se 1 (by rfl) ⟨187052, by rfl⟩ : syracuseStep 249403 = 374105) B374105
theorem B1199809 : Blo 219811 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B249871 : Blo 219811 249871 := bstep (se 1 (by rfl) ⟨187403, by rfl⟩ : syracuseStep 249871 = 374807) B374807
theorem B839747 : Blo 219811 839747 := bstep (se 1 (by rfl) ⟨629810, by rfl⟩ : syracuseStep 839747 = 1259621) B1259621
theorem B250375 : Blo 219811 250375 := bstep (se 1 (by rfl) ⟨187781, by rfl⟩ : syracuseStep 250375 = 375563) B375563
theorem B840203 : Blo 219811 840203 := bstep (se 1 (by rfl) ⟨630152, by rfl⟩ : syracuseStep 840203 = 1260305) B1260305
theorem B905795 : Blo 219811 905795 := bstep (se 1 (by rfl) ⟨679346, by rfl⟩ : syracuseStep 905795 = 1358693) B1358693
theorem B250555 : Blo 219811 250555 := bstep (se 1 (by rfl) ⟨187916, by rfl⟩ : syracuseStep 250555 = 375833) B375833
theorem B906137 : Blo 219811 906137 := bstep (se 2 (by rfl) ⟨339801, by rfl⟩ : syracuseStep 906137 = 679603) B679603
theorem B1692683 : Blo 219811 1692683 := bstep (se 1 (by rfl) ⟨1269512, by rfl⟩ : syracuseStep 1692683 = 2539025) B2539025
theorem B316489 : Blo 219811 316489 := bstep (se 2 (by rfl) ⟨118683, by rfl⟩ : syracuseStep 316489 = 237367) B237367
theorem B251023 : Blo 219811 251023 := bstep (se 1 (by rfl) ⟨188267, by rfl⟩ : syracuseStep 251023 = 376535) B376535
theorem B283819 : Blo 219811 283819 := bstep (se 1 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 283819 = 425729) B425729
theorem B709921 : Blo 219811 709921 := bstep (se 2 (by rfl) ⟨266220, by rfl⟩ : syracuseStep 709921 = 532441) B532441
theorem B742715 : Blo 219811 742715 := bstep (se 1 (by rfl) ⟨557036, by rfl⟩ : syracuseStep 742715 = 1114073) B1114073
theorem B251407 : Blo 219811 251407 := bstep (se 1 (by rfl) ⟨188555, by rfl⟩ : syracuseStep 251407 = 377111) B377111
theorem B2840093 : Blo 219811 2840093 := bstep (se 3 (by rfl) ⟨532517, by rfl⟩ : syracuseStep 2840093 = 1065035) B1065035
theorem B317047 : Blo 219811 317047 := bstep (se 1 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 317047 = 475571) B475571
theorem B251527 : Blo 219811 251527 := bstep (se 1 (by rfl) ⟨188645, by rfl⟩ : syracuseStep 251527 = 377291) B377291
theorem B611993 : Blo 219811 611993 := bstep (se 2 (by rfl) ⟨229497, by rfl⟩ : syracuseStep 611993 = 458995) B458995
theorem B1070765 : Blo 219811 1070765 := bstep (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) B401537
theorem B2119385 : Blo 219811 2119385 := bstep (se 2 (by rfl) ⟨794769, by rfl⟩ : syracuseStep 2119385 = 1589539) B1589539
theorem B743201 : Blo 219811 743201 := bstep (se 2 (by rfl) ⟨278700, by rfl⟩ : syracuseStep 743201 = 557401) B557401
theorem B251707 : Blo 219811 251707 := bstep (se 1 (by rfl) ⟨188780, by rfl⟩ : syracuseStep 251707 = 377561) B377561
theorem B317611 : Blo 219811 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B1267913 : Blo 219811 1267913 := bstep (se 2 (by rfl) ⟨475467, by rfl⟩ : syracuseStep 1267913 = 950935) B950935
theorem B743795 : Blo 219811 743795 := bstep (se 1 (by rfl) ⟨557846, by rfl⟩ : syracuseStep 743795 = 1115693) B1115693
theorem B317839 : Blo 219811 317839 := bstep (se 1 (by rfl) ⟨238379, by rfl⟩ : syracuseStep 317839 = 476759) B476759
theorem B1890935 : Blo 219811 1890935 := bstep (se 1 (by rfl) ⟨1418201, by rfl⟩ : syracuseStep 1890935 = 2836403) B2836403
theorem B842359 : Blo 219811 842359 := bstep (se 1 (by rfl) ⟨631769, by rfl⟩ : syracuseStep 842359 = 1263539) B1263539
theorem B219835 : Blo 219811 219835 := bstep (se 1 (by rfl) ⟨164876, by rfl⟩ : syracuseStep 219835 = 329753) B329753
theorem B219911 : Blo 219811 219911 := bstep (se 1 (by rfl) ⟨164933, by rfl⟩ : syracuseStep 219911 = 329867) B329867
theorem B219919 : Blo 219811 219919 := bstep (se 1 (by rfl) ⟨164939, by rfl⟩ : syracuseStep 219919 = 329879) B329879
theorem B1530661 : Blo 219811 1530661 := bstep (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) B286999
theorem B219963 : Blo 219811 219963 := bstep (se 1 (by rfl) ⟨164972, by rfl⟩ : syracuseStep 219963 = 329945) B329945
theorem B220039 : Blo 219811 220039 := bstep (se 1 (by rfl) ⟨165029, by rfl⟩ : syracuseStep 220039 = 330059) B330059
theorem B220047 : Blo 219811 220047 := bstep (se 1 (by rfl) ⟨165035, by rfl⟩ : syracuseStep 220047 = 330071) B330071
theorem B220091 : Blo 219811 220091 := bstep (se 1 (by rfl) ⟨165068, by rfl⟩ : syracuseStep 220091 = 330137) B330137
theorem B220167 : Blo 219811 220167 := bstep (se 1 (by rfl) ⟨165125, by rfl⟩ : syracuseStep 220167 = 330251) B330251
theorem B220175 : Blo 219811 220175 := bstep (se 1 (by rfl) ⟨165131, by rfl⟩ : syracuseStep 220175 = 330263) B330263
theorem B220219 : Blo 219811 220219 := bstep (se 1 (by rfl) ⟨165164, by rfl⟩ : syracuseStep 220219 = 330329) B330329
theorem B711767 : Blo 219811 711767 := bstep (se 1 (by rfl) ⟨533825, by rfl⟩ : syracuseStep 711767 = 1067651) B1067651
theorem B220295 : Blo 219811 220295 := bstep (se 1 (by rfl) ⟨165221, by rfl⟩ : syracuseStep 220295 = 330443) B330443
theorem B220303 : Blo 219811 220303 := bstep (se 1 (by rfl) ⟨165227, by rfl⟩ : syracuseStep 220303 = 330455) B330455
theorem B220347 : Blo 219811 220347 := bstep (se 1 (by rfl) ⟨165260, by rfl⟩ : syracuseStep 220347 = 330521) B330521
theorem B220423 : Blo 219811 220423 := bstep (se 1 (by rfl) ⟨165317, by rfl⟩ : syracuseStep 220423 = 330635) B330635
theorem B220431 : Blo 219811 220431 := bstep (se 1 (by rfl) ⟨165323, by rfl⟩ : syracuseStep 220431 = 330647) B330647
theorem B220475 : Blo 219811 220475 := bstep (se 1 (by rfl) ⟨165356, by rfl⟩ : syracuseStep 220475 = 330713) B330713
theorem B220551 : Blo 219811 220551 := bstep (se 1 (by rfl) ⟨165413, by rfl⟩ : syracuseStep 220551 = 330827) B330827
theorem B220559 : Blo 219811 220559 := bstep (se 1 (by rfl) ⟨165419, by rfl⟩ : syracuseStep 220559 = 330839) B330839
theorem B1924499 : Blo 219811 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B220603 : Blo 219811 220603 := bstep (se 1 (by rfl) ⟨165452, by rfl⟩ : syracuseStep 220603 = 330905) B330905
theorem B220679 : Blo 219811 220679 := bstep (se 1 (by rfl) ⟨165509, by rfl⟩ : syracuseStep 220679 = 331019) B331019
theorem B220687 : Blo 219811 220687 := bstep (se 1 (by rfl) ⟨165515, by rfl⟩ : syracuseStep 220687 = 331031) B331031
theorem B318991 : Blo 219811 318991 := bstep (se 1 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 318991 = 478487) B478487
theorem B2711069 : Blo 219811 2711069 := bstep (se 3 (by rfl) ⟨508325, by rfl⟩ : syracuseStep 2711069 = 1016651) B1016651
theorem B220731 : Blo 219811 220731 := bstep (se 1 (by rfl) ⟨165548, by rfl⟩ : syracuseStep 220731 = 331097) B331097
theorem B843331 : Blo 219811 843331 := bstep (se 1 (by rfl) ⟨632498, by rfl⟩ : syracuseStep 843331 = 1264997) B1264997
theorem B220807 : Blo 219811 220807 := bstep (se 1 (by rfl) ⟨165605, by rfl⟩ : syracuseStep 220807 = 331211) B331211
theorem B220815 : Blo 219811 220815 := bstep (se 1 (by rfl) ⟨165611, by rfl⟩ : syracuseStep 220815 = 331223) B331223
theorem B220859 : Blo 219811 220859 := bstep (se 1 (by rfl) ⟨165644, by rfl⟩ : syracuseStep 220859 = 331289) B331289
theorem B220935 : Blo 219811 220935 := bstep (se 1 (by rfl) ⟨165701, by rfl⟩ : syracuseStep 220935 = 331403) B331403
theorem B220943 : Blo 219811 220943 := bstep (se 1 (by rfl) ⟨165707, by rfl⟩ : syracuseStep 220943 = 331415) B331415
theorem B4054835 : Blo 219811 4054835 := bstep (se 1 (by rfl) ⟨3041126, by rfl⟩ : syracuseStep 4054835 = 6082253) B6082253
theorem B220987 : Blo 219811 220987 := bstep (se 1 (by rfl) ⟨165740, by rfl⟩ : syracuseStep 220987 = 331481) B331481
theorem B843635 : Blo 219811 843635 := bstep (se 1 (by rfl) ⟨632726, by rfl⟩ : syracuseStep 843635 = 1265453) B1265453
theorem B221063 : Blo 219811 221063 := bstep (se 1 (by rfl) ⟨165797, by rfl⟩ : syracuseStep 221063 = 331595) B331595
theorem B221071 : Blo 219811 221071 := bstep (se 1 (by rfl) ⟨165803, by rfl⟩ : syracuseStep 221071 = 331607) B331607
theorem B221115 : Blo 219811 221115 := bstep (se 1 (by rfl) ⟨165836, by rfl⟩ : syracuseStep 221115 = 331673) B331673
theorem B286651 : Blo 219811 286651 := bstep (se 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) B429977
theorem B221191 : Blo 219811 221191 := bstep (se 1 (by rfl) ⟨165893, by rfl⟩ : syracuseStep 221191 = 331787) B331787
theorem B221199 : Blo 219811 221199 := bstep (se 1 (by rfl) ⟨165899, by rfl⟩ : syracuseStep 221199 = 331799) B331799
theorem B221243 : Blo 219811 221243 := bstep (se 1 (by rfl) ⟨165932, by rfl⟩ : syracuseStep 221243 = 331865) B331865
theorem B1269827 : Blo 219811 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B221319 : Blo 219811 221319 := bstep (se 1 (by rfl) ⟨165989, by rfl⟩ : syracuseStep 221319 = 331979) B331979
theorem B221327 : Blo 219811 221327 := bstep (se 1 (by rfl) ⟨165995, by rfl⟩ : syracuseStep 221327 = 331991) B331991
theorem B680089 : Blo 219811 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B221371 : Blo 219811 221371 := bstep (se 1 (by rfl) ⟨166028, by rfl⟩ : syracuseStep 221371 = 332057) B332057
theorem B221447 : Blo 219811 221447 := bstep (se 1 (by rfl) ⟨166085, by rfl⟩ : syracuseStep 221447 = 332171) B332171
theorem B221455 : Blo 219811 221455 := bstep (se 1 (by rfl) ⟨166091, by rfl⟩ : syracuseStep 221455 = 332183) B332183
theorem B221499 : Blo 219811 221499 := bstep (se 1 (by rfl) ⟨166124, by rfl⟩ : syracuseStep 221499 = 332249) B332249
theorem B844091 : Blo 219811 844091 := bstep (se 1 (by rfl) ⟨633068, by rfl⟩ : syracuseStep 844091 = 1266137) B1266137
theorem B221575 : Blo 219811 221575 := bstep (se 1 (by rfl) ⟨166181, by rfl⟩ : syracuseStep 221575 = 332363) B332363
theorem B221583 : Blo 219811 221583 := bstep (se 1 (by rfl) ⟨166187, by rfl⟩ : syracuseStep 221583 = 332375) B332375
theorem B221627 : Blo 219811 221627 := bstep (se 1 (by rfl) ⟨166220, by rfl⟩ : syracuseStep 221627 = 332441) B332441
theorem B221703 : Blo 219811 221703 := bstep (se 1 (by rfl) ⟨166277, by rfl⟩ : syracuseStep 221703 = 332555) B332555
theorem B221711 : Blo 219811 221711 := bstep (se 1 (by rfl) ⟨166283, by rfl⟩ : syracuseStep 221711 = 332567) B332567
theorem B221755 : Blo 219811 221755 := bstep (se 1 (by rfl) ⟨166316, by rfl⟩ : syracuseStep 221755 = 332633) B332633
theorem B418439 : Blo 219811 418439 := bstep (se 1 (by rfl) ⟨313829, by rfl⟩ : syracuseStep 418439 = 627659) B627659
theorem B221831 : Blo 219811 221831 := bstep (se 1 (by rfl) ⟨166373, by rfl⟩ : syracuseStep 221831 = 332747) B332747
theorem B221839 : Blo 219811 221839 := bstep (se 1 (by rfl) ⟨166379, by rfl⟩ : syracuseStep 221839 = 332759) B332759
theorem B221883 : Blo 219811 221883 := bstep (se 1 (by rfl) ⟨166412, by rfl⟩ : syracuseStep 221883 = 332825) B332825
theorem B221959 : Blo 219811 221959 := bstep (se 1 (by rfl) ⟨166469, by rfl⟩ : syracuseStep 221959 = 332939) B332939
theorem B221967 : Blo 219811 221967 := bstep (se 1 (by rfl) ⟨166475, by rfl⟩ : syracuseStep 221967 = 332951) B332951
theorem B844577 : Blo 219811 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B222011 : Blo 219811 222011 := bstep (se 1 (by rfl) ⟨166508, by rfl⟩ : syracuseStep 222011 = 333017) B333017
theorem B222087 : Blo 219811 222087 := bstep (se 1 (by rfl) ⟨166565, by rfl⟩ : syracuseStep 222087 = 333131) B333131
theorem B222095 : Blo 219811 222095 := bstep (se 1 (by rfl) ⟨166571, by rfl⟩ : syracuseStep 222095 = 333143) B333143
theorem B746387 : Blo 219811 746387 := bstep (se 1 (by rfl) ⟨559790, by rfl⟩ : syracuseStep 746387 = 1119581) B1119581
theorem B222139 : Blo 219811 222139 := bstep (se 1 (by rfl) ⟨166604, by rfl⟩ : syracuseStep 222139 = 333209) B333209
theorem B222215 : Blo 219811 222215 := bstep (se 1 (by rfl) ⟨166661, by rfl⟩ : syracuseStep 222215 = 333323) B333323
theorem B222223 : Blo 219811 222223 := bstep (se 1 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 222223 = 333335) B333335
theorem B222267 : Blo 219811 222267 := bstep (se 1 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 222267 = 333401) B333401
theorem B222343 : Blo 219811 222343 := bstep (se 1 (by rfl) ⟨166757, by rfl⟩ : syracuseStep 222343 = 333515) B333515
theorem B222351 : Blo 219811 222351 := bstep (se 1 (by rfl) ⟨166763, by rfl⟩ : syracuseStep 222351 = 333527) B333527
theorem B222395 : Blo 219811 222395 := bstep (se 1 (by rfl) ⟨166796, by rfl⟩ : syracuseStep 222395 = 333593) B333593
theorem B28697813 : Blo 219811 28697813 := bstep (se 7 (by rfl) ⟨336302, by rfl⟩ : syracuseStep 28697813 = 672605) B672605
theorem B222471 : Blo 219811 222471 := bstep (se 1 (by rfl) ⟨166853, by rfl⟩ : syracuseStep 222471 = 333707) B333707
theorem B222479 : Blo 219811 222479 := bstep (se 1 (by rfl) ⟨166859, by rfl⟩ : syracuseStep 222479 = 333719) B333719
theorem B222523 : Blo 219811 222523 := bstep (se 1 (by rfl) ⟨166892, by rfl⟩ : syracuseStep 222523 = 333785) B333785
theorem B222599 : Blo 219811 222599 := bstep (se 1 (by rfl) ⟨166949, by rfl⟩ : syracuseStep 222599 = 333899) B333899
theorem B222607 : Blo 219811 222607 := bstep (se 1 (by rfl) ⟨166955, by rfl⟩ : syracuseStep 222607 = 333911) B333911
theorem B222651 : Blo 219811 222651 := bstep (se 1 (by rfl) ⟨166988, by rfl⟩ : syracuseStep 222651 = 333977) B333977
theorem B222727 : Blo 219811 222727 := bstep (se 1 (by rfl) ⟨167045, by rfl⟩ : syracuseStep 222727 = 334091) B334091
theorem B222735 : Blo 219811 222735 := bstep (se 1 (by rfl) ⟨167051, by rfl⟩ : syracuseStep 222735 = 334103) B334103
theorem B222779 : Blo 219811 222779 := bstep (se 1 (by rfl) ⟨167084, by rfl⟩ : syracuseStep 222779 = 334169) B334169
theorem B681587 : Blo 219811 681587 := bstep (se 1 (by rfl) ⟨511190, by rfl⟩ : syracuseStep 681587 = 1022381) B1022381
theorem B222855 : Blo 219811 222855 := bstep (se 1 (by rfl) ⟨167141, by rfl⟩ : syracuseStep 222855 = 334283) B334283
theorem B222863 : Blo 219811 222863 := bstep (se 1 (by rfl) ⟨167147, by rfl⟩ : syracuseStep 222863 = 334295) B334295
theorem B222907 : Blo 219811 222907 := bstep (se 1 (by rfl) ⟨167180, by rfl⟩ : syracuseStep 222907 = 334361) B334361
theorem B452297 : Blo 219811 452297 := bstep (se 2 (by rfl) ⟨169611, by rfl⟩ : syracuseStep 452297 = 339223) B339223
theorem B845549 : Blo 219811 845549 := bstep (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) B317081
theorem B222983 : Blo 219811 222983 := bstep (se 1 (by rfl) ⟨167237, by rfl⟩ : syracuseStep 222983 = 334475) B334475
theorem B222991 : Blo 219811 222991 := bstep (se 1 (by rfl) ⟨167243, by rfl⟩ : syracuseStep 222991 = 334487) B334487
theorem B223035 : Blo 219811 223035 := bstep (se 1 (by rfl) ⟨167276, by rfl⟩ : syracuseStep 223035 = 334553) B334553
theorem B14444405 : Blo 219811 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B223111 : Blo 219811 223111 := bstep (se 1 (by rfl) ⟨167333, by rfl⟩ : syracuseStep 223111 = 334667) B334667
theorem B223119 : Blo 219811 223119 := bstep (se 1 (by rfl) ⟨167339, by rfl⟩ : syracuseStep 223119 = 334679) B334679
theorem B4646807 : Blo 219811 4646807 := bstep (se 1 (by rfl) ⟨3485105, by rfl⟩ : syracuseStep 4646807 = 6970211) B6970211
theorem B223163 : Blo 219811 223163 := bstep (se 1 (by rfl) ⟨167372, by rfl⟩ : syracuseStep 223163 = 334745) B334745
theorem B223239 : Blo 219811 223239 := bstep (se 1 (by rfl) ⟨167429, by rfl⟩ : syracuseStep 223239 = 334859) B334859
theorem B223247 : Blo 219811 223247 := bstep (se 1 (by rfl) ⟨167435, by rfl⟩ : syracuseStep 223247 = 334871) B334871
theorem B223291 : Blo 219811 223291 := bstep (se 1 (by rfl) ⟨167468, by rfl⟩ : syracuseStep 223291 = 334937) B334937
theorem B10152053 : Blo 219811 10152053 := bstep (se 5 (by rfl) ⟨475877, by rfl⟩ : syracuseStep 10152053 = 951755) B951755
theorem B223367 : Blo 219811 223367 := bstep (se 1 (by rfl) ⟨167525, by rfl⟩ : syracuseStep 223367 = 335051) B335051
theorem B223375 : Blo 219811 223375 := bstep (se 1 (by rfl) ⟨167531, by rfl⟩ : syracuseStep 223375 = 335063) B335063
theorem B223419 : Blo 219811 223419 := bstep (se 1 (by rfl) ⟨167564, by rfl⟩ : syracuseStep 223419 = 335129) B335129
theorem B420041 : Blo 219811 420041 := bstep (se 2 (by rfl) ⟨157515, by rfl⟩ : syracuseStep 420041 = 315031) B315031
theorem B1599689 : Blo 219811 1599689 := bstep (se 2 (by rfl) ⟨599883, by rfl⟩ : syracuseStep 1599689 = 1199767) B1199767
theorem B223495 : Blo 219811 223495 := bstep (se 1 (by rfl) ⟨167621, by rfl⟩ : syracuseStep 223495 = 335243) B335243
theorem B747791 : Blo 219811 747791 := bstep (se 1 (by rfl) ⟨560843, by rfl⟩ : syracuseStep 747791 = 1121687) B1121687
theorem B223503 : Blo 219811 223503 := bstep (se 1 (by rfl) ⟨167627, by rfl⟩ : syracuseStep 223503 = 335255) B335255
theorem B223547 : Blo 219811 223547 := bstep (se 1 (by rfl) ⟨167660, by rfl⟩ : syracuseStep 223547 = 335321) B335321
theorem B223623 : Blo 219811 223623 := bstep (se 1 (by rfl) ⟨167717, by rfl⟩ : syracuseStep 223623 = 335435) B335435
theorem B223631 : Blo 219811 223631 := bstep (se 1 (by rfl) ⟨167723, by rfl⟩ : syracuseStep 223631 = 335447) B335447
theorem B846233 : Blo 219811 846233 := bstep (se 2 (by rfl) ⟨317337, by rfl⟩ : syracuseStep 846233 = 634675) B634675
theorem B223675 : Blo 219811 223675 := bstep (se 1 (by rfl) ⟨167756, by rfl⟩ : syracuseStep 223675 = 335513) B335513
theorem B223751 : Blo 219811 223751 := bstep (se 1 (by rfl) ⟨167813, by rfl⟩ : syracuseStep 223751 = 335627) B335627
theorem B223759 : Blo 219811 223759 := bstep (se 1 (by rfl) ⟨167819, by rfl⟩ : syracuseStep 223759 = 335639) B335639
theorem B748061 : Blo 219811 748061 := bstep (se 3 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 748061 = 280523) B280523
theorem B223803 : Blo 219811 223803 := bstep (se 1 (by rfl) ⟨167852, by rfl⟩ : syracuseStep 223803 = 335705) B335705
theorem B4025123 : Blo 219811 4025123 := bstep (se 1 (by rfl) ⟨3018842, by rfl⟩ : syracuseStep 4025123 = 6037685) B6037685
theorem B2845529 : Blo 219811 2845529 := bstep (se 2 (by rfl) ⟨1067073, by rfl⟩ : syracuseStep 2845529 = 2134147) B2134147
theorem B355627 : Blo 219811 355627 := bstep (se 1 (by rfl) ⟨266720, by rfl⟩ : syracuseStep 355627 = 533441) B533441
theorem B847219 : Blo 219811 847219 := bstep (se 1 (by rfl) ⟨635414, by rfl⟩ : syracuseStep 847219 = 1270829) B1270829
theorem B1273745 : Blo 219811 1273745 := bstep (se 2 (by rfl) ⟨477654, by rfl⟩ : syracuseStep 1273745 = 955309) B955309
theorem B749465 : Blo 219811 749465 := bstep (se 2 (by rfl) ⟨281049, by rfl⟩ : syracuseStep 749465 = 562099) B562099
theorem B946187 : Blo 219811 946187 := bstep (se 1 (by rfl) ⟨709640, by rfl⟩ : syracuseStep 946187 = 1419281) B1419281
theorem B422023 : Blo 219811 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B1208591 : Blo 219811 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B1274201 : Blo 219811 1274201 := bstep (se 2 (by rfl) ⟨477825, by rfl⟩ : syracuseStep 1274201 = 955651) B955651
theorem B1012121 : Blo 219811 1012121 := bstep (se 2 (by rfl) ⟨379545, by rfl⟩ : syracuseStep 1012121 = 759091) B759091
theorem B750167 : Blo 219811 750167 := bstep (se 1 (by rfl) ⟨562625, by rfl⟩ : syracuseStep 750167 = 1125251) B1125251
theorem B750653 : Blo 219811 750653 := bstep (se 3 (by rfl) ⟨140747, by rfl⟩ : syracuseStep 750653 = 281495) B281495
theorem B9172099 : Blo 219811 9172099 := bstep (se 1 (by rfl) ⟨6879074, by rfl⟩ : syracuseStep 9172099 = 13758149) B13758149
theorem B357691 : Blo 219811 357691 := bstep (se 1 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 357691 = 536537) B536537
theorem B849437 : Blo 219811 849437 := bstep (se 3 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 849437 = 318539) B318539
theorem B357947 : Blo 219811 357947 := bstep (se 1 (by rfl) ⟨268460, by rfl⟩ : syracuseStep 357947 = 536921) B536921
theorem B423625 : Blo 219811 423625 := bstep (se 2 (by rfl) ⟨158859, by rfl⟩ : syracuseStep 423625 = 317719) B317719
theorem B2029349 : Blo 219811 2029349 := bstep (se 4 (by rfl) ⟨190251, by rfl⟩ : syracuseStep 2029349 = 380503) B380503
theorem B2520881 : Blo 219811 2520881 := bstep (se 2 (by rfl) ⟨945330, by rfl⟩ : syracuseStep 2520881 = 1890661) B1890661
theorem B1669409 : Blo 219811 1669409 := bstep (se 2 (by rfl) ⟨626028, by rfl⟩ : syracuseStep 1669409 = 1252057) B1252057
theorem B752057 : Blo 219811 752057 := bstep (se 2 (by rfl) ⟨282021, by rfl⟩ : syracuseStep 752057 = 564043) B564043
theorem B2259533 : Blo 219811 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B1440449 : Blo 219811 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B424649 : Blo 219811 424649 := bstep (se 2 (by rfl) ⟨159243, by rfl⟩ : syracuseStep 424649 = 318487) B318487
theorem B1506251 : Blo 219811 1506251 := bstep (se 1 (by rfl) ⟨1129688, by rfl⟩ : syracuseStep 1506251 = 2259377) B2259377
theorem B752651 : Blo 219811 752651 := bstep (se 1 (by rfl) ⟨564488, by rfl⟩ : syracuseStep 752651 = 1128977) B1128977
theorem B1375255 : Blo 219811 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B752759 : Blo 219811 752759 := bstep (se 1 (by rfl) ⟨564569, by rfl⟩ : syracuseStep 752759 = 1129139) B1129139
theorem B1670381 : Blo 219811 1670381 := bstep (se 3 (by rfl) ⟨313196, by rfl⟩ : syracuseStep 1670381 = 626393) B626393
theorem B753353 : Blo 219811 753353 := bstep (se 2 (by rfl) ⟨282507, by rfl⟩ : syracuseStep 753353 = 565015) B565015
theorem B556915 : Blo 219811 556915 := bstep (se 1 (by rfl) ⟨417686, by rfl⟩ : syracuseStep 556915 = 835373) B835373
theorem B360377 : Blo 219811 360377 := bstep (se 2 (by rfl) ⟨135141, by rfl⟩ : syracuseStep 360377 = 270283) B270283
theorem B754163 : Blo 219811 754163 := bstep (se 1 (by rfl) ⟨565622, by rfl⟩ : syracuseStep 754163 = 1131245) B1131245
theorem B361207 : Blo 219811 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B1409795 : Blo 219811 1409795 := bstep (se 1 (by rfl) ⟨1057346, by rfl⟩ : syracuseStep 1409795 = 2114693) B2114693
theorem B1114883 : Blo 219811 1114883 := bstep (se 1 (by rfl) ⟨836162, by rfl⟩ : syracuseStep 1114883 = 1672325) B1672325
theorem B557999 : Blo 219811 557999 := bstep (se 1 (by rfl) ⟨418499, by rfl⟩ : syracuseStep 557999 = 836999) B836999
theorem B754703 : Blo 219811 754703 := bstep (se 1 (by rfl) ⟨566027, by rfl⟩ : syracuseStep 754703 = 1132055) B1132055
theorem B3671563 : Blo 219811 3671563 := bstep (se 1 (by rfl) ⟨2753672, by rfl⟩ : syracuseStep 3671563 = 5507345) B5507345
theorem B3409451 : Blo 219811 3409451 := bstep (se 1 (by rfl) ⟨2557088, by rfl⟩ : syracuseStep 3409451 = 5114177) B5114177
theorem B755297 : Blo 219811 755297 := bstep (se 2 (by rfl) ⟨283236, by rfl⟩ : syracuseStep 755297 = 566473) B566473
theorem B1410797 : Blo 219811 1410797 := bstep (se 3 (by rfl) ⟨264524, by rfl⟩ : syracuseStep 1410797 = 529049) B529049
theorem B329807 : Blo 219811 329807 := bstep (se 1 (by rfl) ⟨247355, by rfl⟩ : syracuseStep 329807 = 494711) B494711
theorem B559183 : Blo 219811 559183 := bstep (se 1 (by rfl) ⟨419387, by rfl⟩ : syracuseStep 559183 = 838775) B838775
theorem B1673297 : Blo 219811 1673297 := bstep (se 2 (by rfl) ⟨627486, by rfl⟩ : syracuseStep 1673297 = 1254973) B1254973
theorem B329927 : Blo 219811 329927 := bstep (se 1 (by rfl) ⟨247445, by rfl⟩ : syracuseStep 329927 = 494891) B494891
theorem B1804517 : Blo 219811 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B1116503 : Blo 219811 1116503 := bstep (se 1 (by rfl) ⟨837377, by rfl⟩ : syracuseStep 1116503 = 1674755) B1674755
theorem B330089 : Blo 219811 330089 := bstep (se 2 (by rfl) ⟨123783, by rfl⟩ : syracuseStep 330089 = 247567) B247567
theorem B330167 : Blo 219811 330167 := bstep (se 1 (by rfl) ⟨247625, by rfl⟩ : syracuseStep 330167 = 495251) B495251
theorem B330203 : Blo 219811 330203 := bstep (se 1 (by rfl) ⟨247652, by rfl⟩ : syracuseStep 330203 = 495305) B495305
theorem B559831 : Blo 219811 559831 := bstep (se 1 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 559831 = 839747) B839747
theorem B330671 : Blo 219811 330671 := bstep (se 1 (by rfl) ⟨248003, by rfl⟩ : syracuseStep 330671 = 496007) B496007
theorem B560135 : Blo 219811 560135 := bstep (se 1 (by rfl) ⟨420101, by rfl⟩ : syracuseStep 560135 = 840203) B840203
theorem B330761 : Blo 219811 330761 := bstep (se 2 (by rfl) ⟨124035, by rfl⟩ : syracuseStep 330761 = 248071) B248071
theorem B330791 : Blo 219811 330791 := bstep (se 1 (by rfl) ⟨248093, by rfl⟩ : syracuseStep 330791 = 496187) B496187
theorem B756793 : Blo 219811 756793 := bstep (se 2 (by rfl) ⟨283797, by rfl⟩ : syracuseStep 756793 = 567595) B567595
theorem B330875 : Blo 219811 330875 := bstep (se 1 (by rfl) ⟨248156, by rfl⟩ : syracuseStep 330875 = 496313) B496313
theorem B331001 : Blo 219811 331001 := bstep (se 2 (by rfl) ⟨124125, by rfl⟩ : syracuseStep 331001 = 248251) B248251
theorem B331103 : Blo 219811 331103 := bstep (se 1 (by rfl) ⟨248327, by rfl⟩ : syracuseStep 331103 = 496655) B496655
theorem B265567 : Blo 219811 265567 := bstep (se 1 (by rfl) ⟨199175, by rfl⟩ : syracuseStep 265567 = 398351) B398351
theorem B331115 : Blo 219811 331115 := bstep (se 1 (by rfl) ⟨248336, by rfl⟩ : syracuseStep 331115 = 496673) B496673
theorem B396731 : Blo 219811 396731 := bstep (se 1 (by rfl) ⟨297548, by rfl⟩ : syracuseStep 396731 = 595097) B595097
theorem B626201 : Blo 219811 626201 := bstep (se 2 (by rfl) ⟨234825, by rfl⟩ : syracuseStep 626201 = 469651) B469651
theorem B495143 : Blo 219811 495143 := bstep (se 1 (by rfl) ⟨371357, by rfl⟩ : syracuseStep 495143 = 742715) B742715
theorem B331343 : Blo 219811 331343 := bstep (se 1 (by rfl) ⟨248507, by rfl⟩ : syracuseStep 331343 = 497015) B497015
theorem B8261297 : Blo 219811 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B331463 : Blo 219811 331463 := bstep (se 1 (by rfl) ⟨248597, by rfl⟩ : syracuseStep 331463 = 497195) B497195
theorem B1412923 : Blo 219811 1412923 := bstep (se 1 (by rfl) ⟨1059692, by rfl⟩ : syracuseStep 1412923 = 2119385) B2119385
theorem B331625 : Blo 219811 331625 := bstep (se 2 (by rfl) ⟨124359, by rfl⟩ : syracuseStep 331625 = 248719) B248719
theorem B495467 : Blo 219811 495467 := bstep (se 1 (by rfl) ⟨371600, by rfl⟩ : syracuseStep 495467 = 743201) B743201
theorem B495521 : Blo 219811 495521 := bstep (se 2 (by rfl) ⟨185820, by rfl⟩ : syracuseStep 495521 = 371641) B371641
theorem B331703 : Blo 219811 331703 := bstep (se 1 (by rfl) ⟨248777, by rfl⟩ : syracuseStep 331703 = 497555) B497555
theorem B331739 : Blo 219811 331739 := bstep (se 1 (by rfl) ⟨248804, by rfl⟩ : syracuseStep 331739 = 497609) B497609
theorem B495863 : Blo 219811 495863 := bstep (se 1 (by rfl) ⟨371897, by rfl⟩ : syracuseStep 495863 = 743795) B743795
theorem B332207 : Blo 219811 332207 := bstep (se 1 (by rfl) ⟨249155, by rfl⟩ : syracuseStep 332207 = 498311) B498311
theorem B528905 : Blo 219811 528905 := bstep (se 2 (by rfl) ⟨198339, by rfl⟩ : syracuseStep 528905 = 396679) B396679
theorem B332297 : Blo 219811 332297 := bstep (se 2 (by rfl) ⟨124611, by rfl⟩ : syracuseStep 332297 = 249223) B249223
theorem B332327 : Blo 219811 332327 := bstep (se 1 (by rfl) ⟨249245, by rfl⟩ : syracuseStep 332327 = 498491) B498491
theorem B332411 : Blo 219811 332411 := bstep (se 1 (by rfl) ⟨249308, by rfl⟩ : syracuseStep 332411 = 498617) B498617
theorem B332537 : Blo 219811 332537 := bstep (se 2 (by rfl) ⟨124701, by rfl⟩ : syracuseStep 332537 = 249403) B249403
theorem B496457 : Blo 219811 496457 := bstep (se 2 (by rfl) ⟨186171, by rfl⟩ : syracuseStep 496457 = 372343) B372343
theorem B332639 : Blo 219811 332639 := bstep (se 1 (by rfl) ⟨249479, by rfl⟩ : syracuseStep 332639 = 498959) B498959
theorem B332651 : Blo 219811 332651 := bstep (se 1 (by rfl) ⟨249488, by rfl⟩ : syracuseStep 332651 = 498977) B498977
theorem B1282999 : Blo 219811 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B1807379 : Blo 219811 1807379 := bstep (se 1 (by rfl) ⟨1355534, by rfl⟩ : syracuseStep 1807379 = 2711069) B2711069
theorem B332879 : Blo 219811 332879 := bstep (se 1 (by rfl) ⟨249659, by rfl⟩ : syracuseStep 332879 = 499319) B499319
theorem B332999 : Blo 219811 332999 := bstep (se 1 (by rfl) ⟨249749, by rfl⟩ : syracuseStep 332999 = 499499) B499499
theorem B562423 : Blo 219811 562423 := bstep (se 1 (by rfl) ⟨421817, by rfl⟩ : syracuseStep 562423 = 843635) B843635
theorem B333161 : Blo 219811 333161 := bstep (se 2 (by rfl) ⟨124935, by rfl⟩ : syracuseStep 333161 = 249871) B249871
theorem B8131985 : Blo 219811 8131985 := bstep (se 2 (by rfl) ⟨3049494, by rfl⟩ : syracuseStep 8131985 = 6098989) B6098989
theorem B333239 : Blo 219811 333239 := bstep (se 1 (by rfl) ⟨249929, by rfl⟩ : syracuseStep 333239 = 499859) B499859
theorem B333275 : Blo 219811 333275 := bstep (se 1 (by rfl) ⟨249956, by rfl⟩ : syracuseStep 333275 = 499913) B499913
theorem B562697 : Blo 219811 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B562727 : Blo 219811 562727 := bstep (se 1 (by rfl) ⟨422045, by rfl⟩ : syracuseStep 562727 = 844091) B844091
theorem B497249 : Blo 219811 497249 := bstep (se 2 (by rfl) ⟨186468, by rfl⟩ : syracuseStep 497249 = 372937) B372937
theorem B530135 : Blo 219811 530135 := bstep (se 1 (by rfl) ⟨397601, by rfl⟩ : syracuseStep 530135 = 795203) B795203
theorem B1120067 : Blo 219811 1120067 := bstep (se 1 (by rfl) ⟨840050, by rfl⟩ : syracuseStep 1120067 = 1680101) B1680101
theorem B563051 : Blo 219811 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B333743 : Blo 219811 333743 := bstep (se 1 (by rfl) ⟨250307, by rfl⟩ : syracuseStep 333743 = 500615) B500615
theorem B497591 : Blo 219811 497591 := bstep (se 1 (by rfl) ⟨373193, by rfl⟩ : syracuseStep 497591 = 746387) B746387
theorem B333833 : Blo 219811 333833 := bstep (se 2 (by rfl) ⟨125187, by rfl⟩ : syracuseStep 333833 = 250375) B250375
theorem B333863 : Blo 219811 333863 := bstep (se 1 (by rfl) ⟨250397, by rfl⟩ : syracuseStep 333863 = 500795) B500795
theorem B333947 : Blo 219811 333947 := bstep (se 1 (by rfl) ⟨250460, by rfl⟩ : syracuseStep 333947 = 500921) B500921
theorem B334073 : Blo 219811 334073 := bstep (se 2 (by rfl) ⟨125277, by rfl⟩ : syracuseStep 334073 = 250555) B250555
theorem B334175 : Blo 219811 334175 := bstep (se 1 (by rfl) ⟨250631, by rfl⟩ : syracuseStep 334175 = 501263) B501263
theorem B334187 : Blo 219811 334187 := bstep (se 1 (by rfl) ⟨250640, by rfl⟩ : syracuseStep 334187 = 501281) B501281
theorem B629117 : Blo 219811 629117 := bstep (se 3 (by rfl) ⟨117959, by rfl⟩ : syracuseStep 629117 = 235919) B235919
theorem B268763 : Blo 219811 268763 := bstep (se 1 (by rfl) ⟨201572, by rfl⟩ : syracuseStep 268763 = 403145) B403145
theorem B301531 : Blo 219811 301531 := bstep (se 1 (by rfl) ⟨226148, by rfl⟩ : syracuseStep 301531 = 452297) B452297
theorem B563699 : Blo 219811 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B498185 : Blo 219811 498185 := bstep (se 2 (by rfl) ⟨186819, by rfl⟩ : syracuseStep 498185 = 373639) B373639
theorem B891425 : Blo 219811 891425 := bstep (se 2 (by rfl) ⟨334284, by rfl⟩ : syracuseStep 891425 = 668569) B668569
theorem B334415 : Blo 219811 334415 := bstep (se 1 (by rfl) ⟨250811, by rfl⟩ : syracuseStep 334415 = 501623) B501623
theorem B334535 : Blo 219811 334535 := bstep (se 1 (by rfl) ⟨250901, by rfl⟩ : syracuseStep 334535 = 501803) B501803
theorem B1678157 : Blo 219811 1678157 := bstep (se 3 (by rfl) ⟨314654, by rfl⟩ : syracuseStep 1678157 = 629309) B629309
theorem B12229465 : Blo 219811 12229465 := bstep (se 2 (by rfl) ⟨4586049, by rfl⟩ : syracuseStep 12229465 = 9172099) B9172099
theorem B498527 : Blo 219811 498527 := bstep (se 1 (by rfl) ⟨373895, by rfl⟩ : syracuseStep 498527 = 747791) B747791
theorem B334697 : Blo 219811 334697 := bstep (se 2 (by rfl) ⟨125511, by rfl⟩ : syracuseStep 334697 = 251023) B251023
theorem B596911 : Blo 219811 596911 := bstep (se 1 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 596911 = 895367) B895367
theorem B334775 : Blo 219811 334775 := bstep (se 1 (by rfl) ⟨251081, by rfl⟩ : syracuseStep 334775 = 502163) B502163
theorem B564155 : Blo 219811 564155 := bstep (se 1 (by rfl) ⟨423116, by rfl⟩ : syracuseStep 564155 = 846233) B846233
theorem B334811 : Blo 219811 334811 := bstep (se 1 (by rfl) ⟨251108, by rfl⟩ : syracuseStep 334811 = 502217) B502217
theorem B498707 : Blo 219811 498707 := bstep (se 1 (by rfl) ⟨374030, by rfl⟩ : syracuseStep 498707 = 748061) B748061
theorem B793847 : Blo 219811 793847 := bstep (se 1 (by rfl) ⟨595385, by rfl⟩ : syracuseStep 793847 = 1190771) B1190771
theorem B4300121 : Blo 219811 4300121 := bstep (se 2 (by rfl) ⟨1612545, by rfl⟩ : syracuseStep 4300121 = 3225091) B3225091
theorem B499049 : Blo 219811 499049 := bstep (se 2 (by rfl) ⟨187143, by rfl⟩ : syracuseStep 499049 = 374287) B374287
theorem B335279 : Blo 219811 335279 := bstep (se 1 (by rfl) ⟨251459, by rfl⟩ : syracuseStep 335279 = 502919) B502919
theorem B9182645 : Blo 219811 9182645 := bstep (se 5 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 9182645 = 860873) B860873
theorem B892397 : Blo 219811 892397 := bstep (se 3 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 892397 = 334649) B334649
theorem B335369 : Blo 219811 335369 := bstep (se 2 (by rfl) ⟨125763, by rfl⟩ : syracuseStep 335369 = 251527) B251527
theorem B335399 : Blo 219811 335399 := bstep (se 1 (by rfl) ⟨251549, by rfl⟩ : syracuseStep 335399 = 503099) B503099
theorem B564833 : Blo 219811 564833 := bstep (se 2 (by rfl) ⟨211812, by rfl⟩ : syracuseStep 564833 = 423625) B423625
theorem B335483 : Blo 219811 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B335609 : Blo 219811 335609 := bstep (se 2 (by rfl) ⟨125853, by rfl⟩ : syracuseStep 335609 = 251707) B251707
theorem B335711 : Blo 219811 335711 := bstep (se 1 (by rfl) ⟨251783, by rfl⟩ : syracuseStep 335711 = 503567) B503567
theorem B499643 : Blo 219811 499643 := bstep (se 1 (by rfl) ⟨374732, by rfl⟩ : syracuseStep 499643 = 749465) B749465
theorem B630791 : Blo 219811 630791 := bstep (se 1 (by rfl) ⟨473093, by rfl⟩ : syracuseStep 630791 = 946187) B946187
theorem B499769 : Blo 219811 499769 := bstep (se 2 (by rfl) ⟨187413, by rfl⟩ : syracuseStep 499769 = 374827) B374827
theorem B500111 : Blo 219811 500111 := bstep (se 1 (by rfl) ⟨375083, by rfl⟩ : syracuseStep 500111 = 750167) B750167
theorem B893629 : Blo 219811 893629 := bstep (se 3 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 893629 = 335111) B335111
theorem B500435 : Blo 219811 500435 := bstep (se 1 (by rfl) ⟨375326, by rfl⟩ : syracuseStep 500435 = 750653) B750653
theorem B1123145 : Blo 219811 1123145 := bstep (se 2 (by rfl) ⟨421179, by rfl⟩ : syracuseStep 1123145 = 842359) B842359
theorem B271199 : Blo 219811 271199 := bstep (se 1 (by rfl) ⟨203399, by rfl⟩ : syracuseStep 271199 = 406799) B406799
theorem B566291 : Blo 219811 566291 := bstep (se 1 (by rfl) ⟨424718, by rfl⟩ : syracuseStep 566291 = 849437) B849437
theorem B238631 : Blo 219811 238631 := bstep (se 1 (by rfl) ⟨178973, by rfl⟩ : syracuseStep 238631 = 357947) B357947
theorem B2040881 : Blo 219811 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B1352899 : Blo 219811 1352899 := bstep (se 1 (by rfl) ⟨1014674, by rfl⟩ : syracuseStep 1352899 = 2029349) B2029349
theorem B1680587 : Blo 219811 1680587 := bstep (se 1 (by rfl) ⟨1260440, by rfl⟩ : syracuseStep 1680587 = 2520881) B2520881
theorem B796009 : Blo 219811 796009 := bstep (se 2 (by rfl) ⟨298503, by rfl⟩ : syracuseStep 796009 = 597007) B597007
theorem B501371 : Blo 219811 501371 := bstep (se 1 (by rfl) ⟨376028, by rfl⟩ : syracuseStep 501371 = 752057) B752057
theorem B501497 : Blo 219811 501497 := bstep (se 2 (by rfl) ⟨188061, by rfl⟩ : syracuseStep 501497 = 376123) B376123
theorem B960299 : Blo 219811 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B501767 : Blo 219811 501767 := bstep (se 1 (by rfl) ⟨376325, by rfl⟩ : syracuseStep 501767 = 752651) B752651
theorem B403465 : Blo 219811 403465 := bstep (se 2 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 403465 = 302599) B302599
theorem B501839 : Blo 219811 501839 := bstep (se 1 (by rfl) ⟨376379, by rfl⟩ : syracuseStep 501839 = 752759) B752759
theorem B1124441 : Blo 219811 1124441 := bstep (se 2 (by rfl) ⟨421665, by rfl⟩ : syracuseStep 1124441 = 843331) B843331
theorem B403553 : Blo 219811 403553 := bstep (se 2 (by rfl) ⟨151332, by rfl⟩ : syracuseStep 403553 = 302665) B302665
theorem B633217 : Blo 219811 633217 := bstep (se 2 (by rfl) ⟨237456, by rfl⟩ : syracuseStep 633217 = 474913) B474913
theorem B502235 : Blo 219811 502235 := bstep (se 1 (by rfl) ⟨376676, by rfl⟩ : syracuseStep 502235 = 753353) B753353
theorem B371209 : Blo 219811 371209 := bstep (se 2 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 371209 = 278407) B278407
theorem B240251 : Blo 219811 240251 := bstep (se 1 (by rfl) ⟨180188, by rfl⟩ : syracuseStep 240251 = 360377) B360377
theorem B371371 : Blo 219811 371371 := bstep (se 1 (by rfl) ⟨278528, by rfl⟩ : syracuseStep 371371 = 557057) B557057
theorem B633707 : Blo 219811 633707 := bstep (se 1 (by rfl) ⟨475280, by rfl⟩ : syracuseStep 633707 = 950561) B950561
theorem B502703 : Blo 219811 502703 := bstep (se 1 (by rfl) ⟨377027, by rfl⟩ : syracuseStep 502703 = 754055) B754055
theorem B371675 : Blo 219811 371675 := bstep (se 1 (by rfl) ⟨278756, by rfl⟩ : syracuseStep 371675 = 557513) B557513
theorem B1420253 : Blo 219811 1420253 := bstep (se 3 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 1420253 = 532595) B532595
theorem B1420355 : Blo 219811 1420355 := bstep (se 1 (by rfl) ⟨1065266, by rfl⟩ : syracuseStep 1420355 = 2130533) B2130533
theorem B502955 : Blo 219811 502955 := bstep (se 1 (by rfl) ⟨377216, by rfl⟩ : syracuseStep 502955 = 754433) B754433
theorem B371911 : Blo 219811 371911 := bstep (se 1 (by rfl) ⟨278933, by rfl⟩ : syracuseStep 371911 = 557867) B557867
theorem B372073 : Blo 219811 372073 := bstep (se 2 (by rfl) ⟨139527, by rfl⟩ : syracuseStep 372073 = 279055) B279055
theorem B1060499 : Blo 219811 1060499 := bstep (se 1 (by rfl) ⟨795374, by rfl⟩ : syracuseStep 1060499 = 1590749) B1590749
theorem B503495 : Blo 219811 503495 := bstep (se 1 (by rfl) ⟨377621, by rfl⟩ : syracuseStep 503495 = 755243) B755243
theorem B372667 : Blo 219811 372667 := bstep (se 1 (by rfl) ⟨279500, by rfl⟩ : syracuseStep 372667 = 559001) B559001
theorem B372775 : Blo 219811 372775 := bstep (se 1 (by rfl) ⟨279581, by rfl⟩ : syracuseStep 372775 = 559163) B559163
theorem B373099 : Blo 219811 373099 := bstep (se 1 (by rfl) ⟨279824, by rfl⟩ : syracuseStep 373099 = 559649) B559649
theorem B602587 : Blo 219811 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B1192457 : Blo 219811 1192457 := bstep (se 2 (by rfl) ⟨447171, by rfl⟩ : syracuseStep 1192457 = 894343) B894343
theorem B1618717 : Blo 219811 1618717 := bstep (se 3 (by rfl) ⟨303509, by rfl⟩ : syracuseStep 1618717 = 607019) B607019
theorem B1258415 : Blo 219811 1258415 := bstep (se 1 (by rfl) ⟨943811, by rfl⟩ : syracuseStep 1258415 = 1887623) B1887623
theorem B504839 : Blo 219811 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B374159 : Blo 219811 374159 := bstep (se 1 (by rfl) ⟨280619, by rfl⟩ : syracuseStep 374159 = 561239) B561239
theorem B4634003 : Blo 219811 4634003 := bstep (se 1 (by rfl) ⟨3475502, by rfl⟩ : syracuseStep 4634003 = 6951005) B6951005
theorem B374395 : Blo 219811 374395 := bstep (se 1 (by rfl) ⟨280796, by rfl⟩ : syracuseStep 374395 = 561593) B561593
theorem B603863 : Blo 219811 603863 := bstep (se 1 (by rfl) ⟨452897, by rfl⟩ : syracuseStep 603863 = 905795) B905795
theorem B604091 : Blo 219811 604091 := bstep (se 1 (by rfl) ⟨453068, by rfl⟩ : syracuseStep 604091 = 906137) B906137
theorem B1128455 : Blo 219811 1128455 := bstep (se 1 (by rfl) ⟨846341, by rfl⟩ : syracuseStep 1128455 = 1692683) B1692683
theorem B375259 : Blo 219811 375259 := bstep (se 1 (by rfl) ⟨281444, by rfl⟩ : syracuseStep 375259 = 562889) B562889
theorem B1686419 : Blo 219811 1686419 := bstep (se 1 (by rfl) ⟨1264814, by rfl⟩ : syracuseStep 1686419 = 2529629) B2529629
theorem B474169 : Blo 219811 474169 := bstep (se 2 (by rfl) ⟨177813, by rfl⟩ : syracuseStep 474169 = 355627) B355627
theorem B1260623 : Blo 219811 1260623 := bstep (se 1 (by rfl) ⟨945467, by rfl⟩ : syracuseStep 1260623 = 1890935) B1890935
theorem B375887 : Blo 219811 375887 := bstep (se 1 (by rfl) ⟨281915, by rfl⟩ : syracuseStep 375887 = 563831) B563831
theorem B1129625 : Blo 219811 1129625 := bstep (se 2 (by rfl) ⟨423609, by rfl⟩ : syracuseStep 1129625 = 847219) B847219
theorem B1359127 : Blo 219811 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B2014607 : Blo 219811 2014607 := bstep (se 1 (by rfl) ⟨1510955, by rfl⟩ : syracuseStep 2014607 = 3021911) B3021911
theorem B474511 : Blo 219811 474511 := bstep (se 1 (by rfl) ⟨355883, by rfl⟩ : syracuseStep 474511 = 711767) B711767
theorem B1687391 : Blo 219811 1687391 := bstep (se 1 (by rfl) ⟨1265543, by rfl⟩ : syracuseStep 1687391 = 2531087) B2531087
theorem B2703223 : Blo 219811 2703223 := bstep (se 1 (by rfl) ⟨2027417, by rfl⟩ : syracuseStep 2703223 = 4054835) B4054835
theorem B376751 : Blo 219811 376751 := bstep (se 1 (by rfl) ⟨282563, by rfl⟩ : syracuseStep 376751 = 565127) B565127
theorem B704591 : Blo 219811 704591 := bstep (se 1 (by rfl) ⟨528443, by rfl⟩ : syracuseStep 704591 = 1056887) B1056887
theorem B377183 : Blo 219811 377183 := bstep (se 1 (by rfl) ⟨282887, by rfl⟩ : syracuseStep 377183 = 565775) B565775
theorem B278959 : Blo 219811 278959 := bstep (se 1 (by rfl) ⟨209219, by rfl⟩ : syracuseStep 278959 = 418439) B418439
theorem B836041 : Blo 219811 836041 := bstep (se 2 (by rfl) ⟨313515, by rfl⟩ : syracuseStep 836041 = 627031) B627031
theorem B1786349 : Blo 219811 1786349 := bstep (se 3 (by rfl) ⟨334940, by rfl⟩ : syracuseStep 1786349 = 669881) B669881
theorem B836345 : Blo 219811 836345 := bstep (se 2 (by rfl) ⟨313629, by rfl⟩ : syracuseStep 836345 = 627259) B627259
theorem B836513 : Blo 219811 836513 := bstep (se 2 (by rfl) ⟨313692, by rfl⟩ : syracuseStep 836513 = 627385) B627385
theorem B836527 : Blo 219811 836527 := bstep (se 1 (by rfl) ⟨627395, by rfl⟩ : syracuseStep 836527 = 1254791) B1254791
theorem B3097871 : Blo 219811 3097871 := bstep (se 1 (by rfl) ⟨2323403, by rfl⟩ : syracuseStep 3097871 = 4646807) B4646807
theorem B640381 : Blo 219811 640381 := bstep (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) B240143
theorem B6768035 : Blo 219811 6768035 := bstep (se 1 (by rfl) ⟨5076026, by rfl⟩ : syracuseStep 6768035 = 10152053) B10152053
theorem B280027 : Blo 219811 280027 := bstep (se 1 (by rfl) ⟨210020, by rfl⟩ : syracuseStep 280027 = 420041) B420041
theorem B1066459 : Blo 219811 1066459 := bstep (se 1 (by rfl) ⟨799844, by rfl⟩ : syracuseStep 1066459 = 1599689) B1599689
theorem B673289 : Blo 219811 673289 := bstep (se 2 (by rfl) ⟨252483, by rfl⟩ : syracuseStep 673289 = 504967) B504967
theorem B378425 : Blo 219811 378425 := bstep (se 2 (by rfl) ⟨141909, by rfl⟩ : syracuseStep 378425 = 283819) B283819
theorem B247495 : Blo 219811 247495 := bstep (se 1 (by rfl) ⟨185621, by rfl⟩ : syracuseStep 247495 = 371243) B371243
theorem B476921 : Blo 219811 476921 := bstep (se 2 (by rfl) ⟨178845, by rfl⟩ : syracuseStep 476921 = 357691) B357691
theorem B706333 : Blo 219811 706333 := bstep (se 3 (by rfl) ⟨132437, by rfl⟩ : syracuseStep 706333 = 264875) B264875
theorem B837485 : Blo 219811 837485 := bstep (se 3 (by rfl) ⟨157028, by rfl⟩ : syracuseStep 837485 = 314057) B314057
theorem B837803 : Blo 219811 837803 := bstep (se 1 (by rfl) ⟨628352, by rfl⟩ : syracuseStep 837803 = 1256705) B1256705
theorem B248359 : Blo 219811 248359 := bstep (se 1 (by rfl) ⟨186269, by rfl⟩ : syracuseStep 248359 = 372539) B372539
theorem B4410085 : Blo 219811 4410085 := bstep (se 4 (by rfl) ⟨413445, by rfl⟩ : syracuseStep 4410085 = 826891) B826891
theorem B805727 : Blo 219811 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B5393297 : Blo 219811 5393297 := bstep (se 2 (by rfl) ⟨2022486, by rfl⟩ : syracuseStep 5393297 = 4044973) B4044973
theorem B674747 : Blo 219811 674747 := bstep (se 1 (by rfl) ⟨506060, by rfl⟩ : syracuseStep 674747 = 1012121) B1012121
theorem B708281 : Blo 219811 708281 := bstep (se 2 (by rfl) ⟨265605, by rfl⟩ : syracuseStep 708281 = 531211) B531211
theorem B1888271 : Blo 219811 1888271 := bstep (se 1 (by rfl) ⟨1416203, by rfl⟩ : syracuseStep 1888271 = 2832407) B2832407
theorem B1626193 : Blo 219811 1626193 := bstep (se 2 (by rfl) ⟨609822, by rfl⟩ : syracuseStep 1626193 = 1219645) B1219645
theorem B315515 : Blo 219811 315515 := bstep (se 1 (by rfl) ⟨236636, by rfl⟩ : syracuseStep 315515 = 473273) B473273
theorem B249979 : Blo 219811 249979 := bstep (se 1 (by rfl) ⟨187484, by rfl⟩ : syracuseStep 249979 = 374969) B374969
theorem B3592421 : Blo 219811 3592421 := bstep (se 4 (by rfl) ⟨336789, by rfl⟩ : syracuseStep 3592421 = 673579) B673579
theorem B283099 : Blo 219811 283099 := bstep (se 1 (by rfl) ⟨212324, by rfl⟩ : syracuseStep 283099 = 424649) B424649
theorem B250447 : Blo 219811 250447 := bstep (se 1 (by rfl) ⟨187835, by rfl⟩ : syracuseStep 250447 = 375671) B375671
theorem B1004167 : Blo 219811 1004167 := bstep (se 1 (by rfl) ⟨753125, by rfl⟩ : syracuseStep 1004167 = 1506251) B1506251
theorem B840401 : Blo 219811 840401 := bstep (se 2 (by rfl) ⟨315150, by rfl⟩ : syracuseStep 840401 = 630301) B630301
theorem B316153 : Blo 219811 316153 := bstep (se 2 (by rfl) ⟨118557, by rfl⟩ : syracuseStep 316153 = 237115) B237115
theorem B250843 : Blo 219811 250843 := bstep (se 1 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 250843 = 376265) B376265
theorem B840719 : Blo 219811 840719 := bstep (se 1 (by rfl) ⟨630539, by rfl⟩ : syracuseStep 840719 = 1261079) B1261079
theorem B742553 : Blo 219811 742553 := bstep (se 2 (by rfl) ⟨278457, by rfl⟩ : syracuseStep 742553 = 556915) B556915
theorem B382201 : Blo 219811 382201 := bstep (se 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) B286651
theorem B4904339 : Blo 219811 4904339 := bstep (se 1 (by rfl) ⟨3678254, by rfl⟩ : syracuseStep 4904339 = 7356509) B7356509
theorem B251311 : Blo 219811 251311 := bstep (se 1 (by rfl) ⟨188483, by rfl⟩ : syracuseStep 251311 = 376967) B376967
theorem B1267163 : Blo 219811 1267163 := bstep (se 1 (by rfl) ⟨950372, by rfl⟩ : syracuseStep 1267163 = 1900745) B1900745
theorem B710153 : Blo 219811 710153 := bstep (se 2 (by rfl) ⟨266307, by rfl⟩ : syracuseStep 710153 = 532615) B532615
theorem B906785 : Blo 219811 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B1693223 : Blo 219811 1693223 := bstep (se 1 (by rfl) ⟨1269917, by rfl⟩ : syracuseStep 1693223 = 2539835) B2539835
theorem B251743 : Blo 219811 251743 := bstep (se 1 (by rfl) ⟨188807, by rfl⟩ : syracuseStep 251743 = 377615) B377615
theorem B743275 : Blo 219811 743275 := bstep (se 1 (by rfl) ⟨557456, by rfl⟩ : syracuseStep 743275 = 1114913) B1114913
theorem B2545667 : Blo 219811 2545667 := bstep (se 1 (by rfl) ⟨1909250, by rfl⟩ : syracuseStep 2545667 = 3818501) B3818501
theorem B4053149 : Blo 219811 4053149 := bstep (se 3 (by rfl) ⟨759965, by rfl⟩ : syracuseStep 4053149 = 1519931) B1519931
theorem B317639 : Blo 219811 317639 := bstep (se 1 (by rfl) ⟨238229, by rfl⟩ : syracuseStep 317639 = 476459) B476459
theorem B743741 : Blo 219811 743741 := bstep (se 3 (by rfl) ⟨139451, by rfl⟩ : syracuseStep 743741 = 278903) B278903
theorem B481889 : Blo 219811 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B219823 : Blo 219811 219823 := bstep (se 1 (by rfl) ⟨164867, by rfl⟩ : syracuseStep 219823 = 329735) B329735
theorem B219847 : Blo 219811 219847 := bstep (se 1 (by rfl) ⟨164885, by rfl⟩ : syracuseStep 219847 = 329771) B329771
theorem B219867 : Blo 219811 219867 := bstep (se 1 (by rfl) ⟨164900, by rfl⟩ : syracuseStep 219867 = 329801) B329801
theorem B1432349 : Blo 219811 1432349 := bstep (se 3 (by rfl) ⟨268565, by rfl⟩ : syracuseStep 1432349 = 537131) B537131
theorem B219943 : Blo 219811 219943 := bstep (se 1 (by rfl) ⟨164957, by rfl⟩ : syracuseStep 219943 = 329915) B329915
theorem B219983 : Blo 219811 219983 := bstep (se 1 (by rfl) ⟨164987, by rfl⟩ : syracuseStep 219983 = 329975) B329975
theorem B219999 : Blo 219811 219999 := bstep (se 1 (by rfl) ⟨164999, by rfl⟩ : syracuseStep 219999 = 329999) B329999
theorem B220027 : Blo 219811 220027 := bstep (se 1 (by rfl) ⟨165020, by rfl⟩ : syracuseStep 220027 = 330041) B330041
theorem B220079 : Blo 219811 220079 := bstep (se 1 (by rfl) ⟨165059, by rfl⟩ : syracuseStep 220079 = 330119) B330119
theorem B220103 : Blo 219811 220103 := bstep (se 1 (by rfl) ⟨165077, by rfl⟩ : syracuseStep 220103 = 330155) B330155
theorem B220123 : Blo 219811 220123 := bstep (se 1 (by rfl) ⟨165092, by rfl⟩ : syracuseStep 220123 = 330185) B330185
theorem B220199 : Blo 219811 220199 := bstep (se 1 (by rfl) ⟨165149, by rfl⟩ : syracuseStep 220199 = 330299) B330299
theorem B220239 : Blo 219811 220239 := bstep (se 1 (by rfl) ⟨165179, by rfl⟩ : syracuseStep 220239 = 330359) B330359
theorem B842831 : Blo 219811 842831 := bstep (se 1 (by rfl) ⟨632123, by rfl⟩ : syracuseStep 842831 = 1264247) B1264247
theorem B220255 : Blo 219811 220255 := bstep (se 1 (by rfl) ⟨165191, by rfl⟩ : syracuseStep 220255 = 330383) B330383
theorem B220283 : Blo 219811 220283 := bstep (se 1 (by rfl) ⟨165212, by rfl⟩ : syracuseStep 220283 = 330425) B330425
theorem B744605 : Blo 219811 744605 := bstep (se 3 (by rfl) ⟨139613, by rfl⟩ : syracuseStep 744605 = 279227) B279227
theorem B220335 : Blo 219811 220335 := bstep (se 1 (by rfl) ⟨165251, by rfl⟩ : syracuseStep 220335 = 330503) B330503
theorem B1629377 : Blo 219811 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B220359 : Blo 219811 220359 := bstep (se 1 (by rfl) ⟨165269, by rfl⟩ : syracuseStep 220359 = 330539) B330539
theorem B220379 : Blo 219811 220379 := bstep (se 1 (by rfl) ⟨165284, by rfl⟩ : syracuseStep 220379 = 330569) B330569
theorem B220455 : Blo 219811 220455 := bstep (se 1 (by rfl) ⟨165341, by rfl⟩ : syracuseStep 220455 = 330683) B330683
theorem B220495 : Blo 219811 220495 := bstep (se 1 (by rfl) ⟨165371, by rfl⟩ : syracuseStep 220495 = 330743) B330743
theorem B220511 : Blo 219811 220511 := bstep (se 1 (by rfl) ⟨165383, by rfl⟩ : syracuseStep 220511 = 330767) B330767
theorem B220539 : Blo 219811 220539 := bstep (se 1 (by rfl) ⟨165404, by rfl⟩ : syracuseStep 220539 = 330809) B330809
theorem B220591 : Blo 219811 220591 := bstep (se 1 (by rfl) ⟨165443, by rfl⟩ : syracuseStep 220591 = 330887) B330887
theorem B220615 : Blo 219811 220615 := bstep (se 1 (by rfl) ⟨165461, by rfl⟩ : syracuseStep 220615 = 330923) B330923
theorem B220635 : Blo 219811 220635 := bstep (se 1 (by rfl) ⟨165476, by rfl⟩ : syracuseStep 220635 = 330953) B330953
theorem B220711 : Blo 219811 220711 := bstep (se 1 (by rfl) ⟨165533, by rfl⟩ : syracuseStep 220711 = 331067) B331067
theorem B220751 : Blo 219811 220751 := bstep (se 1 (by rfl) ⟨165563, by rfl⟩ : syracuseStep 220751 = 331127) B331127
theorem B220767 : Blo 219811 220767 := bstep (se 1 (by rfl) ⟨165575, by rfl⟩ : syracuseStep 220767 = 331151) B331151
theorem B220795 : Blo 219811 220795 := bstep (se 1 (by rfl) ⟨165596, by rfl⟩ : syracuseStep 220795 = 331193) B331193
theorem B1269371 : Blo 219811 1269371 := bstep (se 1 (by rfl) ⟨952028, by rfl⟩ : syracuseStep 1269371 = 1904057) B1904057
theorem B220847 : Blo 219811 220847 := bstep (se 1 (by rfl) ⟨165635, by rfl⟩ : syracuseStep 220847 = 331271) B331271
theorem B745145 : Blo 219811 745145 := bstep (se 2 (by rfl) ⟨279429, by rfl⟩ : syracuseStep 745145 = 558859) B558859
theorem B220871 : Blo 219811 220871 := bstep (se 1 (by rfl) ⟨165653, by rfl⟩ : syracuseStep 220871 = 331307) B331307
theorem B220891 : Blo 219811 220891 := bstep (se 1 (by rfl) ⟨165668, by rfl⟩ : syracuseStep 220891 = 331337) B331337
theorem B5791493 : Blo 219811 5791493 := bstep (se 4 (by rfl) ⟨542952, by rfl⟩ : syracuseStep 5791493 = 1085905) B1085905
theorem B220967 : Blo 219811 220967 := bstep (se 1 (by rfl) ⟨165725, by rfl⟩ : syracuseStep 220967 = 331451) B331451
theorem B221007 : Blo 219811 221007 := bstep (se 1 (by rfl) ⟨165755, by rfl⟩ : syracuseStep 221007 = 331511) B331511
theorem B221023 : Blo 219811 221023 := bstep (se 1 (by rfl) ⟨165767, by rfl⟩ : syracuseStep 221023 = 331535) B331535
theorem B221051 : Blo 219811 221051 := bstep (se 1 (by rfl) ⟨165788, by rfl⟩ : syracuseStep 221051 = 331577) B331577
theorem B221103 : Blo 219811 221103 := bstep (se 1 (by rfl) ⟨165827, by rfl⟩ : syracuseStep 221103 = 331655) B331655
theorem B2842553 : Blo 219811 2842553 := bstep (se 2 (by rfl) ⟨1065957, by rfl⟩ : syracuseStep 2842553 = 2131915) B2131915
theorem B221127 : Blo 219811 221127 := bstep (se 1 (by rfl) ⟨165845, by rfl⟩ : syracuseStep 221127 = 331691) B331691
theorem B221147 : Blo 219811 221147 := bstep (se 1 (by rfl) ⟨165860, by rfl⟩ : syracuseStep 221147 = 331721) B331721
theorem B221223 : Blo 219811 221223 := bstep (se 1 (by rfl) ⟨165917, by rfl⟩ : syracuseStep 221223 = 331835) B331835
theorem B221263 : Blo 219811 221263 := bstep (se 1 (by rfl) ⟨165947, by rfl⟩ : syracuseStep 221263 = 331895) B331895
theorem B221279 : Blo 219811 221279 := bstep (se 1 (by rfl) ⟨165959, by rfl⟩ : syracuseStep 221279 = 331919) B331919
theorem B221307 : Blo 219811 221307 := bstep (se 1 (by rfl) ⟨165980, by rfl⟩ : syracuseStep 221307 = 331961) B331961
theorem B221359 : Blo 219811 221359 := bstep (se 1 (by rfl) ⟨166019, by rfl⟩ : syracuseStep 221359 = 332039) B332039
theorem B221383 : Blo 219811 221383 := bstep (se 1 (by rfl) ⟨166037, by rfl⟩ : syracuseStep 221383 = 332075) B332075
theorem B221403 : Blo 219811 221403 := bstep (se 1 (by rfl) ⟨166052, by rfl⟩ : syracuseStep 221403 = 332105) B332105
theorem B745739 : Blo 219811 745739 := bstep (se 1 (by rfl) ⟨559304, by rfl⟩ : syracuseStep 745739 = 1118609) B1118609
theorem B221479 : Blo 219811 221479 := bstep (se 1 (by rfl) ⟨166109, by rfl⟩ : syracuseStep 221479 = 332219) B332219
theorem B221519 : Blo 219811 221519 := bstep (se 1 (by rfl) ⟨166139, by rfl⟩ : syracuseStep 221519 = 332279) B332279
theorem B221535 : Blo 219811 221535 := bstep (se 1 (by rfl) ⟨166151, by rfl⟩ : syracuseStep 221535 = 332303) B332303
theorem B221563 : Blo 219811 221563 := bstep (se 1 (by rfl) ⟨166172, by rfl⟩ : syracuseStep 221563 = 332345) B332345
theorem B221615 : Blo 219811 221615 := bstep (se 1 (by rfl) ⟨166211, by rfl⟩ : syracuseStep 221615 = 332423) B332423
theorem B221639 : Blo 219811 221639 := bstep (se 1 (by rfl) ⟨166229, by rfl⟩ : syracuseStep 221639 = 332459) B332459
theorem B221659 : Blo 219811 221659 := bstep (se 1 (by rfl) ⟨166244, by rfl⟩ : syracuseStep 221659 = 332489) B332489
theorem B746009 : Blo 219811 746009 := bstep (se 2 (by rfl) ⟨279753, by rfl⟩ : syracuseStep 746009 = 559507) B559507
theorem B221735 : Blo 219811 221735 := bstep (se 1 (by rfl) ⟨166301, by rfl⟩ : syracuseStep 221735 = 332603) B332603
theorem B221775 : Blo 219811 221775 := bstep (se 1 (by rfl) ⟨166331, by rfl⟩ : syracuseStep 221775 = 332663) B332663
theorem B221791 : Blo 219811 221791 := bstep (se 1 (by rfl) ⟨166343, by rfl⟩ : syracuseStep 221791 = 332687) B332687
theorem B221819 : Blo 219811 221819 := bstep (se 1 (by rfl) ⟨166364, by rfl⟩ : syracuseStep 221819 = 332729) B332729
theorem B221871 : Blo 219811 221871 := bstep (se 1 (by rfl) ⟨166403, by rfl⟩ : syracuseStep 221871 = 332807) B332807
theorem B221895 : Blo 219811 221895 := bstep (se 1 (by rfl) ⟨166421, by rfl⟩ : syracuseStep 221895 = 332843) B332843
theorem B942803 : Blo 219811 942803 := bstep (se 1 (by rfl) ⟨707102, by rfl⟩ : syracuseStep 942803 = 1414205) B1414205
theorem B221915 : Blo 219811 221915 := bstep (se 1 (by rfl) ⟨166436, by rfl⟩ : syracuseStep 221915 = 332873) B332873
theorem B221991 : Blo 219811 221991 := bstep (se 1 (by rfl) ⟨166493, by rfl⟩ : syracuseStep 221991 = 332987) B332987
theorem B3629873 : Blo 219811 3629873 := bstep (se 2 (by rfl) ⟨1361202, by rfl⟩ : syracuseStep 3629873 = 2722405) B2722405
theorem B222031 : Blo 219811 222031 := bstep (se 1 (by rfl) ⟨166523, by rfl⟩ : syracuseStep 222031 = 333047) B333047
theorem B222047 : Blo 219811 222047 := bstep (se 1 (by rfl) ⟨166535, by rfl⟩ : syracuseStep 222047 = 333071) B333071
theorem B222075 : Blo 219811 222075 := bstep (se 1 (by rfl) ⟨166556, by rfl⟩ : syracuseStep 222075 = 333113) B333113
theorem B222127 : Blo 219811 222127 := bstep (se 1 (by rfl) ⟨166595, by rfl⟩ : syracuseStep 222127 = 333191) B333191
theorem B222151 : Blo 219811 222151 := bstep (se 1 (by rfl) ⟨166613, by rfl⟩ : syracuseStep 222151 = 333227) B333227
theorem B222171 : Blo 219811 222171 := bstep (se 1 (by rfl) ⟨166628, by rfl⟩ : syracuseStep 222171 = 333257) B333257
theorem B1893395 : Blo 219811 1893395 := bstep (se 1 (by rfl) ⟨1420046, by rfl⟩ : syracuseStep 1893395 = 2840093) B2840093
theorem B222247 : Blo 219811 222247 := bstep (se 1 (by rfl) ⟨166685, by rfl⟩ : syracuseStep 222247 = 333371) B333371
theorem B222287 : Blo 219811 222287 := bstep (se 1 (by rfl) ⟨166715, by rfl⟩ : syracuseStep 222287 = 333431) B333431
theorem B222303 : Blo 219811 222303 := bstep (se 1 (by rfl) ⟨166727, by rfl⟩ : syracuseStep 222303 = 333455) B333455
theorem B713843 : Blo 219811 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B222331 : Blo 219811 222331 := bstep (se 1 (by rfl) ⟨166748, by rfl⟩ : syracuseStep 222331 = 333497) B333497
theorem B2155673 : Blo 219811 2155673 := bstep (se 2 (by rfl) ⟨808377, by rfl⟩ : syracuseStep 2155673 = 1616755) B1616755
theorem B222383 : Blo 219811 222383 := bstep (se 1 (by rfl) ⟨166787, by rfl⟩ : syracuseStep 222383 = 333575) B333575
theorem B222407 : Blo 219811 222407 := bstep (se 1 (by rfl) ⟨166805, by rfl⟩ : syracuseStep 222407 = 333611) B333611
theorem B222427 : Blo 219811 222427 := bstep (se 1 (by rfl) ⟨166820, by rfl⟩ : syracuseStep 222427 = 333641) B333641
theorem B1074455 : Blo 219811 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B222503 : Blo 219811 222503 := bstep (se 1 (by rfl) ⟨166877, by rfl⟩ : syracuseStep 222503 = 333755) B333755
theorem B222543 : Blo 219811 222543 := bstep (se 1 (by rfl) ⟨166907, by rfl⟩ : syracuseStep 222543 = 333815) B333815
theorem B222559 : Blo 219811 222559 := bstep (se 1 (by rfl) ⟨166919, by rfl⟩ : syracuseStep 222559 = 333839) B333839
theorem B353641 : Blo 219811 353641 := bstep (se 2 (by rfl) ⟨132615, by rfl⟩ : syracuseStep 353641 = 265231) B265231
theorem B222587 : Blo 219811 222587 := bstep (se 1 (by rfl) ⟨166940, by rfl⟩ : syracuseStep 222587 = 333881) B333881
theorem B1009039 : Blo 219811 1009039 := bstep (se 1 (by rfl) ⟨756779, by rfl⟩ : syracuseStep 1009039 = 1513559) B1513559
theorem B222639 : Blo 219811 222639 := bstep (se 1 (by rfl) ⟨166979, by rfl⟩ : syracuseStep 222639 = 333959) B333959
theorem B222663 : Blo 219811 222663 := bstep (se 1 (by rfl) ⟨166997, by rfl⟩ : syracuseStep 222663 = 333995) B333995
theorem B845275 : Blo 219811 845275 := bstep (se 1 (by rfl) ⟨633956, by rfl⟩ : syracuseStep 845275 = 1267913) B1267913
theorem B222683 : Blo 219811 222683 := bstep (se 1 (by rfl) ⟨167012, by rfl⟩ : syracuseStep 222683 = 334025) B334025
theorem B222759 : Blo 219811 222759 := bstep (se 1 (by rfl) ⟨167069, by rfl⟩ : syracuseStep 222759 = 334139) B334139
theorem B222799 : Blo 219811 222799 := bstep (se 1 (by rfl) ⟨167099, by rfl⟩ : syracuseStep 222799 = 334199) B334199
theorem B222815 : Blo 219811 222815 := bstep (se 1 (by rfl) ⟨167111, by rfl⟩ : syracuseStep 222815 = 334223) B334223
theorem B222843 : Blo 219811 222843 := bstep (se 1 (by rfl) ⟨167132, by rfl⟩ : syracuseStep 222843 = 334265) B334265
theorem B747143 : Blo 219811 747143 := bstep (se 1 (by rfl) ⟨560357, by rfl⟩ : syracuseStep 747143 = 1120715) B1120715
theorem B222895 : Blo 219811 222895 := bstep (se 1 (by rfl) ⟨167171, by rfl⟩ : syracuseStep 222895 = 334343) B334343
theorem B747197 : Blo 219811 747197 := bstep (se 3 (by rfl) ⟨140099, by rfl⟩ : syracuseStep 747197 = 280199) B280199
theorem B222919 : Blo 219811 222919 := bstep (se 1 (by rfl) ⟨167189, by rfl⟩ : syracuseStep 222919 = 334379) B334379
theorem B222939 : Blo 219811 222939 := bstep (se 1 (by rfl) ⟨167204, by rfl⟩ : syracuseStep 222939 = 334409) B334409
theorem B1631981 : Blo 219811 1631981 := bstep (se 3 (by rfl) ⟨305996, by rfl⟩ : syracuseStep 1631981 = 611993) B611993
theorem B223015 : Blo 219811 223015 := bstep (se 1 (by rfl) ⟨167261, by rfl⟩ : syracuseStep 223015 = 334523) B334523
theorem B223055 : Blo 219811 223055 := bstep (se 1 (by rfl) ⟨167291, by rfl⟩ : syracuseStep 223055 = 334583) B334583
theorem B747359 : Blo 219811 747359 := bstep (se 1 (by rfl) ⟨560519, by rfl⟩ : syracuseStep 747359 = 1121039) B1121039
theorem B223071 : Blo 219811 223071 := bstep (se 1 (by rfl) ⟨167303, by rfl⟩ : syracuseStep 223071 = 334607) B334607
theorem B223099 : Blo 219811 223099 := bstep (se 1 (by rfl) ⟨167324, by rfl⟩ : syracuseStep 223099 = 334649) B334649
theorem B223151 : Blo 219811 223151 := bstep (se 1 (by rfl) ⟨167363, by rfl⟩ : syracuseStep 223151 = 334727) B334727
theorem B223175 : Blo 219811 223175 := bstep (se 1 (by rfl) ⟨167381, by rfl⟩ : syracuseStep 223175 = 334763) B334763
theorem B1632209 : Blo 219811 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B223195 : Blo 219811 223195 := bstep (se 1 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 223195 = 334793) B334793
theorem B747521 : Blo 219811 747521 := bstep (se 2 (by rfl) ⟨280320, by rfl⟩ : syracuseStep 747521 = 560641) B560641
theorem B223271 : Blo 219811 223271 := bstep (se 1 (by rfl) ⟨167453, by rfl⟩ : syracuseStep 223271 = 334907) B334907
theorem B419897 : Blo 219811 419897 := bstep (se 2 (by rfl) ⟨157461, by rfl⟩ : syracuseStep 419897 = 314923) B314923
theorem B223311 : Blo 219811 223311 := bstep (se 1 (by rfl) ⟨167483, by rfl⟩ : syracuseStep 223311 = 334967) B334967
theorem B223327 : Blo 219811 223327 := bstep (se 1 (by rfl) ⟨167495, by rfl⟩ : syracuseStep 223327 = 334991) B334991
theorem B223355 : Blo 219811 223355 := bstep (se 1 (by rfl) ⟨167516, by rfl⟩ : syracuseStep 223355 = 335033) B335033
theorem B223407 : Blo 219811 223407 := bstep (se 1 (by rfl) ⟨167555, by rfl⟩ : syracuseStep 223407 = 335111) B335111
theorem B223431 : Blo 219811 223431 := bstep (se 1 (by rfl) ⟨167573, by rfl⟩ : syracuseStep 223431 = 335147) B335147
theorem B223451 : Blo 219811 223451 := bstep (se 1 (by rfl) ⟨167588, by rfl⟩ : syracuseStep 223451 = 335177) B335177
theorem B1599745 : Blo 219811 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B223527 : Blo 219811 223527 := bstep (se 1 (by rfl) ⟨167645, by rfl⟩ : syracuseStep 223527 = 335291) B335291
theorem B223567 : Blo 219811 223567 := bstep (se 1 (by rfl) ⟨167675, by rfl⟩ : syracuseStep 223567 = 335351) B335351
theorem B223583 : Blo 219811 223583 := bstep (se 1 (by rfl) ⟨167687, by rfl⟩ : syracuseStep 223583 = 335375) B335375
theorem B223611 : Blo 219811 223611 := bstep (se 1 (by rfl) ⟨167708, by rfl⟩ : syracuseStep 223611 = 335417) B335417
theorem B223663 : Blo 219811 223663 := bstep (se 1 (by rfl) ⟨167747, by rfl⟩ : syracuseStep 223663 = 335495) B335495
theorem B223687 : Blo 219811 223687 := bstep (se 1 (by rfl) ⟨167765, by rfl⟩ : syracuseStep 223687 = 335531) B335531
theorem B846281 : Blo 219811 846281 := bstep (se 2 (by rfl) ⟨317355, by rfl⟩ : syracuseStep 846281 = 634711) B634711
theorem B223707 : Blo 219811 223707 := bstep (se 1 (by rfl) ⟨167780, by rfl⟩ : syracuseStep 223707 = 335561) B335561
theorem B223783 : Blo 219811 223783 := bstep (se 1 (by rfl) ⟨167837, by rfl⟩ : syracuseStep 223783 = 335675) B335675
theorem B846521 : Blo 219811 846521 := bstep (se 2 (by rfl) ⟨317445, by rfl⟩ : syracuseStep 846521 = 634891) B634891
theorem B846551 : Blo 219811 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B748331 : Blo 219811 748331 := bstep (se 1 (by rfl) ⟨561248, by rfl⟩ : syracuseStep 748331 = 1122497) B1122497
theorem B1207315 : Blo 219811 1207315 := bstep (se 1 (by rfl) ⟨905486, by rfl⟩ : syracuseStep 1207315 = 1810973) B1810973
theorem B748601 : Blo 219811 748601 := bstep (se 2 (by rfl) ⟨280725, by rfl⟩ : syracuseStep 748601 = 561451) B561451
theorem B748925 : Blo 219811 748925 := bstep (se 3 (by rfl) ⟨140423, by rfl⟩ : syracuseStep 748925 = 280847) B280847
theorem B19131875 : Blo 219811 19131875 := bstep (se 1 (by rfl) ⟨14348906, by rfl⟩ : syracuseStep 19131875 = 28697813) B28697813
theorem B421499 : Blo 219811 421499 := bstep (se 1 (by rfl) ⟨316124, by rfl⟩ : syracuseStep 421499 = 632249) B632249
theorem B749195 : Blo 219811 749195 := bstep (se 1 (by rfl) ⟨561896, by rfl⟩ : syracuseStep 749195 = 1123793) B1123793
theorem B945863 : Blo 219811 945863 := bstep (se 1 (by rfl) ⟨709397, by rfl⟩ : syracuseStep 945863 = 1418795) B1418795
theorem B454391 : Blo 219811 454391 := bstep (se 1 (by rfl) ⟨340793, by rfl⟩ : syracuseStep 454391 = 681587) B681587
theorem B9629603 : Blo 219811 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B17592227 : Blo 219811 17592227 := bstep (se 1 (by rfl) ⟨13194170, by rfl⟩ : syracuseStep 17592227 = 26388341) B26388341
theorem B1798159 : Blo 219811 1798159 := bstep (se 1 (by rfl) ⟨1348619, by rfl⟩ : syracuseStep 1798159 = 2697239) B2697239
theorem B421985 : Blo 219811 421985 := bstep (se 2 (by rfl) ⟨158244, by rfl⟩ : syracuseStep 421985 = 316489) B316489
theorem B6025421 : Blo 219811 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B946561 : Blo 219811 946561 := bstep (se 2 (by rfl) ⟨354960, by rfl⟩ : syracuseStep 946561 = 709921) B709921
theorem B422327 : Blo 219811 422327 := bstep (se 1 (by rfl) ⟨316745, by rfl⟩ : syracuseStep 422327 = 633491) B633491
theorem B2683415 : Blo 219811 2683415 := bstep (se 1 (by rfl) ⟨2012561, by rfl⟩ : syracuseStep 2683415 = 4025123) B4025123
theorem B750113 : Blo 219811 750113 := bstep (se 2 (by rfl) ⟨281292, by rfl⟩ : syracuseStep 750113 = 562585) B562585
theorem B356903 : Blo 219811 356903 := bstep (se 1 (by rfl) ⟨267677, by rfl⟩ : syracuseStep 356903 = 535355) B535355
theorem B1897019 : Blo 219811 1897019 := bstep (se 1 (by rfl) ⟨1422764, by rfl⟩ : syracuseStep 1897019 = 2845529) B2845529
theorem B750329 : Blo 219811 750329 := bstep (se 2 (by rfl) ⟨281373, by rfl⟩ : syracuseStep 750329 = 562747) B562747
theorem B422729 : Blo 219811 422729 := bstep (se 2 (by rfl) ⟨158523, by rfl⟩ : syracuseStep 422729 = 317047) B317047
theorem B750599 : Blo 219811 750599 := bstep (se 1 (by rfl) ⟨562949, by rfl⟩ : syracuseStep 750599 = 1125899) B1125899
theorem B750707 : Blo 219811 750707 := bstep (se 1 (by rfl) ⟨563030, by rfl⟩ : syracuseStep 750707 = 1126061) B1126061
theorem B849163 : Blo 219811 849163 := bstep (se 1 (by rfl) ⟨636872, by rfl⟩ : syracuseStep 849163 = 1273745) B1273745
theorem B750977 : Blo 219811 750977 := bstep (se 2 (by rfl) ⟨281616, by rfl⟩ : syracuseStep 750977 = 563233) B563233
theorem B1340837 : Blo 219811 1340837 := bstep (se 4 (by rfl) ⟨125703, by rfl⟩ : syracuseStep 1340837 = 251407) B251407
theorem B423443 : Blo 219811 423443 := bstep (se 1 (by rfl) ⟨317582, by rfl⟩ : syracuseStep 423443 = 635165) B635165
theorem B423481 : Blo 219811 423481 := bstep (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) B317611
theorem B849467 : Blo 219811 849467 := bstep (se 1 (by rfl) ⟨637100, by rfl⟩ : syracuseStep 849467 = 1274201) B1274201
theorem B1799819 : Blo 219811 1799819 := bstep (se 1 (by rfl) ⟨1349864, by rfl⟩ : syracuseStep 1799819 = 2699729) B2699729
theorem B423785 : Blo 219811 423785 := bstep (se 2 (by rfl) ⟨158919, by rfl⟩ : syracuseStep 423785 = 317839) B317839
theorem B358319 : Blo 219811 358319 := bstep (se 1 (by rfl) ⟨268739, by rfl⟩ : syracuseStep 358319 = 537479) B537479
theorem B751787 : Blo 219811 751787 := bstep (se 1 (by rfl) ⟨563840, by rfl⟩ : syracuseStep 751787 = 1127681) B1127681
theorem B752327 : Blo 219811 752327 := bstep (se 1 (by rfl) ⟨564245, by rfl⟩ : syracuseStep 752327 = 1128491) B1128491
theorem B1833673 : Blo 219811 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B2849525 : Blo 219811 2849525 := bstep (se 5 (by rfl) ⟨133571, by rfl⟩ : syracuseStep 2849525 = 267143) B267143
theorem B1112939 : Blo 219811 1112939 := bstep (se 1 (by rfl) ⟨834704, by rfl⟩ : syracuseStep 1112939 = 1669409) B1669409
theorem B359311 : Blo 219811 359311 := bstep (se 1 (by rfl) ⟨269483, by rfl⟩ : syracuseStep 359311 = 538967) B538967
theorem B1899409 : Blo 219811 1899409 := bstep (se 2 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 1899409 = 1424557) B1424557
theorem B425321 : Blo 219811 425321 := bstep (se 2 (by rfl) ⟨159495, by rfl⟩ : syracuseStep 425321 = 318991) B318991
theorem B1113587 : Blo 219811 1113587 := bstep (se 1 (by rfl) ⟨835190, by rfl⟩ : syracuseStep 1113587 = 1670381) B1670381
theorem B753191 : Blo 219811 753191 := bstep (se 1 (by rfl) ⟨564893, by rfl⟩ : syracuseStep 753191 = 1129787) B1129787
theorem B753299 : Blo 219811 753299 := bstep (se 1 (by rfl) ⟨564974, by rfl⟩ : syracuseStep 753299 = 1129949) B1129949
theorem B556895 : Blo 219811 556895 := bstep (se 1 (by rfl) ⟨417671, by rfl⟩ : syracuseStep 556895 = 835343) B835343
theorem B753515 : Blo 219811 753515 := bstep (se 1 (by rfl) ⟨565136, by rfl⟩ : syracuseStep 753515 = 1130273) B1130273
theorem B753569 : Blo 219811 753569 := bstep (se 2 (by rfl) ⟨282588, by rfl⟩ : syracuseStep 753569 = 565177) B565177
theorem B557563 : Blo 219811 557563 := bstep (se 1 (by rfl) ⟨418172, by rfl⟩ : syracuseStep 557563 = 836345) B836345
theorem B1114721 : Blo 219811 1114721 := bstep (se 2 (by rfl) ⟨418020, by rfl⟩ : syracuseStep 1114721 = 836041) B836041
theorem B557675 : Blo 219811 557675 := bstep (se 1 (by rfl) ⟨418256, by rfl⟩ : syracuseStep 557675 = 836513) B836513
theorem B2065247 : Blo 219811 2065247 := bstep (se 1 (by rfl) ⟨1548935, by rfl⟩ : syracuseStep 2065247 = 3097871) B3097871
theorem B1115369 : Blo 219811 1115369 := bstep (se 2 (by rfl) ⟨418263, by rfl⟩ : syracuseStep 1115369 = 836527) B836527
theorem B558323 : Blo 219811 558323 := bstep (se 1 (by rfl) ⟨418742, by rfl⟩ : syracuseStep 558323 = 837485) B837485
theorem B1115531 : Blo 219811 1115531 := bstep (se 1 (by rfl) ⟨836648, by rfl⟩ : syracuseStep 1115531 = 1673297) B1673297
theorem B558535 : Blo 219811 558535 := bstep (se 1 (by rfl) ⟨418901, by rfl⟩ : syracuseStep 558535 = 837803) B837803
theorem B1803865 : Blo 219811 1803865 := bstep (se 2 (by rfl) ⟨676449, by rfl⟩ : syracuseStep 1803865 = 1352899) B1352899
theorem B853841 : Blo 219811 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B1345385 : Blo 219811 1345385 := bstep (se 2 (by rfl) ⟨504519, by rfl⟩ : syracuseStep 1345385 = 1009039) B1009039
theorem B723197 : Blo 219811 723197 := bstep (se 3 (by rfl) ⟨135599, by rfl⟩ : syracuseStep 723197 = 271199) B271199
theorem B329993 : Blo 219811 329993 := bstep (se 2 (by rfl) ⟨123747, by rfl⟩ : syracuseStep 329993 = 247495) B247495
theorem B264487 : Blo 219811 264487 := bstep (se 1 (by rfl) ⟨198365, by rfl⟩ : syracuseStep 264487 = 396731) B396731
theorem B330095 : Blo 219811 330095 := bstep (se 1 (by rfl) ⟨247571, by rfl⟩ : syracuseStep 330095 = 495143) B495143
theorem B5507531 : Blo 219811 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B330311 : Blo 219811 330311 := bstep (se 1 (by rfl) ⟨247733, by rfl⟩ : syracuseStep 330311 = 495467) B495467
theorem B330347 : Blo 219811 330347 := bstep (se 1 (by rfl) ⟨247760, by rfl⟩ : syracuseStep 330347 = 495521) B495521
theorem B5442349 : Blo 219811 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B2394947 : Blo 219811 2394947 := bstep (se 1 (by rfl) ⟨1796210, by rfl⟩ : syracuseStep 2394947 = 3592421) B3592421
theorem B330575 : Blo 219811 330575 := bstep (se 1 (by rfl) ⟨247931, by rfl⟩ : syracuseStep 330575 = 495863) B495863
theorem B2132993 : Blo 219811 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B560267 : Blo 219811 560267 := bstep (se 1 (by rfl) ⟨420200, by rfl⟩ : syracuseStep 560267 = 840401) B840401
theorem B330971 : Blo 219811 330971 := bstep (se 1 (by rfl) ⟨248228, by rfl⟩ : syracuseStep 330971 = 496457) B496457
theorem B494945 : Blo 219811 494945 := bstep (se 2 (by rfl) ⟨185604, by rfl⟩ : syracuseStep 494945 = 371209) B371209
theorem B560479 : Blo 219811 560479 := bstep (se 1 (by rfl) ⟨420359, by rfl⟩ : syracuseStep 560479 = 840719) B840719
theorem B331145 : Blo 219811 331145 := bstep (se 2 (by rfl) ⟨124179, by rfl⟩ : syracuseStep 331145 = 248359) B248359
theorem B495035 : Blo 219811 495035 := bstep (se 1 (by rfl) ⟨371276, by rfl⟩ : syracuseStep 495035 = 742553) B742553
theorem B495161 : Blo 219811 495161 := bstep (se 2 (by rfl) ⟨185685, by rfl⟩ : syracuseStep 495161 = 371371) B371371
theorem B331499 : Blo 219811 331499 := bstep (se 1 (by rfl) ⟨248624, by rfl⟩ : syracuseStep 331499 = 497249) B497249
theorem B331727 : Blo 219811 331727 := bstep (se 1 (by rfl) ⟨248795, by rfl⟩ : syracuseStep 331727 = 497591) B497591
theorem B1609753 : Blo 219811 1609753 := bstep (se 2 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 1609753 = 1207315) B1207315
theorem B495827 : Blo 219811 495827 := bstep (se 1 (by rfl) ⟨371870, by rfl⟩ : syracuseStep 495827 = 743741) B743741
theorem B495881 : Blo 219811 495881 := bstep (se 2 (by rfl) ⟨185955, by rfl⟩ : syracuseStep 495881 = 371911) B371911
theorem B332123 : Blo 219811 332123 := bstep (se 1 (by rfl) ⟨249092, by rfl⟩ : syracuseStep 332123 = 498185) B498185
theorem B496097 : Blo 219811 496097 := bstep (se 2 (by rfl) ⟨186036, by rfl⟩ : syracuseStep 496097 = 372073) B372073
theorem B954899 : Blo 219811 954899 := bstep (se 1 (by rfl) ⟨716174, by rfl⟩ : syracuseStep 954899 = 1432349) B1432349
theorem B1118771 : Blo 219811 1118771 := bstep (se 1 (by rfl) ⟨839078, by rfl⟩ : syracuseStep 1118771 = 1678157) B1678157
theorem B332351 : Blo 219811 332351 := bstep (se 1 (by rfl) ⟨249263, by rfl⟩ : syracuseStep 332351 = 498527) B498527
theorem B332471 : Blo 219811 332471 := bstep (se 1 (by rfl) ⟨249353, by rfl⟩ : syracuseStep 332471 = 498707) B498707
theorem B561887 : Blo 219811 561887 := bstep (se 1 (by rfl) ⟨421415, by rfl⟩ : syracuseStep 561887 = 842831) B842831
theorem B496403 : Blo 219811 496403 := bstep (se 1 (by rfl) ⟨372302, by rfl⟩ : syracuseStep 496403 = 744605) B744605
theorem B1086251 : Blo 219811 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B332699 : Blo 219811 332699 := bstep (se 1 (by rfl) ⟨249524, by rfl⟩ : syracuseStep 332699 = 499049) B499049
theorem B594931 : Blo 219811 594931 := bstep (se 1 (by rfl) ⟨446198, by rfl⟩ : syracuseStep 594931 = 892397) B892397
theorem B496763 : Blo 219811 496763 := bstep (se 1 (by rfl) ⟨372572, by rfl⟩ : syracuseStep 496763 = 745145) B745145
theorem B496889 : Blo 219811 496889 := bstep (se 2 (by rfl) ⟨186333, by rfl⟩ : syracuseStep 496889 = 372667) B372667
theorem B333095 : Blo 219811 333095 := bstep (se 1 (by rfl) ⟨249821, by rfl⟩ : syracuseStep 333095 = 499643) B499643
theorem B2397545 : Blo 219811 2397545 := bstep (se 2 (by rfl) ⟨899079, by rfl⟩ : syracuseStep 2397545 = 1798159) B1798159
theorem B333179 : Blo 219811 333179 := bstep (se 1 (by rfl) ⟨249884, by rfl⟩ : syracuseStep 333179 = 499769) B499769
theorem B497033 : Blo 219811 497033 := bstep (se 2 (by rfl) ⟨186387, by rfl⟩ : syracuseStep 497033 = 372775) B372775
theorem B2168257 : Blo 219811 2168257 := bstep (se 2 (by rfl) ⟨813096, by rfl⟩ : syracuseStep 2168257 = 1626193) B1626193
theorem B333305 : Blo 219811 333305 := bstep (se 2 (by rfl) ⟨124989, by rfl⟩ : syracuseStep 333305 = 249979) B249979
theorem B497159 : Blo 219811 497159 := bstep (se 1 (by rfl) ⟨372869, by rfl⟩ : syracuseStep 497159 = 745739) B745739
theorem B333407 : Blo 219811 333407 := bstep (se 1 (by rfl) ⟨250055, by rfl⟩ : syracuseStep 333407 = 500111) B500111
theorem B497339 : Blo 219811 497339 := bstep (se 1 (by rfl) ⟨373004, by rfl⟩ : syracuseStep 497339 = 746009) B746009
theorem B628535 : Blo 219811 628535 := bstep (se 1 (by rfl) ⟨471401, by rfl⟩ : syracuseStep 628535 = 942803) B942803
theorem B333623 : Blo 219811 333623 := bstep (se 1 (by rfl) ⟨250217, by rfl⟩ : syracuseStep 333623 = 500435) B500435
theorem B497465 : Blo 219811 497465 := bstep (se 2 (by rfl) ⟨186549, by rfl⟩ : syracuseStep 497465 = 373099) B373099
theorem B333929 : Blo 219811 333929 := bstep (se 2 (by rfl) ⟨125223, by rfl⟩ : syracuseStep 333929 = 250447) B250447
theorem B1120391 : Blo 219811 1120391 := bstep (se 1 (by rfl) ⟨840293, by rfl⟩ : syracuseStep 1120391 = 1680587) B1680587
theorem B334247 : Blo 219811 334247 := bstep (se 1 (by rfl) ⟨250685, by rfl⟩ : syracuseStep 334247 = 501371) B501371
theorem B498095 : Blo 219811 498095 := bstep (se 1 (by rfl) ⟨373571, by rfl⟩ : syracuseStep 498095 = 747143) B747143
theorem B498131 : Blo 219811 498131 := bstep (se 1 (by rfl) ⟨373598, by rfl⟩ : syracuseStep 498131 = 747197) B747197
theorem B1087987 : Blo 219811 1087987 := bstep (se 1 (by rfl) ⟨815990, by rfl⟩ : syracuseStep 1087987 = 1631981) B1631981
theorem B334331 : Blo 219811 334331 := bstep (se 1 (by rfl) ⟨250748, by rfl⟩ : syracuseStep 334331 = 501497) B501497
theorem B498239 : Blo 219811 498239 := bstep (se 1 (by rfl) ⟨373679, by rfl⟩ : syracuseStep 498239 = 747359) B747359
theorem B1710665 : Blo 219811 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B334457 : Blo 219811 334457 := bstep (se 2 (by rfl) ⟨125421, by rfl⟩ : syracuseStep 334457 = 250843) B250843
theorem B2038405 : Blo 219811 2038405 := bstep (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) B382201
theorem B498347 : Blo 219811 498347 := bstep (se 1 (by rfl) ⟨373760, by rfl⟩ : syracuseStep 498347 = 747521) B747521
theorem B334511 : Blo 219811 334511 := bstep (se 1 (by rfl) ⟨250883, by rfl⟩ : syracuseStep 334511 = 501767) B501767
theorem B334559 : Blo 219811 334559 := bstep (se 1 (by rfl) ⟨250919, by rfl⟩ : syracuseStep 334559 = 501839) B501839
theorem B564187 : Blo 219811 564187 := bstep (se 1 (by rfl) ⟨423140, by rfl⟩ : syracuseStep 564187 = 846281) B846281
theorem B334823 : Blo 219811 334823 := bstep (se 1 (by rfl) ⟨251117, by rfl⟩ : syracuseStep 334823 = 502235) B502235
theorem B564347 : Blo 219811 564347 := bstep (se 1 (by rfl) ⟨423260, by rfl⟩ : syracuseStep 564347 = 846521) B846521
theorem B564367 : Blo 219811 564367 := bstep (se 1 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 564367 = 846551) B846551
theorem B498887 : Blo 219811 498887 := bstep (se 1 (by rfl) ⟨374165, by rfl⟩ : syracuseStep 498887 = 748331) B748331
theorem B335081 : Blo 219811 335081 := bstep (se 2 (by rfl) ⟨125655, by rfl⟩ : syracuseStep 335081 = 251311) B251311
theorem B335135 : Blo 219811 335135 := bstep (se 1 (by rfl) ⟨251351, by rfl⟩ : syracuseStep 335135 = 502703) B502703
theorem B499067 : Blo 219811 499067 := bstep (se 1 (by rfl) ⟨374300, by rfl⟩ : syracuseStep 499067 = 748601) B748601
theorem B564641 : Blo 219811 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B335303 : Blo 219811 335303 := bstep (se 1 (by rfl) ⟨251477, by rfl⟩ : syracuseStep 335303 = 502955) B502955
theorem B499193 : Blo 219811 499193 := bstep (se 2 (by rfl) ⟨187197, by rfl⟩ : syracuseStep 499193 = 374395) B374395
theorem B499283 : Blo 219811 499283 := bstep (se 1 (by rfl) ⟨374462, by rfl⟩ : syracuseStep 499283 = 748925) B748925
theorem B12754583 : Blo 219811 12754583 := bstep (se 1 (by rfl) ⟨9565937, by rfl⟩ : syracuseStep 12754583 = 19131875) B19131875
theorem B499463 : Blo 219811 499463 := bstep (se 1 (by rfl) ⟨374597, by rfl⟩ : syracuseStep 499463 = 749195) B749195
theorem B335657 : Blo 219811 335657 := bstep (se 2 (by rfl) ⟨125871, by rfl⟩ : syracuseStep 335657 = 251743) B251743
theorem B630575 : Blo 219811 630575 := bstep (se 1 (by rfl) ⟨472931, by rfl⟩ : syracuseStep 630575 = 945863) B945863
theorem B335663 : Blo 219811 335663 := bstep (se 1 (by rfl) ⟨251747, by rfl⟩ : syracuseStep 335663 = 503495) B503495
theorem B991033 : Blo 219811 991033 := bstep (se 2 (by rfl) ⟨371637, by rfl⟩ : syracuseStep 991033 = 743275) B743275
theorem B794971 : Blo 219811 794971 := bstep (se 1 (by rfl) ⟨596228, by rfl⟩ : syracuseStep 794971 = 1192457) B1192457
theorem B500075 : Blo 219811 500075 := bstep (se 1 (by rfl) ⟨375056, by rfl⟩ : syracuseStep 500075 = 750113) B750113
theorem B237935 : Blo 219811 237935 := bstep (se 1 (by rfl) ⟨178451, by rfl⟩ : syracuseStep 237935 = 356903) B356903
theorem B500219 : Blo 219811 500219 := bstep (se 1 (by rfl) ⟨375164, by rfl⟩ : syracuseStep 500219 = 750329) B750329
theorem B500345 : Blo 219811 500345 := bstep (se 2 (by rfl) ⟨187629, by rfl⟩ : syracuseStep 500345 = 375259) B375259
theorem B402041 : Blo 219811 402041 := bstep (se 2 (by rfl) ⟨150765, by rfl⟩ : syracuseStep 402041 = 301531) B301531
theorem B336559 : Blo 219811 336559 := bstep (se 1 (by rfl) ⟨252419, by rfl⟩ : syracuseStep 336559 = 504839) B504839
theorem B500399 : Blo 219811 500399 := bstep (se 1 (by rfl) ⟨375299, by rfl⟩ : syracuseStep 500399 = 750599) B750599
theorem B500471 : Blo 219811 500471 := bstep (se 1 (by rfl) ⟨375353, by rfl⟩ : syracuseStep 500471 = 750707) B750707
theorem B500651 : Blo 219811 500651 := bstep (se 1 (by rfl) ⟨375488, by rfl⟩ : syracuseStep 500651 = 750977) B750977
theorem B3089335 : Blo 219811 3089335 := bstep (se 1 (by rfl) ⟨2317001, by rfl⟩ : syracuseStep 3089335 = 4634003) B4634003
theorem B893891 : Blo 219811 893891 := bstep (se 1 (by rfl) ⟨670418, by rfl⟩ : syracuseStep 893891 = 1340837) B1340837
theorem B566311 : Blo 219811 566311 := bstep (se 1 (by rfl) ⟨424733, by rfl⟩ : syracuseStep 566311 = 849467) B849467
theorem B402575 : Blo 219811 402575 := bstep (se 1 (by rfl) ⟨301931, by rfl⟩ : syracuseStep 402575 = 603863) B603863
theorem B2532545 : Blo 219811 2532545 := bstep (se 2 (by rfl) ⟨949704, by rfl⟩ : syracuseStep 2532545 = 1899409) B1899409
theorem B795881 : Blo 219811 795881 := bstep (se 2 (by rfl) ⟨298455, by rfl⟩ : syracuseStep 795881 = 596911) B596911
theorem B238879 : Blo 219811 238879 := bstep (se 1 (by rfl) ⟨179159, by rfl⟩ : syracuseStep 238879 = 358319) B358319
theorem B402727 : Blo 219811 402727 := bstep (se 1 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 402727 = 604091) B604091
theorem B632225 : Blo 219811 632225 := bstep (se 2 (by rfl) ⟨237084, by rfl⟩ : syracuseStep 632225 = 474169) B474169
theorem B501191 : Blo 219811 501191 := bstep (se 1 (by rfl) ⟨375893, by rfl⟩ : syracuseStep 501191 = 751787) B751787
theorem B1812169 : Blo 219811 1812169 := bstep (se 2 (by rfl) ⟨679563, by rfl⟩ : syracuseStep 1812169 = 1359127) B1359127
theorem B2827997 : Blo 219811 2827997 := bstep (se 3 (by rfl) ⟨530249, by rfl⟩ : syracuseStep 2827997 = 1060499) B1060499
theorem B501551 : Blo 219811 501551 := bstep (se 1 (by rfl) ⟨376163, by rfl⟩ : syracuseStep 501551 = 752327) B752327
theorem B632681 : Blo 219811 632681 := bstep (se 2 (by rfl) ⟨237255, by rfl⟩ : syracuseStep 632681 = 474511) B474511
theorem B1124279 : Blo 219811 1124279 := bstep (se 1 (by rfl) ⟨843209, by rfl⟩ : syracuseStep 1124279 = 1686419) B1686419
theorem B17410229 : Blo 219811 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B502127 : Blo 219811 502127 := bstep (se 1 (by rfl) ⟨376595, by rfl⟩ : syracuseStep 502127 = 753191) B753191
theorem B502199 : Blo 219811 502199 := bstep (se 1 (by rfl) ⟨376649, by rfl⟩ : syracuseStep 502199 = 753299) B753299
theorem B371263 : Blo 219811 371263 := bstep (se 1 (by rfl) ⟨278447, by rfl⟩ : syracuseStep 371263 = 556895) B556895
theorem B1124927 : Blo 219811 1124927 := bstep (se 1 (by rfl) ⟨843695, by rfl⟩ : syracuseStep 1124927 = 1687391) B1687391
theorem B502343 : Blo 219811 502343 := bstep (se 1 (by rfl) ⟨376757, by rfl⟩ : syracuseStep 502343 = 753515) B753515
theorem B502379 : Blo 219811 502379 := bstep (se 1 (by rfl) ⟨376784, by rfl⟩ : syracuseStep 502379 = 753569) B753569
theorem B469727 : Blo 219811 469727 := bstep (se 1 (by rfl) ⟨352295, by rfl⟩ : syracuseStep 469727 = 704591) B704591
theorem B1190899 : Blo 219811 1190899 := bstep (se 1 (by rfl) ⟨893174, by rfl⟩ : syracuseStep 1190899 = 1786349) B1786349
theorem B502775 : Blo 219811 502775 := bstep (se 1 (by rfl) ⟨377081, by rfl⟩ : syracuseStep 502775 = 754163) B754163
theorem B371945 : Blo 219811 371945 := bstep (se 2 (by rfl) ⟨139479, by rfl⟩ : syracuseStep 371945 = 278959) B278959
theorem B371999 : Blo 219811 371999 := bstep (se 1 (by rfl) ⟨278999, by rfl⟩ : syracuseStep 371999 = 557999) B557999
theorem B503135 : Blo 219811 503135 := bstep (se 1 (by rfl) ⟨377351, by rfl⟩ : syracuseStep 503135 = 754703) B754703
theorem B1191505 : Blo 219811 1191505 := bstep (se 2 (by rfl) ⟨446814, by rfl⟩ : syracuseStep 1191505 = 893629) B893629
theorem B2272967 : Blo 219811 2272967 := bstep (se 1 (by rfl) ⟨1704725, by rfl⟩ : syracuseStep 2272967 = 3409451) B3409451
theorem B503531 : Blo 219811 503531 := bstep (se 1 (by rfl) ⟨377648, by rfl⟩ : syracuseStep 503531 = 755297) B755297
theorem B7155773 : Blo 219811 7155773 := bstep (se 3 (by rfl) ⟨1341707, by rfl⟩ : syracuseStep 7155773 = 2683415) B2683415
theorem B471521 : Blo 219811 471521 := bstep (se 2 (by rfl) ⟨176820, by rfl⟩ : syracuseStep 471521 = 353641) B353641
theorem B1061345 : Blo 219811 1061345 := bstep (se 2 (by rfl) ⟨398004, by rfl⟩ : syracuseStep 1061345 = 796009) B796009
theorem B373369 : Blo 219811 373369 := bstep (se 2 (by rfl) ⟨140013, by rfl⟩ : syracuseStep 373369 = 280027) B280027
theorem B1421945 : Blo 219811 1421945 := bstep (se 2 (by rfl) ⟨533229, by rfl⟩ : syracuseStep 1421945 = 1066459) B1066459
theorem B1127033 : Blo 219811 1127033 := bstep (se 2 (by rfl) ⟨422637, by rfl⟩ : syracuseStep 1127033 = 845275) B845275
theorem B373423 : Blo 219811 373423 := bstep (se 1 (by rfl) ⟨280067, by rfl⟩ : syracuseStep 373423 = 560135) B560135
theorem B4895417 : Blo 219811 4895417 := bstep (se 2 (by rfl) ⟨1835781, by rfl⟩ : syracuseStep 4895417 = 3671563) B3671563
theorem B9679661 : Blo 219811 9679661 := bstep (se 3 (by rfl) ⟨1814936, by rfl⟩ : syracuseStep 9679661 = 3629873) B3629873
theorem B472187 : Blo 219811 472187 := bstep (se 1 (by rfl) ⟨354140, by rfl⟩ : syracuseStep 472187 = 708281) B708281
theorem B1258847 : Blo 219811 1258847 := bstep (se 1 (by rfl) ⟨944135, by rfl⟩ : syracuseStep 1258847 = 1888271) B1888271
theorem B537953 : Blo 219811 537953 := bstep (se 2 (by rfl) ⟨201732, by rfl⟩ : syracuseStep 537953 = 403465) B403465
theorem B636349 : Blo 219811 636349 := bstep (se 3 (by rfl) ⟨119315, by rfl⟩ : syracuseStep 636349 = 238631) B238631
theorem B5421323 : Blo 219811 5421323 := bstep (se 1 (by rfl) ⟨4065992, by rfl⟩ : syracuseStep 5421323 = 8131985) B8131985
theorem B5880113 : Blo 219811 5880113 := bstep (se 2 (by rfl) ⟨2205042, by rfl⟩ : syracuseStep 5880113 = 4410085) B4410085
theorem B473435 : Blo 219811 473435 := bstep (se 1 (by rfl) ⟨355076, by rfl⟩ : syracuseStep 473435 = 710153) B710153
theorem B375131 : Blo 219811 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B604523 : Blo 219811 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B375151 : Blo 219811 375151 := bstep (se 1 (by rfl) ⟨281363, by rfl⟩ : syracuseStep 375151 = 562727) B562727
theorem B1128815 : Blo 219811 1128815 := bstep (se 1 (by rfl) ⟨846611, by rfl⟩ : syracuseStep 1128815 = 1693223) B1693223
theorem B375367 : Blo 219811 375367 := bstep (se 1 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 375367 = 563051) B563051
theorem B2702099 : Blo 219811 2702099 := bstep (se 1 (by rfl) ⟨2026574, by rfl⟩ : syracuseStep 2702099 = 4053149) B4053149
theorem B52312949 : Blo 219811 52312949 := bstep (se 5 (by rfl) ⟨2452169, by rfl⟩ : syracuseStep 52312949 = 4904339) B4904339
theorem B375799 : Blo 219811 375799 := bstep (se 1 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 375799 = 563699) B563699
theorem B376103 : Blo 219811 376103 := bstep (se 1 (by rfl) ⟨282077, by rfl⟩ : syracuseStep 376103 = 564155) B564155
theorem B2866747 : Blo 219811 2866747 := bstep (se 1 (by rfl) ⟨2150060, by rfl⟩ : syracuseStep 2866747 = 4300121) B4300121
theorem B376555 : Blo 219811 376555 := bstep (se 1 (by rfl) ⟨282416, by rfl⟩ : syracuseStep 376555 = 564833) B564833
theorem B1883897 : Blo 219811 1883897 := bstep (se 2 (by rfl) ⟨706461, by rfl⟩ : syracuseStep 1883897 = 1412923) B1412923
theorem B1262081 : Blo 219811 1262081 := bstep (se 2 (by rfl) ⟨473280, by rfl⟩ : syracuseStep 1262081 = 946561) B946561
theorem B377465 : Blo 219811 377465 := bstep (se 2 (by rfl) ⟨141549, by rfl⟩ : syracuseStep 377465 = 283099) B283099
theorem B803449 : Blo 219811 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B1262263 : Blo 219811 1262263 := bstep (se 1 (by rfl) ⟨946697, by rfl⟩ : syracuseStep 1262263 = 1893395) B1893395
theorem B377527 : Blo 219811 377527 := bstep (se 1 (by rfl) ⟨283145, by rfl⟩ : syracuseStep 377527 = 566291) B566291
theorem B475895 : Blo 219811 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B640199 : Blo 219811 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B279931 : Blo 219811 279931 := bstep (se 1 (by rfl) ⟨209948, by rfl⟩ : syracuseStep 279931 = 419897) B419897
theorem B2377133 : Blo 219811 2377133 := bstep (se 3 (by rfl) ⟨445712, by rfl⟩ : syracuseStep 2377133 = 891425) B891425
theorem B640669 : Blo 219811 640669 := bstep (se 3 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 640669 = 240251) B240251
theorem B1132217 : Blo 219811 1132217 := bstep (se 2 (by rfl) ⟨424581, by rfl⟩ : syracuseStep 1132217 = 849163) B849163
theorem B247783 : Blo 219811 247783 := bstep (se 1 (by rfl) ⟨185837, by rfl⟩ : syracuseStep 247783 = 371675) B371675
theorem B2148605 : Blo 219811 2148605 := bstep (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) B805727
theorem B280999 : Blo 219811 280999 := bstep (se 1 (by rfl) ⟨210749, by rfl⟩ : syracuseStep 280999 = 421499) B421499
theorem B281323 : Blo 219811 281323 := bstep (se 1 (by rfl) ⟨210992, by rfl⟩ : syracuseStep 281323 = 421985) B421985
theorem B4016947 : Blo 219811 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B281551 : Blo 219811 281551 := bstep (se 1 (by rfl) ⟨211163, by rfl⟩ : syracuseStep 281551 = 422327) B422327
theorem B1264679 : Blo 219811 1264679 := bstep (se 1 (by rfl) ⟨948509, by rfl⟩ : syracuseStep 1264679 = 1897019) B1897019
theorem B281819 : Blo 219811 281819 := bstep (se 1 (by rfl) ⟨211364, by rfl⟩ : syracuseStep 281819 = 422729) B422729
theorem B838943 : Blo 219811 838943 := bstep (se 1 (by rfl) ⟨629207, by rfl⟩ : syracuseStep 838943 = 1258415) B1258415
theorem B2116925 : Blo 219811 2116925 := bstep (se 3 (by rfl) ⟨396923, by rfl⟩ : syracuseStep 2116925 = 793847) B793847
theorem B249439 : Blo 219811 249439 := bstep (se 1 (by rfl) ⟨187079, by rfl⟩ : syracuseStep 249439 = 374159) B374159
theorem B2444897 : Blo 219811 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B282295 : Blo 219811 282295 := bstep (se 1 (by rfl) ⟨211721, by rfl⟩ : syracuseStep 282295 = 423443) B423443
theorem B1199879 : Blo 219811 1199879 := bstep (se 1 (by rfl) ⟨899909, by rfl⟩ : syracuseStep 1199879 = 1799819) B1799819
theorem B16305953 : Blo 219811 16305953 := bstep (se 2 (by rfl) ⟨6114732, by rfl⟩ : syracuseStep 16305953 = 12229465) B12229465
theorem B479081 : Blo 219811 479081 := bstep (se 2 (by rfl) ⟨179655, by rfl⟩ : syracuseStep 479081 = 359311) B359311
theorem B282523 : Blo 219811 282523 := bstep (se 1 (by rfl) ⟨211892, by rfl⟩ : syracuseStep 282523 = 423785) B423785
theorem B741959 : Blo 219811 741959 := bstep (se 1 (by rfl) ⟨556469, by rfl⟩ : syracuseStep 741959 = 1112939) B1112939
theorem B840415 : Blo 219811 840415 := bstep (se 1 (by rfl) ⟨630311, by rfl⟩ : syracuseStep 840415 = 1260623) B1260623
theorem B250591 : Blo 219811 250591 := bstep (se 1 (by rfl) ⟨187943, by rfl⟩ : syracuseStep 250591 = 375887) B375887
theorem B283547 : Blo 219811 283547 := bstep (se 1 (by rfl) ⟨212660, by rfl⟩ : syracuseStep 283547 = 425321) B425321
theorem B742391 : Blo 219811 742391 := bstep (se 1 (by rfl) ⟨556793, by rfl⟩ : syracuseStep 742391 = 1113587) B1113587
theorem B251167 : Blo 219811 251167 := bstep (se 1 (by rfl) ⟨188375, by rfl⟩ : syracuseStep 251167 = 376751) B376751
theorem B251455 : Blo 219811 251455 := bstep (se 1 (by rfl) ⟨188591, by rfl⟩ : syracuseStep 251455 = 377183) B377183
theorem B841373 : Blo 219811 841373 := bstep (se 3 (by rfl) ⟨157757, by rfl⟩ : syracuseStep 841373 = 315515) B315515
theorem B939863 : Blo 219811 939863 := bstep (se 1 (by rfl) ⟨704897, by rfl⟩ : syracuseStep 939863 = 1409795) B1409795
theorem B743255 : Blo 219811 743255 := bstep (se 1 (by rfl) ⟨557441, by rfl⟩ : syracuseStep 743255 = 1114883) B1114883
theorem B4512023 : Blo 219811 4512023 := bstep (se 1 (by rfl) ⟨3384017, by rfl⟩ : syracuseStep 4512023 = 6768035) B6768035
theorem B481609 : Blo 219811 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B448859 : Blo 219811 448859 := bstep (se 1 (by rfl) ⟨336644, by rfl⟩ : syracuseStep 448859 = 673289) B673289
theorem B252283 : Blo 219811 252283 := bstep (se 1 (by rfl) ⟨189212, by rfl⟩ : syracuseStep 252283 = 378425) B378425
theorem B940531 : Blo 219811 940531 := bstep (se 1 (by rfl) ⟨705398, by rfl⟩ : syracuseStep 940531 = 1410797) B1410797
theorem B317947 : Blo 219811 317947 := bstep (se 1 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 317947 = 476921) B476921
theorem B219871 : Blo 219811 219871 := bstep (se 1 (by rfl) ⟨164903, by rfl⟩ : syracuseStep 219871 = 329807) B329807
theorem B219951 : Blo 219811 219951 := bstep (se 1 (by rfl) ⟨164963, by rfl⟩ : syracuseStep 219951 = 329927) B329927
theorem B1203011 : Blo 219811 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B744335 : Blo 219811 744335 := bstep (se 1 (by rfl) ⟨558251, by rfl⟩ : syracuseStep 744335 = 1116503) B1116503
theorem B220059 : Blo 219811 220059 := bstep (se 1 (by rfl) ⟨165044, by rfl⟩ : syracuseStep 220059 = 330089) B330089
theorem B220111 : Blo 219811 220111 := bstep (se 1 (by rfl) ⟨165083, by rfl⟩ : syracuseStep 220111 = 330167) B330167
theorem B220135 : Blo 219811 220135 := bstep (se 1 (by rfl) ⟨165101, by rfl⟩ : syracuseStep 220135 = 330203) B330203
theorem B3595531 : Blo 219811 3595531 := bstep (se 1 (by rfl) ⟨2696648, by rfl⟩ : syracuseStep 3595531 = 5393297) B5393297
theorem B220447 : Blo 219811 220447 := bstep (se 1 (by rfl) ⟨165335, by rfl⟩ : syracuseStep 220447 = 330671) B330671
theorem B449831 : Blo 219811 449831 := bstep (se 1 (by rfl) ⟨337373, by rfl⟩ : syracuseStep 449831 = 674747) B674747
theorem B220507 : Blo 219811 220507 := bstep (se 1 (by rfl) ⟨165380, by rfl⟩ : syracuseStep 220507 = 330761) B330761
theorem B220527 : Blo 219811 220527 := bstep (se 1 (by rfl) ⟨165395, by rfl⟩ : syracuseStep 220527 = 330791) B330791
theorem B220583 : Blo 219811 220583 := bstep (se 1 (by rfl) ⟨165437, by rfl⟩ : syracuseStep 220583 = 330875) B330875
theorem B220667 : Blo 219811 220667 := bstep (se 1 (by rfl) ⟨165500, by rfl⟩ : syracuseStep 220667 = 331001) B331001
theorem B220735 : Blo 219811 220735 := bstep (se 1 (by rfl) ⟨165551, by rfl⟩ : syracuseStep 220735 = 331103) B331103
theorem B220743 : Blo 219811 220743 := bstep (se 1 (by rfl) ⟨165557, by rfl⟩ : syracuseStep 220743 = 331115) B331115
theorem B417467 : Blo 219811 417467 := bstep (se 1 (by rfl) ⟨313100, by rfl⟩ : syracuseStep 417467 = 626201) B626201
theorem B941777 : Blo 219811 941777 := bstep (se 2 (by rfl) ⟨353166, by rfl⟩ : syracuseStep 941777 = 706333) B706333
theorem B220895 : Blo 219811 220895 := bstep (se 1 (by rfl) ⟨165671, by rfl⟩ : syracuseStep 220895 = 331343) B331343
theorem B220975 : Blo 219811 220975 := bstep (se 1 (by rfl) ⟨165731, by rfl⟩ : syracuseStep 220975 = 331463) B331463
theorem B221083 : Blo 219811 221083 := bstep (se 1 (by rfl) ⟨165812, by rfl⟩ : syracuseStep 221083 = 331625) B331625
theorem B221135 : Blo 219811 221135 := bstep (se 1 (by rfl) ⟨165851, by rfl⟩ : syracuseStep 221135 = 331703) B331703
theorem B221159 : Blo 219811 221159 := bstep (se 1 (by rfl) ⟨165869, by rfl⟩ : syracuseStep 221159 = 331739) B331739
theorem B745577 : Blo 219811 745577 := bstep (se 2 (by rfl) ⟨279591, by rfl⟩ : syracuseStep 745577 = 559183) B559183
theorem B221471 : Blo 219811 221471 := bstep (se 1 (by rfl) ⟨166103, by rfl⟩ : syracuseStep 221471 = 332207) B332207
theorem B352603 : Blo 219811 352603 := bstep (se 1 (by rfl) ⟨264452, by rfl⟩ : syracuseStep 352603 = 528905) B528905
theorem B221531 : Blo 219811 221531 := bstep (se 1 (by rfl) ⟨166148, by rfl⟩ : syracuseStep 221531 = 332297) B332297
theorem B221551 : Blo 219811 221551 := bstep (se 1 (by rfl) ⟨166163, by rfl⟩ : syracuseStep 221551 = 332327) B332327
theorem B221607 : Blo 219811 221607 := bstep (se 1 (by rfl) ⟨166205, by rfl⟩ : syracuseStep 221607 = 332411) B332411
theorem B221691 : Blo 219811 221691 := bstep (se 1 (by rfl) ⟨166268, by rfl⟩ : syracuseStep 221691 = 332537) B332537
theorem B844289 : Blo 219811 844289 := bstep (se 2 (by rfl) ⟨316608, by rfl⟩ : syracuseStep 844289 = 633217) B633217
theorem B221759 : Blo 219811 221759 := bstep (se 1 (by rfl) ⟨166319, by rfl⟩ : syracuseStep 221759 = 332639) B332639
theorem B221767 : Blo 219811 221767 := bstep (se 1 (by rfl) ⟨166325, by rfl⟩ : syracuseStep 221767 = 332651) B332651
theorem B1204919 : Blo 219811 1204919 := bstep (se 1 (by rfl) ⟨903689, by rfl⟩ : syracuseStep 1204919 = 1807379) B1807379
theorem B221919 : Blo 219811 221919 := bstep (se 1 (by rfl) ⟨166439, by rfl⟩ : syracuseStep 221919 = 332879) B332879
theorem B221999 : Blo 219811 221999 := bstep (se 1 (by rfl) ⟨166499, by rfl⟩ : syracuseStep 221999 = 332999) B332999
theorem B222107 : Blo 219811 222107 := bstep (se 1 (by rfl) ⟨166580, by rfl⟩ : syracuseStep 222107 = 333161) B333161
theorem B746441 : Blo 219811 746441 := bstep (se 2 (by rfl) ⟨279915, by rfl⟩ : syracuseStep 746441 = 559831) B559831
theorem B222159 : Blo 219811 222159 := bstep (se 1 (by rfl) ⟨166619, by rfl⟩ : syracuseStep 222159 = 333239) B333239
theorem B222183 : Blo 219811 222183 := bstep (se 1 (by rfl) ⟨166637, by rfl⟩ : syracuseStep 222183 = 333275) B333275
theorem B844775 : Blo 219811 844775 := bstep (se 1 (by rfl) ⟨633581, by rfl⟩ : syracuseStep 844775 = 1267163) B1267163
theorem B353423 : Blo 219811 353423 := bstep (se 1 (by rfl) ⟨265067, by rfl⟩ : syracuseStep 353423 = 530135) B530135
theorem B746711 : Blo 219811 746711 := bstep (se 1 (by rfl) ⟨560033, by rfl⟩ : syracuseStep 746711 = 1120067) B1120067
theorem B222495 : Blo 219811 222495 := bstep (se 1 (by rfl) ⟨166871, by rfl⟩ : syracuseStep 222495 = 333743) B333743
theorem B1697111 : Blo 219811 1697111 := bstep (se 1 (by rfl) ⟨1272833, by rfl⟩ : syracuseStep 1697111 = 2545667) B2545667
theorem B222555 : Blo 219811 222555 := bstep (se 1 (by rfl) ⟨166916, by rfl⟩ : syracuseStep 222555 = 333833) B333833
theorem B222575 : Blo 219811 222575 := bstep (se 1 (by rfl) ⟨166931, by rfl⟩ : syracuseStep 222575 = 333863) B333863
theorem B1009057 : Blo 219811 1009057 := bstep (se 2 (by rfl) ⟨378396, by rfl⟩ : syracuseStep 1009057 = 756793) B756793
theorem B222631 : Blo 219811 222631 := bstep (se 1 (by rfl) ⟨166973, by rfl⟩ : syracuseStep 222631 = 333947) B333947
theorem B222715 : Blo 219811 222715 := bstep (se 1 (by rfl) ⟨167036, by rfl⟩ : syracuseStep 222715 = 334073) B334073
theorem B222783 : Blo 219811 222783 := bstep (se 1 (by rfl) ⟨167087, by rfl⟩ : syracuseStep 222783 = 334175) B334175
theorem B222791 : Blo 219811 222791 := bstep (se 1 (by rfl) ⟨167093, by rfl⟩ : syracuseStep 222791 = 334187) B334187
theorem B419411 : Blo 219811 419411 := bstep (se 1 (by rfl) ⟨314558, by rfl⟩ : syracuseStep 419411 = 629117) B629117
theorem B222943 : Blo 219811 222943 := bstep (se 1 (by rfl) ⟨167207, by rfl⟩ : syracuseStep 222943 = 334415) B334415
theorem B321259 : Blo 219811 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B354089 : Blo 219811 354089 := bstep (se 2 (by rfl) ⟨132783, by rfl⟩ : syracuseStep 354089 = 265567) B265567
theorem B223023 : Blo 219811 223023 := bstep (se 1 (by rfl) ⟨167267, by rfl⟩ : syracuseStep 223023 = 334535) B334535
theorem B223131 : Blo 219811 223131 := bstep (se 1 (by rfl) ⟨167348, by rfl⟩ : syracuseStep 223131 = 334697) B334697
theorem B223183 : Blo 219811 223183 := bstep (se 1 (by rfl) ⟨167387, by rfl⟩ : syracuseStep 223183 = 334775) B334775
theorem B223207 : Blo 219811 223207 := bstep (se 1 (by rfl) ⟨167405, by rfl⟩ : syracuseStep 223207 = 334811) B334811
theorem B223519 : Blo 219811 223519 := bstep (se 1 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 223519 = 335279) B335279
theorem B6121763 : Blo 219811 6121763 := bstep (se 1 (by rfl) ⟨4591322, by rfl⟩ : syracuseStep 6121763 = 9182645) B9182645
theorem B223579 : Blo 219811 223579 := bstep (se 1 (by rfl) ⟨167684, by rfl⟩ : syracuseStep 223579 = 335369) B335369
theorem B223599 : Blo 219811 223599 := bstep (se 1 (by rfl) ⟨167699, by rfl⟩ : syracuseStep 223599 = 335399) B335399
theorem B846247 : Blo 219811 846247 := bstep (se 1 (by rfl) ⟨634685, by rfl⟩ : syracuseStep 846247 = 1269371) B1269371
theorem B223655 : Blo 219811 223655 := bstep (se 1 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 223655 = 335483) B335483
theorem B223739 : Blo 219811 223739 := bstep (se 1 (by rfl) ⟨167804, by rfl⟩ : syracuseStep 223739 = 335609) B335609
theorem B3860995 : Blo 219811 3860995 := bstep (se 1 (by rfl) ⟨2895746, by rfl⟩ : syracuseStep 3860995 = 5791493) B5791493
theorem B223807 : Blo 219811 223807 := bstep (se 1 (by rfl) ⟨167855, by rfl⟩ : syracuseStep 223807 = 335711) B335711
theorem B1895035 : Blo 219811 1895035 := bstep (se 1 (by rfl) ⟨1421276, by rfl⟩ : syracuseStep 1895035 = 2842553) B2842553
theorem B420527 : Blo 219811 420527 := bstep (se 1 (by rfl) ⟨315395, by rfl⟩ : syracuseStep 420527 = 630791) B630791
theorem B1076141 : Blo 219811 1076141 := bstep (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) B403553
theorem B847037 : Blo 219811 847037 := bstep (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) B317639
theorem B748763 : Blo 219811 748763 := bstep (se 1 (by rfl) ⟨561572, by rfl⟩ : syracuseStep 748763 = 1123145) B1123145
theorem B1437115 : Blo 219811 1437115 := bstep (se 1 (by rfl) ⟨1077836, by rfl⟩ : syracuseStep 1437115 = 2155673) B2155673
theorem B1338889 : Blo 219811 1338889 := bstep (se 2 (by rfl) ⟨502083, by rfl⟩ : syracuseStep 1338889 = 1004167) B1004167
theorem B716303 : Blo 219811 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B421537 : Blo 219811 421537 := bstep (se 2 (by rfl) ⟨158076, by rfl⟩ : syracuseStep 421537 = 316153) B316153
theorem B2158289 : Blo 219811 2158289 := bstep (se 2 (by rfl) ⟨809358, by rfl⟩ : syracuseStep 2158289 = 1618717) B1618717
theorem B716701 : Blo 219811 716701 := bstep (se 3 (by rfl) ⟨134381, by rfl⟩ : syracuseStep 716701 = 268763) B268763
theorem B749627 : Blo 219811 749627 := bstep (se 1 (by rfl) ⟨562220, by rfl⟩ : syracuseStep 749627 = 1124441) B1124441
theorem B749897 : Blo 219811 749897 := bstep (se 2 (by rfl) ⟨281211, by rfl⟩ : syracuseStep 749897 = 562423) B562423
theorem B422471 : Blo 219811 422471 := bstep (se 1 (by rfl) ⟨316853, by rfl⟩ : syracuseStep 422471 = 633707) B633707
theorem B946835 : Blo 219811 946835 := bstep (se 1 (by rfl) ⟨710126, by rfl⟩ : syracuseStep 946835 = 1420253) B1420253
theorem B946903 : Blo 219811 946903 := bstep (se 1 (by rfl) ⟨710177, by rfl⟩ : syracuseStep 946903 = 1420355) B1420355
theorem B4846837 : Blo 219811 4846837 := bstep (se 5 (by rfl) ⟨227195, by rfl⟩ : syracuseStep 4846837 = 454391) B454391
theorem B6419735 : Blo 219811 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B11728151 : Blo 219811 11728151 := bstep (se 1 (by rfl) ⟨8796113, by rfl⟩ : syracuseStep 11728151 = 17592227) B17592227
theorem B752303 : Blo 219811 752303 := bstep (se 1 (by rfl) ⟨564227, by rfl⟩ : syracuseStep 752303 = 1128455) B1128455
theorem B1899683 : Blo 219811 1899683 := bstep (se 1 (by rfl) ⟨1424762, by rfl⟩ : syracuseStep 1899683 = 2849525) B2849525
theorem B753083 : Blo 219811 753083 := bstep (se 1 (by rfl) ⟨564812, by rfl⟩ : syracuseStep 753083 = 1129625) B1129625
theorem B1343071 : Blo 219811 1343071 := bstep (se 1 (by rfl) ⟨1007303, by rfl⟩ : syracuseStep 1343071 = 2014607) B2014607
theorem B3604297 : Blo 219811 3604297 := bstep (se 2 (by rfl) ⟨1351611, by rfl⟩ : syracuseStep 3604297 = 2703223) B2703223
theorem B1376831 : Blo 219811 1376831 := bstep (se 1 (by rfl) ⟨1032623, by rfl⟩ : syracuseStep 1376831 = 2065247) B2065247
theorem B426799 : Blo 219811 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B754811 : Blo 219811 754811 := bstep (se 1 (by rfl) ⟨566108, by rfl⟩ : syracuseStep 754811 = 1132217) B1132217
theorem B755081 : Blo 219811 755081 := bstep (se 2 (by rfl) ⟨283155, by rfl⟩ : syracuseStep 755081 = 566311) B566311
theorem B3671687 : Blo 219811 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B1345409 : Blo 219811 1345409 := bstep (se 2 (by rfl) ⟨504528, by rfl⟩ : syracuseStep 1345409 = 1009057) B1009057
theorem B559295 : Blo 219811 559295 := bstep (se 1 (by rfl) ⟨419471, by rfl⟩ : syracuseStep 559295 = 838943) B838943
theorem B854225 : Blo 219811 854225 := bstep (se 2 (by rfl) ⟨320334, by rfl⟩ : syracuseStep 854225 = 640669) B640669
theorem B1411283 : Blo 219811 1411283 := bstep (se 1 (by rfl) ⟨1058462, by rfl⟩ : syracuseStep 1411283 = 2116925) B2116925
theorem B329963 : Blo 219811 329963 := bstep (se 1 (by rfl) ⟨247472, by rfl⟩ : syracuseStep 329963 = 494945) B494945
theorem B330023 : Blo 219811 330023 := bstep (se 1 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 330023 = 495035) B495035
theorem B428345 : Blo 219811 428345 := bstep (se 2 (by rfl) ⟨160629, by rfl⟩ : syracuseStep 428345 = 321259) B321259
theorem B330107 : Blo 219811 330107 := bstep (se 1 (by rfl) ⟨247580, by rfl⟩ : syracuseStep 330107 = 495161) B495161
theorem B756125 : Blo 219811 756125 := bstep (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) B283547
theorem B330377 : Blo 219811 330377 := bstep (se 2 (by rfl) ⟨123891, by rfl⟩ : syracuseStep 330377 = 247783) B247783
theorem B330551 : Blo 219811 330551 := bstep (se 1 (by rfl) ⟨247913, by rfl⟩ : syracuseStep 330551 = 495827) B495827
theorem B330587 : Blo 219811 330587 := bstep (se 1 (by rfl) ⟨247940, by rfl⟩ : syracuseStep 330587 = 495881) B495881
theorem B330731 : Blo 219811 330731 := bstep (se 1 (by rfl) ⟨248048, by rfl⟩ : syracuseStep 330731 = 496097) B496097
theorem B494639 : Blo 219811 494639 := bstep (se 1 (by rfl) ⟨370979, by rfl⟩ : syracuseStep 494639 = 741959) B741959
theorem B330935 : Blo 219811 330935 := bstep (se 1 (by rfl) ⟨248201, by rfl⟩ : syracuseStep 330935 = 496403) B496403
theorem B494927 : Blo 219811 494927 := bstep (se 1 (by rfl) ⟨371195, by rfl⟩ : syracuseStep 494927 = 742391) B742391
theorem B5147993 : Blo 219811 5147993 := bstep (se 2 (by rfl) ⟨1930497, by rfl⟩ : syracuseStep 5147993 = 3860995) B3860995
theorem B331175 : Blo 219811 331175 := bstep (se 1 (by rfl) ⟨248381, by rfl⟩ : syracuseStep 331175 = 496763) B496763
theorem B495017 : Blo 219811 495017 := bstep (se 2 (by rfl) ⟨185631, by rfl⟩ : syracuseStep 495017 = 371263) B371263
theorem B2526713 : Blo 219811 2526713 := bstep (se 2 (by rfl) ⟨947517, by rfl⟩ : syracuseStep 2526713 = 1895035) B1895035
theorem B331259 : Blo 219811 331259 := bstep (se 1 (by rfl) ⟨248444, by rfl⟩ : syracuseStep 331259 = 496889) B496889
theorem B331355 : Blo 219811 331355 := bstep (se 1 (by rfl) ⟨248516, by rfl⟩ : syracuseStep 331355 = 497033) B497033
theorem B331439 : Blo 219811 331439 := bstep (se 1 (by rfl) ⟨248579, by rfl⟩ : syracuseStep 331439 = 497159) B497159
theorem B5738165 : Blo 219811 5738165 := bstep (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) B537953
theorem B560915 : Blo 219811 560915 := bstep (se 1 (by rfl) ⟨420686, by rfl⟩ : syracuseStep 560915 = 841373) B841373
theorem B331559 : Blo 219811 331559 := bstep (se 1 (by rfl) ⟨248669, by rfl⟩ : syracuseStep 331559 = 497339) B497339
theorem B331643 : Blo 219811 331643 := bstep (se 1 (by rfl) ⟨248732, by rfl⟩ : syracuseStep 331643 = 497465) B497465
theorem B495503 : Blo 219811 495503 := bstep (se 1 (by rfl) ⟨371627, by rfl⟩ : syracuseStep 495503 = 743255) B743255
theorem B332063 : Blo 219811 332063 := bstep (se 1 (by rfl) ⟨249047, by rfl⟩ : syracuseStep 332063 = 498095) B498095
theorem B332087 : Blo 219811 332087 := bstep (se 1 (by rfl) ⟨249065, by rfl⟩ : syracuseStep 332087 = 498131) B498131
theorem B332159 : Blo 219811 332159 := bstep (se 1 (by rfl) ⟨249119, by rfl⟩ : syracuseStep 332159 = 498239) B498239
theorem B332231 : Blo 219811 332231 := bstep (se 1 (by rfl) ⟨249173, by rfl⟩ : syracuseStep 332231 = 498347) B498347
theorem B496223 : Blo 219811 496223 := bstep (se 1 (by rfl) ⟨372167, by rfl⟩ : syracuseStep 496223 = 744335) B744335
theorem B332585 : Blo 219811 332585 := bstep (se 2 (by rfl) ⟨124719, by rfl⟩ : syracuseStep 332585 = 249439) B249439
theorem B332591 : Blo 219811 332591 := bstep (se 1 (by rfl) ⟨249443, by rfl⟩ : syracuseStep 332591 = 498887) B498887
theorem B562049 : Blo 219811 562049 := bstep (se 2 (by rfl) ⟨210768, by rfl⟩ : syracuseStep 562049 = 421537) B421537
theorem B332711 : Blo 219811 332711 := bstep (se 1 (by rfl) ⟨249533, by rfl⟩ : syracuseStep 332711 = 499067) B499067
theorem B332795 : Blo 219811 332795 := bstep (se 1 (by rfl) ⟨249596, by rfl⟩ : syracuseStep 332795 = 499193) B499193
theorem B332855 : Blo 219811 332855 := bstep (se 1 (by rfl) ⟨249641, by rfl⟩ : syracuseStep 332855 = 499283) B499283
theorem B627851 : Blo 219811 627851 := bstep (se 1 (by rfl) ⟨470888, by rfl⟩ : syracuseStep 627851 = 941777) B941777
theorem B332975 : Blo 219811 332975 := bstep (se 1 (by rfl) ⟨249731, by rfl⟩ : syracuseStep 332975 = 499463) B499463
theorem B955601 : Blo 219811 955601 := bstep (se 2 (by rfl) ⟨358350, by rfl⟩ : syracuseStep 955601 = 716701) B716701
theorem B497051 : Blo 219811 497051 := bstep (se 1 (by rfl) ⟨372788, by rfl⟩ : syracuseStep 497051 = 745577) B745577
theorem B333383 : Blo 219811 333383 := bstep (se 1 (by rfl) ⟨250037, by rfl⟩ : syracuseStep 333383 = 500075) B500075
theorem B333479 : Blo 219811 333479 := bstep (se 1 (by rfl) ⟨250109, by rfl⟩ : syracuseStep 333479 = 500219) B500219
theorem B562859 : Blo 219811 562859 := bstep (se 1 (by rfl) ⟨422144, by rfl⟩ : syracuseStep 562859 = 844289) B844289
theorem B333563 : Blo 219811 333563 := bstep (se 1 (by rfl) ⟨250172, by rfl⟩ : syracuseStep 333563 = 500345) B500345
theorem B333599 : Blo 219811 333599 := bstep (se 1 (by rfl) ⟨250199, by rfl⟩ : syracuseStep 333599 = 500399) B500399
theorem B333647 : Blo 219811 333647 := bstep (se 1 (by rfl) ⟨250235, by rfl⟩ : syracuseStep 333647 = 500471) B500471
theorem B333767 : Blo 219811 333767 := bstep (se 1 (by rfl) ⟨250325, by rfl⟩ : syracuseStep 333767 = 500651) B500651
theorem B595927 : Blo 219811 595927 := bstep (se 1 (by rfl) ⟨446945, by rfl⟩ : syracuseStep 595927 = 893891) B893891
theorem B497627 : Blo 219811 497627 := bstep (se 1 (by rfl) ⟨373220, by rfl⟩ : syracuseStep 497627 = 746441) B746441
theorem B563183 : Blo 219811 563183 := bstep (se 1 (by rfl) ⟨422387, by rfl⟩ : syracuseStep 563183 = 844775) B844775
theorem B497807 : Blo 219811 497807 := bstep (se 1 (by rfl) ⟨373355, by rfl⟩ : syracuseStep 497807 = 746711) B746711
theorem B530587 : Blo 219811 530587 := bstep (se 1 (by rfl) ⟨397940, by rfl⟩ : syracuseStep 530587 = 795881) B795881
theorem B497825 : Blo 219811 497825 := bstep (se 2 (by rfl) ⟨186684, by rfl⟩ : syracuseStep 497825 = 373369) B373369
theorem B497897 : Blo 219811 497897 := bstep (se 2 (by rfl) ⟨186711, by rfl⟩ : syracuseStep 497897 = 373423) B373423
theorem B1612061 : Blo 219811 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B1120553 : Blo 219811 1120553 := bstep (se 2 (by rfl) ⟨420207, by rfl⟩ : syracuseStep 1120553 = 840415) B840415
theorem B334121 : Blo 219811 334121 := bstep (se 2 (by rfl) ⟨125295, by rfl⟩ : syracuseStep 334121 = 250591) B250591
theorem B334127 : Blo 219811 334127 := bstep (se 1 (by rfl) ⟨250595, by rfl⟩ : syracuseStep 334127 = 501191) B501191
theorem B21142037 : Blo 219811 21142037 := bstep (se 6 (by rfl) ⟨495516, by rfl⟩ : syracuseStep 21142037 = 991033) B991033
theorem B334367 : Blo 219811 334367 := bstep (se 1 (by rfl) ⟨250775, by rfl⟩ : syracuseStep 334367 = 501551) B501551
theorem B793241 : Blo 219811 793241 := bstep (se 2 (by rfl) ⟨297465, by rfl⟩ : syracuseStep 793241 = 594931) B594931
theorem B11606819 : Blo 219811 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B334751 : Blo 219811 334751 := bstep (se 1 (by rfl) ⟨251063, by rfl⟩ : syracuseStep 334751 = 502127) B502127
theorem B334799 : Blo 219811 334799 := bstep (se 1 (by rfl) ⟨251099, by rfl⟩ : syracuseStep 334799 = 502199) B502199
theorem B6462449 : Blo 219811 6462449 := bstep (se 2 (by rfl) ⟨2423418, by rfl⟩ : syracuseStep 6462449 = 4846837) B4846837
theorem B334889 : Blo 219811 334889 := bstep (se 2 (by rfl) ⟨125583, by rfl⟩ : syracuseStep 334889 = 251167) B251167
theorem B334895 : Blo 219811 334895 := bstep (se 1 (by rfl) ⟨251171, by rfl⟩ : syracuseStep 334895 = 502343) B502343
theorem B334919 : Blo 219811 334919 := bstep (se 1 (by rfl) ⟨251189, by rfl⟩ : syracuseStep 334919 = 502379) B502379
theorem B2891009 : Blo 219811 2891009 := bstep (se 2 (by rfl) ⟨1084128, by rfl⟩ : syracuseStep 2891009 = 2168257) B2168257
theorem B335183 : Blo 219811 335183 := bstep (se 1 (by rfl) ⟨251387, by rfl⟩ : syracuseStep 335183 = 502775) B502775
theorem B335273 : Blo 219811 335273 := bstep (se 2 (by rfl) ⟨125727, by rfl⟩ : syracuseStep 335273 = 251455) B251455
theorem B564691 : Blo 219811 564691 := bstep (se 1 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 564691 = 847037) B847037
theorem B499175 : Blo 219811 499175 := bstep (se 1 (by rfl) ⟨374381, by rfl⟩ : syracuseStep 499175 = 748763) B748763
theorem B335423 : Blo 219811 335423 := bstep (se 1 (by rfl) ⟨251567, by rfl⟩ : syracuseStep 335423 = 503135) B503135
theorem B1515311 : Blo 219811 1515311 := bstep (se 1 (by rfl) ⟨1136483, by rfl⟩ : syracuseStep 1515311 = 2272967) B2272967
theorem B335687 : Blo 219811 335687 := bstep (se 1 (by rfl) ⟨251765, by rfl⟩ : syracuseStep 335687 = 503531) B503531
theorem B499751 : Blo 219811 499751 := bstep (se 1 (by rfl) ⟨374813, by rfl⟩ : syracuseStep 499751 = 749627) B749627
theorem B499931 : Blo 219811 499931 := bstep (se 1 (by rfl) ⟨374948, by rfl⟩ : syracuseStep 499931 = 749897) B749897
theorem B631223 : Blo 219811 631223 := bstep (se 1 (by rfl) ⟨473417, by rfl⟩ : syracuseStep 631223 = 946835) B946835
theorem B500201 : Blo 219811 500201 := bstep (se 2 (by rfl) ⟨187575, by rfl⟩ : syracuseStep 500201 = 375151) B375151
theorem B336377 : Blo 219811 336377 := bstep (se 2 (by rfl) ⟨126141, by rfl⟩ : syracuseStep 336377 = 252283) B252283
theorem B1254041 : Blo 219811 1254041 := bstep (se 2 (by rfl) ⟨470265, by rfl⟩ : syracuseStep 1254041 = 940531) B940531
theorem B1450649 : Blo 219811 1450649 := bstep (se 2 (by rfl) ⟨543993, by rfl⟩ : syracuseStep 1450649 = 1087987) B1087987
theorem B500489 : Blo 219811 500489 := bstep (se 2 (by rfl) ⟨187683, by rfl⟩ : syracuseStep 500489 = 375367) B375367
theorem B501065 : Blo 219811 501065 := bstep (se 2 (by rfl) ⟨187899, by rfl⟩ : syracuseStep 501065 = 375799) B375799
theorem B1910141 : Blo 219811 1910141 := bstep (se 3 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 1910141 = 716303) B716303
theorem B3614215 : Blo 219811 3614215 := bstep (se 1 (by rfl) ⟨2710661, by rfl⟩ : syracuseStep 3614215 = 5421323) B5421323
theorem B4794041 : Blo 219811 4794041 := bstep (se 2 (by rfl) ⟨1797765, by rfl⟩ : syracuseStep 4794041 = 3595531) B3595531
theorem B501535 : Blo 219811 501535 := bstep (se 1 (by rfl) ⟨376151, by rfl⟩ : syracuseStep 501535 = 752303) B752303
theorem B34875299 : Blo 219811 34875299 := bstep (se 1 (by rfl) ⟨26156474, by rfl⟩ : syracuseStep 34875299 = 52312949) B52312949
theorem B502055 : Blo 219811 502055 := bstep (se 1 (by rfl) ⟨376541, by rfl⟩ : syracuseStep 502055 = 753083) B753083
theorem B502073 : Blo 219811 502073 := bstep (se 2 (by rfl) ⟨188277, by rfl⟩ : syracuseStep 502073 = 376555) B376555
theorem B1255931 : Blo 219811 1255931 := bstep (se 1 (by rfl) ⟨941948, by rfl⟩ : syracuseStep 1255931 = 1883897) B1883897
theorem B371783 : Blo 219811 371783 := bstep (se 1 (by rfl) ⟨278837, by rfl⟩ : syracuseStep 371783 = 557675) B557675
theorem B470137 : Blo 219811 470137 := bstep (se 2 (by rfl) ⟨176301, by rfl⟩ : syracuseStep 470137 = 352603) B352603
theorem B1059961 : Blo 219811 1059961 := bstep (se 2 (by rfl) ⟨397485, by rfl⟩ : syracuseStep 1059961 = 794971) B794971
theorem B372215 : Blo 219811 372215 := bstep (se 1 (by rfl) ⟨279161, by rfl⟩ : syracuseStep 372215 = 558323) B558323
theorem B1683017 : Blo 219811 1683017 := bstep (se 2 (by rfl) ⟨631131, by rfl⟩ : syracuseStep 1683017 = 1262263) B1262263
theorem B503369 : Blo 219811 503369 := bstep (se 2 (by rfl) ⟨188763, by rfl⟩ : syracuseStep 503369 = 377527) B377527
theorem B1584755 : Blo 219811 1584755 := bstep (se 1 (by rfl) ⟨1188566, by rfl⟩ : syracuseStep 1584755 = 2377133) B2377133
theorem B634493 : Blo 219811 634493 := bstep (se 3 (by rfl) ⟨118967, by rfl⟩ : syracuseStep 634493 = 237935) B237935
theorem B896923 : Blo 219811 896923 := bstep (se 1 (by rfl) ⟨672692, by rfl⟩ : syracuseStep 896923 = 1345385) B1345385
theorem B1257389 : Blo 219811 1257389 := bstep (se 3 (by rfl) ⟨235760, by rfl⟩ : syracuseStep 1257389 = 471521) B471521
theorem B2568581 : Blo 219811 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B536969 : Blo 219811 536969 := bstep (se 2 (by rfl) ⟨201363, by rfl⟩ : syracuseStep 536969 = 402727) B402727
theorem B13054445 : Blo 219811 13054445 := bstep (se 3 (by rfl) ⟨2447708, by rfl⟩ : syracuseStep 13054445 = 4895417) B4895417
theorem B373241 : Blo 219811 373241 := bstep (se 2 (by rfl) ⟨139965, by rfl⟩ : syracuseStep 373241 = 279931) B279931
theorem B1421995 : Blo 219811 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B373511 : Blo 219811 373511 := bstep (se 1 (by rfl) ⟨280133, by rfl⟩ : syracuseStep 373511 = 560267) B560267
theorem B2896669 : Blo 219811 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B2405153 : Blo 219811 2405153 := bstep (se 2 (by rfl) ⟨901932, by rfl⟩ : syracuseStep 2405153 = 1803865) B1803865
theorem B799919 : Blo 219811 799919 := bstep (se 1 (by rfl) ⟨599939, by rfl⟩ : syracuseStep 799919 = 1199879) B1199879
theorem B1259165 : Blo 219811 1259165 := bstep (se 3 (by rfl) ⟨236093, by rfl⟩ : syracuseStep 1259165 = 472187) B472187
theorem B636599 : Blo 219811 636599 := bstep (se 1 (by rfl) ⟨477449, by rfl⟩ : syracuseStep 636599 = 954899) B954899
theorem B374591 : Blo 219811 374591 := bstep (se 1 (by rfl) ⟨280943, by rfl⟩ : syracuseStep 374591 = 561887) B561887
theorem B374665 : Blo 219811 374665 := bstep (se 2 (by rfl) ⟨140499, by rfl⟩ : syracuseStep 374665 = 280999) B280999
theorem B1128329 : Blo 219811 1128329 := bstep (se 2 (by rfl) ⟨423123, by rfl⟩ : syracuseStep 1128329 = 846247) B846247
theorem B375097 : Blo 219811 375097 := bstep (se 2 (by rfl) ⟨140661, by rfl⟩ : syracuseStep 375097 = 281323) B281323
theorem B7256465 : Blo 219811 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B5355929 : Blo 219811 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B1685933 : Blo 219811 1685933 := bstep (se 3 (by rfl) ⟨316112, by rfl⟩ : syracuseStep 1685933 = 632225) B632225
theorem B375401 : Blo 219811 375401 := bstep (se 2 (by rfl) ⟨140775, by rfl⟩ : syracuseStep 375401 = 281551) B281551
theorem B1587865 : Blo 219811 1587865 := bstep (se 2 (by rfl) ⟨595449, by rfl⟩ : syracuseStep 1587865 = 1190899) B1190899
theorem B802007 : Blo 219811 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B1916153 : Blo 219811 1916153 := bstep (se 2 (by rfl) ⟨718557, by rfl⟩ : syracuseStep 1916153 = 1437115) B1437115
theorem B1785185 : Blo 219811 1785185 := bstep (se 2 (by rfl) ⟨669444, by rfl⟩ : syracuseStep 1785185 = 1338889) B1338889
theorem B376231 : Blo 219811 376231 := bstep (se 1 (by rfl) ⟨282173, by rfl⟩ : syracuseStep 376231 = 564347) B564347
theorem B1588673 : Blo 219811 1588673 := bstep (se 2 (by rfl) ⟨595752, by rfl⟩ : syracuseStep 1588673 = 1191505) B1191505
theorem B2276909 : Blo 219811 2276909 := bstep (se 3 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 2276909 = 853841) B853841
theorem B2506301 : Blo 219811 2506301 := bstep (se 3 (by rfl) ⟨469931, by rfl⟩ : syracuseStep 2506301 = 939863) B939863
theorem B376393 : Blo 219811 376393 := bstep (se 2 (by rfl) ⟨141147, by rfl⟩ : syracuseStep 376393 = 282295) B282295
theorem B376427 : Blo 219811 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B8503055 : Blo 219811 8503055 := bstep (se 1 (by rfl) ⟨6377291, by rfl⟩ : syracuseStep 8503055 = 12754583) B12754583
theorem B278311 : Blo 219811 278311 := bstep (se 1 (by rfl) ⟨208733, by rfl⟩ : syracuseStep 278311 = 417467) B417467
theorem B376697 : Blo 219811 376697 := bstep (se 2 (by rfl) ⟨141261, by rfl⟩ : syracuseStep 376697 = 282523) B282523
theorem B2146337 : Blo 219811 2146337 := bstep (se 2 (by rfl) ⟨804876, by rfl⟩ : syracuseStep 2146337 = 1609753) B1609753
theorem B803279 : Blo 219811 803279 := bstep (se 1 (by rfl) ⟨602459, by rfl⟩ : syracuseStep 803279 = 1204919) B1204919
theorem B1688363 : Blo 219811 1688363 := bstep (se 1 (by rfl) ⟨1266272, by rfl⟩ : syracuseStep 1688363 = 2532545) B2532545
theorem B1131407 : Blo 219811 1131407 := bstep (se 1 (by rfl) ⟨848555, by rfl⟩ : syracuseStep 1131407 = 1697111) B1697111
theorem B1196957 : Blo 219811 1196957 := bstep (se 3 (by rfl) ⟨224429, by rfl⟩ : syracuseStep 1196957 = 448859) B448859
theorem B1262537 : Blo 219811 1262537 := bstep (se 2 (by rfl) ⟨473451, by rfl⟩ : syracuseStep 1262537 = 946903) B946903
theorem B279607 : Blo 219811 279607 := bstep (se 1 (by rfl) ⟨209705, by rfl⟩ : syracuseStep 279607 = 419411) B419411
theorem B1885331 : Blo 219811 1885331 := bstep (se 1 (by rfl) ⟨1413998, by rfl⟩ : syracuseStep 1885331 = 2827997) B2827997
theorem B4081175 : Blo 219811 4081175 := bstep (se 1 (by rfl) ⟨3060881, by rfl⟩ : syracuseStep 4081175 = 6121763) B6121763
theorem B280351 : Blo 219811 280351 := bstep (se 1 (by rfl) ⟨210263, by rfl⟩ : syracuseStep 280351 = 420527) B420527
theorem B313151 : Blo 219811 313151 := bstep (se 1 (by rfl) ⟨234863, by rfl⟩ : syracuseStep 313151 = 469727) B469727
theorem B247963 : Blo 219811 247963 := bstep (se 1 (by rfl) ⟨185972, by rfl⟩ : syracuseStep 247963 = 371945) B371945
theorem B247999 : Blo 219811 247999 := bstep (se 1 (by rfl) ⟨185999, by rfl⟩ : syracuseStep 247999 = 371999) B371999
theorem B4770515 : Blo 219811 4770515 := bstep (se 1 (by rfl) ⟨3577886, by rfl⟩ : syracuseStep 4770515 = 7155773) B7155773
theorem B707563 : Blo 219811 707563 := bstep (se 1 (by rfl) ⟨530672, by rfl⟩ : syracuseStep 707563 = 1061345) B1061345
theorem B281647 : Blo 219811 281647 := bstep (se 1 (by rfl) ⟨211235, by rfl⟩ : syracuseStep 281647 = 422471) B422471
theorem B1199549 : Blo 219811 1199549 := bstep (se 3 (by rfl) ⟨224915, by rfl⟩ : syracuseStep 1199549 = 449831) B449831
theorem B4279823 : Blo 219811 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B7818767 : Blo 219811 7818767 := bstep (se 1 (by rfl) ⟨5864075, by rfl⟩ : syracuseStep 7818767 = 11728151) B11728151
theorem B839231 : Blo 219811 839231 := bstep (se 1 (by rfl) ⟨629423, by rfl⟩ : syracuseStep 839231 = 1258847) B1258847
theorem B3920075 : Blo 219811 3920075 := bstep (se 1 (by rfl) ⟨2940056, by rfl⟩ : syracuseStep 3920075 = 5880113) B5880113
theorem B315623 : Blo 219811 315623 := bstep (se 1 (by rfl) ⟨236717, by rfl⟩ : syracuseStep 315623 = 473435) B473435
theorem B250087 : Blo 219811 250087 := bstep (se 1 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 250087 = 375131) B375131
theorem B3822329 : Blo 219811 3822329 := bstep (se 2 (by rfl) ⟨1433373, by rfl⟩ : syracuseStep 3822329 = 2866747) B2866747
theorem B1266455 : Blo 219811 1266455 := bstep (se 1 (by rfl) ⟨949841, by rfl⟩ : syracuseStep 1266455 = 1899683) B1899683
theorem B1790761 : Blo 219811 1790761 := bstep (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) B1343071
theorem B250735 : Blo 219811 250735 := bstep (se 1 (by rfl) ⟨188051, by rfl⟩ : syracuseStep 250735 = 376103) B376103
theorem B4805729 : Blo 219811 4805729 := bstep (se 2 (by rfl) ⟨1802148, by rfl⟩ : syracuseStep 4805729 = 3604297) B3604297
theorem B841387 : Blo 219811 841387 := bstep (se 1 (by rfl) ⟨631040, by rfl⟩ : syracuseStep 841387 = 1262081) B1262081
theorem B743147 : Blo 219811 743147 := bstep (se 1 (by rfl) ⟨557360, by rfl⟩ : syracuseStep 743147 = 1114721) B1114721
theorem B743417 : Blo 219811 743417 := bstep (se 2 (by rfl) ⟨278781, by rfl⟩ : syracuseStep 743417 = 557563) B557563
theorem B743579 : Blo 219811 743579 := bstep (se 1 (by rfl) ⟨557684, by rfl⟩ : syracuseStep 743579 = 1115369) B1115369
theorem B1071265 : Blo 219811 1071265 := bstep (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) B803449
theorem B448745 : Blo 219811 448745 := bstep (se 2 (by rfl) ⟨168279, by rfl⟩ : syracuseStep 448745 = 336559) B336559
theorem B743687 : Blo 219811 743687 := bstep (se 1 (by rfl) ⟨557765, by rfl⟩ : syracuseStep 743687 = 1115531) B1115531
theorem B4119113 : Blo 219811 4119113 := bstep (se 2 (by rfl) ⟨1544667, by rfl⟩ : syracuseStep 4119113 = 3089335) B3089335
theorem B482131 : Blo 219811 482131 := bstep (se 1 (by rfl) ⟨361598, by rfl⟩ : syracuseStep 482131 = 723197) B723197
theorem B1432403 : Blo 219811 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B219995 : Blo 219811 219995 := bstep (se 1 (by rfl) ⟨164996, by rfl⟩ : syracuseStep 219995 = 329993) B329993
theorem B220063 : Blo 219811 220063 := bstep (se 1 (by rfl) ⟨165047, by rfl⟩ : syracuseStep 220063 = 330095) B330095
theorem B1072109 : Blo 219811 1072109 := bstep (se 3 (by rfl) ⟨201020, by rfl⟩ : syracuseStep 1072109 = 402041) B402041
theorem B1006573 : Blo 219811 1006573 := bstep (se 3 (by rfl) ⟨188732, by rfl⟩ : syracuseStep 1006573 = 377465) B377465
theorem B318505 : Blo 219811 318505 := bstep (se 2 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 318505 = 238879) B238879
theorem B220207 : Blo 219811 220207 := bstep (se 1 (by rfl) ⟨165155, by rfl⟩ : syracuseStep 220207 = 330311) B330311
theorem B220231 : Blo 219811 220231 := bstep (se 1 (by rfl) ⟨165173, by rfl⟩ : syracuseStep 220231 = 330347) B330347
theorem B1596631 : Blo 219811 1596631 := bstep (se 1 (by rfl) ⟨1197473, by rfl⟩ : syracuseStep 1596631 = 2394947) B2394947
theorem B220383 : Blo 219811 220383 := bstep (se 1 (by rfl) ⟨165287, by rfl⟩ : syracuseStep 220383 = 330575) B330575
theorem B744713 : Blo 219811 744713 := bstep (se 2 (by rfl) ⟨279267, by rfl⟩ : syracuseStep 744713 = 558535) B558535
theorem B1269053 : Blo 219811 1269053 := bstep (se 3 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 1269053 = 475895) B475895
theorem B843119 : Blo 219811 843119 := bstep (se 1 (by rfl) ⟨632339, by rfl⟩ : syracuseStep 843119 = 1264679) B1264679
theorem B220647 : Blo 219811 220647 := bstep (se 1 (by rfl) ⟨165485, by rfl⟩ : syracuseStep 220647 = 330971) B330971
theorem B220763 : Blo 219811 220763 := bstep (se 1 (by rfl) ⟨165572, by rfl⟩ : syracuseStep 220763 = 331145) B331145
theorem B2416225 : Blo 219811 2416225 := bstep (se 2 (by rfl) ⟨906084, by rfl⟩ : syracuseStep 2416225 = 1812169) B1812169
theorem B1629931 : Blo 219811 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B220999 : Blo 219811 220999 := bstep (se 1 (by rfl) ⟨165749, by rfl⟩ : syracuseStep 220999 = 331499) B331499
theorem B221151 : Blo 219811 221151 := bstep (se 1 (by rfl) ⟨165863, by rfl⟩ : syracuseStep 221151 = 331727) B331727
theorem B221415 : Blo 219811 221415 := bstep (se 1 (by rfl) ⟨166061, by rfl⟩ : syracuseStep 221415 = 332123) B332123
theorem B745847 : Blo 219811 745847 := bstep (se 1 (by rfl) ⟨559385, by rfl⟩ : syracuseStep 745847 = 1118771) B1118771
theorem B942461 : Blo 219811 942461 := bstep (se 3 (by rfl) ⟨176711, by rfl⟩ : syracuseStep 942461 = 353423) B353423
theorem B1073533 : Blo 219811 1073533 := bstep (se 3 (by rfl) ⟨201287, by rfl⟩ : syracuseStep 1073533 = 402575) B402575
theorem B221567 : Blo 219811 221567 := bstep (se 1 (by rfl) ⟨166175, by rfl⟩ : syracuseStep 221567 = 332351) B332351
theorem B352649 : Blo 219811 352649 := bstep (se 2 (by rfl) ⟨132243, by rfl⟩ : syracuseStep 352649 = 264487) B264487
theorem B221647 : Blo 219811 221647 := bstep (se 1 (by rfl) ⟨166235, by rfl⟩ : syracuseStep 221647 = 332471) B332471
theorem B221799 : Blo 219811 221799 := bstep (se 1 (by rfl) ⟨166349, by rfl⟩ : syracuseStep 221799 = 332699) B332699
theorem B222063 : Blo 219811 222063 := bstep (se 1 (by rfl) ⟨166547, by rfl⟩ : syracuseStep 222063 = 333095) B333095
theorem B1598363 : Blo 219811 1598363 := bstep (se 1 (by rfl) ⟨1198772, by rfl⟩ : syracuseStep 1598363 = 2397545) B2397545
theorem B222119 : Blo 219811 222119 := bstep (se 1 (by rfl) ⟨166589, by rfl⟩ : syracuseStep 222119 = 333179) B333179
theorem B222203 : Blo 219811 222203 := bstep (se 1 (by rfl) ⟨166652, by rfl⟩ : syracuseStep 222203 = 333305) B333305
theorem B222271 : Blo 219811 222271 := bstep (se 1 (by rfl) ⟨166703, by rfl⟩ : syracuseStep 222271 = 333407) B333407
theorem B419023 : Blo 219811 419023 := bstep (se 1 (by rfl) ⟨314267, by rfl⟩ : syracuseStep 419023 = 628535) B628535
theorem B222415 : Blo 219811 222415 := bstep (se 1 (by rfl) ⟨166811, by rfl⟩ : syracuseStep 222415 = 333623) B333623
theorem B222619 : Blo 219811 222619 := bstep (se 1 (by rfl) ⟨166964, by rfl⟩ : syracuseStep 222619 = 333929) B333929
theorem B746927 : Blo 219811 746927 := bstep (se 1 (by rfl) ⟨560195, by rfl⟩ : syracuseStep 746927 = 1120391) B1120391
theorem B3008015 : Blo 219811 3008015 := bstep (se 1 (by rfl) ⟨2256011, by rfl⟩ : syracuseStep 3008015 = 4512023) B4512023
theorem B222831 : Blo 219811 222831 := bstep (se 1 (by rfl) ⟨167123, by rfl⟩ : syracuseStep 222831 = 334247) B334247
theorem B222887 : Blo 219811 222887 := bstep (se 1 (by rfl) ⟨167165, by rfl⟩ : syracuseStep 222887 = 334331) B334331
theorem B1140443 : Blo 219811 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B222971 : Blo 219811 222971 := bstep (se 1 (by rfl) ⟨167228, by rfl⟩ : syracuseStep 222971 = 334457) B334457
theorem B223007 : Blo 219811 223007 := bstep (se 1 (by rfl) ⟨167255, by rfl⟩ : syracuseStep 223007 = 334511) B334511
theorem B747305 : Blo 219811 747305 := bstep (se 2 (by rfl) ⟨280239, by rfl⟩ : syracuseStep 747305 = 560479) B560479
theorem B223039 : Blo 219811 223039 := bstep (se 1 (by rfl) ⟨167279, by rfl⟩ : syracuseStep 223039 = 334559) B334559
theorem B223215 : Blo 219811 223215 := bstep (se 1 (by rfl) ⟨167411, by rfl⟩ : syracuseStep 223215 = 334823) B334823
theorem B944237 : Blo 219811 944237 := bstep (se 3 (by rfl) ⟨177044, by rfl⟩ : syracuseStep 944237 = 354089) B354089
theorem B223387 : Blo 219811 223387 := bstep (se 1 (by rfl) ⟨167540, by rfl⟩ : syracuseStep 223387 = 335081) B335081
theorem B223423 : Blo 219811 223423 := bstep (se 1 (by rfl) ⟨167567, by rfl⟩ : syracuseStep 223423 = 335135) B335135
theorem B223535 : Blo 219811 223535 := bstep (se 1 (by rfl) ⟨167651, by rfl⟩ : syracuseStep 223535 = 335303) B335303
theorem B223771 : Blo 219811 223771 := bstep (se 1 (by rfl) ⟨167828, by rfl⟩ : syracuseStep 223771 = 335657) B335657
theorem B420383 : Blo 219811 420383 := bstep (se 1 (by rfl) ⟨315287, by rfl⟩ : syracuseStep 420383 = 630575) B630575
theorem B223775 : Blo 219811 223775 := bstep (se 1 (by rfl) ⟨167831, by rfl⟩ : syracuseStep 223775 = 335663) B335663
theorem B421787 : Blo 219811 421787 := bstep (se 1 (by rfl) ⟨316340, by rfl⟩ : syracuseStep 421787 = 632681) B632681
theorem B749519 : Blo 219811 749519 := bstep (se 1 (by rfl) ⟨562139, by rfl⟩ : syracuseStep 749519 = 1124279) B1124279
theorem B749951 : Blo 219811 749951 := bstep (se 1 (by rfl) ⟨562463, by rfl⟩ : syracuseStep 749951 = 1124927) B1124927
theorem B848465 : Blo 219811 848465 := bstep (se 2 (by rfl) ⟨318174, by rfl⟩ : syracuseStep 848465 = 636349) B636349
theorem B717427 : Blo 219811 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B7205597 : Blo 219811 7205597 := bstep (se 3 (by rfl) ⟨1351049, by rfl⟩ : syracuseStep 7205597 = 2702099) B2702099
theorem B1438859 : Blo 219811 1438859 := bstep (se 1 (by rfl) ⟨1079144, by rfl⟩ : syracuseStep 1438859 = 2158289) B2158289
theorem B173930165 : Blo 219811 173930165 := bstep (se 5 (by rfl) ⟨8152976, by rfl⟩ : syracuseStep 173930165 = 16305953) B16305953
theorem B947963 : Blo 219811 947963 := bstep (se 1 (by rfl) ⟨710972, by rfl⟩ : syracuseStep 947963 = 1421945) B1421945
theorem B751355 : Blo 219811 751355 := bstep (se 1 (by rfl) ⟨563516, by rfl⟩ : syracuseStep 751355 = 1127033) B1127033
theorem B6453107 : Blo 219811 6453107 := bstep (se 1 (by rfl) ⟨4839830, by rfl⟩ : syracuseStep 6453107 = 9679661) B9679661
theorem B751517 : Blo 219811 751517 := bstep (se 3 (by rfl) ⟨140909, by rfl⟩ : syracuseStep 751517 = 281819) B281819
theorem B423929 : Blo 219811 423929 := bstep (se 2 (by rfl) ⟨158973, by rfl⟩ : syracuseStep 423929 = 317947) B317947
theorem B2717873 : Blo 219811 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B752249 : Blo 219811 752249 := bstep (se 2 (by rfl) ⟨282093, by rfl⟩ : syracuseStep 752249 = 564187) B564187
theorem B752489 : Blo 219811 752489 := bstep (se 2 (by rfl) ⟨282183, by rfl⟩ : syracuseStep 752489 = 564367) B564367
theorem B752543 : Blo 219811 752543 := bstep (se 1 (by rfl) ⟨564407, by rfl⟩ : syracuseStep 752543 = 1128815) B1128815
theorem B1277549 : Blo 219811 1277549 := bstep (se 3 (by rfl) ⟨239540, by rfl⟩ : syracuseStep 1277549 = 479081) B479081
theorem B917887 : Blo 219811 917887 := bstep (se 1 (by rfl) ⟨688415, by rfl⟩ : syracuseStep 917887 = 1376831) B1376831
theorem B754271 : Blo 219811 754271 := bstep (se 1 (by rfl) ⟨565703, by rfl⟩ : syracuseStep 754271 = 1131407) B1131407
theorem B2720783 : Blo 219811 2720783 := bstep (se 1 (by rfl) ⟨2040587, by rfl⟩ : syracuseStep 2720783 = 4081175) B4081175
theorem B558697 : Blo 219811 558697 := bstep (se 2 (by rfl) ⟨209511, by rfl⟩ : syracuseStep 558697 = 419023) B419023
theorem B3180343 : Blo 219811 3180343 := bstep (se 1 (by rfl) ⟨2385257, by rfl⟩ : syracuseStep 3180343 = 4770515) B4770515
theorem B10192877 : Blo 219811 10192877 := bstep (se 3 (by rfl) ⟨1911164, by rfl⟩ : syracuseStep 10192877 = 3822329) B3822329
theorem B4818953 : Blo 219811 4818953 := bstep (se 2 (by rfl) ⟨1807107, by rfl⟩ : syracuseStep 4818953 = 3614215) B3614215
theorem B329759 : Blo 219811 329759 := bstep (se 1 (by rfl) ⟨247319, by rfl⟩ : syracuseStep 329759 = 494639) B494639
theorem B329951 : Blo 219811 329951 := bstep (se 1 (by rfl) ⟨247463, by rfl⟩ : syracuseStep 329951 = 494927) B494927
theorem B330011 : Blo 219811 330011 := bstep (se 1 (by rfl) ⟨247508, by rfl⟩ : syracuseStep 330011 = 495017) B495017
theorem B2853215 : Blo 219811 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B5212511 : Blo 219811 5212511 := bstep (se 1 (by rfl) ⟨3909383, by rfl⟩ : syracuseStep 5212511 = 7818767) B7818767
theorem B559487 : Blo 219811 559487 := bstep (se 1 (by rfl) ⟨419615, by rfl⟩ : syracuseStep 559487 = 839231) B839231
theorem B4786613 : Blo 219811 4786613 := bstep (se 5 (by rfl) ⟨224372, by rfl⟩ : syracuseStep 4786613 = 448745) B448745
theorem B330335 : Blo 219811 330335 := bstep (se 1 (by rfl) ⟨247751, by rfl⟩ : syracuseStep 330335 = 495503) B495503
theorem B330617 : Blo 219811 330617 := bstep (se 2 (by rfl) ⟨123981, by rfl⟩ : syracuseStep 330617 = 247963) B247963
theorem B330665 : Blo 219811 330665 := bstep (se 2 (by rfl) ⟨123999, by rfl⟩ : syracuseStep 330665 = 247999) B247999
theorem B1674269 : Blo 219811 1674269 := bstep (se 3 (by rfl) ⟨313925, by rfl⟩ : syracuseStep 1674269 = 627851) B627851
theorem B330815 : Blo 219811 330815 := bstep (se 1 (by rfl) ⟨248111, by rfl⟩ : syracuseStep 330815 = 496223) B496223
theorem B331367 : Blo 219811 331367 := bstep (se 1 (by rfl) ⟨248525, by rfl⟩ : syracuseStep 331367 = 497051) B497051
theorem B495431 : Blo 219811 495431 := bstep (se 1 (by rfl) ⟨371573, by rfl⟩ : syracuseStep 495431 = 743147) B743147
theorem B331751 : Blo 219811 331751 := bstep (se 1 (by rfl) ⟨248813, by rfl⟩ : syracuseStep 331751 = 497627) B497627
theorem B495611 : Blo 219811 495611 := bstep (se 1 (by rfl) ⟨371708, by rfl⟩ : syracuseStep 495611 = 743417) B743417
theorem B331871 : Blo 219811 331871 := bstep (se 1 (by rfl) ⟨248903, by rfl⟩ : syracuseStep 331871 = 497807) B497807
theorem B495719 : Blo 219811 495719 := bstep (se 1 (by rfl) ⟨371789, by rfl⟩ : syracuseStep 495719 = 743579) B743579
theorem B331883 : Blo 219811 331883 := bstep (se 1 (by rfl) ⟨248912, by rfl⟩ : syracuseStep 331883 = 497825) B497825
theorem B331931 : Blo 219811 331931 := bstep (se 1 (by rfl) ⟨248948, by rfl⟩ : syracuseStep 331931 = 497897) B497897
theorem B626849 : Blo 219811 626849 := bstep (se 2 (by rfl) ⟨235068, by rfl⟩ : syracuseStep 626849 = 470137) B470137
theorem B1413281 : Blo 219811 1413281 := bstep (se 2 (by rfl) ⟨529980, by rfl⟩ : syracuseStep 1413281 = 1059961) B1059961
theorem B495791 : Blo 219811 495791 := bstep (se 1 (by rfl) ⟨371843, by rfl⟩ : syracuseStep 495791 = 743687) B743687
theorem B14094691 : Blo 219811 14094691 := bstep (se 1 (by rfl) ⟨10571018, by rfl⟩ : syracuseStep 14094691 = 21142037) B21142037
theorem B528827 : Blo 219811 528827 := bstep (se 1 (by rfl) ⟨396620, by rfl⟩ : syracuseStep 528827 = 793241) B793241
theorem B954935 : Blo 219811 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B496475 : Blo 219811 496475 := bstep (se 1 (by rfl) ⟨372356, by rfl⟩ : syracuseStep 496475 = 744713) B744713
theorem B562079 : Blo 219811 562079 := bstep (se 1 (by rfl) ⟨421559, by rfl⟩ : syracuseStep 562079 = 843119) B843119
theorem B332783 : Blo 219811 332783 := bstep (se 1 (by rfl) ⟨249587, by rfl⟩ : syracuseStep 332783 = 499175) B499175
theorem B333167 : Blo 219811 333167 := bstep (se 1 (by rfl) ⟨249875, by rfl⟩ : syracuseStep 333167 = 499751) B499751
theorem B333287 : Blo 219811 333287 := bstep (se 1 (by rfl) ⟨249965, by rfl⟩ : syracuseStep 333287 = 499931) B499931
theorem B497231 : Blo 219811 497231 := bstep (se 1 (by rfl) ⟨372923, by rfl⟩ : syracuseStep 497231 = 745847) B745847
theorem B628307 : Blo 219811 628307 := bstep (se 1 (by rfl) ⟨471230, by rfl⟩ : syracuseStep 628307 = 942461) B942461
theorem B235099 : Blo 219811 235099 := bstep (se 1 (by rfl) ⟨176324, by rfl⟩ : syracuseStep 235099 = 352649) B352649
theorem B333449 : Blo 219811 333449 := bstep (se 2 (by rfl) ⟨125043, by rfl⟩ : syracuseStep 333449 = 250087) B250087
theorem B333467 : Blo 219811 333467 := bstep (se 1 (by rfl) ⟨250100, by rfl⟩ : syracuseStep 333467 = 500201) B500201
theorem B333659 : Blo 219811 333659 := bstep (se 1 (by rfl) ⟨250244, by rfl⟩ : syracuseStep 333659 = 500489) B500489
theorem B956569 : Blo 219811 956569 := bstep (se 2 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 956569 = 717427) B717427
theorem B334043 : Blo 219811 334043 := bstep (se 1 (by rfl) ⟨250532, by rfl⟩ : syracuseStep 334043 = 501065) B501065
theorem B497951 : Blo 219811 497951 := bstep (se 1 (by rfl) ⟨373463, by rfl⟩ : syracuseStep 497951 = 746927) B746927
theorem B2005343 : Blo 219811 2005343 := bstep (se 1 (by rfl) ⟨1504007, by rfl⟩ : syracuseStep 2005343 = 3008015) B3008015
theorem B760295 : Blo 219811 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B334313 : Blo 219811 334313 := bstep (se 2 (by rfl) ⟨125367, by rfl⟩ : syracuseStep 334313 = 250735) B250735
theorem B498203 : Blo 219811 498203 := bstep (se 1 (by rfl) ⟨373652, by rfl⟩ : syracuseStep 498203 = 747305) B747305
theorem B334703 : Blo 219811 334703 := bstep (se 1 (by rfl) ⟨251027, by rfl⟩ : syracuseStep 334703 = 502055) B502055
theorem B334715 : Blo 219811 334715 := bstep (se 1 (by rfl) ⟨251036, by rfl⟩ : syracuseStep 334715 = 502073) B502073
theorem B1121849 : Blo 219811 1121849 := bstep (se 2 (by rfl) ⟨420693, by rfl⟩ : syracuseStep 1121849 = 841387) B841387
theorem B1122011 : Blo 219811 1122011 := bstep (se 1 (by rfl) ⟨841508, by rfl⟩ : syracuseStep 1122011 = 1683017) B1683017
theorem B335579 : Blo 219811 335579 := bstep (se 1 (by rfl) ⟨251684, by rfl⟩ : syracuseStep 335579 = 503369) B503369
theorem B1056503 : Blo 219811 1056503 := bstep (se 1 (by rfl) ⟨792377, by rfl⟩ : syracuseStep 1056503 = 1584755) B1584755
theorem B499553 : Blo 219811 499553 := bstep (se 2 (by rfl) ⟨187332, by rfl⟩ : syracuseStep 499553 = 374665) B374665
theorem B794569 : Blo 219811 794569 := bstep (se 2 (by rfl) ⟨297963, by rfl⟩ : syracuseStep 794569 = 595927) B595927
theorem B499679 : Blo 219811 499679 := bstep (se 1 (by rfl) ⟨374759, by rfl⟩ : syracuseStep 499679 = 749519) B749519
theorem B499967 : Blo 219811 499967 := bstep (se 1 (by rfl) ⟨374975, by rfl⟩ : syracuseStep 499967 = 749951) B749951
theorem B1712387 : Blo 219811 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B565643 : Blo 219811 565643 := bstep (se 1 (by rfl) ⟨424232, by rfl⟩ : syracuseStep 565643 = 848465) B848465
theorem B500129 : Blo 219811 500129 := bstep (se 2 (by rfl) ⟨187548, by rfl⟩ : syracuseStep 500129 = 375097) B375097
theorem B7709357 : Blo 219811 7709357 := bstep (se 3 (by rfl) ⟨1445504, by rfl⟩ : syracuseStep 7709357 = 2891009) B2891009
theorem B959239 : Blo 219811 959239 := bstep (se 1 (by rfl) ⟨719429, by rfl⟩ : syracuseStep 959239 = 1438859) B1438859
theorem B533279 : Blo 219811 533279 := bstep (se 1 (by rfl) ⟨399959, by rfl⟩ : syracuseStep 533279 = 799919) B799919
theorem B631975 : Blo 219811 631975 := bstep (se 1 (by rfl) ⟨473981, by rfl⟩ : syracuseStep 631975 = 947963) B947963
theorem B500903 : Blo 219811 500903 := bstep (se 1 (by rfl) ⟨375677, by rfl⟩ : syracuseStep 500903 = 751355) B751355
theorem B4236461 : Blo 219811 4236461 := bstep (se 3 (by rfl) ⟨794336, by rfl⟩ : syracuseStep 4236461 = 1588673) B1588673
theorem B4302071 : Blo 219811 4302071 := bstep (se 1 (by rfl) ⟨3226553, by rfl⟩ : syracuseStep 4302071 = 6453107) B6453107
theorem B501011 : Blo 219811 501011 := bstep (se 1 (by rfl) ⟨375758, by rfl⟩ : syracuseStep 501011 = 751517) B751517
theorem B1811915 : Blo 219811 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B1123955 : Blo 219811 1123955 := bstep (se 1 (by rfl) ⟨842966, by rfl⟩ : syracuseStep 1123955 = 1685933) B1685933
theorem B501499 : Blo 219811 501499 := bstep (se 1 (by rfl) ⟨376124, by rfl⟩ : syracuseStep 501499 = 752249) B752249
theorem B501641 : Blo 219811 501641 := bstep (se 2 (by rfl) ⟨188115, by rfl⟩ : syracuseStep 501641 = 376231) B376231
theorem B501659 : Blo 219811 501659 := bstep (se 1 (by rfl) ⟨376244, by rfl⟩ : syracuseStep 501659 = 752489) B752489
theorem B501695 : Blo 219811 501695 := bstep (se 1 (by rfl) ⟨376271, by rfl⟩ : syracuseStep 501695 = 752543) B752543
theorem B501857 : Blo 219811 501857 := bstep (se 2 (by rfl) ⟨188196, by rfl⟩ : syracuseStep 501857 = 376393) B376393
theorem B3221633 : Blo 219811 3221633 := bstep (se 2 (by rfl) ⟨1208112, by rfl⟩ : syracuseStep 3221633 = 2416225) B2416225
theorem B534671 : Blo 219811 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B1190123 : Blo 219811 1190123 := bstep (se 1 (by rfl) ⟨892592, by rfl⟩ : syracuseStep 1190123 = 1785185) B1785185
theorem B2173241 : Blo 219811 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B1517939 : Blo 219811 1517939 := bstep (se 1 (by rfl) ⟨1138454, by rfl⟩ : syracuseStep 1517939 = 2276909) B2276909
theorem B371081 : Blo 219811 371081 := bstep (se 2 (by rfl) ⟨139155, by rfl⟩ : syracuseStep 371081 = 278311) B278311
theorem B1124765 : Blo 219811 1124765 := bstep (se 3 (by rfl) ⟨210893, by rfl⟩ : syracuseStep 1124765 = 421787) B421787
theorem B535519 : Blo 219811 535519 := bstep (se 1 (by rfl) ⟨401639, by rfl⟩ : syracuseStep 535519 = 803279) B803279
theorem B1125575 : Blo 219811 1125575 := bstep (se 1 (by rfl) ⟨844181, by rfl⟩ : syracuseStep 1125575 = 1688363) B1688363
theorem B797971 : Blo 219811 797971 := bstep (se 1 (by rfl) ⟨598478, by rfl⟩ : syracuseStep 797971 = 1196957) B1196957
theorem B503207 : Blo 219811 503207 := bstep (se 1 (by rfl) ⟨377405, by rfl⟩ : syracuseStep 503207 = 754811) B754811
theorem B1256887 : Blo 219811 1256887 := bstep (se 1 (by rfl) ⟨942665, by rfl⟩ : syracuseStep 1256887 = 1885331) B1885331
theorem B503387 : Blo 219811 503387 := bstep (se 1 (by rfl) ⟨377540, by rfl⟩ : syracuseStep 503387 = 755081) B755081
theorem B569065 : Blo 219811 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B896939 : Blo 219811 896939 := bstep (se 1 (by rfl) ⟨672704, by rfl⟩ : syracuseStep 896939 = 1345409) B1345409
theorem B372809 : Blo 219811 372809 := bstep (se 2 (by rfl) ⟨139803, by rfl⟩ : syracuseStep 372809 = 279607) B279607
theorem B372863 : Blo 219811 372863 := bstep (se 1 (by rfl) ⟨279647, by rfl⟩ : syracuseStep 372863 = 559295) B559295
theorem B569483 : Blo 219811 569483 := bstep (se 1 (by rfl) ⟨427112, by rfl⟩ : syracuseStep 569483 = 854225) B854225
theorem B504083 : Blo 219811 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B1684475 : Blo 219811 1684475 := bstep (se 1 (by rfl) ⟨1263356, by rfl⟩ : syracuseStep 1684475 = 2526713) B2526713
theorem B373801 : Blo 219811 373801 := bstep (se 2 (by rfl) ⟨140175, by rfl⟩ : syracuseStep 373801 = 280351) B280351
theorem B373943 : Blo 219811 373943 := bstep (se 1 (by rfl) ⟨280457, by rfl⟩ : syracuseStep 373943 = 560915) B560915
theorem B374699 : Blo 219811 374699 := bstep (se 1 (by rfl) ⟨281024, by rfl⟩ : syracuseStep 374699 = 562049) B562049
theorem B637067 : Blo 219811 637067 := bstep (se 1 (by rfl) ⟨477800, by rfl⟩ : syracuseStep 637067 = 955601) B955601
theorem B375239 : Blo 219811 375239 := bstep (se 1 (by rfl) ⟨281429, by rfl⟩ : syracuseStep 375239 = 562859) B562859
theorem B375455 : Blo 219811 375455 := bstep (se 1 (by rfl) ⟨281591, by rfl⟩ : syracuseStep 375455 = 563183) B563183
theorem B375529 : Blo 219811 375529 := bstep (se 2 (by rfl) ⟨140823, by rfl⟩ : syracuseStep 375529 = 281647) B281647
theorem B2571365 : Blo 219811 2571365 := bstep (se 4 (by rfl) ⟨241065, by rfl⟩ : syracuseStep 2571365 = 482131) B482131
theorem B4308299 : Blo 219811 4308299 := bstep (se 1 (by rfl) ⟨3231224, by rfl⟩ : syracuseStep 4308299 = 6462449) B6462449
theorem B835069 : Blo 219811 835069 := bstep (se 3 (by rfl) ⟨156575, by rfl⟩ : syracuseStep 835069 = 313151) B313151
theorem B1195897 : Blo 219811 1195897 := bstep (se 2 (by rfl) ⟨448461, by rfl⟩ : syracuseStep 1195897 = 896923) B896923
theorem B836027 : Blo 219811 836027 := bstep (se 1 (by rfl) ⟨627020, by rfl⟩ : syracuseStep 836027 = 1254041) B1254041
theorem B967099 : Blo 219811 967099 := bstep (se 1 (by rfl) ⟨725324, by rfl⟩ : syracuseStep 967099 = 1450649) B1450649
theorem B1065575 : Blo 219811 1065575 := bstep (se 1 (by rfl) ⟨799181, by rfl⟩ : syracuseStep 1065575 = 1598363) B1598363
theorem B3196027 : Blo 219811 3196027 := bstep (se 1 (by rfl) ⟨2397020, by rfl⟩ : syracuseStep 3196027 = 4794041) B4794041
theorem B23250199 : Blo 219811 23250199 := bstep (se 1 (by rfl) ⟨17437649, by rfl⟩ : syracuseStep 23250199 = 34875299) B34875299
theorem B837287 : Blo 219811 837287 := bstep (se 1 (by rfl) ⟨627965, by rfl⟩ : syracuseStep 837287 = 1255931) B1255931
theorem B280255 : Blo 219811 280255 := bstep (se 1 (by rfl) ⟨210191, by rfl⟩ : syracuseStep 280255 = 420383) B420383
theorem B247855 : Blo 219811 247855 := bstep (se 1 (by rfl) ⟨185891, by rfl⟩ : syracuseStep 247855 = 371783) B371783
theorem B30951517 : Blo 219811 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B248143 : Blo 219811 248143 := bstep (se 1 (by rfl) ⟨186107, by rfl⟩ : syracuseStep 248143 = 372215) B372215
theorem B838259 : Blo 219811 838259 := bstep (se 1 (by rfl) ⟨628694, by rfl⟩ : syracuseStep 838259 = 1257389) B1257389
theorem B707449 : Blo 219811 707449 := bstep (se 2 (by rfl) ⟨265293, by rfl⟩ : syracuseStep 707449 = 530587) B530587
theorem B1428353 : Blo 219811 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B8702963 : Blo 219811 8702963 := bstep (se 1 (by rfl) ⟨6527222, by rfl⟩ : syracuseStep 8702963 = 13054445) B13054445
theorem B248827 : Blo 219811 248827 := bstep (se 1 (by rfl) ⟨186620, by rfl⟩ : syracuseStep 248827 = 373241) B373241
theorem B4803731 : Blo 219811 4803731 := bstep (se 1 (by rfl) ⟨3602798, by rfl⟩ : syracuseStep 4803731 = 7205597) B7205597
theorem B249007 : Blo 219811 249007 := bstep (se 1 (by rfl) ⟨186755, by rfl⟩ : syracuseStep 249007 = 373511) B373511
theorem B2117153 : Blo 219811 2117153 := bstep (se 2 (by rfl) ⟨793932, by rfl⟩ : syracuseStep 2117153 = 1587865) B1587865
theorem B839443 : Blo 219811 839443 := bstep (se 1 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 839443 = 1259165) B1259165
theorem B115953443 : Blo 219811 115953443 := bstep (se 1 (by rfl) ⟨86965082, by rfl⟩ : syracuseStep 115953443 = 173930165) B173930165
theorem B3198797 : Blo 219811 3198797 := bstep (se 3 (by rfl) ⟨599774, by rfl⟩ : syracuseStep 3198797 = 1199549) B1199549
theorem B249727 : Blo 219811 249727 := bstep (se 1 (by rfl) ⟨187295, by rfl⟩ : syracuseStep 249727 = 374591) B374591
theorem B282619 : Blo 219811 282619 := bstep (se 1 (by rfl) ⟨211964, by rfl⟩ : syracuseStep 282619 = 423929) B423929
theorem B2674853 : Blo 219811 2674853 := bstep (se 4 (by rfl) ⟨250767, by rfl⟩ : syracuseStep 2674853 = 501535) B501535
theorem B4837643 : Blo 219811 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B250267 : Blo 219811 250267 := bstep (se 1 (by rfl) ⟨187700, by rfl⟩ : syracuseStep 250267 = 375401) B375401
theorem B250951 : Blo 219811 250951 := bstep (se 1 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 250951 = 376427) B376427
theorem B251131 : Blo 219811 251131 := bstep (se 1 (by rfl) ⟨188348, by rfl⟩ : syracuseStep 251131 = 376697) B376697
theorem B1430891 : Blo 219811 1430891 := bstep (se 1 (by rfl) ⟨1073168, by rfl⟩ : syracuseStep 1430891 = 2146337) B2146337
theorem B1431377 : Blo 219811 1431377 := bstep (se 2 (by rfl) ⟨536766, by rfl⟩ : syracuseStep 1431377 = 1073533) B1073533
theorem B841661 : Blo 219811 841661 := bstep (se 3 (by rfl) ⟨157811, by rfl⟩ : syracuseStep 841661 = 315623) B315623
theorem B841691 : Blo 219811 841691 := bstep (se 1 (by rfl) ⟨631268, by rfl⟩ : syracuseStep 841691 = 1262537) B1262537
theorem B1431917 : Blo 219811 1431917 := bstep (se 3 (by rfl) ⟨268484, by rfl⟩ : syracuseStep 1431917 = 536969) B536969
theorem B940855 : Blo 219811 940855 := bstep (se 1 (by rfl) ⟨705641, by rfl⟩ : syracuseStep 940855 = 1411283) B1411283
theorem B219975 : Blo 219811 219975 := bstep (se 1 (by rfl) ⟨164981, by rfl⟩ : syracuseStep 219975 = 329963) B329963
theorem B220015 : Blo 219811 220015 := bstep (se 1 (by rfl) ⟨165011, by rfl⟩ : syracuseStep 220015 = 330023) B330023
theorem B285563 : Blo 219811 285563 := bstep (se 1 (by rfl) ⟨214172, by rfl⟩ : syracuseStep 285563 = 428345) B428345
theorem B220071 : Blo 219811 220071 := bstep (se 1 (by rfl) ⟨165053, by rfl⟩ : syracuseStep 220071 = 330107) B330107
theorem B220251 : Blo 219811 220251 := bstep (se 1 (by rfl) ⟨165188, by rfl⟩ : syracuseStep 220251 = 330377) B330377
theorem B220367 : Blo 219811 220367 := bstep (se 1 (by rfl) ⟨165275, by rfl⟩ : syracuseStep 220367 = 330551) B330551
theorem B220391 : Blo 219811 220391 := bstep (se 1 (by rfl) ⟨165293, by rfl⟩ : syracuseStep 220391 = 330587) B330587
theorem B220487 : Blo 219811 220487 := bstep (se 1 (by rfl) ⟨165365, by rfl⟩ : syracuseStep 220487 = 330731) B330731
theorem B6413741 : Blo 219811 6413741 := bstep (se 3 (by rfl) ⟨1202576, by rfl⟩ : syracuseStep 6413741 = 2405153) B2405153
theorem B220623 : Blo 219811 220623 := bstep (se 1 (by rfl) ⟨165467, by rfl⟩ : syracuseStep 220623 = 330935) B330935
theorem B220783 : Blo 219811 220783 := bstep (se 1 (by rfl) ⟨165587, by rfl⟩ : syracuseStep 220783 = 331175) B331175
theorem B220839 : Blo 219811 220839 := bstep (se 1 (by rfl) ⟨165629, by rfl⟩ : syracuseStep 220839 = 331259) B331259
theorem B220903 : Blo 219811 220903 := bstep (se 1 (by rfl) ⟨165677, by rfl⟩ : syracuseStep 220903 = 331355) B331355
theorem B220959 : Blo 219811 220959 := bstep (se 1 (by rfl) ⟨165719, by rfl⟩ : syracuseStep 220959 = 331439) B331439
theorem B3825443 : Blo 219811 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B221039 : Blo 219811 221039 := bstep (se 1 (by rfl) ⟨165779, by rfl⟩ : syracuseStep 221039 = 331559) B331559
theorem B221095 : Blo 219811 221095 := bstep (se 1 (by rfl) ⟨165821, by rfl⟩ : syracuseStep 221095 = 331643) B331643
theorem B2613383 : Blo 219811 2613383 := bstep (se 1 (by rfl) ⟨1960037, by rfl⟩ : syracuseStep 2613383 = 3920075) B3920075
theorem B221375 : Blo 219811 221375 := bstep (se 1 (by rfl) ⟨166031, by rfl⟩ : syracuseStep 221375 = 332063) B332063
theorem B221391 : Blo 219811 221391 := bstep (se 1 (by rfl) ⟨166043, by rfl⟩ : syracuseStep 221391 = 332087) B332087
theorem B221439 : Blo 219811 221439 := bstep (se 1 (by rfl) ⟨166079, by rfl⟩ : syracuseStep 221439 = 332159) B332159
theorem B221487 : Blo 219811 221487 := bstep (se 1 (by rfl) ⟨166115, by rfl⟩ : syracuseStep 221487 = 332231) B332231
theorem B844303 : Blo 219811 844303 := bstep (se 1 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 844303 = 1266455) B1266455
theorem B221723 : Blo 219811 221723 := bstep (se 1 (by rfl) ⟨166292, by rfl⟩ : syracuseStep 221723 = 332585) B332585
theorem B221727 : Blo 219811 221727 := bstep (se 1 (by rfl) ⟨166295, by rfl⟩ : syracuseStep 221727 = 332591) B332591
theorem B221807 : Blo 219811 221807 := bstep (se 1 (by rfl) ⟨166355, by rfl⟩ : syracuseStep 221807 = 332711) B332711
theorem B221863 : Blo 219811 221863 := bstep (se 1 (by rfl) ⟨166397, by rfl⟩ : syracuseStep 221863 = 332795) B332795
theorem B221903 : Blo 219811 221903 := bstep (se 1 (by rfl) ⟨166427, by rfl⟩ : syracuseStep 221903 = 332855) B332855
theorem B3203819 : Blo 219811 3203819 := bstep (se 1 (by rfl) ⟨2402864, by rfl⟩ : syracuseStep 3203819 = 4805729) B4805729
theorem B221983 : Blo 219811 221983 := bstep (se 1 (by rfl) ⟨166487, by rfl⟩ : syracuseStep 221983 = 332975) B332975
theorem B222255 : Blo 219811 222255 := bstep (se 1 (by rfl) ⟨166691, by rfl⟩ : syracuseStep 222255 = 333383) B333383
theorem B222319 : Blo 219811 222319 := bstep (se 1 (by rfl) ⟨166739, by rfl⟩ : syracuseStep 222319 = 333479) B333479
theorem B222375 : Blo 219811 222375 := bstep (se 1 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 222375 = 333563) B333563
theorem B222399 : Blo 219811 222399 := bstep (se 1 (by rfl) ⟨166799, by rfl⟩ : syracuseStep 222399 = 333599) B333599
theorem B222431 : Blo 219811 222431 := bstep (se 1 (by rfl) ⟨166823, by rfl⟩ : syracuseStep 222431 = 333647) B333647
theorem B222511 : Blo 219811 222511 := bstep (se 1 (by rfl) ⟨166883, by rfl⟩ : syracuseStep 222511 = 333767) B333767
theorem B943417 : Blo 219811 943417 := bstep (se 2 (by rfl) ⟨353781, by rfl⟩ : syracuseStep 943417 = 707563) B707563
theorem B1074707 : Blo 219811 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B747035 : Blo 219811 747035 := bstep (se 1 (by rfl) ⟨560276, by rfl⟩ : syracuseStep 747035 = 1120553) B1120553
theorem B222747 : Blo 219811 222747 := bstep (se 1 (by rfl) ⟨167060, by rfl⟩ : syracuseStep 222747 = 334121) B334121
theorem B222751 : Blo 219811 222751 := bstep (se 1 (by rfl) ⟨167063, by rfl⟩ : syracuseStep 222751 = 334127) B334127
theorem B9791165 : Blo 219811 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B222911 : Blo 219811 222911 := bstep (se 1 (by rfl) ⟨167183, by rfl⟩ : syracuseStep 222911 = 334367) B334367
theorem B2746075 : Blo 219811 2746075 := bstep (se 1 (by rfl) ⟨2059556, by rfl⟩ : syracuseStep 2746075 = 4119113) B4119113
theorem B1697597 : Blo 219811 1697597 := bstep (se 3 (by rfl) ⟨318299, by rfl⟩ : syracuseStep 1697597 = 636599) B636599
theorem B223167 : Blo 219811 223167 := bstep (se 1 (by rfl) ⟨167375, by rfl⟩ : syracuseStep 223167 = 334751) B334751
theorem B223199 : Blo 219811 223199 := bstep (se 1 (by rfl) ⟨167399, by rfl⟩ : syracuseStep 223199 = 334799) B334799
theorem B714739 : Blo 219811 714739 := bstep (se 1 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 714739 = 1072109) B1072109
theorem B223259 : Blo 219811 223259 := bstep (se 1 (by rfl) ⟨167444, by rfl⟩ : syracuseStep 223259 = 334889) B334889
theorem B223263 : Blo 219811 223263 := bstep (se 1 (by rfl) ⟨167447, by rfl⟩ : syracuseStep 223263 = 334895) B334895
theorem B223279 : Blo 219811 223279 := bstep (se 1 (by rfl) ⟨167459, by rfl⟩ : syracuseStep 223279 = 334919) B334919
theorem B846035 : Blo 219811 846035 := bstep (se 1 (by rfl) ⟨634526, by rfl⟩ : syracuseStep 846035 = 1269053) B1269053
theorem B223455 : Blo 219811 223455 := bstep (se 1 (by rfl) ⟨167591, by rfl⟩ : syracuseStep 223455 = 335183) B335183
theorem B223515 : Blo 219811 223515 := bstep (se 1 (by rfl) ⟨167636, by rfl⟩ : syracuseStep 223515 = 335273) B335273
theorem B223615 : Blo 219811 223615 := bstep (se 1 (by rfl) ⟨167711, by rfl⟩ : syracuseStep 223615 = 335423) B335423
theorem B1010207 : Blo 219811 1010207 := bstep (se 1 (by rfl) ⟨757655, by rfl⟩ : syracuseStep 1010207 = 1515311) B1515311
theorem B223791 : Blo 219811 223791 := bstep (se 1 (by rfl) ⟨167843, by rfl⟩ : syracuseStep 223791 = 335687) B335687
theorem B2517965 : Blo 219811 2517965 := bstep (se 3 (by rfl) ⟨472118, by rfl⟩ : syracuseStep 2517965 = 944237) B944237
theorem B420815 : Blo 219811 420815 := bstep (se 1 (by rfl) ⟨315611, by rfl⟩ : syracuseStep 420815 = 631223) B631223
theorem B224251 : Blo 219811 224251 := bstep (se 1 (by rfl) ⟨168188, by rfl⟩ : syracuseStep 224251 = 336377) B336377
theorem B1895993 : Blo 219811 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B1273427 : Blo 219811 1273427 := bstep (se 1 (by rfl) ⟨955070, by rfl⟩ : syracuseStep 1273427 = 1910141) B1910141
theorem B3862225 : Blo 219811 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B2387681 : Blo 219811 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B14282477 : Blo 219811 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B422995 : Blo 219811 422995 := bstep (se 1 (by rfl) ⟨317246, by rfl⟩ : syracuseStep 422995 = 634493) B634493
theorem B13727981 : Blo 219811 13727981 := bstep (se 3 (by rfl) ⟨2573996, by rfl⟩ : syracuseStep 13727981 = 5147993) B5147993
theorem B752219 : Blo 219811 752219 := bstep (se 1 (by rfl) ⟨564164, by rfl⟩ : syracuseStep 752219 = 1128329) B1128329
theorem B1342097 : Blo 219811 1342097 := bstep (se 2 (by rfl) ⟨503286, by rfl⟩ : syracuseStep 1342097 = 1006573) B1006573
theorem B424673 : Blo 219811 424673 := bstep (se 2 (by rfl) ⟨159252, by rfl⟩ : syracuseStep 424673 = 318505) B318505
theorem B2128841 : Blo 219811 2128841 := bstep (se 2 (by rfl) ⟨798315, by rfl⟩ : syracuseStep 2128841 = 1596631) B1596631
theorem B752921 : Blo 219811 752921 := bstep (se 2 (by rfl) ⟨282345, by rfl⟩ : syracuseStep 752921 = 564691) B564691
theorem B1277435 : Blo 219811 1277435 := bstep (se 1 (by rfl) ⟨958076, by rfl⟩ : syracuseStep 1277435 = 1916153) B1916153
theorem B1670867 : Blo 219811 1670867 := bstep (se 1 (by rfl) ⟨1253150, by rfl⟩ : syracuseStep 1670867 = 2506301) B2506301
theorem B851699 : Blo 219811 851699 := bstep (se 1 (by rfl) ⟨638774, by rfl⟩ : syracuseStep 851699 = 1277549) B1277549
theorem B5668703 : Blo 219811 5668703 := bstep (se 1 (by rfl) ⟨4251527, by rfl⟩ : syracuseStep 5668703 = 8503055) B8503055
theorem B557351 : Blo 219811 557351 := bstep (se 1 (by rfl) ⟨418013, by rfl⟩ : syracuseStep 557351 = 836027) B836027
theorem B1344221 : Blo 219811 1344221 := bstep (se 3 (by rfl) ⟨252041, by rfl⟩ : syracuseStep 1344221 = 504083) B504083
theorem B1278985 : Blo 219811 1278985 := bstep (se 2 (by rfl) ⟨479619, by rfl⟩ : syracuseStep 1278985 = 959239) B959239
theorem B558191 : Blo 219811 558191 := bstep (se 1 (by rfl) ⟨418643, by rfl⟩ : syracuseStep 558191 = 837287) B837287
theorem B1410205 : Blo 219811 1410205 := bstep (se 3 (by rfl) ⟨264413, by rfl⟩ : syracuseStep 1410205 = 528827) B528827
theorem B3212635 : Blo 219811 3212635 := bstep (se 1 (by rfl) ⟨2409476, by rfl⟩ : syracuseStep 3212635 = 4818953) B4818953
theorem B4261369 : Blo 219811 4261369 := bstep (se 2 (by rfl) ⟨1598013, by rfl⟩ : syracuseStep 4261369 = 3196027) B3196027
theorem B1902143 : Blo 219811 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B3475007 : Blo 219811 3475007 := bstep (se 1 (by rfl) ⟨2606255, by rfl⟩ : syracuseStep 3475007 = 5212511) B5212511
theorem B31000265 : Blo 219811 31000265 := bstep (se 2 (by rfl) ⟨11625099, by rfl⟩ : syracuseStep 31000265 = 23250199) B23250199
theorem B558839 : Blo 219811 558839 := bstep (se 1 (by rfl) ⟨419129, by rfl⟩ : syracuseStep 558839 = 838259) B838259
theorem B75171685 : Blo 219811 75171685 := bstep (se 4 (by rfl) ⟨7047345, by rfl⟩ : syracuseStep 75171685 = 14094691) B14094691
theorem B952235 : Blo 219811 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B5801975 : Blo 219811 5801975 := bstep (se 1 (by rfl) ⟨4351481, by rfl⟩ : syracuseStep 5801975 = 8702963) B8702963
theorem B1116179 : Blo 219811 1116179 := bstep (se 1 (by rfl) ⟨837134, by rfl⟩ : syracuseStep 1116179 = 1674269) B1674269
theorem B1411435 : Blo 219811 1411435 := bstep (se 1 (by rfl) ⟨1058576, by rfl⟩ : syracuseStep 1411435 = 2117153) B2117153
theorem B77302295 : Blo 219811 77302295 := bstep (se 1 (by rfl) ⟨57976721, by rfl⟩ : syracuseStep 77302295 = 115953443) B115953443
theorem B330287 : Blo 219811 330287 := bstep (se 1 (by rfl) ⟨247715, by rfl⟩ : syracuseStep 330287 = 495431) B495431
theorem B2132531 : Blo 219811 2132531 := bstep (se 1 (by rfl) ⟨1599398, by rfl⟩ : syracuseStep 2132531 = 3198797) B3198797
theorem B952985 : Blo 219811 952985 := bstep (se 2 (by rfl) ⟨357369, by rfl⟩ : syracuseStep 952985 = 714739) B714739
theorem B330407 : Blo 219811 330407 := bstep (se 1 (by rfl) ⟨247805, by rfl⟩ : syracuseStep 330407 = 495611) B495611
theorem B330473 : Blo 219811 330473 := bstep (se 2 (by rfl) ⟨123927, by rfl⟩ : syracuseStep 330473 = 247855) B247855
theorem B330479 : Blo 219811 330479 := bstep (se 1 (by rfl) ⟨247859, by rfl⟩ : syracuseStep 330479 = 495719) B495719
theorem B330527 : Blo 219811 330527 := bstep (se 1 (by rfl) ⟨247895, by rfl⟩ : syracuseStep 330527 = 495791) B495791
theorem B330857 : Blo 219811 330857 := bstep (se 2 (by rfl) ⟨124071, by rfl⟩ : syracuseStep 330857 = 248143) B248143
theorem B330983 : Blo 219811 330983 := bstep (se 1 (by rfl) ⟨248237, by rfl⟩ : syracuseStep 330983 = 496475) B496475
theorem B953927 : Blo 219811 953927 := bstep (se 1 (by rfl) ⟨715445, by rfl⟩ : syracuseStep 953927 = 1430891) B1430891
theorem B331487 : Blo 219811 331487 := bstep (se 1 (by rfl) ⟨248615, by rfl⟩ : syracuseStep 331487 = 497231) B497231
theorem B954251 : Blo 219811 954251 := bstep (se 1 (by rfl) ⟨715688, by rfl⟩ : syracuseStep 954251 = 1431377) B1431377
theorem B561107 : Blo 219811 561107 := bstep (se 1 (by rfl) ⟨420830, by rfl⟩ : syracuseStep 561107 = 841661) B841661
theorem B561127 : Blo 219811 561127 := bstep (se 1 (by rfl) ⟨420845, by rfl⟩ : syracuseStep 561127 = 841691) B841691
theorem B331769 : Blo 219811 331769 := bstep (se 2 (by rfl) ⟨124413, by rfl⟩ : syracuseStep 331769 = 248827) B248827
theorem B331967 : Blo 219811 331967 := bstep (se 1 (by rfl) ⟨248975, by rfl⟩ : syracuseStep 331967 = 497951) B497951
theorem B332009 : Blo 219811 332009 := bstep (se 2 (by rfl) ⟨124503, by rfl⟩ : syracuseStep 332009 = 249007) B249007
theorem B954611 : Blo 219811 954611 := bstep (se 1 (by rfl) ⟨715958, by rfl⟩ : syracuseStep 954611 = 1431917) B1431917
theorem B332135 : Blo 219811 332135 := bstep (se 1 (by rfl) ⟨249101, by rfl⟩ : syracuseStep 332135 = 498203) B498203
theorem B758753 : Blo 219811 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B1119257 : Blo 219811 1119257 := bstep (se 2 (by rfl) ⟨419721, by rfl⟩ : syracuseStep 1119257 = 839443) B839443
theorem B332969 : Blo 219811 332969 := bstep (se 2 (by rfl) ⟨124863, by rfl⟩ : syracuseStep 332969 = 249727) B249727
theorem B333035 : Blo 219811 333035 := bstep (se 1 (by rfl) ⟨249776, by rfl⟩ : syracuseStep 333035 = 499553) B499553
theorem B333119 : Blo 219811 333119 := bstep (se 1 (by rfl) ⟨249839, by rfl⟩ : syracuseStep 333119 = 499679) B499679
theorem B1742255 : Blo 219811 1742255 := bstep (se 1 (by rfl) ⟨1306691, by rfl⟩ : syracuseStep 1742255 = 2613383) B2613383
theorem B333311 : Blo 219811 333311 := bstep (se 1 (by rfl) ⟨249983, by rfl⟩ : syracuseStep 333311 = 499967) B499967
theorem B333419 : Blo 219811 333419 := bstep (se 1 (by rfl) ⟨250064, by rfl⟩ : syracuseStep 333419 = 500129) B500129
theorem B2135879 : Blo 219811 2135879 := bstep (se 1 (by rfl) ⟨1601909, by rfl⟩ : syracuseStep 2135879 = 3203819) B3203819
theorem B333689 : Blo 219811 333689 := bstep (se 2 (by rfl) ⟨125133, by rfl⟩ : syracuseStep 333689 = 250267) B250267
theorem B333935 : Blo 219811 333935 := bstep (se 1 (by rfl) ⟨250451, by rfl⟩ : syracuseStep 333935 = 500903) B500903
theorem B2824307 : Blo 219811 2824307 := bstep (se 1 (by rfl) ⟨2118230, by rfl⟩ : syracuseStep 2824307 = 4236461) B4236461
theorem B334007 : Blo 219811 334007 := bstep (se 1 (by rfl) ⟨250505, by rfl⟩ : syracuseStep 334007 = 501011) B501011
theorem B498023 : Blo 219811 498023 := bstep (se 1 (by rfl) ⟨373517, by rfl⟩ : syracuseStep 498023 = 747035) B747035
theorem B334427 : Blo 219811 334427 := bstep (se 1 (by rfl) ⟨250820, by rfl⟩ : syracuseStep 334427 = 501641) B501641
theorem B334439 : Blo 219811 334439 := bstep (se 1 (by rfl) ⟨250829, by rfl⟩ : syracuseStep 334439 = 501659) B501659
theorem B334463 : Blo 219811 334463 := bstep (se 1 (by rfl) ⟨250847, by rfl⟩ : syracuseStep 334463 = 501695) B501695
theorem B498401 : Blo 219811 498401 := bstep (se 2 (by rfl) ⟨186900, by rfl⟩ : syracuseStep 498401 = 373801) B373801
theorem B334571 : Blo 219811 334571 := bstep (se 1 (by rfl) ⟨250928, by rfl⟩ : syracuseStep 334571 = 501857) B501857
theorem B334601 : Blo 219811 334601 := bstep (se 2 (by rfl) ⟨125475, by rfl⟩ : syracuseStep 334601 = 250951) B250951
theorem B563993 : Blo 219811 563993 := bstep (se 2 (by rfl) ⟨211497, by rfl⟩ : syracuseStep 563993 = 422995) B422995
theorem B564023 : Blo 219811 564023 := bstep (se 1 (by rfl) ⟨423017, by rfl⟩ : syracuseStep 564023 = 846035) B846035
theorem B793415 : Blo 219811 793415 := bstep (se 1 (by rfl) ⟨595061, by rfl⟩ : syracuseStep 793415 = 1190123) B1190123
theorem B334841 : Blo 219811 334841 := bstep (se 2 (by rfl) ⟨125565, by rfl⟩ : syracuseStep 334841 = 251131) B251131
theorem B1678643 : Blo 219811 1678643 := bstep (se 1 (by rfl) ⟨1258982, by rfl⟩ : syracuseStep 1678643 = 2517965) B2517965
theorem B335471 : Blo 219811 335471 := bstep (se 1 (by rfl) ⟨251603, by rfl⟩ : syracuseStep 335471 = 503207) B503207
theorem B761501 : Blo 219811 761501 := bstep (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) B285563
theorem B335591 : Blo 219811 335591 := bstep (se 1 (by rfl) ⟨251693, by rfl⟩ : syracuseStep 335591 = 503387) B503387
theorem B1122173 : Blo 219811 1122173 := bstep (se 3 (by rfl) ⟨210407, by rfl⟩ : syracuseStep 1122173 = 420815) B420815
theorem B597959 : Blo 219811 597959 := bstep (se 1 (by rfl) ⟨448469, by rfl⟩ : syracuseStep 597959 = 896939) B896939
theorem B1122983 : Blo 219811 1122983 := bstep (se 1 (by rfl) ⟨842237, by rfl⟩ : syracuseStep 1122983 = 1684475) B1684475
theorem B500705 : Blo 219811 500705 := bstep (se 2 (by rfl) ⟨187764, by rfl⟩ : syracuseStep 500705 = 375529) B375529
theorem B1254473 : Blo 219811 1254473 := bstep (se 2 (by rfl) ⟨470427, by rfl⟩ : syracuseStep 1254473 = 940855) B940855
theorem B9151987 : Blo 219811 9151987 := bstep (se 1 (by rfl) ⟨6863990, by rfl⟩ : syracuseStep 9151987 = 13727981) B13727981
theorem B501479 : Blo 219811 501479 := bstep (se 1 (by rfl) ⟨376109, by rfl⟩ : syracuseStep 501479 = 752219) B752219
theorem B894731 : Blo 219811 894731 := bstep (se 1 (by rfl) ⟨671048, by rfl⟩ : syracuseStep 894731 = 1342097) B1342097
theorem B1419227 : Blo 219811 1419227 := bstep (se 1 (by rfl) ⟨1064420, by rfl⟩ : syracuseStep 1419227 = 2128841) B2128841
theorem B1714243 : Blo 219811 1714243 := bstep (se 1 (by rfl) ⟨1285682, by rfl⟩ : syracuseStep 1714243 = 2571365) B2571365
theorem B501947 : Blo 219811 501947 := bstep (se 1 (by rfl) ⟨376460, by rfl⟩ : syracuseStep 501947 = 752921) B752921
theorem B567799 : Blo 219811 567799 := bstep (se 1 (by rfl) ⟨425849, by rfl⟩ : syracuseStep 567799 = 851699) B851699
theorem B3779135 : Blo 219811 3779135 := bstep (se 1 (by rfl) ⟨2834351, by rfl⟩ : syracuseStep 3779135 = 5668703) B5668703
theorem B1059425 : Blo 219811 1059425 := bstep (se 2 (by rfl) ⟨397284, by rfl⟩ : syracuseStep 1059425 = 794569) B794569
theorem B502847 : Blo 219811 502847 := bstep (se 1 (by rfl) ⟨377135, by rfl⟩ : syracuseStep 502847 = 754271) B754271
theorem B1223849 : Blo 219811 1223849 := bstep (se 2 (by rfl) ⟨458943, by rfl⟩ : syracuseStep 1223849 = 917887) B917887
theorem B1289465 : Blo 219811 1289465 := bstep (se 2 (by rfl) ⟨483549, by rfl⟩ : syracuseStep 1289465 = 967099) B967099
theorem B4566365 : Blo 219811 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B1813855 : Blo 219811 1813855 := bstep (se 1 (by rfl) ⟨1360391, by rfl⟩ : syracuseStep 1813855 = 2720783) B2720783
theorem B1125737 : Blo 219811 1125737 := bstep (se 2 (by rfl) ⟨422151, by rfl⟩ : syracuseStep 1125737 = 844303) B844303
theorem B6795251 : Blo 219811 6795251 := bstep (se 1 (by rfl) ⟨5096438, by rfl⟩ : syracuseStep 6795251 = 10192877) B10192877
theorem B372991 : Blo 219811 372991 := bstep (se 1 (by rfl) ⟨279743, by rfl⟩ : syracuseStep 372991 = 559487) B559487
theorem B3191075 : Blo 219811 3191075 := bstep (se 1 (by rfl) ⟨2393306, by rfl⟩ : syracuseStep 3191075 = 4786613) B4786613
theorem B1257889 : Blo 219811 1257889 := bstep (se 2 (by rfl) ⟨471708, by rfl⟩ : syracuseStep 1257889 = 943417) B943417
theorem B373673 : Blo 219811 373673 := bstep (se 2 (by rfl) ⟨140127, by rfl⟩ : syracuseStep 373673 = 280255) B280255
theorem B668665 : Blo 219811 668665 := bstep (se 2 (by rfl) ⟨250749, by rfl⟩ : syracuseStep 668665 = 501499) B501499
theorem B4240457 : Blo 219811 4240457 := bstep (se 2 (by rfl) ⟨1590171, by rfl⟩ : syracuseStep 4240457 = 3180343) B3180343
theorem B1783235 : Blo 219811 1783235 := bstep (se 1 (by rfl) ⟨1337426, by rfl⟩ : syracuseStep 1783235 = 2674853) B2674853
theorem B41268689 : Blo 219811 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B3225095 : Blo 219811 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B636623 : Blo 219811 636623 := bstep (se 1 (by rfl) ⟨477467, by rfl⟩ : syracuseStep 636623 = 954935) B954935
theorem B374719 : Blo 219811 374719 := bstep (se 1 (by rfl) ⟨281039, by rfl⟩ : syracuseStep 374719 = 562079) B562079
theorem B506863 : Blo 219811 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B1063961 : Blo 219811 1063961 := bstep (se 2 (by rfl) ⟨398985, by rfl⟩ : syracuseStep 1063961 = 797971) B797971
theorem B4275827 : Blo 219811 4275827 := bstep (se 1 (by rfl) ⟨3206870, by rfl⟩ : syracuseStep 4275827 = 6413741) B6413741
theorem B704335 : Blo 219811 704335 := bstep (se 1 (by rfl) ⟨528251, by rfl⟩ : syracuseStep 704335 = 1056503) B1056503
theorem B1196005 : Blo 219811 1196005 := bstep (se 4 (by rfl) ⟨112125, by rfl⟩ : syracuseStep 1196005 = 224251) B224251
theorem B376825 : Blo 219811 376825 := bstep (se 2 (by rfl) ⟨141309, by rfl⟩ : syracuseStep 376825 = 282619) B282619
theorem B377095 : Blo 219811 377095 := bstep (se 1 (by rfl) ⟨282821, by rfl⟩ : syracuseStep 377095 = 565643) B565643
theorem B2868047 : Blo 219811 2868047 := bstep (se 1 (by rfl) ⟨2151035, by rfl⟩ : syracuseStep 2868047 = 4302071) B4302071
theorem B1131731 : Blo 219811 1131731 := bstep (se 1 (by rfl) ⟨848798, by rfl⟩ : syracuseStep 1131731 = 1697597) B1697597
theorem B2147755 : Blo 219811 2147755 := bstep (se 1 (by rfl) ⟨1610816, by rfl⟩ : syracuseStep 2147755 = 3221633) B3221633
theorem B247387 : Blo 219811 247387 := bstep (se 1 (by rfl) ⟨185540, by rfl⟩ : syracuseStep 247387 = 371081) B371081
theorem B673471 : Blo 219811 673471 := bstep (se 1 (by rfl) ⟨505103, by rfl⟩ : syracuseStep 673471 = 1010207) B1010207
theorem B313465 : Blo 219811 313465 := bstep (se 2 (by rfl) ⟨117549, by rfl⟩ : syracuseStep 313465 = 235099) B235099
theorem B6703397 : Blo 219811 6703397 := bstep (se 4 (by rfl) ⟨628443, by rfl⟩ : syracuseStep 6703397 = 1256887) B1256887
theorem B1263995 : Blo 219811 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B1591787 : Blo 219811 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B9521651 : Blo 219811 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B248539 : Blo 219811 248539 := bstep (se 1 (by rfl) ⟨186404, by rfl⟩ : syracuseStep 248539 = 372809) B372809
theorem B248575 : Blo 219811 248575 := bstep (se 1 (by rfl) ⟨186431, by rfl⟩ : syracuseStep 248575 = 372863) B372863
theorem B379655 : Blo 219811 379655 := bstep (se 1 (by rfl) ⟨284741, by rfl⟩ : syracuseStep 379655 = 569483) B569483
theorem B249295 : Blo 219811 249295 := bstep (se 1 (by rfl) ⟨186971, by rfl⟩ : syracuseStep 249295 = 373943) B373943
theorem B20598533 : Blo 219811 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B249799 : Blo 219811 249799 := bstep (se 1 (by rfl) ⟨187349, by rfl⟩ : syracuseStep 249799 = 374699) B374699
theorem B250159 : Blo 219811 250159 := bstep (se 1 (by rfl) ⟨187619, by rfl⟩ : syracuseStep 250159 = 375239) B375239
theorem B250303 : Blo 219811 250303 := bstep (se 1 (by rfl) ⟨187727, by rfl⟩ : syracuseStep 250303 = 375455) B375455
theorem B283115 : Blo 219811 283115 := bstep (se 1 (by rfl) ⟨212336, by rfl⟩ : syracuseStep 283115 = 424673) B424673
theorem B2872199 : Blo 219811 2872199 := bstep (se 1 (by rfl) ⟨2154149, by rfl⟩ : syracuseStep 2872199 = 4308299) B4308299
theorem B1594529 : Blo 219811 1594529 := bstep (se 2 (by rfl) ⟨597948, by rfl⟩ : syracuseStep 1594529 = 1195897) B1195897
theorem B710383 : Blo 219811 710383 := bstep (se 1 (by rfl) ⟨532787, by rfl⟩ : syracuseStep 710383 = 1065575) B1065575
theorem B219839 : Blo 219811 219839 := bstep (se 1 (by rfl) ⟨164879, by rfl⟩ : syracuseStep 219839 = 329759) B329759
theorem B219967 : Blo 219811 219967 := bstep (se 1 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 219967 = 329951) B329951
theorem B220007 : Blo 219811 220007 := bstep (se 1 (by rfl) ⟨165005, by rfl⟩ : syracuseStep 220007 = 330011) B330011
theorem B842633 : Blo 219811 842633 := bstep (se 2 (by rfl) ⟨315987, by rfl⟩ : syracuseStep 842633 = 631975) B631975
theorem B220223 : Blo 219811 220223 := bstep (se 1 (by rfl) ⟨165167, by rfl⟩ : syracuseStep 220223 = 330335) B330335
theorem B220411 : Blo 219811 220411 := bstep (se 1 (by rfl) ⟨165308, by rfl⟩ : syracuseStep 220411 = 330617) B330617
theorem B220443 : Blo 219811 220443 := bstep (se 1 (by rfl) ⟨165332, by rfl⟩ : syracuseStep 220443 = 330665) B330665
theorem B220543 : Blo 219811 220543 := bstep (se 1 (by rfl) ⟨165407, by rfl⟩ : syracuseStep 220543 = 330815) B330815
theorem B3202487 : Blo 219811 3202487 := bstep (se 1 (by rfl) ⟨2401865, by rfl⟩ : syracuseStep 3202487 = 4803731) B4803731
theorem B744929 : Blo 219811 744929 := bstep (se 2 (by rfl) ⟨279348, by rfl⟩ : syracuseStep 744929 = 558697) B558697
theorem B3661433 : Blo 219811 3661433 := bstep (se 2 (by rfl) ⟨1373037, by rfl⟩ : syracuseStep 3661433 = 2746075) B2746075
theorem B220911 : Blo 219811 220911 := bstep (se 1 (by rfl) ⟨165683, by rfl⟩ : syracuseStep 220911 = 331367) B331367
theorem B221167 : Blo 219811 221167 := bstep (se 1 (by rfl) ⟨165875, by rfl⟩ : syracuseStep 221167 = 331751) B331751
theorem B221247 : Blo 219811 221247 := bstep (se 1 (by rfl) ⟨165935, by rfl⟩ : syracuseStep 221247 = 331871) B331871
theorem B221255 : Blo 219811 221255 := bstep (se 1 (by rfl) ⟨165941, by rfl⟩ : syracuseStep 221255 = 331883) B331883
theorem B221287 : Blo 219811 221287 := bstep (se 1 (by rfl) ⟨165965, by rfl⟩ : syracuseStep 221287 = 331931) B331931
theorem B417899 : Blo 219811 417899 := bstep (se 1 (by rfl) ⟨313424, by rfl⟩ : syracuseStep 417899 = 626849) B626849
theorem B942187 : Blo 219811 942187 := bstep (se 1 (by rfl) ⟨706640, by rfl⟩ : syracuseStep 942187 = 1413281) B1413281
theorem B221855 : Blo 219811 221855 := bstep (se 1 (by rfl) ⟨166391, by rfl⟩ : syracuseStep 221855 = 332783) B332783
theorem B222111 : Blo 219811 222111 := bstep (se 1 (by rfl) ⟨166583, by rfl⟩ : syracuseStep 222111 = 333167) B333167
theorem B222191 : Blo 219811 222191 := bstep (se 1 (by rfl) ⟨166643, by rfl⟩ : syracuseStep 222191 = 333287) B333287
theorem B418871 : Blo 219811 418871 := bstep (se 1 (by rfl) ⟨314153, by rfl⟩ : syracuseStep 418871 = 628307) B628307
theorem B222299 : Blo 219811 222299 := bstep (se 1 (by rfl) ⟨166724, by rfl⟩ : syracuseStep 222299 = 333449) B333449
theorem B222311 : Blo 219811 222311 := bstep (se 1 (by rfl) ⟨166733, by rfl⟩ : syracuseStep 222311 = 333467) B333467
theorem B943265 : Blo 219811 943265 := bstep (se 2 (by rfl) ⟨353724, by rfl⟩ : syracuseStep 943265 = 707449) B707449
theorem B222439 : Blo 219811 222439 := bstep (se 1 (by rfl) ⟨166829, by rfl⟩ : syracuseStep 222439 = 333659) B333659
theorem B714025 : Blo 219811 714025 := bstep (se 2 (by rfl) ⟨267759, by rfl⟩ : syracuseStep 714025 = 535519) B535519
theorem B222695 : Blo 219811 222695 := bstep (se 1 (by rfl) ⟨167021, by rfl⟩ : syracuseStep 222695 = 334043) B334043
theorem B1336895 : Blo 219811 1336895 := bstep (se 1 (by rfl) ⟨1002671, by rfl⟩ : syracuseStep 1336895 = 2005343) B2005343
theorem B222875 : Blo 219811 222875 := bstep (se 1 (by rfl) ⟨167156, by rfl⟩ : syracuseStep 222875 = 334313) B334313
theorem B26109773 : Blo 219811 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B223135 : Blo 219811 223135 := bstep (se 1 (by rfl) ⟨167351, by rfl⟩ : syracuseStep 223135 = 334703) B334703
theorem B223143 : Blo 219811 223143 := bstep (se 1 (by rfl) ⟨167357, by rfl⟩ : syracuseStep 223143 = 334715) B334715
theorem B747899 : Blo 219811 747899 := bstep (se 1 (by rfl) ⟨560924, by rfl⟩ : syracuseStep 747899 = 1121849) B1121849
theorem B748007 : Blo 219811 748007 := bstep (se 1 (by rfl) ⟨561005, by rfl⟩ : syracuseStep 748007 = 1122011) B1122011
theorem B223719 : Blo 219811 223719 := bstep (se 1 (by rfl) ⟨167789, by rfl⟩ : syracuseStep 223719 = 335579) B335579
theorem B2550295 : Blo 219811 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B5139571 : Blo 219811 5139571 := bstep (se 1 (by rfl) ⟨3854678, by rfl⟩ : syracuseStep 5139571 = 7709357) B7709357
theorem B355519 : Blo 219811 355519 := bstep (se 1 (by rfl) ⟨266639, by rfl⟩ : syracuseStep 355519 = 533279) B533279
theorem B5795309 : Blo 219811 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B1207943 : Blo 219811 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B716471 : Blo 219811 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B749303 : Blo 219811 749303 := bstep (se 1 (by rfl) ⟨561977, by rfl⟩ : syracuseStep 749303 = 1123955) B1123955
theorem B356447 : Blo 219811 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B1011959 : Blo 219811 1011959 := bstep (se 1 (by rfl) ⟨758969, by rfl⟩ : syracuseStep 1011959 = 1517939) B1517939
theorem B749843 : Blo 219811 749843 := bstep (se 1 (by rfl) ⟨562382, by rfl⟩ : syracuseStep 749843 = 1124765) B1124765
theorem B750383 : Blo 219811 750383 := bstep (se 1 (by rfl) ⟨562787, by rfl⟩ : syracuseStep 750383 = 1125575) B1125575
theorem B848951 : Blo 219811 848951 := bstep (se 1 (by rfl) ⟨636713, by rfl⟩ : syracuseStep 848951 = 1273427) B1273427
theorem B1275425 : Blo 219811 1275425 := bstep (se 2 (by rfl) ⟨478284, by rfl⟩ : syracuseStep 1275425 = 956569) B956569
theorem B424711 : Blo 219811 424711 := bstep (se 1 (by rfl) ⟨318533, by rfl⟩ : syracuseStep 424711 = 637067) B637067
theorem B1113425 : Blo 219811 1113425 := bstep (se 2 (by rfl) ⟨417534, by rfl⟩ : syracuseStep 1113425 = 835069) B835069
theorem B851623 : Blo 219811 851623 := bstep (se 1 (by rfl) ⟨638717, by rfl⟩ : syracuseStep 851623 = 1277435) B1277435
theorem B1113911 : Blo 219811 1113911 := bstep (se 1 (by rfl) ⟨835433, by rfl⟩ : syracuseStep 1113911 = 1670867) B1670867
theorem B950525 : Blo 219811 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B1114397 : Blo 219811 1114397 := bstep (se 3 (by rfl) ⟨208949, by rfl⟩ : syracuseStep 1114397 = 417899) B417899
theorem B754487 : Blo 219811 754487 := bstep (se 1 (by rfl) ⟨565865, by rfl⟩ : syracuseStep 754487 = 1131731) B1131731
theorem B754973 : Blo 219811 754973 := bstep (se 3 (by rfl) ⟨141557, by rfl⟩ : syracuseStep 754973 = 283115) B283115
theorem B3867983 : Blo 219811 3867983 := bstep (se 1 (by rfl) ⟨2900987, by rfl⟩ : syracuseStep 3867983 = 5801975) B5801975
theorem B1705313 : Blo 219811 1705313 := bstep (se 2 (by rfl) ⟨639492, by rfl⟩ : syracuseStep 1705313 = 1278985) B1278985
theorem B952033 : Blo 219811 952033 := bstep (se 2 (by rfl) ⟨357012, by rfl⟩ : syracuseStep 952033 = 714025) B714025
theorem B329849 : Blo 219811 329849 := bstep (se 2 (by rfl) ⟨123693, by rfl⟩ : syracuseStep 329849 = 247387) B247387
theorem B13732355 : Blo 219811 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B1116989 : Blo 219811 1116989 := bstep (se 3 (by rfl) ⟨209435, by rfl⟩ : syracuseStep 1116989 = 418871) B418871
theorem B331385 : Blo 219811 331385 := bstep (se 2 (by rfl) ⟨124269, by rfl⟩ : syracuseStep 331385 = 248539) B248539
theorem B331433 : Blo 219811 331433 := bstep (se 2 (by rfl) ⟨124287, by rfl⟩ : syracuseStep 331433 = 248575) B248575
theorem B6852761 : Blo 219811 6852761 := bstep (se 2 (by rfl) ⟨2569785, by rfl⟩ : syracuseStep 6852761 = 5139571) B5139571
theorem B332015 : Blo 219811 332015 := bstep (se 1 (by rfl) ⟨249011, by rfl⟩ : syracuseStep 332015 = 498023) B498023
theorem B332267 : Blo 219811 332267 := bstep (se 1 (by rfl) ⟨249200, by rfl⟩ : syracuseStep 332267 = 498401) B498401
theorem B528943 : Blo 219811 528943 := bstep (se 1 (by rfl) ⟨396707, by rfl⟩ : syracuseStep 528943 = 793415) B793415
theorem B561755 : Blo 219811 561755 := bstep (se 1 (by rfl) ⟨421316, by rfl⟩ : syracuseStep 561755 = 842633) B842633
theorem B332393 : Blo 219811 332393 := bstep (se 2 (by rfl) ⟨124647, by rfl⟩ : syracuseStep 332393 = 249295) B249295
theorem B1119095 : Blo 219811 1119095 := bstep (se 1 (by rfl) ⟨839321, by rfl⟩ : syracuseStep 1119095 = 1678643) B1678643
theorem B2134991 : Blo 219811 2134991 := bstep (se 1 (by rfl) ⟨1601243, by rfl⟩ : syracuseStep 2134991 = 3202487) B3202487
theorem B496619 : Blo 219811 496619 := bstep (se 1 (by rfl) ⟨372464, by rfl⟩ : syracuseStep 496619 = 744929) B744929
theorem B333065 : Blo 219811 333065 := bstep (se 2 (by rfl) ⟨124899, by rfl⟩ : syracuseStep 333065 = 249799) B249799
theorem B398639 : Blo 219811 398639 := bstep (se 1 (by rfl) ⟨298979, by rfl⟩ : syracuseStep 398639 = 597959) B597959
theorem B497321 : Blo 219811 497321 := bstep (se 2 (by rfl) ⟨186495, by rfl⟩ : syracuseStep 497321 = 372991) B372991
theorem B333545 : Blo 219811 333545 := bstep (se 2 (by rfl) ⟨125079, by rfl⟩ : syracuseStep 333545 = 250159) B250159
theorem B1677185 : Blo 219811 1677185 := bstep (se 2 (by rfl) ⟨628944, by rfl⟩ : syracuseStep 1677185 = 1257889) B1257889
theorem B333737 : Blo 219811 333737 := bstep (se 2 (by rfl) ⟨125151, by rfl⟩ : syracuseStep 333737 = 250303) B250303
theorem B333803 : Blo 219811 333803 := bstep (se 1 (by rfl) ⟨250352, by rfl⟩ : syracuseStep 333803 = 500705) B500705
theorem B628843 : Blo 219811 628843 := bstep (se 1 (by rfl) ⟨471632, by rfl⟩ : syracuseStep 628843 = 943265) B943265
theorem B891263 : Blo 219811 891263 := bstep (se 1 (by rfl) ⟨668447, by rfl⟩ : syracuseStep 891263 = 1336895) B1336895
theorem B334319 : Blo 219811 334319 := bstep (se 1 (by rfl) ⟨250739, by rfl⟩ : syracuseStep 334319 = 501479) B501479
theorem B17406515 : Blo 219811 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B334631 : Blo 219811 334631 := bstep (se 1 (by rfl) ⟨250973, by rfl⟩ : syracuseStep 334631 = 501947) B501947
theorem B498599 : Blo 219811 498599 := bstep (se 1 (by rfl) ⟨373949, by rfl⟩ : syracuseStep 498599 = 747899) B747899
theorem B498671 : Blo 219811 498671 := bstep (se 1 (by rfl) ⟨374003, by rfl⟩ : syracuseStep 498671 = 748007) B748007
theorem B335231 : Blo 219811 335231 := bstep (se 1 (by rfl) ⟨251423, by rfl⟩ : syracuseStep 335231 = 502847) B502847
theorem B859643 : Blo 219811 859643 := bstep (se 1 (by rfl) ⟨644732, by rfl⟩ : syracuseStep 859643 = 1289465) B1289465
theorem B499535 : Blo 219811 499535 := bstep (se 1 (by rfl) ⟨374651, by rfl⟩ : syracuseStep 499535 = 749303) B749303
theorem B499625 : Blo 219811 499625 := bstep (se 2 (by rfl) ⟨187359, by rfl⟩ : syracuseStep 499625 = 374719) B374719
theorem B4530167 : Blo 219811 4530167 := bstep (se 1 (by rfl) ⟨3397625, by rfl⟩ : syracuseStep 4530167 = 6795251) B6795251
theorem B499895 : Blo 219811 499895 := bstep (se 1 (by rfl) ⟨374921, by rfl⟩ : syracuseStep 499895 = 749843) B749843
theorem B500255 : Blo 219811 500255 := bstep (se 1 (by rfl) ⟨375191, by rfl⟩ : syracuseStep 500255 = 750383) B750383
theorem B565967 : Blo 219811 565967 := bstep (se 1 (by rfl) ⟨424475, by rfl⟩ : syracuseStep 565967 = 848951) B848951
theorem B2826971 : Blo 219811 2826971 := bstep (se 1 (by rfl) ⟨2120228, by rfl⟩ : syracuseStep 2826971 = 4240457) B4240457
theorem B1188823 : Blo 219811 1188823 := bstep (se 1 (by rfl) ⟨891617, by rfl⟩ : syracuseStep 1188823 = 1783235) B1783235
theorem B566281 : Blo 219811 566281 := bstep (se 2 (by rfl) ⟨212355, by rfl⟩ : syracuseStep 566281 = 424711) B424711
theorem B502433 : Blo 219811 502433 := bstep (se 2 (by rfl) ⟨188412, by rfl⟩ : syracuseStep 502433 = 376825) B376825
theorem B1256249 : Blo 219811 1256249 := bstep (se 2 (by rfl) ⟨471093, by rfl⟩ : syracuseStep 1256249 = 942187) B942187
theorem B371567 : Blo 219811 371567 := bstep (se 1 (by rfl) ⟨278675, by rfl⟩ : syracuseStep 371567 = 557351) B557351
theorem B502793 : Blo 219811 502793 := bstep (se 2 (by rfl) ⟨188547, by rfl⟩ : syracuseStep 502793 = 377095) B377095
theorem B896147 : Blo 219811 896147 := bstep (se 1 (by rfl) ⟨672110, by rfl⟩ : syracuseStep 896147 = 1344221) B1344221
theorem B1912031 : Blo 219811 1912031 := bstep (se 1 (by rfl) ⟨1434023, by rfl⟩ : syracuseStep 1912031 = 2868047) B2868047
theorem B372127 : Blo 219811 372127 := bstep (se 1 (by rfl) ⟨279095, by rfl⟩ : syracuseStep 372127 = 558191) B558191
theorem B372559 : Blo 219811 372559 := bstep (se 1 (by rfl) ⟨279419, by rfl⟩ : syracuseStep 372559 = 558839) B558839
theorem B634823 : Blo 219811 634823 := bstep (se 1 (by rfl) ⟨476117, by rfl⟩ : syracuseStep 634823 = 952235) B952235
theorem B4468931 : Blo 219811 4468931 := bstep (se 1 (by rfl) ⟨3351698, by rfl⟩ : syracuseStep 4468931 = 6703397) B6703397
theorem B1880273 : Blo 219811 1880273 := bstep (se 2 (by rfl) ⟨705102, by rfl⟩ : syracuseStep 1880273 = 1410205) B1410205
theorem B1061191 : Blo 219811 1061191 := bstep (se 1 (by rfl) ⟨795893, by rfl⟩ : syracuseStep 1061191 = 1591787) B1591787
theorem B1421687 : Blo 219811 1421687 := bstep (se 1 (by rfl) ⟨1066265, by rfl⟩ : syracuseStep 1421687 = 2132531) B2132531
theorem B2863673 : Blo 219811 2863673 := bstep (se 2 (by rfl) ⟨1073877, by rfl⟩ : syracuseStep 2863673 = 2147755) B2147755
theorem B12202649 : Blo 219811 12202649 := bstep (se 2 (by rfl) ⟨4575993, by rfl⟩ : syracuseStep 12202649 = 9151987) B9151987
theorem B5681825 : Blo 219811 5681825 := bstep (se 2 (by rfl) ⟨2130684, by rfl⟩ : syracuseStep 5681825 = 4261369) B4261369
theorem B897961 : Blo 219811 897961 := bstep (se 2 (by rfl) ⟨336735, by rfl⟩ : syracuseStep 897961 = 673471) B673471
theorem B635951 : Blo 219811 635951 := bstep (se 1 (by rfl) ⟨476963, by rfl⟩ : syracuseStep 635951 = 953927) B953927
theorem B636167 : Blo 219811 636167 := bstep (se 1 (by rfl) ⟨477125, by rfl⟩ : syracuseStep 636167 = 954251) B954251
theorem B3028261 : Blo 219811 3028261 := bstep (se 4 (by rfl) ⟨283899, by rfl⟩ : syracuseStep 3028261 = 567799) B567799
theorem B374071 : Blo 219811 374071 := bstep (se 1 (by rfl) ⟨280553, by rfl⟩ : syracuseStep 374071 = 561107) B561107
theorem B636407 : Blo 219811 636407 := bstep (se 1 (by rfl) ⟨477305, by rfl⟩ : syracuseStep 636407 = 954611) B954611
theorem B1881913 : Blo 219811 1881913 := bstep (se 2 (by rfl) ⟨705717, by rfl⟩ : syracuseStep 1881913 = 1411435) B1411435
theorem B1914799 : Blo 219811 1914799 := bstep (se 1 (by rfl) ⟨1436099, by rfl⟩ : syracuseStep 1914799 = 2872199) B2872199
theorem B505835 : Blo 219811 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B1063019 : Blo 219811 1063019 := bstep (se 1 (by rfl) ⟨797264, by rfl⟩ : syracuseStep 1063019 = 1594529) B1594529
theorem B1161503 : Blo 219811 1161503 := bstep (se 1 (by rfl) ⟨871127, by rfl⟩ : syracuseStep 1161503 = 1742255) B1742255
theorem B1423919 : Blo 219811 1423919 := bstep (se 1 (by rfl) ⟨1067939, by rfl⟩ : syracuseStep 1423919 = 2135879) B2135879
theorem B1882871 : Blo 219811 1882871 := bstep (se 1 (by rfl) ⟨1412153, by rfl⟩ : syracuseStep 1882871 = 2824307) B2824307
theorem B474025 : Blo 219811 474025 := bstep (se 2 (by rfl) ⟨177759, by rfl⟩ : syracuseStep 474025 = 355519) B355519
theorem B375995 : Blo 219811 375995 := bstep (se 1 (by rfl) ⟨281996, by rfl⟩ : syracuseStep 375995 = 563993) B563993
theorem B376015 : Blo 219811 376015 := bstep (se 1 (by rfl) ⟨282011, by rfl⟩ : syracuseStep 376015 = 564023) B564023
theorem B2440955 : Blo 219811 2440955 := bstep (se 1 (by rfl) ⟨1830716, by rfl⟩ : syracuseStep 2440955 = 3661433) B3661433
theorem B507667 : Blo 219811 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B2703269 : Blo 219811 2703269 := bstep (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) B506863
theorem B836315 : Blo 219811 836315 := bstep (se 1 (by rfl) ⟨627236, by rfl⟩ : syracuseStep 836315 = 1254473) B1254473
theorem B706283 : Blo 219811 706283 := bstep (se 1 (by rfl) ⟨529712, by rfl⟩ : syracuseStep 706283 = 1059425) B1059425
theorem B2541293 : Blo 219811 2541293 := bstep (se 3 (by rfl) ⟨476492, by rfl⟩ : syracuseStep 2541293 = 952985) B952985
theorem B805295 : Blo 219811 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B477647 : Blo 219811 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B674639 : Blo 219811 674639 := bstep (se 1 (by rfl) ⟨505979, by rfl⟩ : syracuseStep 674639 = 1011959) B1011959
theorem B3263597 : Blo 219811 3263597 := bstep (se 3 (by rfl) ⟨611924, by rfl⟩ : syracuseStep 3263597 = 1223849) B1223849
theorem B249115 : Blo 219811 249115 := bstep (se 1 (by rfl) ⟨186836, by rfl⟩ : syracuseStep 249115 = 373673) B373673
theorem B4541989 : Blo 219811 4541989 := bstep (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) B851623
theorem B27512459 : Blo 219811 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B2150063 : Blo 219811 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B709307 : Blo 219811 709307 := bstep (se 1 (by rfl) ⟨531980, by rfl⟩ : syracuseStep 709307 = 1063961) B1063961
theorem B742283 : Blo 219811 742283 := bstep (se 1 (by rfl) ⟨556712, by rfl⟩ : syracuseStep 742283 = 1113425) B1113425
theorem B939113 : Blo 219811 939113 := bstep (se 2 (by rfl) ⟨352167, by rfl⟩ : syracuseStep 939113 = 704335) B704335
theorem B742607 : Blo 219811 742607 := bstep (se 1 (by rfl) ⟨556955, by rfl⟩ : syracuseStep 742607 = 1113911) B1113911
theorem B1594673 : Blo 219811 1594673 := bstep (se 2 (by rfl) ⟨598002, by rfl⟩ : syracuseStep 1594673 = 1196005) B1196005
theorem B1268095 : Blo 219811 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B2316671 : Blo 219811 2316671 := bstep (se 1 (by rfl) ⟨1737503, by rfl⟩ : syracuseStep 2316671 = 3475007) B3475007
theorem B20666843 : Blo 219811 20666843 := bstep (se 1 (by rfl) ⟨15500132, by rfl⟩ : syracuseStep 20666843 = 31000265) B31000265
theorem B744119 : Blo 219811 744119 := bstep (se 1 (by rfl) ⟨558089, by rfl⟩ : syracuseStep 744119 = 1116179) B1116179
theorem B842663 : Blo 219811 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B6347767 : Blo 219811 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B51534863 : Blo 219811 51534863 := bstep (se 1 (by rfl) ⟨38651147, by rfl⟩ : syracuseStep 51534863 = 77302295) B77302295
theorem B220191 : Blo 219811 220191 := bstep (se 1 (by rfl) ⟨165143, by rfl⟩ : syracuseStep 220191 = 330287) B330287
theorem B220271 : Blo 219811 220271 := bstep (se 1 (by rfl) ⟨165203, by rfl⟩ : syracuseStep 220271 = 330407) B330407
theorem B4283513 : Blo 219811 4283513 := bstep (se 2 (by rfl) ⟨1606317, by rfl⟩ : syracuseStep 4283513 = 3212635) B3212635
theorem B220315 : Blo 219811 220315 := bstep (se 1 (by rfl) ⟨165236, by rfl⟩ : syracuseStep 220315 = 330473) B330473
theorem B220319 : Blo 219811 220319 := bstep (se 1 (by rfl) ⟨165239, by rfl⟩ : syracuseStep 220319 = 330479) B330479
theorem B253103 : Blo 219811 253103 := bstep (se 1 (by rfl) ⟨189827, by rfl⟩ : syracuseStep 253103 = 379655) B379655
theorem B220351 : Blo 219811 220351 := bstep (se 1 (by rfl) ⟨165263, by rfl⟩ : syracuseStep 220351 = 330527) B330527
theorem B220571 : Blo 219811 220571 := bstep (se 1 (by rfl) ⟨165428, by rfl⟩ : syracuseStep 220571 = 330857) B330857
theorem B220655 : Blo 219811 220655 := bstep (se 1 (by rfl) ⟨165491, by rfl⟩ : syracuseStep 220655 = 330983) B330983
theorem B100228913 : Blo 219811 100228913 := bstep (se 2 (by rfl) ⟨37585842, by rfl⟩ : syracuseStep 100228913 = 75171685) B75171685
theorem B220991 : Blo 219811 220991 := bstep (se 1 (by rfl) ⟨165743, by rfl⟩ : syracuseStep 220991 = 331487) B331487
theorem B221179 : Blo 219811 221179 := bstep (se 1 (by rfl) ⟨165884, by rfl⟩ : syracuseStep 221179 = 331769) B331769
theorem B2285657 : Blo 219811 2285657 := bstep (se 2 (by rfl) ⟨857121, by rfl⟩ : syracuseStep 2285657 = 1714243) B1714243
theorem B221311 : Blo 219811 221311 := bstep (se 1 (by rfl) ⟨165983, by rfl⟩ : syracuseStep 221311 = 331967) B331967
theorem B221339 : Blo 219811 221339 := bstep (se 1 (by rfl) ⟨166004, by rfl⟩ : syracuseStep 221339 = 332009) B332009
theorem B417953 : Blo 219811 417953 := bstep (se 2 (by rfl) ⟨156732, by rfl⟩ : syracuseStep 417953 = 313465) B313465
theorem B221423 : Blo 219811 221423 := bstep (se 1 (by rfl) ⟨166067, by rfl⟩ : syracuseStep 221423 = 332135) B332135
theorem B746171 : Blo 219811 746171 := bstep (se 1 (by rfl) ⟨559628, by rfl⟩ : syracuseStep 746171 = 1119257) B1119257
theorem B3400393 : Blo 219811 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B221979 : Blo 219811 221979 := bstep (se 1 (by rfl) ⟨166484, by rfl⟩ : syracuseStep 221979 = 332969) B332969
theorem B222023 : Blo 219811 222023 := bstep (se 1 (by rfl) ⟨166517, by rfl⟩ : syracuseStep 222023 = 333035) B333035
theorem B222079 : Blo 219811 222079 := bstep (se 1 (by rfl) ⟨166559, by rfl⟩ : syracuseStep 222079 = 333119) B333119
theorem B222207 : Blo 219811 222207 := bstep (se 1 (by rfl) ⟨166655, by rfl⟩ : syracuseStep 222207 = 333311) B333311
theorem B222279 : Blo 219811 222279 := bstep (se 1 (by rfl) ⟨166709, by rfl⟩ : syracuseStep 222279 = 333419) B333419
theorem B222459 : Blo 219811 222459 := bstep (se 1 (by rfl) ⟨166844, by rfl⟩ : syracuseStep 222459 = 333689) B333689
theorem B222623 : Blo 219811 222623 := bstep (se 1 (by rfl) ⟨166967, by rfl⟩ : syracuseStep 222623 = 333935) B333935
theorem B222671 : Blo 219811 222671 := bstep (se 1 (by rfl) ⟨167003, by rfl⟩ : syracuseStep 222671 = 334007) B334007
theorem B222951 : Blo 219811 222951 := bstep (se 1 (by rfl) ⟨167213, by rfl⟩ : syracuseStep 222951 = 334427) B334427
theorem B222959 : Blo 219811 222959 := bstep (se 1 (by rfl) ⟨167219, by rfl⟩ : syracuseStep 222959 = 334439) B334439
theorem B222975 : Blo 219811 222975 := bstep (se 1 (by rfl) ⟨167231, by rfl⟩ : syracuseStep 222975 = 334463) B334463
theorem B2418473 : Blo 219811 2418473 := bstep (se 2 (by rfl) ⟨906927, by rfl⟩ : syracuseStep 2418473 = 1813855) B1813855
theorem B223047 : Blo 219811 223047 := bstep (se 1 (by rfl) ⟨167285, by rfl⟩ : syracuseStep 223047 = 334571) B334571
theorem B223067 : Blo 219811 223067 := bstep (se 1 (by rfl) ⟨167300, by rfl⟩ : syracuseStep 223067 = 334601) B334601
theorem B223227 : Blo 219811 223227 := bstep (se 1 (by rfl) ⟨167420, by rfl⟩ : syracuseStep 223227 = 334841) B334841
theorem B2385949 : Blo 219811 2385949 := bstep (se 3 (by rfl) ⟨447365, by rfl⟩ : syracuseStep 2385949 = 894731) B894731
theorem B223647 : Blo 219811 223647 := bstep (se 1 (by rfl) ⟨167735, by rfl⟩ : syracuseStep 223647 = 335471) B335471
theorem B223727 : Blo 219811 223727 := bstep (se 1 (by rfl) ⟨167795, by rfl⟩ : syracuseStep 223727 = 335591) B335591
theorem B748115 : Blo 219811 748115 := bstep (se 1 (by rfl) ⟨561086, by rfl⟩ : syracuseStep 748115 = 1122173) B1122173
theorem B3566213 : Blo 219811 3566213 := bstep (se 4 (by rfl) ⟨334332, by rfl⟩ : syracuseStep 3566213 = 668665) B668665
theorem B748169 : Blo 219811 748169 := bstep (se 2 (by rfl) ⟨280563, by rfl⟩ : syracuseStep 748169 = 561127) B561127
theorem B748655 : Blo 219811 748655 := bstep (se 1 (by rfl) ⟨561491, by rfl⟩ : syracuseStep 748655 = 1122983) B1122983
theorem B946151 : Blo 219811 946151 := bstep (se 1 (by rfl) ⟨709613, by rfl⟩ : syracuseStep 946151 = 1419227) B1419227
theorem B2519423 : Blo 219811 2519423 := bstep (se 1 (by rfl) ⟨1889567, by rfl⟩ : syracuseStep 2519423 = 3779135) B3779135
theorem B3044243 : Blo 219811 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B750491 : Blo 219811 750491 := bstep (se 1 (by rfl) ⟨562868, by rfl⟩ : syracuseStep 750491 = 1125737) B1125737
theorem B947177 : Blo 219811 947177 := bstep (se 2 (by rfl) ⟨355191, by rfl⟩ : syracuseStep 947177 = 710383) B710383
theorem B3863539 : Blo 219811 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B2127383 : Blo 219811 2127383 := bstep (se 1 (by rfl) ⟨1595537, by rfl⟩ : syracuseStep 2127383 = 3191075) B3191075
theorem B850283 : Blo 219811 850283 := bstep (se 1 (by rfl) ⟨637712, by rfl⟩ : syracuseStep 850283 = 1275425) B1275425
theorem B424415 : Blo 219811 424415 := bstep (se 1 (by rfl) ⟨318311, by rfl⟩ : syracuseStep 424415 = 636623) B636623
theorem B2850551 : Blo 219811 2850551 := bstep (se 1 (by rfl) ⟨2137913, by rfl⟩ : syracuseStep 2850551 = 4275827) B4275827
theorem B557543 : Blo 219811 557543 := bstep (se 1 (by rfl) ⟨418157, by rfl⟩ : syracuseStep 557543 = 836315) B836315
theorem B3181265 : Blo 219811 3181265 := bstep (se 2 (by rfl) ⟨1192974, by rfl⟩ : syracuseStep 3181265 = 2385949) B2385949
theorem B494855 : Blo 219811 494855 := bstep (se 1 (by rfl) ⟨371141, by rfl⟩ : syracuseStep 494855 = 742283) B742283
theorem B331079 : Blo 219811 331079 := bstep (se 1 (by rfl) ⟨248309, by rfl⟩ : syracuseStep 331079 = 496619) B496619
theorem B626075 : Blo 219811 626075 := bstep (se 1 (by rfl) ⟨469556, by rfl⟩ : syracuseStep 626075 = 939113) B939113
theorem B495071 : Blo 219811 495071 := bstep (se 1 (by rfl) ⟨371303, by rfl⟩ : syracuseStep 495071 = 742607) B742607
theorem B331547 : Blo 219811 331547 := bstep (se 1 (by rfl) ⟨248660, by rfl⟩ : syracuseStep 331547 = 497321) B497321
theorem B1118123 : Blo 219811 1118123 := bstep (se 1 (by rfl) ⟨838592, by rfl⟩ : syracuseStep 1118123 = 1677185) B1677185
theorem B1544447 : Blo 219811 1544447 := bstep (se 1 (by rfl) ⟨1158335, by rfl⟩ : syracuseStep 1544447 = 2316671) B2316671
theorem B11604343 : Blo 219811 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B332153 : Blo 219811 332153 := bstep (se 2 (by rfl) ⟨124557, by rfl⟩ : syracuseStep 332153 = 249115) B249115
theorem B496079 : Blo 219811 496079 := bstep (se 1 (by rfl) ⟨372059, by rfl⟩ : syracuseStep 496079 = 744119) B744119
theorem B496169 : Blo 219811 496169 := bstep (se 2 (by rfl) ⟨186063, by rfl⟩ : syracuseStep 496169 = 372127) B372127
theorem B332399 : Blo 219811 332399 := bstep (se 1 (by rfl) ⟨249299, by rfl⟩ : syracuseStep 332399 = 498599) B498599
theorem B561775 : Blo 219811 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B332447 : Blo 219811 332447 := bstep (se 1 (by rfl) ⟨249335, by rfl⟩ : syracuseStep 332447 = 498671) B498671
theorem B2855675 : Blo 219811 2855675 := bstep (se 1 (by rfl) ⟨2141756, by rfl⟩ : syracuseStep 2855675 = 4283513) B4283513
theorem B496745 : Blo 219811 496745 := bstep (se 2 (by rfl) ⟨186279, by rfl⟩ : syracuseStep 496745 = 372559) B372559
theorem B66819275 : Blo 219811 66819275 := bstep (se 1 (by rfl) ⟨50114456, by rfl⟩ : syracuseStep 66819275 = 100228913) B100228913
theorem B333023 : Blo 219811 333023 := bstep (se 1 (by rfl) ⟨249767, by rfl⟩ : syracuseStep 333023 = 499535) B499535
theorem B333083 : Blo 219811 333083 := bstep (se 1 (by rfl) ⟨249812, by rfl⟩ : syracuseStep 333083 = 499625) B499625
theorem B3020111 : Blo 219811 3020111 := bstep (se 1 (by rfl) ⟨2265083, by rfl⟩ : syracuseStep 3020111 = 4530167) B4530167
theorem B3020165 : Blo 219811 3020165 := bstep (se 4 (by rfl) ⟨283140, by rfl⟩ : syracuseStep 3020165 = 566281) B566281
theorem B333263 : Blo 219811 333263 := bstep (se 1 (by rfl) ⟨249947, by rfl⟩ : syracuseStep 333263 = 499895) B499895
theorem B333503 : Blo 219811 333503 := bstep (se 1 (by rfl) ⟨250127, by rfl⟩ : syracuseStep 333503 = 500255) B500255
theorem B1414921 : Blo 219811 1414921 := bstep (se 2 (by rfl) ⟨530595, by rfl⟩ : syracuseStep 1414921 = 1061191) B1061191
theorem B497447 : Blo 219811 497447 := bstep (se 1 (by rfl) ⟨373085, by rfl⟩ : syracuseStep 497447 = 746171) B746171
theorem B1612315 : Blo 219811 1612315 := bstep (se 1 (by rfl) ⟨1209236, by rfl⟩ : syracuseStep 1612315 = 2418473) B2418473
theorem B5151385 : Blo 219811 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B4037681 : Blo 219811 4037681 := bstep (se 2 (by rfl) ⟨1514130, by rfl⟩ : syracuseStep 4037681 = 3028261) B3028261
theorem B498743 : Blo 219811 498743 := bstep (se 1 (by rfl) ⟨374057, by rfl⟩ : syracuseStep 498743 = 748115) B748115
theorem B498761 : Blo 219811 498761 := bstep (se 2 (by rfl) ⟨187035, by rfl⟩ : syracuseStep 498761 = 374071) B374071
theorem B498779 : Blo 219811 498779 := bstep (se 1 (by rfl) ⟨374084, by rfl⟩ : syracuseStep 498779 = 748169) B748169
theorem B334955 : Blo 219811 334955 := bstep (se 1 (by rfl) ⟨251216, by rfl⟩ : syracuseStep 334955 = 502433) B502433
theorem B335195 : Blo 219811 335195 := bstep (se 1 (by rfl) ⟨251396, by rfl⟩ : syracuseStep 335195 = 502793) B502793
theorem B499103 : Blo 219811 499103 := bstep (se 1 (by rfl) ⟨374327, by rfl⟩ : syracuseStep 499103 = 748655) B748655
theorem B597431 : Blo 219811 597431 := bstep (se 1 (by rfl) ⟨448073, by rfl⟩ : syracuseStep 597431 = 896147) B896147
theorem B630767 : Blo 219811 630767 := bstep (se 1 (by rfl) ⟨473075, by rfl⟩ : syracuseStep 630767 = 946151) B946151
theorem B1253515 : Blo 219811 1253515 := bstep (se 1 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 1253515 = 1880273) B1880273
theorem B1679615 : Blo 219811 1679615 := bstep (se 1 (by rfl) ⟨1259711, by rfl⟩ : syracuseStep 1679615 = 2519423) B2519423
theorem B1909115 : Blo 219811 1909115 := bstep (se 1 (by rfl) ⟨1431836, by rfl⟩ : syracuseStep 1909115 = 2863673) B2863673
theorem B8135099 : Blo 219811 8135099 := bstep (se 1 (by rfl) ⟨6101324, by rfl⟩ : syracuseStep 8135099 = 12202649) B12202649
theorem B500327 : Blo 219811 500327 := bstep (se 1 (by rfl) ⟨375245, by rfl⟩ : syracuseStep 500327 = 750491) B750491
theorem B631451 : Blo 219811 631451 := bstep (se 1 (by rfl) ⟨473588, by rfl⟩ : syracuseStep 631451 = 947177) B947177
theorem B1418255 : Blo 219811 1418255 := bstep (se 1 (by rfl) ⟨1063691, by rfl⟩ : syracuseStep 1418255 = 2127383) B2127383
theorem B632033 : Blo 219811 632033 := bstep (se 2 (by rfl) ⟨237012, by rfl⟩ : syracuseStep 632033 = 474025) B474025
theorem B337223 : Blo 219811 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B8463689 : Blo 219811 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B566855 : Blo 219811 566855 := bstep (se 1 (by rfl) ⟨425141, by rfl⟩ : syracuseStep 566855 = 850283) B850283
theorem B501353 : Blo 219811 501353 := bstep (se 2 (by rfl) ⟨188007, by rfl⟩ : syracuseStep 501353 = 376015) B376015
theorem B1255247 : Blo 219811 1255247 := bstep (se 1 (by rfl) ⟨941435, by rfl⟩ : syracuseStep 1255247 = 1882871) B1882871
theorem B633683 : Blo 219811 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B502991 : Blo 219811 502991 := bstep (se 1 (by rfl) ⟨377243, by rfl⟩ : syracuseStep 502991 = 754487) B754487
theorem B503315 : Blo 219811 503315 := bstep (se 1 (by rfl) ⟨377486, by rfl⟩ : syracuseStep 503315 = 754973) B754973
theorem B4533857 : Blo 219811 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B470855 : Blo 219811 470855 := bstep (se 1 (by rfl) ⟨353141, by rfl⟩ : syracuseStep 470855 = 706283) B706283
theorem B1585097 : Blo 219811 1585097 := bstep (se 2 (by rfl) ⟨594411, by rfl⟩ : syracuseStep 1585097 = 1188823) B1188823
theorem B536863 : Blo 219811 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B9154903 : Blo 219811 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B2175731 : Blo 219811 2175731 := bstep (se 1 (by rfl) ⟨1631798, by rfl⟩ : syracuseStep 2175731 = 3263597) B3263597
theorem B4568507 : Blo 219811 4568507 := bstep (se 1 (by rfl) ⟨3426380, by rfl⟩ : syracuseStep 4568507 = 6852761) B6852761
theorem B374503 : Blo 219811 374503 := bstep (se 1 (by rfl) ⟨280877, by rfl⟩ : syracuseStep 374503 = 561755) B561755
theorem B472871 : Blo 219811 472871 := bstep (se 1 (by rfl) ⟨354653, by rfl⟩ : syracuseStep 472871 = 709307) B709307
theorem B1423327 : Blo 219811 1423327 := bstep (se 1 (by rfl) ⟨1067495, by rfl⟩ : syracuseStep 1423327 = 2134991) B2134991
theorem B1063037 : Blo 219811 1063037 := bstep (se 3 (by rfl) ⟨199319, by rfl⟩ : syracuseStep 1063037 = 398639) B398639
theorem B1063115 : Blo 219811 1063115 := bstep (se 1 (by rfl) ⟨797336, by rfl⟩ : syracuseStep 1063115 = 1594673) B1594673
theorem B13777895 : Blo 219811 13777895 := bstep (se 1 (by rfl) ⟨10333421, by rfl⟩ : syracuseStep 13777895 = 20666843) B20666843
theorem B34356575 : Blo 219811 34356575 := bstep (se 1 (by rfl) ⟨25767431, by rfl⟩ : syracuseStep 34356575 = 51534863) B51534863
theorem B573095 : Blo 219811 573095 := bstep (se 1 (by rfl) ⟨429821, by rfl⟩ : syracuseStep 573095 = 859643) B859643
theorem B1523771 : Blo 219811 1523771 := bstep (se 1 (by rfl) ⟨1142828, by rfl⟩ : syracuseStep 1523771 = 2285657) B2285657
theorem B278635 : Blo 219811 278635 := bstep (se 1 (by rfl) ⟨208976, by rfl⟩ : syracuseStep 278635 = 417953) B417953
theorem B377311 : Blo 219811 377311 := bstep (se 1 (by rfl) ⟨282983, by rfl⟩ : syracuseStep 377311 = 565967) B565967
theorem B1884647 : Blo 219811 1884647 := bstep (se 1 (by rfl) ⟨1413485, by rfl⟩ : syracuseStep 1884647 = 2826971) B2826971
theorem B705257 : Blo 219811 705257 := bstep (se 2 (by rfl) ⟨264471, by rfl⟩ : syracuseStep 705257 = 528943) B528943
theorem B2376701 : Blo 219811 2376701 := bstep (se 3 (by rfl) ⟨445631, by rfl⟩ : syracuseStep 2376701 = 891263) B891263
theorem B1197281 : Blo 219811 1197281 := bstep (se 2 (by rfl) ⟨448980, by rfl⟩ : syracuseStep 1197281 = 897961) B897961
theorem B2377475 : Blo 219811 2377475 := bstep (se 1 (by rfl) ⟨1783106, by rfl⟩ : syracuseStep 2377475 = 3566213) B3566213
theorem B837499 : Blo 219811 837499 := bstep (se 1 (by rfl) ⟨628124, by rfl⟩ : syracuseStep 837499 = 1256249) B1256249
theorem B247711 : Blo 219811 247711 := bstep (se 1 (by rfl) ⟨185783, by rfl⟩ : syracuseStep 247711 = 371567) B371567
theorem B2509217 : Blo 219811 2509217 := bstep (se 2 (by rfl) ⟨940956, by rfl⟩ : syracuseStep 2509217 = 1881913) B1881913
theorem B838457 : Blo 219811 838457 := bstep (se 2 (by rfl) ⟨314421, by rfl⟩ : syracuseStep 838457 = 628843) B628843
theorem B3787883 : Blo 219811 3787883 := bstep (se 1 (by rfl) ⟨2840912, by rfl⟩ : syracuseStep 3787883 = 5681825) B5681825
theorem B674941 : Blo 219811 674941 := bstep (se 3 (by rfl) ⟨126551, by rfl⟩ : syracuseStep 674941 = 253103) B253103
theorem B1690793 : Blo 219811 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B708679 : Blo 219811 708679 := bstep (se 1 (by rfl) ⟨531509, by rfl⟩ : syracuseStep 708679 = 1063019) B1063019
theorem B774335 : Blo 219811 774335 := bstep (se 1 (by rfl) ⟨580751, by rfl⟩ : syracuseStep 774335 = 1161503) B1161503
theorem B282943 : Blo 219811 282943 := bstep (se 1 (by rfl) ⟨212207, by rfl⟩ : syracuseStep 282943 = 424415) B424415
theorem B250663 : Blo 219811 250663 := bstep (se 1 (by rfl) ⟨187997, by rfl⟩ : syracuseStep 250663 = 375995) B375995
theorem B676889 : Blo 219811 676889 := bstep (se 2 (by rfl) ⟨253833, by rfl⟩ : syracuseStep 676889 = 507667) B507667
theorem B1627303 : Blo 219811 1627303 := bstep (se 1 (by rfl) ⟨1220477, by rfl⟩ : syracuseStep 1627303 = 2440955) B2440955
theorem B742931 : Blo 219811 742931 := bstep (se 1 (by rfl) ⟨557198, by rfl⟩ : syracuseStep 742931 = 1114397) B1114397
theorem B2578655 : Blo 219811 2578655 := bstep (se 1 (by rfl) ⟨1933991, by rfl⟩ : syracuseStep 2578655 = 3867983) B3867983
theorem B1136875 : Blo 219811 1136875 := bstep (se 1 (by rfl) ⟨852656, by rfl⟩ : syracuseStep 1136875 = 1705313) B1705313
theorem B1694195 : Blo 219811 1694195 := bstep (se 1 (by rfl) ⟨1270646, by rfl⟩ : syracuseStep 1694195 = 2541293) B2541293
theorem B219899 : Blo 219811 219899 := bstep (se 1 (by rfl) ⟨164924, by rfl⟩ : syracuseStep 219899 = 329849) B329849
theorem B318431 : Blo 219811 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B744659 : Blo 219811 744659 := bstep (se 1 (by rfl) ⟨558494, by rfl⟩ : syracuseStep 744659 = 1116989) B1116989
theorem B449759 : Blo 219811 449759 := bstep (se 1 (by rfl) ⟨337319, by rfl⟩ : syracuseStep 449759 = 674639) B674639
theorem B1269377 : Blo 219811 1269377 := bstep (se 2 (by rfl) ⟨476016, by rfl⟩ : syracuseStep 1269377 = 952033) B952033
theorem B220923 : Blo 219811 220923 := bstep (se 1 (by rfl) ⟨165692, by rfl⟩ : syracuseStep 220923 = 331385) B331385
theorem B18341639 : Blo 219811 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B220955 : Blo 219811 220955 := bstep (se 1 (by rfl) ⟨165716, by rfl⟩ : syracuseStep 220955 = 331433) B331433
theorem B1433375 : Blo 219811 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B221343 : Blo 219811 221343 := bstep (se 1 (by rfl) ⟨166007, by rfl⟩ : syracuseStep 221343 = 332015) B332015
theorem B221511 : Blo 219811 221511 := bstep (se 1 (by rfl) ⟨166133, by rfl⟩ : syracuseStep 221511 = 332267) B332267
theorem B221595 : Blo 219811 221595 := bstep (se 1 (by rfl) ⟨166196, by rfl⟩ : syracuseStep 221595 = 332393) B332393
theorem B746063 : Blo 219811 746063 := bstep (se 1 (by rfl) ⟨559547, by rfl⟩ : syracuseStep 746063 = 1119095) B1119095
theorem B222043 : Blo 219811 222043 := bstep (se 1 (by rfl) ⟨166532, by rfl⟩ : syracuseStep 222043 = 333065) B333065
theorem B222363 : Blo 219811 222363 := bstep (se 1 (by rfl) ⟨166772, by rfl⟩ : syracuseStep 222363 = 333545) B333545
theorem B222491 : Blo 219811 222491 := bstep (se 1 (by rfl) ⟨166868, by rfl⟩ : syracuseStep 222491 = 333737) B333737
theorem B222535 : Blo 219811 222535 := bstep (se 1 (by rfl) ⟨166901, by rfl⟩ : syracuseStep 222535 = 333803) B333803
theorem B222879 : Blo 219811 222879 := bstep (se 1 (by rfl) ⟨167159, by rfl⟩ : syracuseStep 222879 = 334319) B334319
theorem B223087 : Blo 219811 223087 := bstep (se 1 (by rfl) ⟨167315, by rfl⟩ : syracuseStep 223087 = 334631) B334631
theorem B6055985 : Blo 219811 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B223487 : Blo 219811 223487 := bstep (se 1 (by rfl) ⟨167615, by rfl⟩ : syracuseStep 223487 = 335231) B335231
theorem B1274687 : Blo 219811 1274687 := bstep (se 1 (by rfl) ⟨956015, by rfl⟩ : syracuseStep 1274687 = 1912031) B1912031
theorem B2553065 : Blo 219811 2553065 := bstep (se 2 (by rfl) ⟨957399, by rfl⟩ : syracuseStep 2553065 = 1914799) B1914799
theorem B423215 : Blo 219811 423215 := bstep (se 1 (by rfl) ⟨317411, by rfl⟩ : syracuseStep 423215 = 634823) B634823
theorem B2979287 : Blo 219811 2979287 := bstep (se 1 (by rfl) ⟨2234465, by rfl⟩ : syracuseStep 2979287 = 4468931) B4468931
theorem B947791 : Blo 219811 947791 := bstep (se 1 (by rfl) ⟨710843, by rfl⟩ : syracuseStep 947791 = 1421687) B1421687
theorem B2029495 : Blo 219811 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B423967 : Blo 219811 423967 := bstep (se 1 (by rfl) ⟨317975, by rfl⟩ : syracuseStep 423967 = 635951) B635951
theorem B424111 : Blo 219811 424111 := bstep (se 1 (by rfl) ⟨318083, by rfl⟩ : syracuseStep 424111 = 636167) B636167
theorem B424271 : Blo 219811 424271 := bstep (se 1 (by rfl) ⟨318203, by rfl⟩ : syracuseStep 424271 = 636407) B636407
theorem B949279 : Blo 219811 949279 := bstep (se 1 (by rfl) ⟨711959, by rfl⟩ : syracuseStep 949279 = 1423919) B1423919
theorem B1900367 : Blo 219811 1900367 := bstep (se 1 (by rfl) ⟨1425275, by rfl⟩ : syracuseStep 1900367 = 2850551) B2850551
theorem B1802179 : Blo 219811 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B1015847 : Blo 219811 1015847 := bstep (se 1 (by rfl) ⟨761885, by rfl⟩ : syracuseStep 1015847 = 1523771) B1523771
theorem B1671353 : Blo 219811 1671353 := bstep (se 2 (by rfl) ⟨626757, by rfl⟩ : syracuseStep 1671353 = 1253515) B1253515
theorem B1672811 : Blo 219811 1672811 := bstep (se 1 (by rfl) ⟨1254608, by rfl⟩ : syracuseStep 1672811 = 2509217) B2509217
theorem B558971 : Blo 219811 558971 := bstep (se 1 (by rfl) ⟨419228, by rfl⟩ : syracuseStep 558971 = 838457) B838457
theorem B2525255 : Blo 219811 2525255 := bstep (se 1 (by rfl) ⟨1893941, by rfl⟩ : syracuseStep 2525255 = 3787883) B3787883
theorem B329903 : Blo 219811 329903 := bstep (se 1 (by rfl) ⟨247427, by rfl⟩ : syracuseStep 329903 = 494855) B494855
theorem B330047 : Blo 219811 330047 := bstep (se 1 (by rfl) ⟨247535, by rfl⟩ : syracuseStep 330047 = 495071) B495071
theorem B1116665 : Blo 219811 1116665 := bstep (se 2 (by rfl) ⟨418749, by rfl⟩ : syracuseStep 1116665 = 837499) B837499
theorem B330281 : Blo 219811 330281 := bstep (se 2 (by rfl) ⟨123855, by rfl⟩ : syracuseStep 330281 = 247711) B247711
theorem B330719 : Blo 219811 330719 := bstep (se 1 (by rfl) ⟨248039, by rfl⟩ : syracuseStep 330719 = 496079) B496079
theorem B330779 : Blo 219811 330779 := bstep (se 1 (by rfl) ⟨248084, by rfl⟩ : syracuseStep 330779 = 496169) B496169
theorem B1903783 : Blo 219811 1903783 := bstep (se 1 (by rfl) ⟨1427837, by rfl⟩ : syracuseStep 1903783 = 2855675) B2855675
theorem B331163 : Blo 219811 331163 := bstep (se 1 (by rfl) ⟨248372, by rfl⟩ : syracuseStep 331163 = 496745) B496745
theorem B495287 : Blo 219811 495287 := bstep (se 1 (by rfl) ⟨371465, by rfl⟩ : syracuseStep 495287 = 742931) B742931
theorem B331631 : Blo 219811 331631 := bstep (se 1 (by rfl) ⟨248723, by rfl⟩ : syracuseStep 331631 = 497447) B497447
theorem B2691787 : Blo 219811 2691787 := bstep (se 1 (by rfl) ⟨2018840, by rfl⟩ : syracuseStep 2691787 = 4037681) B4037681
theorem B332495 : Blo 219811 332495 := bstep (se 1 (by rfl) ⟨249371, by rfl⟩ : syracuseStep 332495 = 498743) B498743
theorem B332507 : Blo 219811 332507 := bstep (se 1 (by rfl) ⟨249380, by rfl⟩ : syracuseStep 332507 = 498761) B498761
theorem B332519 : Blo 219811 332519 := bstep (se 1 (by rfl) ⟨249389, by rfl⟩ : syracuseStep 332519 = 498779) B498779
theorem B496439 : Blo 219811 496439 := bstep (se 1 (by rfl) ⟨372329, by rfl⟩ : syracuseStep 496439 = 744659) B744659
theorem B332735 : Blo 219811 332735 := bstep (se 1 (by rfl) ⟨249551, by rfl⟩ : syracuseStep 332735 = 499103) B499103
theorem B398287 : Blo 219811 398287 := bstep (se 1 (by rfl) ⟨298715, by rfl⟩ : syracuseStep 398287 = 597431) B597431
theorem B12227759 : Blo 219811 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B955583 : Blo 219811 955583 := bstep (se 1 (by rfl) ⟨716687, by rfl⟩ : syracuseStep 955583 = 1433375) B1433375
theorem B1119743 : Blo 219811 1119743 := bstep (se 1 (by rfl) ⟨839807, by rfl⟩ : syracuseStep 1119743 = 1679615) B1679615
theorem B497375 : Blo 219811 497375 := bstep (se 1 (by rfl) ⟨373031, by rfl⟩ : syracuseStep 497375 = 746063) B746063
theorem B333551 : Blo 219811 333551 := bstep (se 1 (by rfl) ⟨250163, by rfl⟩ : syracuseStep 333551 = 500327) B500327
theorem B15472457 : Blo 219811 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B5642459 : Blo 219811 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B334217 : Blo 219811 334217 := bstep (se 2 (by rfl) ⟨125331, by rfl⟩ : syracuseStep 334217 = 250663) B250663
theorem B334235 : Blo 219811 334235 := bstep (se 1 (by rfl) ⟨250676, by rfl⟩ : syracuseStep 334235 = 501353) B501353
theorem B4037323 : Blo 219811 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B2169737 : Blo 219811 2169737 := bstep (se 2 (by rfl) ⟨813651, by rfl⟩ : syracuseStep 2169737 = 1627303) B1627303
theorem B335327 : Blo 219811 335327 := bstep (se 1 (by rfl) ⟨251495, by rfl⟩ : syracuseStep 335327 = 502991) B502991
theorem B499337 : Blo 219811 499337 := bstep (se 2 (by rfl) ⟨187251, by rfl⟩ : syracuseStep 499337 = 374503) B374503
theorem B335543 : Blo 219811 335543 := bstep (se 1 (by rfl) ⟨251657, by rfl⟩ : syracuseStep 335543 = 503315) B503315
theorem B3022571 : Blo 219811 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B36741053 : Blo 219811 36741053 := bstep (se 3 (by rfl) ⟨6888947, by rfl⟩ : syracuseStep 36741053 = 13777895) B13777895
theorem B1056731 : Blo 219811 1056731 := bstep (se 1 (by rfl) ⟨792548, by rfl⟩ : syracuseStep 1056731 = 1585097) B1585097
theorem B565289 : Blo 219811 565289 := bstep (se 2 (by rfl) ⟨211983, by rfl⟩ : syracuseStep 565289 = 423967) B423967
theorem B565481 : Blo 219811 565481 := bstep (se 2 (by rfl) ⟨212055, by rfl⟩ : syracuseStep 565481 = 424111) B424111
theorem B1515833 : Blo 219811 1515833 := bstep (se 2 (by rfl) ⟨568437, by rfl⟩ : syracuseStep 1515833 = 1136875) B1136875
theorem B1450487 : Blo 219811 1450487 := bstep (se 1 (by rfl) ⟨1087865, by rfl⟩ : syracuseStep 1450487 = 2175731) B2175731
theorem B2402905 : Blo 219811 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B1682045 : Blo 219811 1682045 := bstep (se 3 (by rfl) ⟨315383, by rfl⟩ : syracuseStep 1682045 = 630767) B630767
theorem B371513 : Blo 219811 371513 := bstep (se 2 (by rfl) ⟨139317, by rfl⟩ : syracuseStep 371513 = 278635) B278635
theorem B371695 : Blo 219811 371695 := bstep (se 1 (by rfl) ⟨278771, by rfl⟩ : syracuseStep 371695 = 557543) B557543
theorem B1256431 : Blo 219811 1256431 := bstep (se 1 (by rfl) ⟨942323, by rfl⟩ : syracuseStep 1256431 = 1884647) B1884647
theorem B470171 : Blo 219811 470171 := bstep (se 1 (by rfl) ⟨352628, by rfl⟩ : syracuseStep 470171 = 705257) B705257
theorem B503081 : Blo 219811 503081 := bstep (se 2 (by rfl) ⟨188655, by rfl⟩ : syracuseStep 503081 = 377311) B377311
theorem B1584467 : Blo 219811 1584467 := bstep (se 1 (by rfl) ⟨1188350, by rfl⟩ : syracuseStep 1584467 = 2376701) B2376701
theorem B798187 : Blo 219811 798187 := bstep (se 1 (by rfl) ⟨598640, by rfl⟩ : syracuseStep 798187 = 1197281) B1197281
theorem B1584983 : Blo 219811 1584983 := bstep (se 1 (by rfl) ⟨1188737, by rfl⟩ : syracuseStep 1584983 = 2377475) B2377475
theorem B1127195 : Blo 219811 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B1029631 : Blo 219811 1029631 := bstep (se 1 (by rfl) ⟨772223, by rfl⟩ : syracuseStep 1029631 = 1544447) B1544447
theorem B44546183 : Blo 219811 44546183 := bstep (se 1 (by rfl) ⟨33409637, by rfl⟩ : syracuseStep 44546183 = 66819275) B66819275
theorem B899261 : Blo 219811 899261 := bstep (se 3 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 899261 = 337223) B337223
theorem B2013407 : Blo 219811 2013407 := bstep (se 1 (by rfl) ⟨1510055, by rfl⟩ : syracuseStep 2013407 = 3020111) B3020111
theorem B2013443 : Blo 219811 2013443 := bstep (se 1 (by rfl) ⟨1510082, by rfl⟩ : syracuseStep 2013443 = 3020165) B3020165
theorem B1719103 : Blo 219811 1719103 := bstep (se 1 (by rfl) ⟨1289327, by rfl⟩ : syracuseStep 1719103 = 2578655) B2578655
theorem B899921 : Blo 219811 899921 := bstep (se 2 (by rfl) ⟨337470, by rfl⟩ : syracuseStep 899921 = 674941) B674941
theorem B1129463 : Blo 219811 1129463 := bstep (se 1 (by rfl) ⟨847097, by rfl⟩ : syracuseStep 1129463 = 1694195) B1694195
theorem B5423399 : Blo 219811 5423399 := bstep (se 1 (by rfl) ⟨4067549, by rfl⟩ : syracuseStep 5423399 = 8135099) B8135099
theorem B377257 : Blo 219811 377257 := bstep (se 2 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 377257 = 282943) B282943
theorem B12206537 : Blo 219811 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B377903 : Blo 219811 377903 := bstep (se 1 (by rfl) ⟨283427, by rfl⟩ : syracuseStep 377903 = 566855) B566855
theorem B836831 : Blo 219811 836831 := bstep (se 1 (by rfl) ⟨627623, by rfl⟩ : syracuseStep 836831 = 1255247) B1255247
theorem B1263721 : Blo 219811 1263721 := bstep (se 2 (by rfl) ⟨473895, by rfl⟩ : syracuseStep 1263721 = 947791) B947791
theorem B1689821 : Blo 219811 1689821 := bstep (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) B633683
theorem B1886561 : Blo 219811 1886561 := bstep (se 2 (by rfl) ⟨707460, by rfl⟩ : syracuseStep 1886561 = 1414921) B1414921
theorem B313903 : Blo 219811 313903 := bstep (se 1 (by rfl) ⟨235427, by rfl⟩ : syracuseStep 313903 = 470855) B470855
theorem B2705993 : Blo 219811 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B1199357 : Blo 219811 1199357 := bstep (se 3 (by rfl) ⟨224879, by rfl⟩ : syracuseStep 1199357 = 449759) B449759
theorem B2149753 : Blo 219811 2149753 := bstep (se 2 (by rfl) ⟨806157, by rfl⟩ : syracuseStep 2149753 = 1612315) B1612315
theorem B282143 : Blo 219811 282143 := bstep (se 1 (by rfl) ⟨211607, by rfl⟩ : syracuseStep 282143 = 423215) B423215
theorem B6868513 : Blo 219811 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B1986191 : Blo 219811 1986191 := bstep (se 1 (by rfl) ⟨1489643, by rfl⟩ : syracuseStep 1986191 = 2979287) B2979287
theorem B315247 : Blo 219811 315247 := bstep (se 1 (by rfl) ⟨236435, by rfl⟩ : syracuseStep 315247 = 472871) B472871
theorem B1265705 : Blo 219811 1265705 := bstep (se 2 (by rfl) ⟨474639, by rfl⟩ : syracuseStep 1265705 = 949279) B949279
theorem B708691 : Blo 219811 708691 := bstep (se 1 (by rfl) ⟨531518, by rfl⟩ : syracuseStep 708691 = 1063037) B1063037
theorem B708743 : Blo 219811 708743 := bstep (se 1 (by rfl) ⟨531557, by rfl⟩ : syracuseStep 708743 = 1063115) B1063115
theorem B282847 : Blo 219811 282847 := bstep (se 1 (by rfl) ⟨212135, by rfl⟩ : syracuseStep 282847 = 424271) B424271
theorem B1528253 : Blo 219811 1528253 := bstep (se 3 (by rfl) ⟨286547, by rfl⟩ : syracuseStep 1528253 = 573095) B573095
theorem B1266911 : Blo 219811 1266911 := bstep (se 1 (by rfl) ⟨950183, by rfl⟩ : syracuseStep 1266911 = 1900367) B1900367
theorem B2120843 : Blo 219811 2120843 := bstep (se 1 (by rfl) ⟨1590632, by rfl⟩ : syracuseStep 2120843 = 3181265) B3181265
theorem B220719 : Blo 219811 220719 := bstep (se 1 (by rfl) ⟨165539, by rfl⟩ : syracuseStep 220719 = 331079) B331079
theorem B417383 : Blo 219811 417383 := bstep (se 1 (by rfl) ⟨313037, by rfl⟩ : syracuseStep 417383 = 626075) B626075
theorem B221031 : Blo 219811 221031 := bstep (se 1 (by rfl) ⟨165773, by rfl⟩ : syracuseStep 221031 = 331547) B331547
theorem B745415 : Blo 219811 745415 := bstep (se 1 (by rfl) ⟨559061, by rfl⟩ : syracuseStep 745415 = 1118123) B1118123
theorem B516223 : Blo 219811 516223 := bstep (se 1 (by rfl) ⟨387167, by rfl⟩ : syracuseStep 516223 = 774335) B774335
theorem B221435 : Blo 219811 221435 := bstep (se 1 (by rfl) ⟨166076, by rfl⟩ : syracuseStep 221435 = 332153) B332153
theorem B221599 : Blo 219811 221599 := bstep (se 1 (by rfl) ⟨166199, by rfl⟩ : syracuseStep 221599 = 332399) B332399
theorem B221631 : Blo 219811 221631 := bstep (se 1 (by rfl) ⟨166223, by rfl⟩ : syracuseStep 221631 = 332447) B332447
theorem B451259 : Blo 219811 451259 := bstep (se 1 (by rfl) ⟨338444, by rfl⟩ : syracuseStep 451259 = 676889) B676889
theorem B222015 : Blo 219811 222015 := bstep (se 1 (by rfl) ⟨166511, by rfl⟩ : syracuseStep 222015 = 333023) B333023
theorem B222055 : Blo 219811 222055 := bstep (se 1 (by rfl) ⟨166541, by rfl⟩ : syracuseStep 222055 = 333083) B333083
theorem B222175 : Blo 219811 222175 := bstep (se 1 (by rfl) ⟨166631, by rfl⟩ : syracuseStep 222175 = 333263) B333263
theorem B222335 : Blo 219811 222335 := bstep (se 1 (by rfl) ⟨166751, by rfl⟩ : syracuseStep 222335 = 333503) B333503
theorem B223303 : Blo 219811 223303 := bstep (se 1 (by rfl) ⟨167477, by rfl⟩ : syracuseStep 223303 = 334955) B334955
theorem B223463 : Blo 219811 223463 := bstep (se 1 (by rfl) ⟨167597, by rfl⟩ : syracuseStep 223463 = 335195) B335195
theorem B846251 : Blo 219811 846251 := bstep (se 1 (by rfl) ⟨634688, by rfl⟩ : syracuseStep 846251 = 1269377) B1269377
theorem B944905 : Blo 219811 944905 := bstep (se 2 (by rfl) ⟨354339, by rfl⟩ : syracuseStep 944905 = 708679) B708679
theorem B1272743 : Blo 219811 1272743 := bstep (se 1 (by rfl) ⟨954557, by rfl⟩ : syracuseStep 1272743 = 1909115) B1909115
theorem B715817 : Blo 219811 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B420967 : Blo 219811 420967 := bstep (se 1 (by rfl) ⟨315725, by rfl⟩ : syracuseStep 420967 = 631451) B631451
theorem B945503 : Blo 219811 945503 := bstep (se 1 (by rfl) ⟨709127, by rfl⟩ : syracuseStep 945503 = 1418255) B1418255
theorem B749033 : Blo 219811 749033 := bstep (se 2 (by rfl) ⟨280887, by rfl⟩ : syracuseStep 749033 = 561775) B561775
theorem B421355 : Blo 219811 421355 := bstep (se 1 (by rfl) ⟨316016, by rfl⟩ : syracuseStep 421355 = 632033) B632033
theorem B849149 : Blo 219811 849149 := bstep (se 3 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 849149 = 318431) B318431
theorem B1897769 : Blo 219811 1897769 := bstep (se 2 (by rfl) ⟨711663, by rfl⟩ : syracuseStep 1897769 = 1423327) B1423327
theorem B849791 : Blo 219811 849791 := bstep (se 1 (by rfl) ⟨637343, by rfl⟩ : syracuseStep 849791 = 1274687) B1274687
theorem B1702043 : Blo 219811 1702043 := bstep (se 1 (by rfl) ⟨1276532, by rfl⟩ : syracuseStep 1702043 = 2553065) B2553065
theorem B3045671 : Blo 219811 3045671 := bstep (se 1 (by rfl) ⟨2284253, by rfl⟩ : syracuseStep 3045671 = 4568507) B4568507
theorem B22904383 : Blo 219811 22904383 := bstep (se 1 (by rfl) ⟨17178287, by rfl⟩ : syracuseStep 22904383 = 34356575) B34356575
theorem B1114235 : Blo 219811 1114235 := bstep (se 1 (by rfl) ⟨835676, by rfl⟩ : syracuseStep 1114235 = 1671353) B1671353
theorem B688297 : Blo 219811 688297 := bstep (se 2 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 688297 = 516223) B516223
theorem B557887 : Blo 219811 557887 := bstep (se 1 (by rfl) ⟨418415, by rfl⟩ : syracuseStep 557887 = 836831) B836831
theorem B1115207 : Blo 219811 1115207 := bstep (se 1 (by rfl) ⟨836405, by rfl⟩ : syracuseStep 1115207 = 1672811) B1672811
theorem B1803995 : Blo 219811 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B330191 : Blo 219811 330191 := bstep (se 1 (by rfl) ⟨247643, by rfl⟩ : syracuseStep 330191 = 495287) B495287
theorem B1018835 : Blo 219811 1018835 := bstep (se 1 (by rfl) ⟨764126, by rfl⟩ : syracuseStep 1018835 = 1528253) B1528253
theorem B330959 : Blo 219811 330959 := bstep (se 1 (by rfl) ⟨248219, by rfl⟩ : syracuseStep 330959 = 496439) B496439
theorem B331583 : Blo 219811 331583 := bstep (se 1 (by rfl) ⟨248687, by rfl⟩ : syracuseStep 331583 = 497375) B497375
theorem B495593 : Blo 219811 495593 := bstep (se 2 (by rfl) ⟨185847, by rfl⟩ : syracuseStep 495593 = 371695) B371695
theorem B1675241 : Blo 219811 1675241 := bstep (se 2 (by rfl) ⟨628215, by rfl⟩ : syracuseStep 1675241 = 1256431) B1256431
theorem B561289 : Blo 219811 561289 := bstep (se 2 (by rfl) ⟨210483, by rfl⟩ : syracuseStep 561289 = 420967) B420967
theorem B1446491 : Blo 219811 1446491 := bstep (se 1 (by rfl) ⟨1084868, by rfl⟩ : syracuseStep 1446491 = 2169737) B2169737
theorem B332891 : Blo 219811 332891 := bstep (se 1 (by rfl) ⟨249668, by rfl⟩ : syracuseStep 332891 = 499337) B499337
theorem B496943 : Blo 219811 496943 := bstep (se 1 (by rfl) ⟨372707, by rfl⟩ : syracuseStep 496943 = 745415) B745415
theorem B300839 : Blo 219811 300839 := bstep (se 1 (by rfl) ⟨225629, by rfl⟩ : syracuseStep 300839 = 451259) B451259
theorem B531049 : Blo 219811 531049 := bstep (se 2 (by rfl) ⟨199143, by rfl⟩ : syracuseStep 531049 = 398287) B398287
theorem B564167 : Blo 219811 564167 := bstep (se 1 (by rfl) ⟨423125, by rfl⟩ : syracuseStep 564167 = 846251) B846251
theorem B1121363 : Blo 219811 1121363 := bstep (se 1 (by rfl) ⟨841022, by rfl⟩ : syracuseStep 1121363 = 1682045) B1682045
theorem B335387 : Blo 219811 335387 := bstep (se 1 (by rfl) ⟨251540, by rfl⟩ : syracuseStep 335387 = 503081) B503081
theorem B2399789 : Blo 219811 2399789 := bstep (se 3 (by rfl) ⟨449960, by rfl⟩ : syracuseStep 2399789 = 899921) B899921
theorem B1056311 : Blo 219811 1056311 := bstep (se 1 (by rfl) ⟨792233, by rfl⟩ : syracuseStep 1056311 = 1584467) B1584467
theorem B630335 : Blo 219811 630335 := bstep (se 1 (by rfl) ⟨472751, by rfl⟩ : syracuseStep 630335 = 945503) B945503
theorem B499355 : Blo 219811 499355 := bstep (se 1 (by rfl) ⟨374516, by rfl⟩ : syracuseStep 499355 = 749033) B749033
theorem B1056655 : Blo 219811 1056655 := bstep (se 1 (by rfl) ⟨792491, by rfl⟩ : syracuseStep 1056655 = 1584983) B1584983
theorem B1253789 : Blo 219811 1253789 := bstep (se 3 (by rfl) ⟨235085, by rfl⟩ : syracuseStep 1253789 = 470171) B470171
theorem B566099 : Blo 219811 566099 := bstep (se 1 (by rfl) ⟨424574, by rfl⟩ : syracuseStep 566099 = 849149) B849149
theorem B5383097 : Blo 219811 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B566527 : Blo 219811 566527 := bstep (se 1 (by rfl) ⟨424895, by rfl⟩ : syracuseStep 566527 = 849791) B849791
theorem B29697455 : Blo 219811 29697455 := bstep (se 1 (by rfl) ⟨22273091, by rfl⟩ : syracuseStep 29697455 = 44546183) B44546183
theorem B599507 : Blo 219811 599507 := bstep (se 1 (by rfl) ⟨449630, by rfl⟩ : syracuseStep 599507 = 899261) B899261
theorem B3615599 : Blo 219811 3615599 := bstep (se 1 (by rfl) ⟨2711699, by rfl⟩ : syracuseStep 3615599 = 5423399) B5423399
theorem B8137691 : Blo 219811 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B503009 : Blo 219811 503009 := bstep (se 2 (by rfl) ⟨188628, by rfl⟩ : syracuseStep 503009 = 377257) B377257
theorem B372647 : Blo 219811 372647 := bstep (se 1 (by rfl) ⟨279485, by rfl⟩ : syracuseStep 372647 = 558971) B558971
theorem B1683503 : Blo 219811 1683503 := bstep (se 1 (by rfl) ⟨1262627, by rfl⟩ : syracuseStep 1683503 = 2525255) B2525255
theorem B1126547 : Blo 219811 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B1257707 : Blo 219811 1257707 := bstep (se 1 (by rfl) ⟨943280, by rfl⟩ : syracuseStep 1257707 = 1886561) B1886561
theorem B799571 : Blo 219811 799571 := bstep (se 1 (by rfl) ⟨599678, by rfl⟩ : syracuseStep 799571 = 1199357) B1199357
theorem B1324127 : Blo 219811 1324127 := bstep (se 1 (by rfl) ⟨993095, by rfl⟩ : syracuseStep 1324127 = 1986191) B1986191
theorem B472495 : Blo 219811 472495 := bstep (se 1 (by rfl) ⟨354371, by rfl⟩ : syracuseStep 472495 = 708743) B708743
theorem B1684961 : Blo 219811 1684961 := bstep (se 2 (by rfl) ⟨631860, by rfl⟩ : syracuseStep 1684961 = 1263721) B1263721
theorem B637055 : Blo 219811 637055 := bstep (se 1 (by rfl) ⟨477791, by rfl⟩ : syracuseStep 637055 = 955583) B955583
theorem B1259873 : Blo 219811 1259873 := bstep (se 2 (by rfl) ⟨472452, by rfl⟩ : syracuseStep 1259873 = 944905) B944905
theorem B2538377 : Blo 219811 2538377 := bstep (se 2 (by rfl) ⟨951891, by rfl⟩ : syracuseStep 2538377 = 1903783) B1903783
theorem B2866337 : Blo 219811 2866337 := bstep (se 2 (by rfl) ⟨1074876, by rfl⟩ : syracuseStep 2866337 = 2149753) B2149753
theorem B1064249 : Blo 219811 1064249 := bstep (se 2 (by rfl) ⟨399093, by rfl⟩ : syracuseStep 1064249 = 798187) B798187
theorem B9158017 : Blo 219811 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B278255 : Blo 219811 278255 := bstep (se 1 (by rfl) ⟨208691, by rfl⟩ : syracuseStep 278255 = 417383) B417383
theorem B2015047 : Blo 219811 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B24494035 : Blo 219811 24494035 := bstep (se 1 (by rfl) ⟨18370526, by rfl⟩ : syracuseStep 24494035 = 36741053) B36741053
theorem B376859 : Blo 219811 376859 := bstep (se 1 (by rfl) ⟨282644, by rfl⟩ : syracuseStep 376859 = 565289) B565289
theorem B376987 : Blo 219811 376987 := bstep (se 1 (by rfl) ⟨282740, by rfl⟩ : syracuseStep 376987 = 565481) B565481
theorem B377129 : Blo 219811 377129 := bstep (se 2 (by rfl) ⟨141423, by rfl⟩ : syracuseStep 377129 = 282847) B282847
theorem B966991 : Blo 219811 966991 := bstep (se 1 (by rfl) ⟨725243, by rfl⟩ : syracuseStep 966991 = 1450487) B1450487
theorem B3589049 : Blo 219811 3589049 := bstep (se 2 (by rfl) ⟨1345893, by rfl⟩ : syracuseStep 3589049 = 2691787) B2691787
theorem B247675 : Blo 219811 247675 := bstep (se 1 (by rfl) ⟨185756, by rfl⟩ : syracuseStep 247675 = 371513) B371513
theorem B477211 : Blo 219811 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B280903 : Blo 219811 280903 := bstep (se 1 (by rfl) ⟨210677, by rfl⟩ : syracuseStep 280903 = 421355) B421355
theorem B5655581 : Blo 219811 5655581 := bstep (se 3 (by rfl) ⟨1060421, by rfl⟩ : syracuseStep 5655581 = 2120843) B2120843
theorem B1265179 : Blo 219811 1265179 := bstep (se 1 (by rfl) ⟨948884, by rfl⟩ : syracuseStep 1265179 = 1897769) B1897769
theorem B1134695 : Blo 219811 1134695 := bstep (se 1 (by rfl) ⟨851021, by rfl⟩ : syracuseStep 1134695 = 1702043) B1702043
theorem B677231 : Blo 219811 677231 := bstep (se 1 (by rfl) ⟨507923, by rfl⟩ : syracuseStep 677231 = 1015847) B1015847
theorem B251935 : Blo 219811 251935 := bstep (se 1 (by rfl) ⟨188951, by rfl⟩ : syracuseStep 251935 = 377903) B377903
theorem B219935 : Blo 219811 219935 := bstep (se 1 (by rfl) ⟨164951, by rfl⟩ : syracuseStep 219935 = 329903) B329903
theorem B220031 : Blo 219811 220031 := bstep (se 1 (by rfl) ⟨165023, by rfl⟩ : syracuseStep 220031 = 330047) B330047
theorem B744443 : Blo 219811 744443 := bstep (se 1 (by rfl) ⟨558332, by rfl⟩ : syracuseStep 744443 = 1116665) B1116665
theorem B220187 : Blo 219811 220187 := bstep (se 1 (by rfl) ⟨165140, by rfl⟩ : syracuseStep 220187 = 330281) B330281
theorem B220479 : Blo 219811 220479 := bstep (se 1 (by rfl) ⟨165359, by rfl⟩ : syracuseStep 220479 = 330719) B330719
theorem B220519 : Blo 219811 220519 := bstep (se 1 (by rfl) ⟨165389, by rfl⟩ : syracuseStep 220519 = 330779) B330779
theorem B220775 : Blo 219811 220775 := bstep (se 1 (by rfl) ⟨165581, by rfl⟩ : syracuseStep 220775 = 331163) B331163
theorem B221087 : Blo 219811 221087 := bstep (se 1 (by rfl) ⟨165815, by rfl⟩ : syracuseStep 221087 = 331631) B331631
theorem B843803 : Blo 219811 843803 := bstep (se 1 (by rfl) ⟨632852, by rfl⟩ : syracuseStep 843803 = 1265705) B1265705
theorem B221663 : Blo 219811 221663 := bstep (se 1 (by rfl) ⟨166247, by rfl⟩ : syracuseStep 221663 = 332495) B332495
theorem B221671 : Blo 219811 221671 := bstep (se 1 (by rfl) ⟨166253, by rfl⟩ : syracuseStep 221671 = 332507) B332507
theorem B221679 : Blo 219811 221679 := bstep (se 1 (by rfl) ⟨166259, by rfl⟩ : syracuseStep 221679 = 332519) B332519
theorem B221823 : Blo 219811 221823 := bstep (se 1 (by rfl) ⟨166367, by rfl⟩ : syracuseStep 221823 = 332735) B332735
theorem B418537 : Blo 219811 418537 := bstep (se 2 (by rfl) ⟨156951, by rfl⟩ : syracuseStep 418537 = 313903) B313903
theorem B8151839 : Blo 219811 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B3203873 : Blo 219811 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B844607 : Blo 219811 844607 := bstep (se 1 (by rfl) ⟨633455, by rfl⟩ : syracuseStep 844607 = 1266911) B1266911
theorem B746495 : Blo 219811 746495 := bstep (se 1 (by rfl) ⟨559871, by rfl⟩ : syracuseStep 746495 = 1119743) B1119743
theorem B222367 : Blo 219811 222367 := bstep (se 1 (by rfl) ⟨166775, by rfl⟩ : syracuseStep 222367 = 333551) B333551
theorem B10314971 : Blo 219811 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B3761639 : Blo 219811 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B222811 : Blo 219811 222811 := bstep (se 1 (by rfl) ⟨167108, by rfl⟩ : syracuseStep 222811 = 334217) B334217
theorem B222823 : Blo 219811 222823 := bstep (se 1 (by rfl) ⟨167117, by rfl⟩ : syracuseStep 222823 = 334235) B334235
theorem B223551 : Blo 219811 223551 := bstep (se 1 (by rfl) ⟨167663, by rfl⟩ : syracuseStep 223551 = 335327) B335327
theorem B223695 : Blo 219811 223695 := bstep (se 1 (by rfl) ⟨167771, by rfl⟩ : syracuseStep 223695 = 335543) B335543
theorem B420329 : Blo 219811 420329 := bstep (se 2 (by rfl) ⟨157623, by rfl⟩ : syracuseStep 420329 = 315247) B315247
theorem B944921 : Blo 219811 944921 := bstep (se 2 (by rfl) ⟨354345, by rfl⟩ : syracuseStep 944921 = 708691) B708691
theorem B1010555 : Blo 219811 1010555 := bstep (se 1 (by rfl) ⟨757916, by rfl⟩ : syracuseStep 1010555 = 1515833) B1515833
theorem B848495 : Blo 219811 848495 := bstep (se 1 (by rfl) ⟨636371, by rfl⟩ : syracuseStep 848495 = 1272743) B1272743
theorem B1372841 : Blo 219811 1372841 := bstep (se 2 (by rfl) ⟨514815, by rfl⟩ : syracuseStep 1372841 = 1029631) B1029631
theorem B751463 : Blo 219811 751463 := bstep (se 1 (by rfl) ⟨563597, by rfl⟩ : syracuseStep 751463 = 1127195) B1127195
theorem B2292137 : Blo 219811 2292137 := bstep (se 2 (by rfl) ⟨859551, by rfl⟩ : syracuseStep 2292137 = 1719103) B1719103
theorem B752381 : Blo 219811 752381 := bstep (se 3 (by rfl) ⟨141071, by rfl⟩ : syracuseStep 752381 = 282143) B282143
theorem B1342271 : Blo 219811 1342271 := bstep (se 1 (by rfl) ⟨1006703, by rfl⟩ : syracuseStep 1342271 = 2013407) B2013407
theorem B1342295 : Blo 219811 1342295 := bstep (se 1 (by rfl) ⟨1006721, by rfl⟩ : syracuseStep 1342295 = 2013443) B2013443
theorem B2030447 : Blo 219811 2030447 := bstep (se 1 (by rfl) ⟨1522835, by rfl⟩ : syracuseStep 2030447 = 3045671) B3045671
theorem B752975 : Blo 219811 752975 := bstep (se 1 (by rfl) ⟨564731, by rfl⟩ : syracuseStep 752975 = 1129463) B1129463
theorem B30539177 : Blo 219811 30539177 := bstep (se 2 (by rfl) ⟨11452191, by rfl⟩ : syracuseStep 30539177 = 22904383) B22904383
theorem B2817949 : Blo 219811 2817949 := bstep (se 3 (by rfl) ⟨528365, by rfl⟩ : syracuseStep 2817949 = 1056731) B1056731
theorem B917729 : Blo 219811 917729 := bstep (se 2 (by rfl) ⟨344148, by rfl⟩ : syracuseStep 917729 = 688297) B688297
theorem B2392699 : Blo 219811 2392699 := bstep (se 1 (by rfl) ⟨1794524, by rfl⟩ : syracuseStep 2392699 = 3589049) B3589049
theorem B5374613 : Blo 219811 5374613 := bstep (se 6 (by rfl) ⟨125967, by rfl⟩ : syracuseStep 5374613 = 251935) B251935
theorem B558049 : Blo 219811 558049 := bstep (se 2 (by rfl) ⟨209268, by rfl⟩ : syracuseStep 558049 = 418537) B418537
theorem B755369 : Blo 219811 755369 := bstep (se 2 (by rfl) ⟨283263, by rfl⟩ : syracuseStep 755369 = 566527) B566527
theorem B3770387 : Blo 219811 3770387 := bstep (se 1 (by rfl) ⟨2827790, by rfl⟩ : syracuseStep 3770387 = 5655581) B5655581
theorem B2132189 : Blo 219811 2132189 := bstep (se 3 (by rfl) ⟨399785, by rfl⟩ : syracuseStep 2132189 = 799571) B799571
theorem B330233 : Blo 219811 330233 := bstep (se 2 (by rfl) ⟨123837, by rfl⟩ : syracuseStep 330233 = 247675) B247675
theorem B330395 : Blo 219811 330395 := bstep (se 1 (by rfl) ⟨247796, by rfl⟩ : syracuseStep 330395 = 495593) B495593
theorem B1116827 : Blo 219811 1116827 := bstep (se 1 (by rfl) ⟨837620, by rfl⟩ : syracuseStep 1116827 = 1675241) B1675241
theorem B756463 : Blo 219811 756463 := bstep (se 1 (by rfl) ⟨567347, by rfl⟩ : syracuseStep 756463 = 1134695) B1134695
theorem B331295 : Blo 219811 331295 := bstep (se 1 (by rfl) ⟨248471, by rfl⟩ : syracuseStep 331295 = 496943) B496943
theorem B496295 : Blo 219811 496295 := bstep (se 1 (by rfl) ⟨372221, by rfl⟩ : syracuseStep 496295 = 744443) B744443
theorem B332903 : Blo 219811 332903 := bstep (se 1 (by rfl) ⟨249677, by rfl⟩ : syracuseStep 332903 = 499355) B499355
theorem B562535 : Blo 219811 562535 := bstep (se 1 (by rfl) ⟨421901, by rfl⟩ : syracuseStep 562535 = 843803) B843803
theorem B2135915 : Blo 219811 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B563071 : Blo 219811 563071 := bstep (se 1 (by rfl) ⟨422303, by rfl⟩ : syracuseStep 563071 = 844607) B844607
theorem B497663 : Blo 219811 497663 := bstep (se 1 (by rfl) ⟨373247, by rfl⟩ : syracuseStep 497663 = 746495) B746495
theorem B399671 : Blo 219811 399671 := bstep (se 1 (by rfl) ⟨299753, by rfl⟩ : syracuseStep 399671 = 599507) B599507
theorem B1120877 : Blo 219811 1120877 := bstep (se 3 (by rfl) ⟨210164, by rfl⟩ : syracuseStep 1120877 = 420329) B420329
theorem B629947 : Blo 219811 629947 := bstep (se 1 (by rfl) ⟨472460, by rfl⟩ : syracuseStep 629947 = 944921) B944921
theorem B629993 : Blo 219811 629993 := bstep (se 2 (by rfl) ⟨236247, by rfl⟩ : syracuseStep 629993 = 472495) B472495
theorem B335339 : Blo 219811 335339 := bstep (se 1 (by rfl) ⟨251504, by rfl⟩ : syracuseStep 335339 = 503009) B503009
theorem B3579389 : Blo 219811 3579389 := bstep (se 3 (by rfl) ⟨671135, by rfl⟩ : syracuseStep 3579389 = 1342271) B1342271
theorem B1122335 : Blo 219811 1122335 := bstep (se 1 (by rfl) ⟨841751, by rfl⟩ : syracuseStep 1122335 = 1683503) B1683503
theorem B565663 : Blo 219811 565663 := bstep (se 1 (by rfl) ⟨424247, by rfl⟩ : syracuseStep 565663 = 848495) B848495
theorem B1123307 : Blo 219811 1123307 := bstep (se 1 (by rfl) ⟨842480, by rfl⟩ : syracuseStep 1123307 = 1684961) B1684961
theorem B500975 : Blo 219811 500975 := bstep (se 1 (by rfl) ⟨375731, by rfl⟩ : syracuseStep 500975 = 751463) B751463
theorem B501587 : Blo 219811 501587 := bstep (se 1 (by rfl) ⟨376190, by rfl⟩ : syracuseStep 501587 = 752381) B752381
theorem B894863 : Blo 219811 894863 := bstep (se 1 (by rfl) ⟨671147, by rfl⟩ : syracuseStep 894863 = 1342295) B1342295
theorem B1353631 : Blo 219811 1353631 := bstep (se 1 (by rfl) ⟨1015223, by rfl⟩ : syracuseStep 1353631 = 2030447) B2030447
theorem B1910891 : Blo 219811 1910891 := bstep (se 1 (by rfl) ⟨1433168, by rfl⟩ : syracuseStep 1910891 = 2866337) B2866337
theorem B501983 : Blo 219811 501983 := bstep (se 1 (by rfl) ⟨376487, by rfl⟩ : syracuseStep 501983 = 752975) B752975
theorem B20359451 : Blo 219811 20359451 := bstep (se 1 (by rfl) ⟨15269588, by rfl⟩ : syracuseStep 20359451 = 30539177) B30539177
theorem B502649 : Blo 219811 502649 := bstep (se 2 (by rfl) ⟨188493, by rfl⟩ : syracuseStep 502649 = 376987) B376987
theorem B1289321 : Blo 219811 1289321 := bstep (se 2 (by rfl) ⟨483495, by rfl⟩ : syracuseStep 1289321 = 966991) B966991
theorem B636281 : Blo 219811 636281 := bstep (se 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) B477211
theorem B964327 : Blo 219811 964327 := bstep (se 1 (by rfl) ⟨723245, by rfl⟩ : syracuseStep 964327 = 1446491) B1446491
theorem B374537 : Blo 219811 374537 := bstep (se 2 (by rfl) ⟨140451, by rfl⟩ : syracuseStep 374537 = 280903) B280903
theorem B376111 : Blo 219811 376111 := bstep (se 1 (by rfl) ⟨282083, by rfl⟩ : syracuseStep 376111 = 564167) B564167
theorem B1686905 : Blo 219811 1686905 := bstep (se 2 (by rfl) ⟨632589, by rfl⟩ : syracuseStep 1686905 = 1265179) B1265179
theorem B802237 : Blo 219811 802237 := bstep (se 3 (by rfl) ⟨150419, by rfl⟩ : syracuseStep 802237 = 300839) B300839
theorem B704207 : Blo 219811 704207 := bstep (se 1 (by rfl) ⟨528155, by rfl⟩ : syracuseStep 704207 = 1056311) B1056311
theorem B835859 : Blo 219811 835859 := bstep (se 1 (by rfl) ⟨626894, by rfl⟩ : syracuseStep 835859 = 1253789) B1253789
theorem B377399 : Blo 219811 377399 := bstep (se 1 (by rfl) ⟨283049, by rfl⟩ : syracuseStep 377399 = 566099) B566099
theorem B3588731 : Blo 219811 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B2507759 : Blo 219811 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B2410399 : Blo 219811 2410399 := bstep (se 1 (by rfl) ⟨1807799, by rfl⟩ : syracuseStep 2410399 = 3615599) B3615599
theorem B673703 : Blo 219811 673703 := bstep (se 1 (by rfl) ⟨505277, by rfl⟩ : syracuseStep 673703 = 1010555) B1010555
theorem B5425127 : Blo 219811 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B248431 : Blo 219811 248431 := bstep (se 1 (by rfl) ⟨186323, by rfl⟩ : syracuseStep 248431 = 372647) B372647
theorem B838471 : Blo 219811 838471 := bstep (se 1 (by rfl) ⟨628853, by rfl⟩ : syracuseStep 838471 = 1257707) B1257707
theorem B708065 : Blo 219811 708065 := bstep (se 2 (by rfl) ⟨265524, by rfl⟩ : syracuseStep 708065 = 531049) B531049
theorem B839915 : Blo 219811 839915 := bstep (se 1 (by rfl) ⟨629936, by rfl⟩ : syracuseStep 839915 = 1259873) B1259873
theorem B1528091 : Blo 219811 1528091 := bstep (se 1 (by rfl) ⟨1146068, by rfl⟩ : syracuseStep 1528091 = 2292137) B2292137
theorem B12210689 : Blo 219811 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B1692251 : Blo 219811 1692251 := bstep (se 1 (by rfl) ⟨1269188, by rfl⟩ : syracuseStep 1692251 = 2538377) B2538377
theorem B742013 : Blo 219811 742013 := bstep (se 3 (by rfl) ⟨139127, by rfl⟩ : syracuseStep 742013 = 278255) B278255
theorem B709499 : Blo 219811 709499 := bstep (se 1 (by rfl) ⟨532124, by rfl⟩ : syracuseStep 709499 = 1064249) B1064249
theorem B3757265 : Blo 219811 3757265 := bstep (se 2 (by rfl) ⟨1408974, by rfl⟩ : syracuseStep 3757265 = 2817949) B2817949
theorem B32658713 : Blo 219811 32658713 := bstep (se 2 (by rfl) ⟨12247017, by rfl⟩ : syracuseStep 32658713 = 24494035) B24494035
theorem B251239 : Blo 219811 251239 := bstep (se 1 (by rfl) ⟨188429, by rfl⟩ : syracuseStep 251239 = 376859) B376859
theorem B742823 : Blo 219811 742823 := bstep (se 1 (by rfl) ⟨557117, by rfl⟩ : syracuseStep 742823 = 1114235) B1114235
theorem B251419 : Blo 219811 251419 := bstep (se 1 (by rfl) ⟨188564, by rfl⟩ : syracuseStep 251419 = 377129) B377129
theorem B743471 : Blo 219811 743471 := bstep (se 1 (by rfl) ⟨557603, by rfl⟩ : syracuseStep 743471 = 1115207) B1115207
theorem B743849 : Blo 219811 743849 := bstep (se 2 (by rfl) ⟨278943, by rfl⟩ : syracuseStep 743849 = 557887) B557887
theorem B1202663 : Blo 219811 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B220127 : Blo 219811 220127 := bstep (se 1 (by rfl) ⟨165095, by rfl⟩ : syracuseStep 220127 = 330191) B330191
theorem B679223 : Blo 219811 679223 := bstep (se 1 (by rfl) ⟨509417, by rfl⟩ : syracuseStep 679223 = 1018835) B1018835
theorem B220639 : Blo 219811 220639 := bstep (se 1 (by rfl) ⟨165479, by rfl⟩ : syracuseStep 220639 = 330959) B330959
theorem B221055 : Blo 219811 221055 := bstep (se 1 (by rfl) ⟨165791, by rfl⟩ : syracuseStep 221055 = 331583) B331583
theorem B3531005 : Blo 219811 3531005 := bstep (se 3 (by rfl) ⟨662063, by rfl⟩ : syracuseStep 3531005 = 1324127) B1324127
theorem B221927 : Blo 219811 221927 := bstep (se 1 (by rfl) ⟨166445, by rfl⟩ : syracuseStep 221927 = 332891) B332891
theorem B451487 : Blo 219811 451487 := bstep (se 1 (by rfl) ⟨338615, by rfl⟩ : syracuseStep 451487 = 677231) B677231
theorem B79193213 : Blo 219811 79193213 := bstep (se 3 (by rfl) ⟨14848727, by rfl⟩ : syracuseStep 79193213 = 29697455) B29697455
theorem B747575 : Blo 219811 747575 := bstep (se 1 (by rfl) ⟨560681, by rfl⟩ : syracuseStep 747575 = 1121363) B1121363
theorem B223591 : Blo 219811 223591 := bstep (se 1 (by rfl) ⟨167693, by rfl⟩ : syracuseStep 223591 = 335387) B335387
theorem B1599859 : Blo 219811 1599859 := bstep (se 1 (by rfl) ⟨1199894, by rfl⟩ : syracuseStep 1599859 = 2399789) B2399789
theorem B420223 : Blo 219811 420223 := bstep (se 1 (by rfl) ⟨315167, by rfl⟩ : syracuseStep 420223 = 630335) B630335
theorem B748385 : Blo 219811 748385 := bstep (se 2 (by rfl) ⟨280644, by rfl⟩ : syracuseStep 748385 = 561289) B561289
theorem B5434559 : Blo 219811 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B6876647 : Blo 219811 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B751031 : Blo 219811 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B915227 : Blo 219811 915227 := bstep (se 1 (by rfl) ⟨686420, by rfl⟩ : syracuseStep 915227 = 1372841) B1372841
theorem B424703 : Blo 219811 424703 := bstep (se 1 (by rfl) ⟨318527, by rfl⟩ : syracuseStep 424703 = 637055) B637055
theorem B10746917 : Blo 219811 10746917 := bstep (se 4 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 10746917 = 2015047) B2015047
theorem B1408873 : Blo 219811 1408873 := bstep (se 2 (by rfl) ⟨528327, by rfl⟩ : syracuseStep 1408873 = 1056655) B1056655
theorem B557239 : Blo 219811 557239 := bstep (se 1 (by rfl) ⟨417929, by rfl⟩ : syracuseStep 557239 = 835859) B835859
theorem B2392487 : Blo 219811 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B754217 : Blo 219811 754217 := bstep (se 2 (by rfl) ⟨282831, by rfl⟩ : syracuseStep 754217 = 565663) B565663
theorem B1671839 : Blo 219811 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B3213865 : Blo 219811 3213865 := bstep (se 2 (by rfl) ⟨1205199, by rfl⟩ : syracuseStep 3213865 = 2410399) B2410399
theorem B1804841 : Blo 219811 1804841 := bstep (se 2 (by rfl) ⟨676815, by rfl⟩ : syracuseStep 1804841 = 1353631) B1353631
theorem B559943 : Blo 219811 559943 := bstep (se 1 (by rfl) ⟨419957, by rfl⟩ : syracuseStep 559943 = 839915) B839915
theorem B1018727 : Blo 219811 1018727 := bstep (se 1 (by rfl) ⟨764045, by rfl⟩ : syracuseStep 1018727 = 1528091) B1528091
theorem B494675 : Blo 219811 494675 := bstep (se 1 (by rfl) ⟨371006, by rfl⟩ : syracuseStep 494675 = 742013) B742013
theorem B330863 : Blo 219811 330863 := bstep (se 1 (by rfl) ⟨248147, by rfl⟩ : syracuseStep 330863 = 496295) B496295
theorem B2133145 : Blo 219811 2133145 := bstep (se 2 (by rfl) ⟨799929, by rfl⟩ : syracuseStep 2133145 = 1599859) B1599859
theorem B560297 : Blo 219811 560297 := bstep (se 2 (by rfl) ⟨210111, by rfl⟩ : syracuseStep 560297 = 420223) B420223
theorem B331241 : Blo 219811 331241 := bstep (se 2 (by rfl) ⟨124215, by rfl⟩ : syracuseStep 331241 = 248431) B248431
theorem B495215 : Blo 219811 495215 := bstep (se 1 (by rfl) ⟨371411, by rfl⟩ : syracuseStep 495215 = 742823) B742823
theorem B1117961 : Blo 219811 1117961 := bstep (se 2 (by rfl) ⟨419235, by rfl⟩ : syracuseStep 1117961 = 838471) B838471
theorem B331775 : Blo 219811 331775 := bstep (se 1 (by rfl) ⟨248831, by rfl⟩ : syracuseStep 331775 = 497663) B497663
theorem B495647 : Blo 219811 495647 := bstep (se 1 (by rfl) ⟨371735, by rfl⟩ : syracuseStep 495647 = 743471) B743471
theorem B266447 : Blo 219811 266447 := bstep (se 1 (by rfl) ⟨199835, by rfl⟩ : syracuseStep 266447 = 399671) B399671
theorem B495899 : Blo 219811 495899 := bstep (se 1 (by rfl) ⟨371924, by rfl⟩ : syracuseStep 495899 = 743849) B743849
theorem B300991 : Blo 219811 300991 := bstep (se 1 (by rfl) ⟨225743, by rfl⟩ : syracuseStep 300991 = 451487) B451487
theorem B52795475 : Blo 219811 52795475 := bstep (se 1 (by rfl) ⟨39596606, by rfl⟩ : syracuseStep 52795475 = 79193213) B79193213
theorem B333983 : Blo 219811 333983 := bstep (se 1 (by rfl) ⟨250487, by rfl⟩ : syracuseStep 333983 = 500975) B500975
theorem B334391 : Blo 219811 334391 := bstep (se 1 (by rfl) ⟨250793, by rfl⟩ : syracuseStep 334391 = 501587) B501587
theorem B596575 : Blo 219811 596575 := bstep (se 1 (by rfl) ⟨447431, by rfl⟩ : syracuseStep 596575 = 894863) B894863
theorem B498383 : Blo 219811 498383 := bstep (se 1 (by rfl) ⟨373787, by rfl⟩ : syracuseStep 498383 = 747575) B747575
theorem B334655 : Blo 219811 334655 := bstep (se 1 (by rfl) ⟨250991, by rfl⟩ : syracuseStep 334655 = 501983) B501983
theorem B13572967 : Blo 219811 13572967 := bstep (se 1 (by rfl) ⟨10179725, by rfl⟩ : syracuseStep 13572967 = 20359451) B20359451
theorem B334985 : Blo 219811 334985 := bstep (se 2 (by rfl) ⟨125619, by rfl⟩ : syracuseStep 334985 = 251239) B251239
theorem B498923 : Blo 219811 498923 := bstep (se 1 (by rfl) ⟨374192, by rfl⟩ : syracuseStep 498923 = 748385) B748385
theorem B335099 : Blo 219811 335099 := bstep (se 1 (by rfl) ⟨251324, by rfl⟩ : syracuseStep 335099 = 502649) B502649
theorem B335225 : Blo 219811 335225 := bstep (se 2 (by rfl) ⟨125709, by rfl⟩ : syracuseStep 335225 = 251419) B251419
theorem B859547 : Blo 219811 859547 := bstep (se 1 (by rfl) ⟨644660, by rfl⟩ : syracuseStep 859547 = 1289321) B1289321
theorem B1285769 : Blo 219811 1285769 := bstep (se 2 (by rfl) ⟨482163, by rfl⟩ : syracuseStep 1285769 = 964327) B964327
theorem B1811261 : Blo 219811 1811261 := bstep (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) B679223
theorem B500687 : Blo 219811 500687 := bstep (se 1 (by rfl) ⟨375515, by rfl⟩ : syracuseStep 500687 = 751031) B751031
theorem B501481 : Blo 219811 501481 := bstep (se 2 (by rfl) ⟨188055, by rfl⟩ : syracuseStep 501481 = 376111) B376111
theorem B1124603 : Blo 219811 1124603 := bstep (se 1 (by rfl) ⟨843452, by rfl⟩ : syracuseStep 1124603 = 1686905) B1686905
theorem B469471 : Blo 219811 469471 := bstep (se 1 (by rfl) ⟨352103, by rfl⟩ : syracuseStep 469471 = 704207) B704207
theorem B1878497 : Blo 219811 1878497 := bstep (se 2 (by rfl) ⟨704436, by rfl⟩ : syracuseStep 1878497 = 1408873) B1408873
theorem B3190265 : Blo 219811 3190265 := bstep (se 2 (by rfl) ⟨1196349, by rfl⟩ : syracuseStep 3190265 = 2392699) B2392699
theorem B503579 : Blo 219811 503579 := bstep (se 1 (by rfl) ⟨377684, by rfl⟩ : syracuseStep 503579 = 755369) B755369
theorem B3616751 : Blo 219811 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B1421459 : Blo 219811 1421459 := bstep (se 1 (by rfl) ⟨1066094, by rfl⟩ : syracuseStep 1421459 = 2132189) B2132189
theorem B14332301 : Blo 219811 14332301 := bstep (se 3 (by rfl) ⟨2687306, by rfl⟩ : syracuseStep 14332301 = 5374613) B5374613
theorem B472043 : Blo 219811 472043 := bstep (se 1 (by rfl) ⟨354032, by rfl⟩ : syracuseStep 472043 = 708065) B708065
theorem B8140459 : Blo 219811 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B1128167 : Blo 219811 1128167 := bstep (se 1 (by rfl) ⟨846125, by rfl⟩ : syracuseStep 1128167 = 1692251) B1692251
theorem B2504843 : Blo 219811 2504843 := bstep (se 1 (by rfl) ⟨1878632, by rfl⟩ : syracuseStep 2504843 = 3757265) B3757265
theorem B21772475 : Blo 219811 21772475 := bstep (se 1 (by rfl) ⟨16329356, by rfl⟩ : syracuseStep 21772475 = 32658713) B32658713
theorem B375023 : Blo 219811 375023 := bstep (se 1 (by rfl) ⟨281267, by rfl⟩ : syracuseStep 375023 = 562535) B562535
theorem B1423943 : Blo 219811 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B801775 : Blo 219811 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B1132541 : Blo 219811 1132541 := bstep (se 3 (by rfl) ⟨212351, by rfl⟩ : syracuseStep 1132541 = 424703) B424703
theorem B3623039 : Blo 219811 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B249691 : Blo 219811 249691 := bstep (se 1 (by rfl) ⟨187268, by rfl⟩ : syracuseStep 249691 = 374537) B374537
theorem B610151 : Blo 219811 610151 := bstep (se 1 (by rfl) ⟨457613, by rfl⟩ : syracuseStep 610151 = 915227) B915227
theorem B839929 : Blo 219811 839929 := bstep (se 2 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 839929 = 629947) B629947
theorem B1069649 : Blo 219811 1069649 := bstep (se 2 (by rfl) ⟨401118, by rfl⟩ : syracuseStep 1069649 = 802237) B802237
theorem B7164611 : Blo 219811 7164611 := bstep (se 1 (by rfl) ⟨5373458, by rfl⟩ : syracuseStep 7164611 = 10746917) B10746917
theorem B611819 : Blo 219811 611819 := bstep (se 1 (by rfl) ⟨458864, by rfl⟩ : syracuseStep 611819 = 917729) B917729
theorem B251599 : Blo 219811 251599 := bstep (se 1 (by rfl) ⟨188699, by rfl⟩ : syracuseStep 251599 = 377399) B377399
theorem B449135 : Blo 219811 449135 := bstep (se 1 (by rfl) ⟨336851, by rfl⟩ : syracuseStep 449135 = 673703) B673703
theorem B744065 : Blo 219811 744065 := bstep (se 2 (by rfl) ⟨279024, by rfl⟩ : syracuseStep 744065 = 558049) B558049
theorem B2513591 : Blo 219811 2513591 := bstep (se 1 (by rfl) ⟨1885193, by rfl⟩ : syracuseStep 2513591 = 3770387) B3770387
theorem B220155 : Blo 219811 220155 := bstep (se 1 (by rfl) ⟨165116, by rfl⟩ : syracuseStep 220155 = 330233) B330233
theorem B744551 : Blo 219811 744551 := bstep (se 1 (by rfl) ⟨558413, by rfl⟩ : syracuseStep 744551 = 1116827) B1116827
theorem B220263 : Blo 219811 220263 := bstep (se 1 (by rfl) ⟨165197, by rfl⟩ : syracuseStep 220263 = 330395) B330395
theorem B1891997 : Blo 219811 1891997 := bstep (se 3 (by rfl) ⟨354749, by rfl⟩ : syracuseStep 1891997 = 709499) B709499
theorem B220863 : Blo 219811 220863 := bstep (se 1 (by rfl) ⟨165647, by rfl⟩ : syracuseStep 220863 = 331295) B331295
theorem B221935 : Blo 219811 221935 := bstep (se 1 (by rfl) ⟨166451, by rfl⟩ : syracuseStep 221935 = 332903) B332903
theorem B1008617 : Blo 219811 1008617 := bstep (se 2 (by rfl) ⟨378231, by rfl⟩ : syracuseStep 1008617 = 756463) B756463
theorem B747251 : Blo 219811 747251 := bstep (se 1 (by rfl) ⟨560438, by rfl⟩ : syracuseStep 747251 = 1120877) B1120877
theorem B419995 : Blo 219811 419995 := bstep (se 1 (by rfl) ⟨314996, by rfl⟩ : syracuseStep 419995 = 629993) B629993
theorem B223559 : Blo 219811 223559 := bstep (se 1 (by rfl) ⟨167669, by rfl⟩ : syracuseStep 223559 = 335339) B335339
theorem B2386259 : Blo 219811 2386259 := bstep (se 1 (by rfl) ⟨1789694, by rfl⟩ : syracuseStep 2386259 = 3579389) B3579389
theorem B748223 : Blo 219811 748223 := bstep (se 1 (by rfl) ⟨561167, by rfl⟩ : syracuseStep 748223 = 1122335) B1122335
theorem B2354003 : Blo 219811 2354003 := bstep (se 1 (by rfl) ⟨1765502, by rfl⟩ : syracuseStep 2354003 = 3531005) B3531005
theorem B748871 : Blo 219811 748871 := bstep (se 1 (by rfl) ⟨561653, by rfl⟩ : syracuseStep 748871 = 1123307) B1123307
theorem B1273927 : Blo 219811 1273927 := bstep (se 1 (by rfl) ⟨955445, by rfl⟩ : syracuseStep 1273927 = 1910891) B1910891
theorem B4584431 : Blo 219811 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B750761 : Blo 219811 750761 := bstep (se 2 (by rfl) ⟨281535, by rfl⟩ : syracuseStep 750761 = 563071) B563071
theorem B424187 : Blo 219811 424187 := bstep (se 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) B636281
theorem B1114559 : Blo 219811 1114559 := bstep (se 1 (by rfl) ⟨835919, by rfl⟩ : syracuseStep 1114559 = 1671839) B1671839
theorem B755027 : Blo 219811 755027 := bstep (se 1 (by rfl) ⟨566270, by rfl⟩ : syracuseStep 755027 = 1132541) B1132541
theorem B329783 : Blo 219811 329783 := bstep (se 1 (by rfl) ⟨247337, by rfl⟩ : syracuseStep 329783 = 494675) B494675
theorem B330143 : Blo 219811 330143 := bstep (se 1 (by rfl) ⟨247607, by rfl⟩ : syracuseStep 330143 = 495215) B495215
theorem B2689645 : Blo 219811 2689645 := bstep (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) B1008617
theorem B330431 : Blo 219811 330431 := bstep (se 1 (by rfl) ⟨247823, by rfl⟩ : syracuseStep 330431 = 495647) B495647
theorem B330599 : Blo 219811 330599 := bstep (se 1 (by rfl) ⟨247949, by rfl⟩ : syracuseStep 330599 = 495899) B495899
theorem B559993 : Blo 219811 559993 := bstep (se 2 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 559993 = 419995) B419995
theorem B625961 : Blo 219811 625961 := bstep (se 2 (by rfl) ⟨234735, by rfl⟩ : syracuseStep 625961 = 469471) B469471
theorem B35196983 : Blo 219811 35196983 := bstep (se 1 (by rfl) ⟨26397737, by rfl⟩ : syracuseStep 35196983 = 52795475) B52795475
theorem B299423 : Blo 219811 299423 := bstep (se 1 (by rfl) ⟨224567, by rfl⟩ : syracuseStep 299423 = 449135) B449135
theorem B496043 : Blo 219811 496043 := bstep (se 1 (by rfl) ⟨372032, by rfl⟩ : syracuseStep 496043 = 744065) B744065
theorem B1675727 : Blo 219811 1675727 := bstep (se 1 (by rfl) ⟨1256795, by rfl⟩ : syracuseStep 1675727 = 2513591) B2513591
theorem B332255 : Blo 219811 332255 := bstep (se 1 (by rfl) ⟨249191, by rfl⟩ : syracuseStep 332255 = 498383) B498383
theorem B496367 : Blo 219811 496367 := bstep (se 1 (by rfl) ⟨372275, by rfl⟩ : syracuseStep 496367 = 744551) B744551
theorem B332615 : Blo 219811 332615 := bstep (se 1 (by rfl) ⟨249461, by rfl⟩ : syracuseStep 332615 = 498923) B498923
theorem B857179 : Blo 219811 857179 := bstep (se 1 (by rfl) ⟨642884, by rfl⟩ : syracuseStep 857179 = 1285769) B1285769
theorem B332921 : Blo 219811 332921 := bstep (se 2 (by rfl) ⟨124845, by rfl⟩ : syracuseStep 332921 = 249691) B249691
theorem B1119905 : Blo 219811 1119905 := bstep (se 2 (by rfl) ⟨419964, by rfl⟩ : syracuseStep 1119905 = 839929) B839929
theorem B333791 : Blo 219811 333791 := bstep (se 1 (by rfl) ⟨250343, by rfl⟩ : syracuseStep 333791 = 500687) B500687
theorem B498167 : Blo 219811 498167 := bstep (se 1 (by rfl) ⟨373625, by rfl⟩ : syracuseStep 498167 = 747251) B747251
theorem B1252331 : Blo 219811 1252331 := bstep (se 1 (by rfl) ⟨939248, by rfl⟩ : syracuseStep 1252331 = 1878497) B1878497
theorem B498815 : Blo 219811 498815 := bstep (se 1 (by rfl) ⟨374111, by rfl⟩ : syracuseStep 498815 = 748223) B748223
theorem B499247 : Blo 219811 499247 := bstep (se 1 (by rfl) ⟨374435, by rfl⟩ : syracuseStep 499247 = 748871) B748871
theorem B10853945 : Blo 219811 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B335465 : Blo 219811 335465 := bstep (se 2 (by rfl) ⟨125799, by rfl⟩ : syracuseStep 335465 = 251599) B251599
theorem B335719 : Blo 219811 335719 := bstep (se 1 (by rfl) ⟨251789, by rfl⟩ : syracuseStep 335719 = 503579) B503579
theorem B401321 : Blo 219811 401321 := bstep (se 2 (by rfl) ⟨150495, by rfl⟩ : syracuseStep 401321 = 300991) B300991
theorem B3056287 : Blo 219811 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B500507 : Blo 219811 500507 := bstep (se 1 (by rfl) ⟨375380, by rfl⟩ : syracuseStep 500507 = 750761) B750761
theorem B795433 : Blo 219811 795433 := bstep (se 2 (by rfl) ⟨298287, by rfl⟩ : syracuseStep 795433 = 596575) B596575
theorem B25109365 : Blo 219811 25109365 := bstep (se 5 (by rfl) ⟨1177001, by rfl⟩ : syracuseStep 25109365 = 2354003) B2354003
theorem B18097289 : Blo 219811 18097289 := bstep (se 2 (by rfl) ⟨6786483, by rfl⟩ : syracuseStep 18097289 = 13572967) B13572967
theorem B9644669 : Blo 219811 9644669 := bstep (se 3 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 9644669 = 3616751) B3616751
theorem B502811 : Blo 219811 502811 := bstep (se 1 (by rfl) ⟨377108, by rfl⟩ : syracuseStep 502811 = 754217) B754217
theorem B373295 : Blo 219811 373295 := bstep (se 1 (by rfl) ⟨279971, by rfl⟩ : syracuseStep 373295 = 559943) B559943
theorem B373531 : Blo 219811 373531 := bstep (se 1 (by rfl) ⟨280148, by rfl⟩ : syracuseStep 373531 = 560297) B560297
theorem B407879 : Blo 219811 407879 := bstep (se 1 (by rfl) ⟨305909, by rfl⟩ : syracuseStep 407879 = 611819) B611819
theorem B573031 : Blo 219811 573031 := bstep (se 1 (by rfl) ⟨429773, by rfl⟩ : syracuseStep 573031 = 859547) B859547
theorem B1261331 : Blo 219811 1261331 := bstep (se 1 (by rfl) ⟨945998, by rfl⟩ : syracuseStep 1261331 = 1891997) B1891997
theorem B1590839 : Blo 219811 1590839 := bstep (se 1 (by rfl) ⟨1193129, by rfl⟩ : syracuseStep 1590839 = 2386259) B2386259
theorem B9554867 : Blo 219811 9554867 := bstep (se 1 (by rfl) ⟨7166150, by rfl⟩ : syracuseStep 9554867 = 14332301) B14332301
theorem B314695 : Blo 219811 314695 := bstep (se 1 (by rfl) ⟨236021, by rfl⟩ : syracuseStep 314695 = 472043) B472043
theorem B2674565 : Blo 219811 2674565 := bstep (se 4 (by rfl) ⟨250740, by rfl⟩ : syracuseStep 2674565 = 501481) B501481
theorem B1069033 : Blo 219811 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B250015 : Blo 219811 250015 := bstep (se 1 (by rfl) ⟨187511, by rfl⟩ : syracuseStep 250015 = 375023) B375023
theorem B282791 : Blo 219811 282791 := bstep (se 1 (by rfl) ⟨212093, by rfl⟩ : syracuseStep 282791 = 424187) B424187
theorem B1627069 : Blo 219811 1627069 := bstep (se 3 (by rfl) ⟨305075, by rfl⟩ : syracuseStep 1627069 = 610151) B610151
theorem B742985 : Blo 219811 742985 := bstep (se 2 (by rfl) ⟨278619, by rfl⟩ : syracuseStep 742985 = 557239) B557239
theorem B1594991 : Blo 219811 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B710525 : Blo 219811 710525 := bstep (se 3 (by rfl) ⟨133223, by rfl⟩ : syracuseStep 710525 = 266447) B266447
theorem B2415359 : Blo 219811 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B1203227 : Blo 219811 1203227 := bstep (se 1 (by rfl) ⟨902420, by rfl⟩ : syracuseStep 1203227 = 1804841) B1804841
theorem B679151 : Blo 219811 679151 := bstep (se 1 (by rfl) ⟨509363, by rfl⟩ : syracuseStep 679151 = 1018727) B1018727
theorem B220575 : Blo 219811 220575 := bstep (se 1 (by rfl) ⟨165431, by rfl⟩ : syracuseStep 220575 = 330863) B330863
theorem B220827 : Blo 219811 220827 := bstep (se 1 (by rfl) ⟨165620, by rfl⟩ : syracuseStep 220827 = 331241) B331241
theorem B745307 : Blo 219811 745307 := bstep (se 1 (by rfl) ⟨558980, by rfl⟩ : syracuseStep 745307 = 1117961) B1117961
theorem B221183 : Blo 219811 221183 := bstep (se 1 (by rfl) ⟨165887, by rfl⟩ : syracuseStep 221183 = 331775) B331775
theorem B713099 : Blo 219811 713099 := bstep (se 1 (by rfl) ⟨534824, by rfl⟩ : syracuseStep 713099 = 1069649) B1069649
theorem B4776407 : Blo 219811 4776407 := bstep (se 1 (by rfl) ⟨3582305, by rfl⟩ : syracuseStep 4776407 = 7164611) B7164611
theorem B4285153 : Blo 219811 4285153 := bstep (se 2 (by rfl) ⟨1606932, by rfl⟩ : syracuseStep 4285153 = 3213865) B3213865
theorem B222655 : Blo 219811 222655 := bstep (se 1 (by rfl) ⟨166991, by rfl⟩ : syracuseStep 222655 = 333983) B333983
theorem B2844193 : Blo 219811 2844193 := bstep (se 2 (by rfl) ⟨1066572, by rfl⟩ : syracuseStep 2844193 = 2133145) B2133145
theorem B222927 : Blo 219811 222927 := bstep (se 1 (by rfl) ⟨167195, by rfl⟩ : syracuseStep 222927 = 334391) B334391
theorem B223103 : Blo 219811 223103 := bstep (se 1 (by rfl) ⟨167327, by rfl⟩ : syracuseStep 223103 = 334655) B334655
theorem B223323 : Blo 219811 223323 := bstep (se 1 (by rfl) ⟨167492, by rfl⟩ : syracuseStep 223323 = 334985) B334985
theorem B223399 : Blo 219811 223399 := bstep (se 1 (by rfl) ⟨167549, by rfl⟩ : syracuseStep 223399 = 335099) B335099
theorem B223483 : Blo 219811 223483 := bstep (se 1 (by rfl) ⟨167612, by rfl⟩ : syracuseStep 223483 = 335225) B335225
theorem B1698569 : Blo 219811 1698569 := bstep (se 2 (by rfl) ⟨636963, by rfl⟩ : syracuseStep 1698569 = 1273927) B1273927
theorem B1207507 : Blo 219811 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B749735 : Blo 219811 749735 := bstep (se 1 (by rfl) ⟨562301, by rfl⟩ : syracuseStep 749735 = 1124603) B1124603
theorem B2126843 : Blo 219811 2126843 := bstep (se 1 (by rfl) ⟨1595132, by rfl⟩ : syracuseStep 2126843 = 3190265) B3190265
theorem B947639 : Blo 219811 947639 := bstep (se 1 (by rfl) ⟨710729, by rfl⟩ : syracuseStep 947639 = 1421459) B1421459
theorem B752111 : Blo 219811 752111 := bstep (se 1 (by rfl) ⟨564083, by rfl⟩ : syracuseStep 752111 = 1128167) B1128167
theorem B1669895 : Blo 219811 1669895 := bstep (se 1 (by rfl) ⟨1252421, by rfl⟩ : syracuseStep 1669895 = 2504843) B2504843
theorem B14514983 : Blo 219811 14514983 := bstep (se 1 (by rfl) ⟨10886237, by rfl⟩ : syracuseStep 14514983 = 21772475) B21772475
theorem B949295 : Blo 219811 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B754109 : Blo 219811 754109 := bstep (se 3 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 754109 = 282791) B282791
theorem B23464655 : Blo 219811 23464655 := bstep (se 1 (by rfl) ⟨17598491, by rfl⟩ : syracuseStep 23464655 = 35196983) B35196983
theorem B330695 : Blo 219811 330695 := bstep (se 1 (by rfl) ⟨248021, by rfl⟩ : syracuseStep 330695 = 496043) B496043
theorem B1117151 : Blo 219811 1117151 := bstep (se 1 (by rfl) ⟨837863, by rfl⟩ : syracuseStep 1117151 = 1675727) B1675727
theorem B330911 : Blo 219811 330911 := bstep (se 1 (by rfl) ⟨248183, by rfl⟩ : syracuseStep 330911 = 496367) B496367
theorem B495323 : Blo 219811 495323 := bstep (se 1 (by rfl) ⟨371492, by rfl⟩ : syracuseStep 495323 = 742985) B742985
theorem B1610009 : Blo 219811 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B332111 : Blo 219811 332111 := bstep (se 1 (by rfl) ⟨249083, by rfl⟩ : syracuseStep 332111 = 498167) B498167
theorem B332543 : Blo 219811 332543 := bstep (se 1 (by rfl) ⟨249407, by rfl⟩ : syracuseStep 332543 = 498815) B498815
theorem B332831 : Blo 219811 332831 := bstep (se 1 (by rfl) ⟨249623, by rfl⟩ : syracuseStep 332831 = 499247) B499247
theorem B496871 : Blo 219811 496871 := bstep (se 1 (by rfl) ⟨372653, by rfl⟩ : syracuseStep 496871 = 745307) B745307
theorem B267547 : Blo 219811 267547 := bstep (se 1 (by rfl) ⟨200660, by rfl⟩ : syracuseStep 267547 = 401321) B401321
theorem B333353 : Blo 219811 333353 := bstep (se 2 (by rfl) ⟨125007, by rfl⟩ : syracuseStep 333353 = 250015) B250015
theorem B3184271 : Blo 219811 3184271 := bstep (se 1 (by rfl) ⟨2388203, by rfl⟩ : syracuseStep 3184271 = 4776407) B4776407
theorem B333671 : Blo 219811 333671 := bstep (se 1 (by rfl) ⟨250253, by rfl⟩ : syracuseStep 333671 = 500507) B500507
theorem B12064859 : Blo 219811 12064859 := bstep (se 1 (by rfl) ⟨9048644, by rfl⟩ : syracuseStep 12064859 = 18097289) B18097289
theorem B498041 : Blo 219811 498041 := bstep (se 2 (by rfl) ⟨186765, by rfl⟩ : syracuseStep 498041 = 373531) B373531
theorem B2169425 : Blo 219811 2169425 := bstep (se 2 (by rfl) ⟨813534, by rfl⟩ : syracuseStep 2169425 = 1627069) B1627069
theorem B6429779 : Blo 219811 6429779 := bstep (se 1 (by rfl) ⟨4822334, by rfl⟩ : syracuseStep 6429779 = 9644669) B9644669
theorem B335207 : Blo 219811 335207 := bstep (se 1 (by rfl) ⟨251405, by rfl⟩ : syracuseStep 335207 = 502811) B502811
theorem B499823 : Blo 219811 499823 := bstep (se 1 (by rfl) ⟨374867, by rfl⟩ : syracuseStep 499823 = 749735) B749735
theorem B1811069 : Blo 219811 1811069 := bstep (se 3 (by rfl) ⟨339575, by rfl⟩ : syracuseStep 1811069 = 679151) B679151
theorem B1417895 : Blo 219811 1417895 := bstep (se 1 (by rfl) ⟨1063421, by rfl⟩ : syracuseStep 1417895 = 2126843) B2126843
theorem B631759 : Blo 219811 631759 := bstep (se 1 (by rfl) ⟨473819, by rfl⟩ : syracuseStep 631759 = 947639) B947639
theorem B271919 : Blo 219811 271919 := bstep (se 1 (by rfl) ⟨203939, by rfl⟩ : syracuseStep 271919 = 407879) B407879
theorem B501407 : Blo 219811 501407 := bstep (se 1 (by rfl) ⟨376055, by rfl⟩ : syracuseStep 501407 = 752111) B752111
theorem B9676655 : Blo 219811 9676655 := bstep (se 1 (by rfl) ⟨7257491, by rfl⟩ : syracuseStep 9676655 = 14514983) B14514983
theorem B632863 : Blo 219811 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B764041 : Blo 219811 764041 := bstep (se 2 (by rfl) ⟨286515, by rfl⟩ : syracuseStep 764041 = 573031) B573031
theorem B4075049 : Blo 219811 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B503351 : Blo 219811 503351 := bstep (se 1 (by rfl) ⟨377513, by rfl⟩ : syracuseStep 503351 = 755027) B755027
theorem B5713537 : Blo 219811 5713537 := bstep (se 2 (by rfl) ⟨2142576, by rfl⟩ : syracuseStep 5713537 = 4285153) B4285153
theorem B1060559 : Blo 219811 1060559 := bstep (se 1 (by rfl) ⟨795419, by rfl⟩ : syracuseStep 1060559 = 1590839) B1590839
theorem B1060577 : Blo 219811 1060577 := bstep (se 2 (by rfl) ⟨397716, by rfl⟩ : syracuseStep 1060577 = 795433) B795433
theorem B798461 : Blo 219811 798461 := bstep (se 3 (by rfl) ⟨149711, by rfl⟩ : syracuseStep 798461 = 299423) B299423
theorem B6369911 : Blo 219811 6369911 := bstep (se 1 (by rfl) ⟨4777433, by rfl⟩ : syracuseStep 6369911 = 9554867) B9554867
theorem B1783043 : Blo 219811 1783043 := bstep (se 1 (by rfl) ⟨1337282, by rfl⟩ : syracuseStep 1783043 = 2674565) B2674565
theorem B3586193 : Blo 219811 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1063327 : Blo 219811 1063327 := bstep (se 1 (by rfl) ⟨797495, by rfl⟩ : syracuseStep 1063327 = 1594991) B1594991
theorem B473683 : Blo 219811 473683 := bstep (se 1 (by rfl) ⟨355262, by rfl⟩ : syracuseStep 473683 = 710525) B710525
theorem B834887 : Blo 219811 834887 := bstep (se 1 (by rfl) ⟨626165, by rfl⟩ : syracuseStep 834887 = 1252331) B1252331
theorem B802151 : Blo 219811 802151 := bstep (se 1 (by rfl) ⟨601613, by rfl⟩ : syracuseStep 802151 = 1203227) B1203227
theorem B1425377 : Blo 219811 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B475399 : Blo 219811 475399 := bstep (se 1 (by rfl) ⟨356549, by rfl⟩ : syracuseStep 475399 = 713099) B713099
theorem B1132379 : Blo 219811 1132379 := bstep (se 1 (by rfl) ⟨849284, by rfl⟩ : syracuseStep 1132379 = 1698569) B1698569
theorem B6440957 : Blo 219811 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B248863 : Blo 219811 248863 := bstep (se 1 (by rfl) ⟨186647, by rfl⟩ : syracuseStep 248863 = 373295) B373295
theorem B447625 : Blo 219811 447625 := bstep (se 2 (by rfl) ⟨167859, by rfl⟩ : syracuseStep 447625 = 335719) B335719
theorem B840887 : Blo 219811 840887 := bstep (se 1 (by rfl) ⟨630665, by rfl⟩ : syracuseStep 840887 = 1261331) B1261331
theorem B743039 : Blo 219811 743039 := bstep (se 1 (by rfl) ⟨557279, by rfl⟩ : syracuseStep 743039 = 1114559) B1114559
theorem B33479153 : Blo 219811 33479153 := bstep (se 2 (by rfl) ⟨12554682, by rfl⟩ : syracuseStep 33479153 = 25109365) B25109365
theorem B219855 : Blo 219811 219855 := bstep (se 1 (by rfl) ⟨164891, by rfl⟩ : syracuseStep 219855 = 329783) B329783
theorem B220095 : Blo 219811 220095 := bstep (se 1 (by rfl) ⟨165071, by rfl⟩ : syracuseStep 220095 = 330143) B330143
theorem B220287 : Blo 219811 220287 := bstep (se 1 (by rfl) ⟨165215, by rfl⟩ : syracuseStep 220287 = 330431) B330431
theorem B220399 : Blo 219811 220399 := bstep (se 1 (by rfl) ⟨165299, by rfl⟩ : syracuseStep 220399 = 330599) B330599
theorem B3792257 : Blo 219811 3792257 := bstep (se 2 (by rfl) ⟨1422096, by rfl⟩ : syracuseStep 3792257 = 2844193) B2844193
theorem B417307 : Blo 219811 417307 := bstep (se 1 (by rfl) ⟨312980, by rfl⟩ : syracuseStep 417307 = 625961) B625961
theorem B221503 : Blo 219811 221503 := bstep (se 1 (by rfl) ⟨166127, by rfl⟩ : syracuseStep 221503 = 332255) B332255
theorem B221743 : Blo 219811 221743 := bstep (se 1 (by rfl) ⟨166307, by rfl⟩ : syracuseStep 221743 = 332615) B332615
theorem B221947 : Blo 219811 221947 := bstep (se 1 (by rfl) ⟨166460, by rfl⟩ : syracuseStep 221947 = 332921) B332921
theorem B746603 : Blo 219811 746603 := bstep (se 1 (by rfl) ⟨559952, by rfl⟩ : syracuseStep 746603 = 1119905) B1119905
theorem B746657 : Blo 219811 746657 := bstep (se 2 (by rfl) ⟨279996, by rfl⟩ : syracuseStep 746657 = 559993) B559993
theorem B222527 : Blo 219811 222527 := bstep (se 1 (by rfl) ⟨166895, by rfl⟩ : syracuseStep 222527 = 333791) B333791
theorem B419593 : Blo 219811 419593 := bstep (se 2 (by rfl) ⟨157347, by rfl⟩ : syracuseStep 419593 = 314695) B314695
theorem B7235963 : Blo 219811 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B223643 : Blo 219811 223643 := bstep (se 1 (by rfl) ⟨167732, by rfl⟩ : syracuseStep 223643 = 335465) B335465
theorem B1142905 : Blo 219811 1142905 := bstep (se 2 (by rfl) ⟨428589, by rfl⟩ : syracuseStep 1142905 = 857179) B857179
theorem B1113263 : Blo 219811 1113263 := bstep (se 1 (by rfl) ⟨834947, by rfl⟩ : syracuseStep 1113263 = 1669895) B1669895
theorem B754919 : Blo 219811 754919 := bstep (se 1 (by rfl) ⟨566189, by rfl⟩ : syracuseStep 754919 = 1132379) B1132379
theorem B4293971 : Blo 219811 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B559457 : Blo 219811 559457 := bstep (se 2 (by rfl) ⟨209796, by rfl⟩ : syracuseStep 559457 = 419593) B419593
theorem B330215 : Blo 219811 330215 := bstep (se 1 (by rfl) ⟨247661, by rfl⟩ : syracuseStep 330215 = 495323) B495323
theorem B1018721 : Blo 219811 1018721 := bstep (se 2 (by rfl) ⟨382020, by rfl⟩ : syracuseStep 1018721 = 764041) B764041
theorem B560591 : Blo 219811 560591 := bstep (se 1 (by rfl) ⟨420443, by rfl⟩ : syracuseStep 560591 = 840887) B840887
theorem B331247 : Blo 219811 331247 := bstep (se 1 (by rfl) ⟨248435, by rfl⟩ : syracuseStep 331247 = 496871) B496871
theorem B495359 : Blo 219811 495359 := bstep (se 1 (by rfl) ⟨371519, by rfl⟩ : syracuseStep 495359 = 743039) B743039
theorem B331817 : Blo 219811 331817 := bstep (se 2 (by rfl) ⟨124431, by rfl⟩ : syracuseStep 331817 = 248863) B248863
theorem B725117 : Blo 219811 725117 := bstep (se 3 (by rfl) ⟨135959, by rfl⟩ : syracuseStep 725117 = 271919) B271919
theorem B332027 : Blo 219811 332027 := bstep (se 1 (by rfl) ⟨249020, by rfl⟩ : syracuseStep 332027 = 498041) B498041
theorem B22319435 : Blo 219811 22319435 := bstep (se 1 (by rfl) ⟨16739576, by rfl⟩ : syracuseStep 22319435 = 33479153) B33479153
theorem B1446283 : Blo 219811 1446283 := bstep (se 1 (by rfl) ⟨1084712, by rfl⟩ : syracuseStep 1446283 = 2169425) B2169425
theorem B2528171 : Blo 219811 2528171 := bstep (se 1 (by rfl) ⟨1896128, by rfl⟩ : syracuseStep 2528171 = 3792257) B3792257
theorem B333215 : Blo 219811 333215 := bstep (se 1 (by rfl) ⟨249911, by rfl⟩ : syracuseStep 333215 = 499823) B499823
theorem B497735 : Blo 219811 497735 := bstep (se 1 (by rfl) ⟨373301, by rfl⟩ : syracuseStep 497735 = 746603) B746603
theorem B497771 : Blo 219811 497771 := bstep (se 1 (by rfl) ⟨373328, by rfl⟩ : syracuseStep 497771 = 746657) B746657
theorem B334271 : Blo 219811 334271 := bstep (se 1 (by rfl) ⟨250703, by rfl⟩ : syracuseStep 334271 = 501407) B501407
theorem B4823975 : Blo 219811 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B335567 : Blo 219811 335567 := bstep (se 1 (by rfl) ⟨251675, by rfl⟩ : syracuseStep 335567 = 503351) B503351
theorem B532307 : Blo 219811 532307 := bstep (se 1 (by rfl) ⟨399230, by rfl⟩ : syracuseStep 532307 = 798461) B798461
theorem B1417769 : Blo 219811 1417769 := bstep (se 2 (by rfl) ⟨531663, by rfl⟩ : syracuseStep 1417769 = 1063327) B1063327
theorem B631577 : Blo 219811 631577 := bstep (se 2 (by rfl) ⟨236841, by rfl⟩ : syracuseStep 631577 = 473683) B473683
theorem B1188695 : Blo 219811 1188695 := bstep (se 1 (by rfl) ⟨891521, by rfl⟩ : syracuseStep 1188695 = 1783043) B1783043
theorem B534767 : Blo 219811 534767 := bstep (se 1 (by rfl) ⟨401075, by rfl⟩ : syracuseStep 534767 = 802151) B802151
theorem B502739 : Blo 219811 502739 := bstep (se 1 (by rfl) ⟨377054, by rfl⟩ : syracuseStep 502739 = 754109) B754109
theorem B2535461 : Blo 219811 2535461 := bstep (se 4 (by rfl) ⟨237699, by rfl⟩ : syracuseStep 2535461 = 475399) B475399
theorem B15643103 : Blo 219811 15643103 := bstep (se 1 (by rfl) ⟨11732327, by rfl⟩ : syracuseStep 15643103 = 23464655) B23464655
theorem B8043239 : Blo 219811 8043239 := bstep (se 1 (by rfl) ⟨6032429, by rfl⟩ : syracuseStep 8043239 = 12064859) B12064859
theorem B7618049 : Blo 219811 7618049 := bstep (se 2 (by rfl) ⟨2856768, by rfl⟩ : syracuseStep 7618049 = 5713537) B5713537
theorem B1523873 : Blo 219811 1523873 := bstep (se 2 (by rfl) ⟨571452, by rfl⟩ : syracuseStep 1523873 = 1142905) B1142905
theorem B707039 : Blo 219811 707039 := bstep (se 1 (by rfl) ⟨530279, by rfl⟩ : syracuseStep 707039 = 1060559) B1060559
theorem B707051 : Blo 219811 707051 := bstep (se 1 (by rfl) ⟨530288, by rfl⟩ : syracuseStep 707051 = 1060577) B1060577
theorem B4246607 : Blo 219811 4246607 := bstep (se 1 (by rfl) ⟨3184955, by rfl⟩ : syracuseStep 4246607 = 6369911) B6369911
theorem B742175 : Blo 219811 742175 := bstep (se 1 (by rfl) ⟨556631, by rfl⟩ : syracuseStep 742175 = 1113263) B1113263
theorem B842345 : Blo 219811 842345 := bstep (se 2 (by rfl) ⟨315879, by rfl⟩ : syracuseStep 842345 = 631759) B631759
theorem B220463 : Blo 219811 220463 := bstep (se 1 (by rfl) ⟨165347, by rfl⟩ : syracuseStep 220463 = 330695) B330695
theorem B744767 : Blo 219811 744767 := bstep (se 1 (by rfl) ⟨558575, by rfl⟩ : syracuseStep 744767 = 1117151) B1117151
theorem B220607 : Blo 219811 220607 := bstep (se 1 (by rfl) ⟨165455, by rfl⟩ : syracuseStep 220607 = 330911) B330911
theorem B843817 : Blo 219811 843817 := bstep (se 2 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 843817 = 632863) B632863
theorem B1073339 : Blo 219811 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B221407 : Blo 219811 221407 := bstep (se 1 (by rfl) ⟨166055, by rfl⟩ : syracuseStep 221407 = 332111) B332111
theorem B221695 : Blo 219811 221695 := bstep (se 1 (by rfl) ⟨166271, by rfl⟩ : syracuseStep 221695 = 332543) B332543
theorem B221887 : Blo 219811 221887 := bstep (se 1 (by rfl) ⟨166415, by rfl⟩ : syracuseStep 221887 = 332831) B332831
theorem B222235 : Blo 219811 222235 := bstep (se 1 (by rfl) ⟨166676, by rfl⟩ : syracuseStep 222235 = 333353) B333353
theorem B2122847 : Blo 219811 2122847 := bstep (se 1 (by rfl) ⟨1592135, by rfl⟩ : syracuseStep 2122847 = 3184271) B3184271
theorem B222447 : Blo 219811 222447 := bstep (se 1 (by rfl) ⟨166835, by rfl⟩ : syracuseStep 222447 = 333671) B333671
theorem B4286519 : Blo 219811 4286519 := bstep (se 1 (by rfl) ⟨3214889, by rfl⟩ : syracuseStep 4286519 = 6429779) B6429779
theorem B223471 : Blo 219811 223471 := bstep (se 1 (by rfl) ⟨167603, by rfl⟩ : syracuseStep 223471 = 335207) B335207
theorem B1207379 : Blo 219811 1207379 := bstep (se 1 (by rfl) ⟨905534, by rfl⟩ : syracuseStep 1207379 = 1811069) B1811069
theorem B945263 : Blo 219811 945263 := bstep (se 1 (by rfl) ⟨708947, by rfl⟩ : syracuseStep 945263 = 1417895) B1417895
theorem B2387333 : Blo 219811 2387333 := bstep (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) B447625
theorem B6451103 : Blo 219811 6451103 := bstep (se 1 (by rfl) ⟨4838327, by rfl⟩ : syracuseStep 6451103 = 9676655) B9676655
theorem B356729 : Blo 219811 356729 := bstep (se 2 (by rfl) ⟨133773, by rfl⟩ : syracuseStep 356729 = 267547) B267547
theorem B2716699 : Blo 219811 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B2390795 : Blo 219811 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B556409 : Blo 219811 556409 := bstep (se 2 (by rfl) ⟨208653, by rfl⟩ : syracuseStep 556409 = 417307) B417307
theorem B556591 : Blo 219811 556591 := bstep (se 1 (by rfl) ⟨417443, by rfl⟩ : syracuseStep 556591 = 834887) B834887
theorem B3801005 : Blo 219811 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B1015915 : Blo 219811 1015915 := bstep (se 1 (by rfl) ⟨761936, by rfl⟩ : syracuseStep 1015915 = 1523873) B1523873
theorem B1933645 : Blo 219811 1933645 := bstep (se 3 (by rfl) ⟨362558, by rfl⟩ : syracuseStep 1933645 = 725117) B725117
theorem B951277 : Blo 219811 951277 := bstep (se 3 (by rfl) ⟨178364, by rfl⟩ : syracuseStep 951277 = 356729) B356729
theorem B41714941 : Blo 219811 41714941 := bstep (se 3 (by rfl) ⟨7821551, by rfl⟩ : syracuseStep 41714941 = 15643103) B15643103
theorem B330239 : Blo 219811 330239 := bstep (se 1 (by rfl) ⟨247679, by rfl⟩ : syracuseStep 330239 = 495359) B495359
theorem B14879623 : Blo 219811 14879623 := bstep (se 1 (by rfl) ⟨11159717, by rfl⟩ : syracuseStep 14879623 = 22319435) B22319435
theorem B494783 : Blo 219811 494783 := bstep (se 1 (by rfl) ⟨371087, by rfl⟩ : syracuseStep 494783 = 742175) B742175
theorem B331823 : Blo 219811 331823 := bstep (se 1 (by rfl) ⟨248867, by rfl⟩ : syracuseStep 331823 = 497735) B497735
theorem B331847 : Blo 219811 331847 := bstep (se 1 (by rfl) ⟨248885, by rfl⟩ : syracuseStep 331847 = 497771) B497771
theorem B561563 : Blo 219811 561563 := bstep (se 1 (by rfl) ⟨421172, by rfl⟩ : syracuseStep 561563 = 842345) B842345
theorem B3215983 : Blo 219811 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B496511 : Blo 219811 496511 := bstep (se 1 (by rfl) ⟨372383, by rfl⟩ : syracuseStep 496511 = 744767) B744767
theorem B1415231 : Blo 219811 1415231 := bstep (se 1 (by rfl) ⟨1061423, by rfl⟩ : syracuseStep 1415231 = 2122847) B2122847
theorem B2857679 : Blo 219811 2857679 := bstep (se 1 (by rfl) ⟨2143259, by rfl⟩ : syracuseStep 2857679 = 4286519) B4286519
theorem B335159 : Blo 219811 335159 := bstep (se 1 (by rfl) ⟨251369, by rfl⟩ : syracuseStep 335159 = 502739) B502739
theorem B630175 : Blo 219811 630175 := bstep (se 1 (by rfl) ⟨472631, by rfl⟩ : syracuseStep 630175 = 945263) B945263
theorem B4300735 : Blo 219811 4300735 := bstep (se 1 (by rfl) ⟨3225551, by rfl⟩ : syracuseStep 4300735 = 6451103) B6451103
theorem B6366221 : Blo 219811 6366221 := bstep (se 3 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 6366221 = 2387333) B2387333
theorem B370939 : Blo 219811 370939 := bstep (se 1 (by rfl) ⟨278204, by rfl⟩ : syracuseStep 370939 = 556409) B556409
theorem B2534003 : Blo 219811 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B1125089 : Blo 219811 1125089 := bstep (se 2 (by rfl) ⟨421908, by rfl⟩ : syracuseStep 1125089 = 843817) B843817
theorem B503279 : Blo 219811 503279 := bstep (se 1 (by rfl) ⟨377459, by rfl⟩ : syracuseStep 503279 = 754919) B754919
theorem B2862647 : Blo 219811 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B372971 : Blo 219811 372971 := bstep (se 1 (by rfl) ⟨279728, by rfl⟩ : syracuseStep 372971 = 559457) B559457
theorem B471359 : Blo 219811 471359 := bstep (se 1 (by rfl) ⟨353519, by rfl⟩ : syracuseStep 471359 = 707039) B707039
theorem B471367 : Blo 219811 471367 := bstep (se 1 (by rfl) ⟨353525, by rfl⟩ : syracuseStep 471367 = 707051) B707051
theorem B2831071 : Blo 219811 2831071 := bstep (se 1 (by rfl) ⟨2123303, by rfl⟩ : syracuseStep 2831071 = 4246607) B4246607
theorem B373727 : Blo 219811 373727 := bstep (se 1 (by rfl) ⟨280295, by rfl⟩ : syracuseStep 373727 = 560591) B560591
theorem B1685447 : Blo 219811 1685447 := bstep (se 1 (by rfl) ⟨1264085, by rfl⟩ : syracuseStep 1685447 = 2528171) B2528171
theorem B1426045 : Blo 219811 1426045 := bstep (se 3 (by rfl) ⟨267383, by rfl⟩ : syracuseStep 1426045 = 534767) B534767
theorem B3622265 : Blo 219811 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B804919 : Blo 219811 804919 := bstep (se 1 (by rfl) ⟨603689, by rfl⟩ : syracuseStep 804919 = 1207379) B1207379
theorem B1690307 : Blo 219811 1690307 := bstep (se 1 (by rfl) ⟨1267730, by rfl⟩ : syracuseStep 1690307 = 2535461) B2535461
theorem B5362159 : Blo 219811 5362159 := bstep (se 1 (by rfl) ⟨4021619, by rfl⟩ : syracuseStep 5362159 = 8043239) B8043239
theorem B1593863 : Blo 219811 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B742121 : Blo 219811 742121 := bstep (se 2 (by rfl) ⟨278295, by rfl⟩ : syracuseStep 742121 = 556591) B556591
theorem B220143 : Blo 219811 220143 := bstep (se 1 (by rfl) ⟨165107, by rfl⟩ : syracuseStep 220143 = 330215) B330215
theorem B679147 : Blo 219811 679147 := bstep (se 1 (by rfl) ⟨509360, by rfl⟩ : syracuseStep 679147 = 1018721) B1018721
theorem B3169853 : Blo 219811 3169853 := bstep (se 3 (by rfl) ⟨594347, by rfl⟩ : syracuseStep 3169853 = 1188695) B1188695
theorem B220831 : Blo 219811 220831 := bstep (se 1 (by rfl) ⟨165623, by rfl⟩ : syracuseStep 220831 = 331247) B331247
theorem B221211 : Blo 219811 221211 := bstep (se 1 (by rfl) ⟨165908, by rfl⟩ : syracuseStep 221211 = 331817) B331817
theorem B221351 : Blo 219811 221351 := bstep (se 1 (by rfl) ⟨166013, by rfl⟩ : syracuseStep 221351 = 332027) B332027
theorem B222143 : Blo 219811 222143 := bstep (se 1 (by rfl) ⟨166607, by rfl⟩ : syracuseStep 222143 = 333215) B333215
theorem B222847 : Blo 219811 222847 := bstep (se 1 (by rfl) ⟨167135, by rfl⟩ : syracuseStep 222847 = 334271) B334271
theorem B223711 : Blo 219811 223711 := bstep (se 1 (by rfl) ⟨167783, by rfl⟩ : syracuseStep 223711 = 335567) B335567
theorem B354871 : Blo 219811 354871 := bstep (se 1 (by rfl) ⟨266153, by rfl⟩ : syracuseStep 354871 = 532307) B532307
theorem B715559 : Blo 219811 715559 := bstep (se 1 (by rfl) ⟨536669, by rfl⟩ : syracuseStep 715559 = 1073339) B1073339
theorem B945179 : Blo 219811 945179 := bstep (se 1 (by rfl) ⟨708884, by rfl⟩ : syracuseStep 945179 = 1417769) B1417769
theorem B1928377 : Blo 219811 1928377 := bstep (se 2 (by rfl) ⟨723141, by rfl⟩ : syracuseStep 1928377 = 1446283) B1446283
theorem B421051 : Blo 219811 421051 := bstep (se 1 (by rfl) ⟨315788, by rfl⟩ : syracuseStep 421051 = 631577) B631577
theorem B5078699 : Blo 219811 5078699 := bstep (se 1 (by rfl) ⟨3809024, by rfl⟩ : syracuseStep 5078699 = 7618049) B7618049
theorem B1901393 : Blo 219811 1901393 := bstep (se 2 (by rfl) ⟨713022, by rfl⟩ : syracuseStep 1901393 = 1426045) B1426045
theorem B329855 : Blo 219811 329855 := bstep (se 1 (by rfl) ⟨247391, by rfl⟩ : syracuseStep 329855 = 494783) B494783
theorem B494585 : Blo 219811 494585 := bstep (se 2 (by rfl) ⟨185469, by rfl⟩ : syracuseStep 494585 = 370939) B370939
theorem B494747 : Blo 219811 494747 := bstep (se 1 (by rfl) ⟨371060, by rfl⟩ : syracuseStep 494747 = 742121) B742121
theorem B331007 : Blo 219811 331007 := bstep (se 1 (by rfl) ⟨248255, by rfl⟩ : syracuseStep 331007 = 496511) B496511
theorem B561401 : Blo 219811 561401 := bstep (se 2 (by rfl) ⟨210525, by rfl⟩ : syracuseStep 561401 = 421051) B421051
theorem B1905119 : Blo 219811 1905119 := bstep (se 1 (by rfl) ⟨1428839, by rfl⟩ : syracuseStep 1905119 = 2857679) B2857679
theorem B628489 : Blo 219811 628489 := bstep (se 2 (by rfl) ⟨235683, by rfl⟩ : syracuseStep 628489 = 471367) B471367
theorem B7149545 : Blo 219811 7149545 := bstep (se 2 (by rfl) ⟨2681079, by rfl⟩ : syracuseStep 7149545 = 5362159) B5362159
theorem B3774761 : Blo 219811 3774761 := bstep (se 2 (by rfl) ⟨1415535, by rfl⟩ : syracuseStep 3774761 = 2831071) B2831071
theorem B630119 : Blo 219811 630119 := bstep (se 1 (by rfl) ⟨472589, by rfl⟩ : syracuseStep 630119 = 945179) B945179
theorem B1908157 : Blo 219811 1908157 := bstep (se 3 (by rfl) ⟨357779, by rfl⟩ : syracuseStep 1908157 = 715559) B715559
theorem B335519 : Blo 219811 335519 := bstep (se 1 (by rfl) ⟨251639, by rfl⟩ : syracuseStep 335519 = 503279) B503279
theorem B1908431 : Blo 219811 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B1123631 : Blo 219811 1123631 := bstep (se 1 (by rfl) ⟨842723, by rfl⟩ : syracuseStep 1123631 = 1685447) B1685447
theorem B3385799 : Blo 219811 3385799 := bstep (se 1 (by rfl) ⟨2539349, by rfl⟩ : syracuseStep 3385799 = 5078699) B5078699
theorem B1354553 : Blo 219811 1354553 := bstep (se 2 (by rfl) ⟨507957, by rfl⟩ : syracuseStep 1354553 = 1015915) B1015915
theorem B1256957 : Blo 219811 1256957 := bstep (se 3 (by rfl) ⟨235679, by rfl⟩ : syracuseStep 1256957 = 471359) B471359
theorem B55619921 : Blo 219811 55619921 := bstep (se 2 (by rfl) ⟨20857470, by rfl⟩ : syracuseStep 55619921 = 41714941) B41714941
theorem B1126871 : Blo 219811 1126871 := bstep (se 1 (by rfl) ⟨845153, by rfl⟩ : syracuseStep 1126871 = 1690307) B1690307
theorem B374375 : Blo 219811 374375 := bstep (se 1 (by rfl) ⟨280781, by rfl⟩ : syracuseStep 374375 = 561563) B561563
theorem B1062575 : Blo 219811 1062575 := bstep (se 1 (by rfl) ⟨796931, by rfl⟩ : syracuseStep 1062575 = 1593863) B1593863
theorem B19839497 : Blo 219811 19839497 := bstep (se 2 (by rfl) ⟨7439811, by rfl⟩ : syracuseStep 19839497 = 14879623) B14879623
theorem B2113235 : Blo 219811 2113235 := bstep (se 1 (by rfl) ⟨1584926, by rfl⟩ : syracuseStep 2113235 = 3169853) B3169853
theorem B4244147 : Blo 219811 4244147 := bstep (se 1 (by rfl) ⟨3183110, by rfl⟩ : syracuseStep 4244147 = 6366221) B6366221
theorem B3622117 : Blo 219811 3622117 := bstep (se 4 (by rfl) ⟨339573, by rfl⟩ : syracuseStep 3622117 = 679147) B679147
theorem B1689335 : Blo 219811 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B248647 : Blo 219811 248647 := bstep (se 1 (by rfl) ⟨186485, by rfl⟩ : syracuseStep 248647 = 372971) B372971
theorem B249151 : Blo 219811 249151 := bstep (se 1 (by rfl) ⟨186863, by rfl⟩ : syracuseStep 249151 = 373727) B373727
theorem B840233 : Blo 219811 840233 := bstep (se 2 (by rfl) ⟨315087, by rfl⟩ : syracuseStep 840233 = 630175) B630175
theorem B2578193 : Blo 219811 2578193 := bstep (se 2 (by rfl) ⟨966822, by rfl⟩ : syracuseStep 2578193 = 1933645) B1933645
theorem B2414843 : Blo 219811 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B1268369 : Blo 219811 1268369 := bstep (se 2 (by rfl) ⟨475638, by rfl⟩ : syracuseStep 1268369 = 951277) B951277
theorem B220159 : Blo 219811 220159 := bstep (se 1 (by rfl) ⟨165119, by rfl⟩ : syracuseStep 220159 = 330239) B330239
theorem B221215 : Blo 219811 221215 := bstep (se 1 (by rfl) ⟨165911, by rfl⟩ : syracuseStep 221215 = 331823) B331823
theorem B221231 : Blo 219811 221231 := bstep (se 1 (by rfl) ⟨165923, by rfl⟩ : syracuseStep 221231 = 331847) B331847
theorem B1073225 : Blo 219811 1073225 := bstep (se 2 (by rfl) ⟨402459, by rfl⟩ : syracuseStep 1073225 = 804919) B804919
theorem B1892645 : Blo 219811 1892645 := bstep (se 4 (by rfl) ⟨177435, by rfl⟩ : syracuseStep 1892645 = 354871) B354871
theorem B943487 : Blo 219811 943487 := bstep (se 1 (by rfl) ⟨707615, by rfl⟩ : syracuseStep 943487 = 1415231) B1415231
theorem B223439 : Blo 219811 223439 := bstep (se 1 (by rfl) ⟨167579, by rfl⟩ : syracuseStep 223439 = 335159) B335159
theorem B4287977 : Blo 219811 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B10284677 : Blo 219811 10284677 := bstep (se 4 (by rfl) ⟨964188, by rfl⟩ : syracuseStep 10284677 = 1928377) B1928377
theorem B750059 : Blo 219811 750059 := bstep (se 1 (by rfl) ⟨562544, by rfl⟩ : syracuseStep 750059 = 1125089) B1125089
theorem B5734313 : Blo 219811 5734313 := bstep (se 2 (by rfl) ⟨2150367, by rfl⟩ : syracuseStep 5734313 = 4300735) B4300735
theorem B329723 : Blo 219811 329723 := bstep (se 1 (by rfl) ⟨247292, by rfl⟩ : syracuseStep 329723 = 494585) B494585
theorem B329831 : Blo 219811 329831 := bstep (se 1 (by rfl) ⟨247373, by rfl⟩ : syracuseStep 329831 = 494747) B494747
theorem B560155 : Blo 219811 560155 := bstep (se 1 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 560155 = 840233) B840233
theorem B331529 : Blo 219811 331529 := bstep (se 2 (by rfl) ⟨124323, by rfl⟩ : syracuseStep 331529 = 248647) B248647
theorem B1609895 : Blo 219811 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B332201 : Blo 219811 332201 := bstep (se 2 (by rfl) ⟨124575, by rfl⟩ : syracuseStep 332201 = 249151) B249151
theorem B628991 : Blo 219811 628991 := bstep (se 1 (by rfl) ⟨471743, by rfl⟩ : syracuseStep 628991 = 943487) B943487
theorem B2858651 : Blo 219811 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B6856451 : Blo 219811 6856451 := bstep (se 1 (by rfl) ⟨5142338, by rfl⟩ : syracuseStep 6856451 = 10284677) B10284677
theorem B500039 : Blo 219811 500039 := bstep (se 1 (by rfl) ⟨375029, by rfl⟩ : syracuseStep 500039 = 750059) B750059
theorem B2829431 : Blo 219811 2829431 := bstep (se 1 (by rfl) ⟨2122073, by rfl⟩ : syracuseStep 2829431 = 4244147) B4244147
theorem B1126223 : Blo 219811 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B4829489 : Blo 219811 4829489 := bstep (se 2 (by rfl) ⟨1811058, by rfl⟩ : syracuseStep 4829489 = 3622117) B3622117
theorem B374267 : Blo 219811 374267 := bstep (se 1 (by rfl) ⟨280700, by rfl⟩ : syracuseStep 374267 = 561401) B561401
theorem B1718795 : Blo 219811 1718795 := bstep (se 1 (by rfl) ⟨1289096, by rfl⟩ : syracuseStep 1718795 = 2578193) B2578193
theorem B4766363 : Blo 219811 4766363 := bstep (se 1 (by rfl) ⟨3574772, by rfl⟩ : syracuseStep 4766363 = 7149545) B7149545
theorem B1261763 : Blo 219811 1261763 := bstep (se 1 (by rfl) ⟨946322, by rfl⟩ : syracuseStep 1261763 = 1892645) B1892645
theorem B52905325 : Blo 219811 52905325 := bstep (se 3 (by rfl) ⟨9919748, by rfl⟩ : syracuseStep 52905325 = 19839497) B19839497
theorem B903035 : Blo 219811 903035 := bstep (se 1 (by rfl) ⟨677276, by rfl⟩ : syracuseStep 903035 = 1354553) B1354553
theorem B837971 : Blo 219811 837971 := bstep (se 1 (by rfl) ⟨628478, by rfl⟩ : syracuseStep 837971 = 1256957) B1256957
theorem B837985 : Blo 219811 837985 := bstep (se 2 (by rfl) ⟨314244, by rfl⟩ : syracuseStep 837985 = 628489) B628489
theorem B37079947 : Blo 219811 37079947 := bstep (se 1 (by rfl) ⟨27809960, by rfl⟩ : syracuseStep 37079947 = 55619921) B55619921
theorem B249583 : Blo 219811 249583 := bstep (se 1 (by rfl) ⟨187187, by rfl⟩ : syracuseStep 249583 = 374375) B374375
theorem B708383 : Blo 219811 708383 := bstep (se 1 (by rfl) ⟨531287, by rfl⟩ : syracuseStep 708383 = 1062575) B1062575
theorem B2544209 : Blo 219811 2544209 := bstep (se 2 (by rfl) ⟨954078, by rfl⟩ : syracuseStep 2544209 = 1908157) B1908157
theorem B3822875 : Blo 219811 3822875 := bstep (se 1 (by rfl) ⟨2867156, by rfl⟩ : syracuseStep 3822875 = 5734313) B5734313
theorem B1267595 : Blo 219811 1267595 := bstep (se 1 (by rfl) ⟨950696, by rfl⟩ : syracuseStep 1267595 = 1901393) B1901393
theorem B219903 : Blo 219811 219903 := bstep (se 1 (by rfl) ⟨164927, by rfl⟩ : syracuseStep 219903 = 329855) B329855
theorem B220671 : Blo 219811 220671 := bstep (se 1 (by rfl) ⟨165503, by rfl⟩ : syracuseStep 220671 = 331007) B331007
theorem B1270079 : Blo 219811 1270079 := bstep (se 1 (by rfl) ⟨952559, by rfl⟩ : syracuseStep 1270079 = 1905119) B1905119
theorem B2516507 : Blo 219811 2516507 := bstep (se 1 (by rfl) ⟨1887380, by rfl⟩ : syracuseStep 2516507 = 3774761) B3774761
theorem B845579 : Blo 219811 845579 := bstep (se 1 (by rfl) ⟨634184, by rfl⟩ : syracuseStep 845579 = 1268369) B1268369
theorem B420079 : Blo 219811 420079 := bstep (se 1 (by rfl) ⟨315059, by rfl⟩ : syracuseStep 420079 = 630119) B630119
theorem B223679 : Blo 219811 223679 := bstep (se 1 (by rfl) ⟨167759, by rfl⟩ : syracuseStep 223679 = 335519) B335519
theorem B1272287 : Blo 219811 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B715483 : Blo 219811 715483 := bstep (se 1 (by rfl) ⟨536612, by rfl⟩ : syracuseStep 715483 = 1073225) B1073225
theorem B749087 : Blo 219811 749087 := bstep (se 1 (by rfl) ⟨561815, by rfl⟩ : syracuseStep 749087 = 1123631) B1123631
theorem B2257199 : Blo 219811 2257199 := bstep (se 1 (by rfl) ⟨1692899, by rfl⟩ : syracuseStep 2257199 = 3385799) B3385799
theorem B751247 : Blo 219811 751247 := bstep (se 1 (by rfl) ⟨563435, by rfl⟩ : syracuseStep 751247 = 1126871) B1126871
theorem B1408823 : Blo 219811 1408823 := bstep (se 1 (by rfl) ⟨1056617, by rfl⟩ : syracuseStep 1408823 = 2113235) B2113235
theorem B558647 : Blo 219811 558647 := bstep (se 1 (by rfl) ⟨418985, by rfl⟩ : syracuseStep 558647 = 837971) B837971
theorem B560105 : Blo 219811 560105 := bstep (se 2 (by rfl) ⟨210039, by rfl⟩ : syracuseStep 560105 = 420079) B420079
theorem B1117313 : Blo 219811 1117313 := bstep (se 2 (by rfl) ⟨418992, by rfl⟩ : syracuseStep 1117313 = 837985) B837985
theorem B953977 : Blo 219811 953977 := bstep (se 2 (by rfl) ⟨357741, by rfl⟩ : syracuseStep 953977 = 715483) B715483
theorem B197759717 : Blo 219811 197759717 := bstep (se 4 (by rfl) ⟨18539973, by rfl⟩ : syracuseStep 197759717 = 37079947) B37079947
theorem B332777 : Blo 219811 332777 := bstep (se 2 (by rfl) ⟨124791, by rfl⟩ : syracuseStep 332777 = 249583) B249583
theorem B1905767 : Blo 219811 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B333359 : Blo 219811 333359 := bstep (se 1 (by rfl) ⟨250019, by rfl⟩ : syracuseStep 333359 = 500039) B500039
theorem B1677671 : Blo 219811 1677671 := bstep (se 1 (by rfl) ⟨1258253, by rfl⟩ : syracuseStep 1677671 = 2516507) B2516507
theorem B563719 : Blo 219811 563719 := bstep (se 1 (by rfl) ⟨422789, by rfl⟩ : syracuseStep 563719 = 845579) B845579
theorem B499391 : Blo 219811 499391 := bstep (se 1 (by rfl) ⟨374543, by rfl⟩ : syracuseStep 499391 = 749087) B749087
theorem B3219659 : Blo 219811 3219659 := bstep (se 1 (by rfl) ⟨2414744, by rfl⟩ : syracuseStep 3219659 = 4829489) B4829489
theorem B500831 : Blo 219811 500831 := bstep (se 1 (by rfl) ⟨375623, by rfl⟩ : syracuseStep 500831 = 751247) B751247
theorem B2408093 : Blo 219811 2408093 := bstep (se 3 (by rfl) ⟨451517, by rfl⟩ : syracuseStep 2408093 = 903035) B903035
theorem B4570967 : Blo 219811 4570967 := bstep (se 1 (by rfl) ⟨3428225, by rfl⟩ : syracuseStep 4570967 = 6856451) B6856451
theorem B1886287 : Blo 219811 1886287 := bstep (se 1 (by rfl) ⟨1414715, by rfl⟩ : syracuseStep 1886287 = 2829431) B2829431
theorem B249511 : Blo 219811 249511 := bstep (se 1 (by rfl) ⟨187133, by rfl⟩ : syracuseStep 249511 = 374267) B374267
theorem B1889021 : Blo 219811 1889021 := bstep (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) B708383
theorem B939215 : Blo 219811 939215 := bstep (se 1 (by rfl) ⟨704411, by rfl⟩ : syracuseStep 939215 = 1408823) B1408823
theorem B841175 : Blo 219811 841175 := bstep (se 1 (by rfl) ⟨630881, by rfl⟩ : syracuseStep 841175 = 1261763) B1261763
theorem B219815 : Blo 219811 219815 := bstep (se 1 (by rfl) ⟨164861, by rfl⟩ : syracuseStep 219815 = 329723) B329723
theorem B219887 : Blo 219811 219887 := bstep (se 1 (by rfl) ⟨164915, by rfl⟩ : syracuseStep 219887 = 329831) B329831
theorem B70540433 : Blo 219811 70540433 := bstep (se 2 (by rfl) ⟨26452662, by rfl⟩ : syracuseStep 70540433 = 52905325) B52905325
theorem B221019 : Blo 219811 221019 := bstep (se 1 (by rfl) ⟨165764, by rfl⟩ : syracuseStep 221019 = 331529) B331529
theorem B1073263 : Blo 219811 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B221467 : Blo 219811 221467 := bstep (se 1 (by rfl) ⟨166100, by rfl⟩ : syracuseStep 221467 = 332201) B332201
theorem B1696139 : Blo 219811 1696139 := bstep (se 1 (by rfl) ⟨1272104, by rfl⟩ : syracuseStep 1696139 = 2544209) B2544209
theorem B2548583 : Blo 219811 2548583 := bstep (se 1 (by rfl) ⟨1911437, by rfl⟩ : syracuseStep 2548583 = 3822875) B3822875
theorem B845063 : Blo 219811 845063 := bstep (se 1 (by rfl) ⟨633797, by rfl⟩ : syracuseStep 845063 = 1267595) B1267595
theorem B746873 : Blo 219811 746873 := bstep (se 2 (by rfl) ⟨280077, by rfl⟩ : syracuseStep 746873 = 560155) B560155
theorem B419327 : Blo 219811 419327 := bstep (se 1 (by rfl) ⟨314495, by rfl⟩ : syracuseStep 419327 = 628991) B628991
theorem B846719 : Blo 219811 846719 := bstep (se 1 (by rfl) ⟨635039, by rfl⟩ : syracuseStep 846719 = 1270079) B1270079
theorem B848191 : Blo 219811 848191 := bstep (se 1 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 848191 = 1272287) B1272287
theorem B750815 : Blo 219811 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B1504799 : Blo 219811 1504799 := bstep (se 1 (by rfl) ⟨1128599, by rfl⟩ : syracuseStep 1504799 = 2257199) B2257199
theorem B1145863 : Blo 219811 1145863 := bstep (se 1 (by rfl) ⟨859397, by rfl⟩ : syracuseStep 1145863 = 1718795) B1718795
theorem B3177575 : Blo 219811 3177575 := bstep (se 1 (by rfl) ⟨2383181, by rfl⟩ : syracuseStep 3177575 = 4766363) B4766363
theorem B626143 : Blo 219811 626143 := bstep (se 1 (by rfl) ⟨469607, by rfl⟩ : syracuseStep 626143 = 939215) B939215
theorem B560783 : Blo 219811 560783 := bstep (se 1 (by rfl) ⟨420587, by rfl⟩ : syracuseStep 560783 = 841175) B841175
theorem B1118447 : Blo 219811 1118447 := bstep (se 1 (by rfl) ⟨838835, by rfl⟩ : syracuseStep 1118447 = 1677671) B1677671
theorem B47026955 : Blo 219811 47026955 := bstep (se 1 (by rfl) ⟨35270216, by rfl⟩ : syracuseStep 47026955 = 70540433) B70540433
theorem B332681 : Blo 219811 332681 := bstep (se 2 (by rfl) ⟨124755, by rfl⟩ : syracuseStep 332681 = 249511) B249511
theorem B332927 : Blo 219811 332927 := bstep (se 1 (by rfl) ⟨249695, by rfl⟩ : syracuseStep 332927 = 499391) B499391
theorem B333887 : Blo 219811 333887 := bstep (se 1 (by rfl) ⟨250415, by rfl⟩ : syracuseStep 333887 = 500831) B500831
theorem B563375 : Blo 219811 563375 := bstep (se 1 (by rfl) ⟨422531, by rfl⟩ : syracuseStep 563375 = 845063) B845063
theorem B497915 : Blo 219811 497915 := bstep (se 1 (by rfl) ⟨373436, by rfl⟩ : syracuseStep 497915 = 746873) B746873
theorem B564479 : Blo 219811 564479 := bstep (se 1 (by rfl) ⟨423359, by rfl⟩ : syracuseStep 564479 = 846719) B846719
theorem B500543 : Blo 219811 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B372431 : Blo 219811 372431 := bstep (se 1 (by rfl) ⟨279323, by rfl⟩ : syracuseStep 372431 = 558647) B558647
theorem B373403 : Blo 219811 373403 := bstep (se 1 (by rfl) ⟨280052, by rfl⟩ : syracuseStep 373403 = 560105) B560105
theorem B131839811 : Blo 219811 131839811 := bstep (se 1 (by rfl) ⟨98879858, by rfl⟩ : syracuseStep 131839811 = 197759717) B197759717
theorem B1259347 : Blo 219811 1259347 := bstep (se 1 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 1259347 = 1889021) B1889021
theorem B2146439 : Blo 219811 2146439 := bstep (se 1 (by rfl) ⟨1609829, by rfl⟩ : syracuseStep 2146439 = 3219659) B3219659
theorem B1130759 : Blo 219811 1130759 := bstep (se 1 (by rfl) ⟨848069, by rfl⟩ : syracuseStep 1130759 = 1696139) B1696139
theorem B1130921 : Blo 219811 1130921 := bstep (se 2 (by rfl) ⟨424095, by rfl⟩ : syracuseStep 1130921 = 848191) B848191
theorem B279551 : Blo 219811 279551 := bstep (se 1 (by rfl) ⟨209663, by rfl⟩ : syracuseStep 279551 = 419327) B419327
theorem B1003199 : Blo 219811 1003199 := bstep (se 1 (by rfl) ⟨752399, by rfl⟩ : syracuseStep 1003199 = 1504799) B1504799
theorem B1527817 : Blo 219811 1527817 := bstep (se 2 (by rfl) ⟨572931, by rfl⟩ : syracuseStep 1527817 = 1145863) B1145863
theorem B2118383 : Blo 219811 2118383 := bstep (se 1 (by rfl) ⟨1588787, by rfl⟩ : syracuseStep 2118383 = 3177575) B3177575
theorem B1431017 : Blo 219811 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B744875 : Blo 219811 744875 := bstep (se 1 (by rfl) ⟨558656, by rfl⟩ : syracuseStep 744875 = 1117313) B1117313
theorem B2515049 : Blo 219811 2515049 := bstep (se 2 (by rfl) ⟨943143, by rfl⟩ : syracuseStep 2515049 = 1886287) B1886287
theorem B221851 : Blo 219811 221851 := bstep (se 1 (by rfl) ⟨166388, by rfl⟩ : syracuseStep 221851 = 332777) B332777
theorem B1270511 : Blo 219811 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B222239 : Blo 219811 222239 := bstep (se 1 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 222239 = 333359) B333359
theorem B1271969 : Blo 219811 1271969 := bstep (se 2 (by rfl) ⟨476988, by rfl⟩ : syracuseStep 1271969 = 953977) B953977
theorem B1699055 : Blo 219811 1699055 := bstep (se 1 (by rfl) ⟨1274291, by rfl⟩ : syracuseStep 1699055 = 2548583) B2548583
theorem B751625 : Blo 219811 751625 := bstep (se 2 (by rfl) ⟨281859, by rfl⟩ : syracuseStep 751625 = 563719) B563719
theorem B1605395 : Blo 219811 1605395 := bstep (se 1 (by rfl) ⟨1204046, by rfl⟩ : syracuseStep 1605395 = 2408093) B2408093
theorem B3047311 : Blo 219811 3047311 := bstep (se 1 (by rfl) ⟨2285483, by rfl⟩ : syracuseStep 3047311 = 4570967) B4570967
theorem B753839 : Blo 219811 753839 := bstep (se 1 (by rfl) ⟨565379, by rfl⟩ : syracuseStep 753839 = 1130759) B1130759
theorem B753947 : Blo 219811 753947 := bstep (se 1 (by rfl) ⟨565460, by rfl⟩ : syracuseStep 753947 = 1130921) B1130921
theorem B1412255 : Blo 219811 1412255 := bstep (se 1 (by rfl) ⟨1059191, by rfl⟩ : syracuseStep 1412255 = 2118383) B2118383
theorem B954011 : Blo 219811 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B331943 : Blo 219811 331943 := bstep (se 1 (by rfl) ⟨248957, by rfl⟩ : syracuseStep 331943 = 497915) B497915
theorem B496583 : Blo 219811 496583 := bstep (se 1 (by rfl) ⟨372437, by rfl⟩ : syracuseStep 496583 = 744875) B744875
theorem B2037089 : Blo 219811 2037089 := bstep (se 2 (by rfl) ⟨763908, by rfl⟩ : syracuseStep 2037089 = 1527817) B1527817
theorem B1676699 : Blo 219811 1676699 := bstep (se 1 (by rfl) ⟨1257524, by rfl⟩ : syracuseStep 1676699 = 2515049) B2515049
theorem B333695 : Blo 219811 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B1679129 : Blo 219811 1679129 := bstep (se 2 (by rfl) ⟨629673, by rfl⟩ : syracuseStep 1679129 = 1259347) B1259347
theorem B87893207 : Blo 219811 87893207 := bstep (se 1 (by rfl) ⟨65919905, by rfl⟩ : syracuseStep 87893207 = 131839811) B131839811
theorem B501083 : Blo 219811 501083 := bstep (se 1 (by rfl) ⟨375812, by rfl⟩ : syracuseStep 501083 = 751625) B751625
theorem B373855 : Blo 219811 373855 := bstep (se 1 (by rfl) ⟨280391, by rfl⟩ : syracuseStep 373855 = 560783) B560783
theorem B375583 : Blo 219811 375583 := bstep (se 1 (by rfl) ⟨281687, by rfl⟩ : syracuseStep 375583 = 563375) B563375
theorem B834857 : Blo 219811 834857 := bstep (se 2 (by rfl) ⟨313071, by rfl⟩ : syracuseStep 834857 = 626143) B626143
theorem B376319 : Blo 219811 376319 := bstep (se 1 (by rfl) ⟨282239, by rfl⟩ : syracuseStep 376319 = 564479) B564479
theorem B1132703 : Blo 219811 1132703 := bstep (se 1 (by rfl) ⟨849527, by rfl⟩ : syracuseStep 1132703 = 1699055) B1699055
theorem B248287 : Blo 219811 248287 := bstep (se 1 (by rfl) ⟨186215, by rfl⟩ : syracuseStep 248287 = 372431) B372431
theorem B248935 : Blo 219811 248935 := bstep (se 1 (by rfl) ⟨186701, by rfl⟩ : syracuseStep 248935 = 373403) B373403
theorem B2675197 : Blo 219811 2675197 := bstep (se 3 (by rfl) ⟨501599, by rfl⟩ : syracuseStep 2675197 = 1003199) B1003199
theorem B1070263 : Blo 219811 1070263 := bstep (se 1 (by rfl) ⟨802697, by rfl⟩ : syracuseStep 1070263 = 1605395) B1605395
theorem B1430959 : Blo 219811 1430959 := bstep (se 1 (by rfl) ⟨1073219, by rfl⟩ : syracuseStep 1430959 = 2146439) B2146439
theorem B745469 : Blo 219811 745469 := bstep (se 3 (by rfl) ⟨139775, by rfl⟩ : syracuseStep 745469 = 279551) B279551
theorem B745631 : Blo 219811 745631 := bstep (se 1 (by rfl) ⟨559223, by rfl⟩ : syracuseStep 745631 = 1118447) B1118447
theorem B31351303 : Blo 219811 31351303 := bstep (se 1 (by rfl) ⟨23513477, by rfl⟩ : syracuseStep 31351303 = 47026955) B47026955
theorem B221787 : Blo 219811 221787 := bstep (se 1 (by rfl) ⟨166340, by rfl⟩ : syracuseStep 221787 = 332681) B332681
theorem B221951 : Blo 219811 221951 := bstep (se 1 (by rfl) ⟨166463, by rfl⟩ : syracuseStep 221951 = 332927) B332927
theorem B222591 : Blo 219811 222591 := bstep (se 1 (by rfl) ⟨166943, by rfl⟩ : syracuseStep 222591 = 333887) B333887
theorem B847007 : Blo 219811 847007 := bstep (se 1 (by rfl) ⟨635255, by rfl⟩ : syracuseStep 847007 = 1270511) B1270511
theorem B847979 : Blo 219811 847979 := bstep (se 1 (by rfl) ⟨635984, by rfl⟩ : syracuseStep 847979 = 1271969) B1271969
theorem B4063081 : Blo 219811 4063081 := bstep (se 2 (by rfl) ⟨1523655, by rfl⟩ : syracuseStep 4063081 = 3047311) B3047311
theorem B755135 : Blo 219811 755135 := bstep (se 1 (by rfl) ⟨566351, by rfl⟩ : syracuseStep 755135 = 1132703) B1132703
theorem B331049 : Blo 219811 331049 := bstep (se 2 (by rfl) ⟨124143, by rfl⟩ : syracuseStep 331049 = 248287) B248287
theorem B331055 : Blo 219811 331055 := bstep (se 1 (by rfl) ⟨248291, by rfl⟩ : syracuseStep 331055 = 496583) B496583
theorem B1117799 : Blo 219811 1117799 := bstep (se 1 (by rfl) ⟨838349, by rfl⟩ : syracuseStep 1117799 = 1676699) B1676699
theorem B331913 : Blo 219811 331913 := bstep (se 2 (by rfl) ⟨124467, by rfl⟩ : syracuseStep 331913 = 248935) B248935
theorem B1119419 : Blo 219811 1119419 := bstep (se 1 (by rfl) ⟨839564, by rfl⟩ : syracuseStep 1119419 = 1679129) B1679129
theorem B496979 : Blo 219811 496979 := bstep (se 1 (by rfl) ⟨372734, by rfl⟩ : syracuseStep 496979 = 745469) B745469
theorem B497087 : Blo 219811 497087 := bstep (se 1 (by rfl) ⟨372815, by rfl⟩ : syracuseStep 497087 = 745631) B745631
theorem B58595471 : Blo 219811 58595471 := bstep (se 1 (by rfl) ⟨43946603, by rfl⟩ : syracuseStep 58595471 = 87893207) B87893207
theorem B334055 : Blo 219811 334055 := bstep (se 1 (by rfl) ⟨250541, by rfl⟩ : syracuseStep 334055 = 501083) B501083
theorem B5708069 : Blo 219811 5708069 := bstep (se 4 (by rfl) ⟨535131, by rfl⟩ : syracuseStep 5708069 = 1070263) B1070263
theorem B498473 : Blo 219811 498473 := bstep (se 2 (by rfl) ⟨186927, by rfl⟩ : syracuseStep 498473 = 373855) B373855
theorem B1907945 : Blo 219811 1907945 := bstep (se 2 (by rfl) ⟨715479, by rfl⟩ : syracuseStep 1907945 = 1430959) B1430959
theorem B564671 : Blo 219811 564671 := bstep (se 1 (by rfl) ⟨423503, by rfl⟩ : syracuseStep 564671 = 847007) B847007
theorem B565319 : Blo 219811 565319 := bstep (se 1 (by rfl) ⟨423989, by rfl⟩ : syracuseStep 565319 = 847979) B847979
theorem B500777 : Blo 219811 500777 := bstep (se 2 (by rfl) ⟨187791, by rfl⟩ : syracuseStep 500777 = 375583) B375583
theorem B5417441 : Blo 219811 5417441 := bstep (se 2 (by rfl) ⟨2031540, by rfl⟩ : syracuseStep 5417441 = 4063081) B4063081
theorem B502559 : Blo 219811 502559 := bstep (se 1 (by rfl) ⟨376919, by rfl⟩ : syracuseStep 502559 = 753839) B753839
theorem B502631 : Blo 219811 502631 := bstep (se 1 (by rfl) ⟨376973, by rfl⟩ : syracuseStep 502631 = 753947) B753947
theorem B636007 : Blo 219811 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B1358059 : Blo 219811 1358059 := bstep (se 1 (by rfl) ⟨1018544, by rfl⟩ : syracuseStep 1358059 = 2037089) B2037089
theorem B250879 : Blo 219811 250879 := bstep (se 1 (by rfl) ⟨188159, by rfl⟩ : syracuseStep 250879 = 376319) B376319
theorem B167206949 : Blo 219811 167206949 := bstep (se 4 (by rfl) ⟨15675651, by rfl⟩ : syracuseStep 167206949 = 31351303) B31351303
theorem B221295 : Blo 219811 221295 := bstep (se 1 (by rfl) ⟨165971, by rfl⟩ : syracuseStep 221295 = 331943) B331943
theorem B222463 : Blo 219811 222463 := bstep (se 1 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 222463 = 333695) B333695
theorem B3566929 : Blo 219811 3566929 := bstep (se 2 (by rfl) ⟨1337598, by rfl⟩ : syracuseStep 3566929 = 2675197) B2675197
theorem B3766013 : Blo 219811 3766013 := bstep (se 3 (by rfl) ⟨706127, by rfl⟩ : syracuseStep 3766013 = 1412255) B1412255
theorem B556571 : Blo 219811 556571 := bstep (se 1 (by rfl) ⟨417428, by rfl⟩ : syracuseStep 556571 = 834857) B834857
theorem B331319 : Blo 219811 331319 := bstep (se 1 (by rfl) ⟨248489, by rfl⟩ : syracuseStep 331319 = 496979) B496979
theorem B331391 : Blo 219811 331391 := bstep (se 1 (by rfl) ⟨248543, by rfl⟩ : syracuseStep 331391 = 497087) B497087
theorem B39063647 : Blo 219811 39063647 := bstep (se 1 (by rfl) ⟨29297735, by rfl⟩ : syracuseStep 39063647 = 58595471) B58595471
theorem B3805379 : Blo 219811 3805379 := bstep (se 1 (by rfl) ⟨2854034, by rfl⟩ : syracuseStep 3805379 = 5708069) B5708069
theorem B4755905 : Blo 219811 4755905 := bstep (se 2 (by rfl) ⟨1783464, by rfl⟩ : syracuseStep 4755905 = 3566929) B3566929
theorem B332315 : Blo 219811 332315 := bstep (se 1 (by rfl) ⟨249236, by rfl⟩ : syracuseStep 332315 = 498473) B498473
theorem B333851 : Blo 219811 333851 := bstep (se 1 (by rfl) ⟨250388, by rfl⟩ : syracuseStep 333851 = 500777) B500777
theorem B334505 : Blo 219811 334505 := bstep (se 2 (by rfl) ⟨125439, by rfl⟩ : syracuseStep 334505 = 250879) B250879
theorem B3611627 : Blo 219811 3611627 := bstep (se 1 (by rfl) ⟨2708720, by rfl⟩ : syracuseStep 3611627 = 5417441) B5417441
theorem B335039 : Blo 219811 335039 := bstep (se 1 (by rfl) ⟨251279, by rfl⟩ : syracuseStep 335039 = 502559) B502559
theorem B335087 : Blo 219811 335087 := bstep (se 1 (by rfl) ⟨251315, by rfl⟩ : syracuseStep 335087 = 502631) B502631
theorem B1810745 : Blo 219811 1810745 := bstep (se 2 (by rfl) ⟨679029, by rfl⟩ : syracuseStep 1810745 = 1358059) B1358059
theorem B371047 : Blo 219811 371047 := bstep (se 1 (by rfl) ⟨278285, by rfl⟩ : syracuseStep 371047 = 556571) B556571
theorem B503423 : Blo 219811 503423 := bstep (se 1 (by rfl) ⟨377567, by rfl⟩ : syracuseStep 503423 = 755135) B755135
theorem B376447 : Blo 219811 376447 := bstep (se 1 (by rfl) ⟨282335, by rfl⟩ : syracuseStep 376447 = 564671) B564671
theorem B376879 : Blo 219811 376879 := bstep (se 1 (by rfl) ⟨282659, by rfl⟩ : syracuseStep 376879 = 565319) B565319
theorem B2510675 : Blo 219811 2510675 := bstep (se 1 (by rfl) ⟨1883006, by rfl⟩ : syracuseStep 2510675 = 3766013) B3766013
theorem B220699 : Blo 219811 220699 := bstep (se 1 (by rfl) ⟨165524, by rfl⟩ : syracuseStep 220699 = 331049) B331049
theorem B220703 : Blo 219811 220703 := bstep (se 1 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 220703 = 331055) B331055
theorem B745199 : Blo 219811 745199 := bstep (se 1 (by rfl) ⟨558899, by rfl⟩ : syracuseStep 745199 = 1117799) B1117799
theorem B221275 : Blo 219811 221275 := bstep (se 1 (by rfl) ⟨165956, by rfl⟩ : syracuseStep 221275 = 331913) B331913
theorem B746279 : Blo 219811 746279 := bstep (se 1 (by rfl) ⟨559709, by rfl⟩ : syracuseStep 746279 = 1119419) B1119419
theorem B222703 : Blo 219811 222703 := bstep (se 1 (by rfl) ⟨167027, by rfl⟩ : syracuseStep 222703 = 334055) B334055
theorem B1271963 : Blo 219811 1271963 := bstep (se 1 (by rfl) ⟨953972, by rfl⟩ : syracuseStep 1271963 = 1907945) B1907945
theorem B111471299 : Blo 219811 111471299 := bstep (se 1 (by rfl) ⟨83603474, by rfl⟩ : syracuseStep 111471299 = 167206949) B167206949
theorem B848009 : Blo 219811 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B1673783 : Blo 219811 1673783 := bstep (se 1 (by rfl) ⟨1255337, by rfl⟩ : syracuseStep 1673783 = 2510675) B2510675
theorem B494729 : Blo 219811 494729 := bstep (se 2 (by rfl) ⟨185523, by rfl⟩ : syracuseStep 494729 = 371047) B371047
theorem B496799 : Blo 219811 496799 := bstep (se 1 (by rfl) ⟨372599, by rfl⟩ : syracuseStep 496799 = 745199) B745199
theorem B497519 : Blo 219811 497519 := bstep (se 1 (by rfl) ⟨373139, by rfl⟩ : syracuseStep 497519 = 746279) B746279
theorem B335615 : Blo 219811 335615 := bstep (se 1 (by rfl) ⟨251711, by rfl⟩ : syracuseStep 335615 = 503423) B503423
theorem B565339 : Blo 219811 565339 := bstep (se 1 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 565339 = 848009) B848009
theorem B501929 : Blo 219811 501929 := bstep (se 2 (by rfl) ⟨188223, by rfl⟩ : syracuseStep 501929 = 376447) B376447
theorem B502505 : Blo 219811 502505 := bstep (se 2 (by rfl) ⟨188439, by rfl⟩ : syracuseStep 502505 = 376879) B376879
theorem B2536919 : Blo 219811 2536919 := bstep (se 1 (by rfl) ⟨1902689, by rfl⟩ : syracuseStep 2536919 = 3805379) B3805379
theorem B2407751 : Blo 219811 2407751 := bstep (se 1 (by rfl) ⟨1805813, by rfl⟩ : syracuseStep 2407751 = 3611627) B3611627
theorem B3391901 : Blo 219811 3391901 := bstep (se 3 (by rfl) ⟨635981, by rfl⟩ : syracuseStep 3391901 = 1271963) B1271963
theorem B220879 : Blo 219811 220879 := bstep (se 1 (by rfl) ⟨165659, by rfl⟩ : syracuseStep 220879 = 331319) B331319
theorem B220927 : Blo 219811 220927 := bstep (se 1 (by rfl) ⟨165695, by rfl⟩ : syracuseStep 220927 = 331391) B331391
theorem B26042431 : Blo 219811 26042431 := bstep (se 1 (by rfl) ⟨19531823, by rfl⟩ : syracuseStep 26042431 = 39063647) B39063647
theorem B3170603 : Blo 219811 3170603 := bstep (se 1 (by rfl) ⟨2377952, by rfl⟩ : syracuseStep 3170603 = 4755905) B4755905
theorem B221543 : Blo 219811 221543 := bstep (se 1 (by rfl) ⟨166157, by rfl⟩ : syracuseStep 221543 = 332315) B332315
theorem B222567 : Blo 219811 222567 := bstep (se 1 (by rfl) ⟨166925, by rfl⟩ : syracuseStep 222567 = 333851) B333851
theorem B223003 : Blo 219811 223003 := bstep (se 1 (by rfl) ⟨167252, by rfl⟩ : syracuseStep 223003 = 334505) B334505
theorem B223359 : Blo 219811 223359 := bstep (se 1 (by rfl) ⟨167519, by rfl⟩ : syracuseStep 223359 = 335039) B335039
theorem B223391 : Blo 219811 223391 := bstep (se 1 (by rfl) ⟨167543, by rfl⟩ : syracuseStep 223391 = 335087) B335087
theorem B1207163 : Blo 219811 1207163 := bstep (se 1 (by rfl) ⟨905372, by rfl⟩ : syracuseStep 1207163 = 1810745) B1810745
theorem B74314199 : Blo 219811 74314199 := bstep (se 1 (by rfl) ⟨55735649, by rfl⟩ : syracuseStep 74314199 = 111471299) B111471299
theorem B753785 : Blo 219811 753785 := bstep (se 2 (by rfl) ⟨282669, by rfl⟩ : syracuseStep 753785 = 565339) B565339
theorem B2261267 : Blo 219811 2261267 := bstep (se 1 (by rfl) ⟨1695950, by rfl⟩ : syracuseStep 2261267 = 3391901) B3391901
theorem B1115855 : Blo 219811 1115855 := bstep (se 1 (by rfl) ⟨836891, by rfl⟩ : syracuseStep 1115855 = 1673783) B1673783
theorem B329819 : Blo 219811 329819 := bstep (se 1 (by rfl) ⟨247364, by rfl⟩ : syracuseStep 329819 = 494729) B494729
theorem B331199 : Blo 219811 331199 := bstep (se 1 (by rfl) ⟨248399, by rfl⟩ : syracuseStep 331199 = 496799) B496799
theorem B331679 : Blo 219811 331679 := bstep (se 1 (by rfl) ⟨248759, by rfl⟩ : syracuseStep 331679 = 497519) B497519
theorem B334619 : Blo 219811 334619 := bstep (se 1 (by rfl) ⟨250964, by rfl⟩ : syracuseStep 334619 = 501929) B501929
theorem B335003 : Blo 219811 335003 := bstep (se 1 (by rfl) ⟨251252, by rfl⟩ : syracuseStep 335003 = 502505) B502505
theorem B2113735 : Blo 219811 2113735 := bstep (se 1 (by rfl) ⟨1585301, by rfl⟩ : syracuseStep 2113735 = 3170603) B3170603
theorem B804775 : Blo 219811 804775 := bstep (se 1 (by rfl) ⟨603581, by rfl⟩ : syracuseStep 804775 = 1207163) B1207163
theorem B1691279 : Blo 219811 1691279 := bstep (se 1 (by rfl) ⟨1268459, by rfl⟩ : syracuseStep 1691279 = 2536919) B2536919
theorem B34723241 : Blo 219811 34723241 := bstep (se 2 (by rfl) ⟨13021215, by rfl⟩ : syracuseStep 34723241 = 26042431) B26042431
theorem B223743 : Blo 219811 223743 := bstep (se 1 (by rfl) ⟨167807, by rfl⟩ : syracuseStep 223743 = 335615) B335615
theorem B49542799 : Blo 219811 49542799 := bstep (se 1 (by rfl) ⟨37157099, by rfl⟩ : syracuseStep 49542799 = 74314199) B74314199
theorem B1605167 : Blo 219811 1605167 := bstep (se 1 (by rfl) ⟨1203875, by rfl⟩ : syracuseStep 1605167 = 2407751) B2407751
theorem B1507511 : Blo 219811 1507511 := bstep (se 1 (by rfl) ⟨1130633, by rfl⟩ : syracuseStep 1507511 = 2261267) B2261267
theorem B2818313 : Blo 219811 2818313 := bstep (se 2 (by rfl) ⟨1056867, by rfl⟩ : syracuseStep 2818313 = 2113735) B2113735
theorem B502523 : Blo 219811 502523 := bstep (se 1 (by rfl) ⟨376892, by rfl⟩ : syracuseStep 502523 = 753785) B753785
theorem B1127519 : Blo 219811 1127519 := bstep (se 1 (by rfl) ⟨845639, by rfl⟩ : syracuseStep 1127519 = 1691279) B1691279
theorem B23148827 : Blo 219811 23148827 := bstep (se 1 (by rfl) ⟨17361620, by rfl⟩ : syracuseStep 23148827 = 34723241) B34723241
theorem B1070111 : Blo 219811 1070111 := bstep (se 1 (by rfl) ⟨802583, by rfl⟩ : syracuseStep 1070111 = 1605167) B1605167
theorem B743903 : Blo 219811 743903 := bstep (se 1 (by rfl) ⟨557927, by rfl⟩ : syracuseStep 743903 = 1115855) B1115855
theorem B219879 : Blo 219811 219879 := bstep (se 1 (by rfl) ⟨164909, by rfl⟩ : syracuseStep 219879 = 329819) B329819
theorem B220799 : Blo 219811 220799 := bstep (se 1 (by rfl) ⟨165599, by rfl⟩ : syracuseStep 220799 = 331199) B331199
theorem B1073033 : Blo 219811 1073033 := bstep (se 2 (by rfl) ⟨402387, by rfl⟩ : syracuseStep 1073033 = 804775) B804775
theorem B221119 : Blo 219811 221119 := bstep (se 1 (by rfl) ⟨165839, by rfl⟩ : syracuseStep 221119 = 331679) B331679
theorem B223079 : Blo 219811 223079 := bstep (se 1 (by rfl) ⟨167309, by rfl⟩ : syracuseStep 223079 = 334619) B334619
theorem B223335 : Blo 219811 223335 := bstep (se 1 (by rfl) ⟨167501, by rfl⟩ : syracuseStep 223335 = 335003) B335003
theorem B66057065 : Blo 219811 66057065 := bstep (se 2 (by rfl) ⟨24771399, by rfl⟩ : syracuseStep 66057065 = 49542799) B49542799
theorem B495935 : Blo 219811 495935 := bstep (se 1 (by rfl) ⟨371951, by rfl⟩ : syracuseStep 495935 = 743903) B743903
theorem B335015 : Blo 219811 335015 := bstep (se 1 (by rfl) ⟨251261, by rfl⟩ : syracuseStep 335015 = 502523) B502523
theorem B1878875 : Blo 219811 1878875 := bstep (se 1 (by rfl) ⟨1409156, by rfl⟩ : syracuseStep 1878875 = 2818313) B2818313
theorem B1005007 : Blo 219811 1005007 := bstep (se 1 (by rfl) ⟨753755, by rfl⟩ : syracuseStep 1005007 = 1507511) B1507511
theorem B713407 : Blo 219811 713407 := bstep (se 1 (by rfl) ⟨535055, by rfl⟩ : syracuseStep 713407 = 1070111) B1070111
theorem B715355 : Blo 219811 715355 := bstep (se 1 (by rfl) ⟨536516, by rfl⟩ : syracuseStep 715355 = 1073033) B1073033
theorem B44038043 : Blo 219811 44038043 := bstep (se 1 (by rfl) ⟨33028532, by rfl⟩ : syracuseStep 44038043 = 66057065) B66057065
theorem B751679 : Blo 219811 751679 := bstep (se 1 (by rfl) ⟨563759, by rfl⟩ : syracuseStep 751679 = 1127519) B1127519
theorem B15432551 : Blo 219811 15432551 := bstep (se 1 (by rfl) ⟨11574413, by rfl⟩ : syracuseStep 15432551 = 23148827) B23148827
theorem B951209 : Blo 219811 951209 := bstep (se 2 (by rfl) ⟨356703, by rfl⟩ : syracuseStep 951209 = 713407) B713407
theorem B330623 : Blo 219811 330623 := bstep (se 1 (by rfl) ⟨247967, by rfl⟩ : syracuseStep 330623 = 495935) B495935
theorem B1252583 : Blo 219811 1252583 := bstep (se 1 (by rfl) ⟨939437, by rfl⟩ : syracuseStep 1252583 = 1878875) B1878875
theorem B501119 : Blo 219811 501119 := bstep (se 1 (by rfl) ⟨375839, by rfl⟩ : syracuseStep 501119 = 751679) B751679
theorem B476903 : Blo 219811 476903 := bstep (se 1 (by rfl) ⟨357677, by rfl⟩ : syracuseStep 476903 = 715355) B715355
theorem B223343 : Blo 219811 223343 := bstep (se 1 (by rfl) ⟨167507, by rfl⟩ : syracuseStep 223343 = 335015) B335015
theorem B1340009 : Blo 219811 1340009 := bstep (se 2 (by rfl) ⟨502503, by rfl⟩ : syracuseStep 1340009 = 1005007) B1005007
theorem B29358695 : Blo 219811 29358695 := bstep (se 1 (by rfl) ⟨22019021, by rfl⟩ : syracuseStep 29358695 = 44038043) B44038043
theorem B10288367 : Blo 219811 10288367 := bstep (se 1 (by rfl) ⟨7716275, by rfl⟩ : syracuseStep 10288367 = 15432551) B15432551
theorem B334079 : Blo 219811 334079 := bstep (se 1 (by rfl) ⟨250559, by rfl⟩ : syracuseStep 334079 = 501119) B501119
theorem B893339 : Blo 219811 893339 := bstep (se 1 (by rfl) ⟨670004, by rfl⟩ : syracuseStep 893339 = 1340009) B1340009
theorem B19572463 : Blo 219811 19572463 := bstep (se 1 (by rfl) ⟨14679347, by rfl⟩ : syracuseStep 19572463 = 29358695) B29358695
theorem B6858911 : Blo 219811 6858911 := bstep (se 1 (by rfl) ⟨5144183, by rfl⟩ : syracuseStep 6858911 = 10288367) B10288367
theorem B634139 : Blo 219811 634139 := bstep (se 1 (by rfl) ⟨475604, by rfl⟩ : syracuseStep 634139 = 951209) B951209
theorem B835055 : Blo 219811 835055 := bstep (se 1 (by rfl) ⟨626291, by rfl⟩ : syracuseStep 835055 = 1252583) B1252583
theorem B317935 : Blo 219811 317935 := bstep (se 1 (by rfl) ⟨238451, by rfl⟩ : syracuseStep 317935 = 476903) B476903
theorem B220415 : Blo 219811 220415 := bstep (se 1 (by rfl) ⟨165311, by rfl⟩ : syracuseStep 220415 = 330623) B330623
theorem B595559 : Blo 219811 595559 := bstep (se 1 (by rfl) ⟨446669, by rfl⟩ : syracuseStep 595559 = 893339) B893339
theorem B26096617 : Blo 219811 26096617 := bstep (se 2 (by rfl) ⟨9786231, by rfl⟩ : syracuseStep 26096617 = 19572463) B19572463
theorem B4572607 : Blo 219811 4572607 := bstep (se 1 (by rfl) ⟨3429455, by rfl⟩ : syracuseStep 4572607 = 6858911) B6858911
theorem B1695653 : Blo 219811 1695653 := bstep (se 4 (by rfl) ⟨158967, by rfl⟩ : syracuseStep 1695653 = 317935) B317935
theorem B222719 : Blo 219811 222719 := bstep (se 1 (by rfl) ⟨167039, by rfl⟩ : syracuseStep 222719 = 334079) B334079
theorem B422759 : Blo 219811 422759 := bstep (se 1 (by rfl) ⟨317069, by rfl⟩ : syracuseStep 422759 = 634139) B634139
theorem B556703 : Blo 219811 556703 := bstep (se 1 (by rfl) ⟨417527, by rfl⟩ : syracuseStep 556703 = 835055) B835055
theorem B6096809 : Blo 219811 6096809 := bstep (se 2 (by rfl) ⟨2286303, by rfl⟩ : syracuseStep 6096809 = 4572607) B4572607
theorem B371135 : Blo 219811 371135 := bstep (se 1 (by rfl) ⟨278351, by rfl⟩ : syracuseStep 371135 = 556703) B556703
theorem B1127357 : Blo 219811 1127357 := bstep (se 3 (by rfl) ⟨211379, by rfl⟩ : syracuseStep 1127357 = 422759) B422759
theorem B1588157 : Blo 219811 1588157 := bstep (se 3 (by rfl) ⟨297779, by rfl⟩ : syracuseStep 1588157 = 595559) B595559
theorem B1130435 : Blo 219811 1130435 := bstep (se 1 (by rfl) ⟨847826, by rfl⟩ : syracuseStep 1130435 = 1695653) B1695653
theorem B34795489 : Blo 219811 34795489 := bstep (se 2 (by rfl) ⟨13048308, by rfl⟩ : syracuseStep 34795489 = 26096617) B26096617
theorem B16258157 : Blo 219811 16258157 := bstep (se 3 (by rfl) ⟨3048404, by rfl⟩ : syracuseStep 16258157 = 6096809) B6096809
theorem B1058771 : Blo 219811 1058771 := bstep (se 1 (by rfl) ⟨794078, by rfl⟩ : syracuseStep 1058771 = 1588157) B1588157
theorem B247423 : Blo 219811 247423 := bstep (se 1 (by rfl) ⟨185567, by rfl⟩ : syracuseStep 247423 = 371135) B371135
theorem B46393985 : Blo 219811 46393985 := bstep (se 2 (by rfl) ⟨17397744, by rfl⟩ : syracuseStep 46393985 = 34795489) B34795489
theorem B751571 : Blo 219811 751571 := bstep (se 1 (by rfl) ⟨563678, by rfl⟩ : syracuseStep 751571 = 1127357) B1127357
theorem B753623 : Blo 219811 753623 := bstep (se 1 (by rfl) ⟨565217, by rfl⟩ : syracuseStep 753623 = 1130435) B1130435
theorem B329897 : Blo 219811 329897 := bstep (se 2 (by rfl) ⟨123711, by rfl⟩ : syracuseStep 329897 = 247423) B247423
theorem B501047 : Blo 219811 501047 := bstep (se 1 (by rfl) ⟨375785, by rfl⟩ : syracuseStep 501047 = 751571) B751571
theorem B502415 : Blo 219811 502415 := bstep (se 1 (by rfl) ⟨376811, by rfl⟩ : syracuseStep 502415 = 753623) B753623
theorem B705847 : Blo 219811 705847 := bstep (se 1 (by rfl) ⟨529385, by rfl⟩ : syracuseStep 705847 = 1058771) B1058771
theorem B123717293 : Blo 219811 123717293 := bstep (se 3 (by rfl) ⟨23196992, by rfl⟩ : syracuseStep 123717293 = 46393985) B46393985
theorem B10838771 : Blo 219811 10838771 := bstep (se 1 (by rfl) ⟨8129078, by rfl⟩ : syracuseStep 10838771 = 16258157) B16258157
theorem B82478195 : Blo 219811 82478195 := bstep (se 1 (by rfl) ⟨61858646, by rfl⟩ : syracuseStep 82478195 = 123717293) B123717293
theorem B334031 : Blo 219811 334031 := bstep (se 1 (by rfl) ⟨250523, by rfl⟩ : syracuseStep 334031 = 501047) B501047
theorem B334943 : Blo 219811 334943 := bstep (se 1 (by rfl) ⟨251207, by rfl⟩ : syracuseStep 334943 = 502415) B502415
theorem B7225847 : Blo 219811 7225847 := bstep (se 1 (by rfl) ⟨5419385, by rfl⟩ : syracuseStep 7225847 = 10838771) B10838771
theorem B219931 : Blo 219811 219931 := bstep (se 1 (by rfl) ⟨164948, by rfl⟩ : syracuseStep 219931 = 329897) B329897
theorem B941129 : Blo 219811 941129 := bstep (se 2 (by rfl) ⟨352923, by rfl⟩ : syracuseStep 941129 = 705847) B705847
theorem B4817231 : Blo 219811 4817231 := bstep (se 1 (by rfl) ⟨3612923, by rfl⟩ : syracuseStep 4817231 = 7225847) B7225847
theorem B54985463 : Blo 219811 54985463 := bstep (se 1 (by rfl) ⟨41239097, by rfl⟩ : syracuseStep 54985463 = 82478195) B82478195
theorem B627419 : Blo 219811 627419 := bstep (se 1 (by rfl) ⟨470564, by rfl⟩ : syracuseStep 627419 = 941129) B941129
theorem B222687 : Blo 219811 222687 := bstep (se 1 (by rfl) ⟨167015, by rfl⟩ : syracuseStep 222687 = 334031) B334031
theorem B223295 : Blo 219811 223295 := bstep (se 1 (by rfl) ⟨167471, by rfl⟩ : syracuseStep 223295 = 334943) B334943
theorem B3211487 : Blo 219811 3211487 := bstep (se 1 (by rfl) ⟨2408615, by rfl⟩ : syracuseStep 3211487 = 4817231) B4817231
theorem B36656975 : Blo 219811 36656975 := bstep (se 1 (by rfl) ⟨27492731, by rfl⟩ : syracuseStep 36656975 = 54985463) B54985463
theorem B418279 : Blo 219811 418279 := bstep (se 1 (by rfl) ⟨313709, by rfl⟩ : syracuseStep 418279 = 627419) B627419
theorem B557705 : Blo 219811 557705 := bstep (se 2 (by rfl) ⟨209139, by rfl⟩ : syracuseStep 557705 = 418279) B418279
theorem B2140991 : Blo 219811 2140991 := bstep (se 1 (by rfl) ⟨1605743, by rfl⟩ : syracuseStep 2140991 = 3211487) B3211487
theorem B24437983 : Blo 219811 24437983 := bstep (se 1 (by rfl) ⟨18328487, by rfl⟩ : syracuseStep 24437983 = 36656975) B36656975
theorem B371803 : Blo 219811 371803 := bstep (se 1 (by rfl) ⟨278852, by rfl⟩ : syracuseStep 371803 = 557705) B557705
theorem B32583977 : Blo 219811 32583977 := bstep (se 2 (by rfl) ⟨12218991, by rfl⟩ : syracuseStep 32583977 = 24437983) B24437983
theorem B1427327 : Blo 219811 1427327 := bstep (se 1 (by rfl) ⟨1070495, by rfl⟩ : syracuseStep 1427327 = 2140991) B2140991
theorem B951551 : Blo 219811 951551 := bstep (se 1 (by rfl) ⟨713663, by rfl⟩ : syracuseStep 951551 = 1427327) B1427327
theorem B495737 : Blo 219811 495737 := bstep (se 2 (by rfl) ⟨185901, by rfl⟩ : syracuseStep 495737 = 371803) B371803
theorem B21722651 : Blo 219811 21722651 := bstep (se 1 (by rfl) ⟨16291988, by rfl⟩ : syracuseStep 21722651 = 32583977) B32583977
theorem B330491 : Blo 219811 330491 := bstep (se 1 (by rfl) ⟨247868, by rfl⟩ : syracuseStep 330491 = 495737) B495737
theorem B634367 : Blo 219811 634367 := bstep (se 1 (by rfl) ⟨475775, by rfl⟩ : syracuseStep 634367 = 951551) B951551
theorem B14481767 : Blo 219811 14481767 := bstep (se 1 (by rfl) ⟨10861325, by rfl⟩ : syracuseStep 14481767 = 21722651) B21722651
theorem B9654511 : Blo 219811 9654511 := bstep (se 1 (by rfl) ⟨7240883, by rfl⟩ : syracuseStep 9654511 = 14481767) B14481767
theorem B220327 : Blo 219811 220327 := bstep (se 1 (by rfl) ⟨165245, by rfl⟩ : syracuseStep 220327 = 330491) B330491
theorem B422911 : Blo 219811 422911 := bstep (se 1 (by rfl) ⟨317183, by rfl⟩ : syracuseStep 422911 = 634367) B634367
theorem B563881 : Blo 219811 563881 := bstep (se 2 (by rfl) ⟨211455, by rfl⟩ : syracuseStep 563881 = 422911) B422911
theorem B12872681 : Blo 219811 12872681 := bstep (se 2 (by rfl) ⟨4827255, by rfl⟩ : syracuseStep 12872681 = 9654511) B9654511
theorem B8581787 : Blo 219811 8581787 := bstep (se 1 (by rfl) ⟨6436340, by rfl⟩ : syracuseStep 8581787 = 12872681) B12872681
theorem B751841 : Blo 219811 751841 := bstep (se 2 (by rfl) ⟨281940, by rfl⟩ : syracuseStep 751841 = 563881) B563881
theorem B501227 : Blo 219811 501227 := bstep (se 1 (by rfl) ⟨375920, by rfl⟩ : syracuseStep 501227 = 751841) B751841
theorem B5721191 : Blo 219811 5721191 := bstep (se 1 (by rfl) ⟨4290893, by rfl⟩ : syracuseStep 5721191 = 8581787) B8581787
theorem B334151 : Blo 219811 334151 := bstep (se 1 (by rfl) ⟨250613, by rfl⟩ : syracuseStep 334151 = 501227) B501227
theorem B3814127 : Blo 219811 3814127 := bstep (se 1 (by rfl) ⟨2860595, by rfl⟩ : syracuseStep 3814127 = 5721191) B5721191
theorem B2542751 : Blo 219811 2542751 := bstep (se 1 (by rfl) ⟨1907063, by rfl⟩ : syracuseStep 2542751 = 3814127) B3814127
theorem B222767 : Blo 219811 222767 := bstep (se 1 (by rfl) ⟨167075, by rfl⟩ : syracuseStep 222767 = 334151) B334151
theorem B1695167 : Blo 219811 1695167 := bstep (se 1 (by rfl) ⟨1271375, by rfl⟩ : syracuseStep 1695167 = 2542751) B2542751
theorem B1130111 : Blo 219811 1130111 := bstep (se 1 (by rfl) ⟨847583, by rfl⟩ : syracuseStep 1130111 = 1695167) B1695167
theorem B753407 : Blo 219811 753407 := bstep (se 1 (by rfl) ⟨565055, by rfl⟩ : syracuseStep 753407 = 1130111) B1130111
theorem B502271 : Blo 219811 502271 := bstep (se 1 (by rfl) ⟨376703, by rfl⟩ : syracuseStep 502271 = 753407) B753407
theorem B334847 : Blo 219811 334847 := bstep (se 1 (by rfl) ⟨251135, by rfl⟩ : syracuseStep 334847 = 502271) B502271
theorem B223231 : Blo 219811 223231 := bstep (se 1 (by rfl) ⟨167423, by rfl⟩ : syracuseStep 223231 = 334847) B334847

theorem C0 (j : ℕ) (h1 : 54952 ≤ j) (h2 : j ≤ 55651) : Blo 219811 (4 * j + 3) := by
  interval_cases j
  · exact B219811
  · exact B219815
  · exact B219819
  · exact B219823
  · exact B219827
  · exact B219831
  · exact B219835
  · exact B219839
  · exact B219843
  · exact B219847
  · exact B219851
  · exact B219855
  · exact B219859
  · exact B219863
  · exact B219867
  · exact B219871
  · exact B219875
  · exact B219879
  · exact B219883
  · exact B219887
  · exact B219891
  · exact B219895
  · exact B219899
  · exact B219903
  · exact B219907
  · exact B219911
  · exact B219915
  · exact B219919
  · exact B219923
  · exact B219927
  · exact B219931
  · exact B219935
  · exact B219939
  · exact B219943
  · exact B219947
  · exact B219951
  · exact B219955
  · exact B219959
  · exact B219963
  · exact B219967
  · exact B219971
  · exact B219975
  · exact B219979
  · exact B219983
  · exact B219987
  · exact B219991
  · exact B219995
  · exact B219999
  · exact B220003
  · exact B220007
  · exact B220011
  · exact B220015
  · exact B220019
  · exact B220023
  · exact B220027
  · exact B220031
  · exact B220035
  · exact B220039
  · exact B220043
  · exact B220047
  · exact B220051
  · exact B220055
  · exact B220059
  · exact B220063
  · exact B220067
  · exact B220071
  · exact B220075
  · exact B220079
  · exact B220083
  · exact B220087
  · exact B220091
  · exact B220095
  · exact B220099
  · exact B220103
  · exact B220107
  · exact B220111
  · exact B220115
  · exact B220119
  · exact B220123
  · exact B220127
  · exact B220131
  · exact B220135
  · exact B220139
  · exact B220143
  · exact B220147
  · exact B220151
  · exact B220155
  · exact B220159
  · exact B220163
  · exact B220167
  · exact B220171
  · exact B220175
  · exact B220179
  · exact B220183
  · exact B220187
  · exact B220191
  · exact B220195
  · exact B220199
  · exact B220203
  · exact B220207
  · exact B220211
  · exact B220215
  · exact B220219
  · exact B220223
  · exact B220227
  · exact B220231
  · exact B220235
  · exact B220239
  · exact B220243
  · exact B220247
  · exact B220251
  · exact B220255
  · exact B220259
  · exact B220263
  · exact B220267
  · exact B220271
  · exact B220275
  · exact B220279
  · exact B220283
  · exact B220287
  · exact B220291
  · exact B220295
  · exact B220299
  · exact B220303
  · exact B220307
  · exact B220311
  · exact B220315
  · exact B220319
  · exact B220323
  · exact B220327
  · exact B220331
  · exact B220335
  · exact B220339
  · exact B220343
  · exact B220347
  · exact B220351
  · exact B220355
  · exact B220359
  · exact B220363
  · exact B220367
  · exact B220371
  · exact B220375
  · exact B220379
  · exact B220383
  · exact B220387
  · exact B220391
  · exact B220395
  · exact B220399
  · exact B220403
  · exact B220407
  · exact B220411
  · exact B220415
  · exact B220419
  · exact B220423
  · exact B220427
  · exact B220431
  · exact B220435
  · exact B220439
  · exact B220443
  · exact B220447
  · exact B220451
  · exact B220455
  · exact B220459
  · exact B220463
  · exact B220467
  · exact B220471
  · exact B220475
  · exact B220479
  · exact B220483
  · exact B220487
  · exact B220491
  · exact B220495
  · exact B220499
  · exact B220503
  · exact B220507
  · exact B220511
  · exact B220515
  · exact B220519
  · exact B220523
  · exact B220527
  · exact B220531
  · exact B220535
  · exact B220539
  · exact B220543
  · exact B220547
  · exact B220551
  · exact B220555
  · exact B220559
  · exact B220563
  · exact B220567
  · exact B220571
  · exact B220575
  · exact B220579
  · exact B220583
  · exact B220587
  · exact B220591
  · exact B220595
  · exact B220599
  · exact B220603
  · exact B220607
  · exact B220611
  · exact B220615
  · exact B220619
  · exact B220623
  · exact B220627
  · exact B220631
  · exact B220635
  · exact B220639
  · exact B220643
  · exact B220647
  · exact B220651
  · exact B220655
  · exact B220659
  · exact B220663
  · exact B220667
  · exact B220671
  · exact B220675
  · exact B220679
  · exact B220683
  · exact B220687
  · exact B220691
  · exact B220695
  · exact B220699
  · exact B220703
  · exact B220707
  · exact B220711
  · exact B220715
  · exact B220719
  · exact B220723
  · exact B220727
  · exact B220731
  · exact B220735
  · exact B220739
  · exact B220743
  · exact B220747
  · exact B220751
  · exact B220755
  · exact B220759
  · exact B220763
  · exact B220767
  · exact B220771
  · exact B220775
  · exact B220779
  · exact B220783
  · exact B220787
  · exact B220791
  · exact B220795
  · exact B220799
  · exact B220803
  · exact B220807
  · exact B220811
  · exact B220815
  · exact B220819
  · exact B220823
  · exact B220827
  · exact B220831
  · exact B220835
  · exact B220839
  · exact B220843
  · exact B220847
  · exact B220851
  · exact B220855
  · exact B220859
  · exact B220863
  · exact B220867
  · exact B220871
  · exact B220875
  · exact B220879
  · exact B220883
  · exact B220887
  · exact B220891
  · exact B220895
  · exact B220899
  · exact B220903
  · exact B220907
  · exact B220911
  · exact B220915
  · exact B220919
  · exact B220923
  · exact B220927
  · exact B220931
  · exact B220935
  · exact B220939
  · exact B220943
  · exact B220947
  · exact B220951
  · exact B220955
  · exact B220959
  · exact B220963
  · exact B220967
  · exact B220971
  · exact B220975
  · exact B220979
  · exact B220983
  · exact B220987
  · exact B220991
  · exact B220995
  · exact B220999
  · exact B221003
  · exact B221007
  · exact B221011
  · exact B221015
  · exact B221019
  · exact B221023
  · exact B221027
  · exact B221031
  · exact B221035
  · exact B221039
  · exact B221043
  · exact B221047
  · exact B221051
  · exact B221055
  · exact B221059
  · exact B221063
  · exact B221067
  · exact B221071
  · exact B221075
  · exact B221079
  · exact B221083
  · exact B221087
  · exact B221091
  · exact B221095
  · exact B221099
  · exact B221103
  · exact B221107
  · exact B221111
  · exact B221115
  · exact B221119
  · exact B221123
  · exact B221127
  · exact B221131
  · exact B221135
  · exact B221139
  · exact B221143
  · exact B221147
  · exact B221151
  · exact B221155
  · exact B221159
  · exact B221163
  · exact B221167
  · exact B221171
  · exact B221175
  · exact B221179
  · exact B221183
  · exact B221187
  · exact B221191
  · exact B221195
  · exact B221199
  · exact B221203
  · exact B221207
  · exact B221211
  · exact B221215
  · exact B221219
  · exact B221223
  · exact B221227
  · exact B221231
  · exact B221235
  · exact B221239
  · exact B221243
  · exact B221247
  · exact B221251
  · exact B221255
  · exact B221259
  · exact B221263
  · exact B221267
  · exact B221271
  · exact B221275
  · exact B221279
  · exact B221283
  · exact B221287
  · exact B221291
  · exact B221295
  · exact B221299
  · exact B221303
  · exact B221307
  · exact B221311
  · exact B221315
  · exact B221319
  · exact B221323
  · exact B221327
  · exact B221331
  · exact B221335
  · exact B221339
  · exact B221343
  · exact B221347
  · exact B221351
  · exact B221355
  · exact B221359
  · exact B221363
  · exact B221367
  · exact B221371
  · exact B221375
  · exact B221379
  · exact B221383
  · exact B221387
  · exact B221391
  · exact B221395
  · exact B221399
  · exact B221403
  · exact B221407
  · exact B221411
  · exact B221415
  · exact B221419
  · exact B221423
  · exact B221427
  · exact B221431
  · exact B221435
  · exact B221439
  · exact B221443
  · exact B221447
  · exact B221451
  · exact B221455
  · exact B221459
  · exact B221463
  · exact B221467
  · exact B221471
  · exact B221475
  · exact B221479
  · exact B221483
  · exact B221487
  · exact B221491
  · exact B221495
  · exact B221499
  · exact B221503
  · exact B221507
  · exact B221511
  · exact B221515
  · exact B221519
  · exact B221523
  · exact B221527
  · exact B221531
  · exact B221535
  · exact B221539
  · exact B221543
  · exact B221547
  · exact B221551
  · exact B221555
  · exact B221559
  · exact B221563
  · exact B221567
  · exact B221571
  · exact B221575
  · exact B221579
  · exact B221583
  · exact B221587
  · exact B221591
  · exact B221595
  · exact B221599
  · exact B221603
  · exact B221607
  · exact B221611
  · exact B221615
  · exact B221619
  · exact B221623
  · exact B221627
  · exact B221631
  · exact B221635
  · exact B221639
  · exact B221643
  · exact B221647
  · exact B221651
  · exact B221655
  · exact B221659
  · exact B221663
  · exact B221667
  · exact B221671
  · exact B221675
  · exact B221679
  · exact B221683
  · exact B221687
  · exact B221691
  · exact B221695
  · exact B221699
  · exact B221703
  · exact B221707
  · exact B221711
  · exact B221715
  · exact B221719
  · exact B221723
  · exact B221727
  · exact B221731
  · exact B221735
  · exact B221739
  · exact B221743
  · exact B221747
  · exact B221751
  · exact B221755
  · exact B221759
  · exact B221763
  · exact B221767
  · exact B221771
  · exact B221775
  · exact B221779
  · exact B221783
  · exact B221787
  · exact B221791
  · exact B221795
  · exact B221799
  · exact B221803
  · exact B221807
  · exact B221811
  · exact B221815
  · exact B221819
  · exact B221823
  · exact B221827
  · exact B221831
  · exact B221835
  · exact B221839
  · exact B221843
  · exact B221847
  · exact B221851
  · exact B221855
  · exact B221859
  · exact B221863
  · exact B221867
  · exact B221871
  · exact B221875
  · exact B221879
  · exact B221883
  · exact B221887
  · exact B221891
  · exact B221895
  · exact B221899
  · exact B221903
  · exact B221907
  · exact B221911
  · exact B221915
  · exact B221919
  · exact B221923
  · exact B221927
  · exact B221931
  · exact B221935
  · exact B221939
  · exact B221943
  · exact B221947
  · exact B221951
  · exact B221955
  · exact B221959
  · exact B221963
  · exact B221967
  · exact B221971
  · exact B221975
  · exact B221979
  · exact B221983
  · exact B221987
  · exact B221991
  · exact B221995
  · exact B221999
  · exact B222003
  · exact B222007
  · exact B222011
  · exact B222015
  · exact B222019
  · exact B222023
  · exact B222027
  · exact B222031
  · exact B222035
  · exact B222039
  · exact B222043
  · exact B222047
  · exact B222051
  · exact B222055
  · exact B222059
  · exact B222063
  · exact B222067
  · exact B222071
  · exact B222075
  · exact B222079
  · exact B222083
  · exact B222087
  · exact B222091
  · exact B222095
  · exact B222099
  · exact B222103
  · exact B222107
  · exact B222111
  · exact B222115
  · exact B222119
  · exact B222123
  · exact B222127
  · exact B222131
  · exact B222135
  · exact B222139
  · exact B222143
  · exact B222147
  · exact B222151
  · exact B222155
  · exact B222159
  · exact B222163
  · exact B222167
  · exact B222171
  · exact B222175
  · exact B222179
  · exact B222183
  · exact B222187
  · exact B222191
  · exact B222195
  · exact B222199
  · exact B222203
  · exact B222207
  · exact B222211
  · exact B222215
  · exact B222219
  · exact B222223
  · exact B222227
  · exact B222231
  · exact B222235
  · exact B222239
  · exact B222243
  · exact B222247
  · exact B222251
  · exact B222255
  · exact B222259
  · exact B222263
  · exact B222267
  · exact B222271
  · exact B222275
  · exact B222279
  · exact B222283
  · exact B222287
  · exact B222291
  · exact B222295
  · exact B222299
  · exact B222303
  · exact B222307
  · exact B222311
  · exact B222315
  · exact B222319
  · exact B222323
  · exact B222327
  · exact B222331
  · exact B222335
  · exact B222339
  · exact B222343
  · exact B222347
  · exact B222351
  · exact B222355
  · exact B222359
  · exact B222363
  · exact B222367
  · exact B222371
  · exact B222375
  · exact B222379
  · exact B222383
  · exact B222387
  · exact B222391
  · exact B222395
  · exact B222399
  · exact B222403
  · exact B222407
  · exact B222411
  · exact B222415
  · exact B222419
  · exact B222423
  · exact B222427
  · exact B222431
  · exact B222435
  · exact B222439
  · exact B222443
  · exact B222447
  · exact B222451
  · exact B222455
  · exact B222459
  · exact B222463
  · exact B222467
  · exact B222471
  · exact B222475
  · exact B222479
  · exact B222483
  · exact B222487
  · exact B222491
  · exact B222495
  · exact B222499
  · exact B222503
  · exact B222507
  · exact B222511
  · exact B222515
  · exact B222519
  · exact B222523
  · exact B222527
  · exact B222531
  · exact B222535
  · exact B222539
  · exact B222543
  · exact B222547
  · exact B222551
  · exact B222555
  · exact B222559
  · exact B222563
  · exact B222567
  · exact B222571
  · exact B222575
  · exact B222579
  · exact B222583
  · exact B222587
  · exact B222591
  · exact B222595
  · exact B222599
  · exact B222603
  · exact B222607

theorem C1 (j : ℕ) (h1 : 55652 ≤ j) (h2 : j ≤ 55952) : Blo 219811 (4 * j + 3) := by
  interval_cases j
  · exact B222611
  · exact B222615
  · exact B222619
  · exact B222623
  · exact B222627
  · exact B222631
  · exact B222635
  · exact B222639
  · exact B222643
  · exact B222647
  · exact B222651
  · exact B222655
  · exact B222659
  · exact B222663
  · exact B222667
  · exact B222671
  · exact B222675
  · exact B222679
  · exact B222683
  · exact B222687
  · exact B222691
  · exact B222695
  · exact B222699
  · exact B222703
  · exact B222707
  · exact B222711
  · exact B222715
  · exact B222719
  · exact B222723
  · exact B222727
  · exact B222731
  · exact B222735
  · exact B222739
  · exact B222743
  · exact B222747
  · exact B222751
  · exact B222755
  · exact B222759
  · exact B222763
  · exact B222767
  · exact B222771
  · exact B222775
  · exact B222779
  · exact B222783
  · exact B222787
  · exact B222791
  · exact B222795
  · exact B222799
  · exact B222803
  · exact B222807
  · exact B222811
  · exact B222815
  · exact B222819
  · exact B222823
  · exact B222827
  · exact B222831
  · exact B222835
  · exact B222839
  · exact B222843
  · exact B222847
  · exact B222851
  · exact B222855
  · exact B222859
  · exact B222863
  · exact B222867
  · exact B222871
  · exact B222875
  · exact B222879
  · exact B222883
  · exact B222887
  · exact B222891
  · exact B222895
  · exact B222899
  · exact B222903
  · exact B222907
  · exact B222911
  · exact B222915
  · exact B222919
  · exact B222923
  · exact B222927
  · exact B222931
  · exact B222935
  · exact B222939
  · exact B222943
  · exact B222947
  · exact B222951
  · exact B222955
  · exact B222959
  · exact B222963
  · exact B222967
  · exact B222971
  · exact B222975
  · exact B222979
  · exact B222983
  · exact B222987
  · exact B222991
  · exact B222995
  · exact B222999
  · exact B223003
  · exact B223007
  · exact B223011
  · exact B223015
  · exact B223019
  · exact B223023
  · exact B223027
  · exact B223031
  · exact B223035
  · exact B223039
  · exact B223043
  · exact B223047
  · exact B223051
  · exact B223055
  · exact B223059
  · exact B223063
  · exact B223067
  · exact B223071
  · exact B223075
  · exact B223079
  · exact B223083
  · exact B223087
  · exact B223091
  · exact B223095
  · exact B223099
  · exact B223103
  · exact B223107
  · exact B223111
  · exact B223115
  · exact B223119
  · exact B223123
  · exact B223127
  · exact B223131
  · exact B223135
  · exact B223139
  · exact B223143
  · exact B223147
  · exact B223151
  · exact B223155
  · exact B223159
  · exact B223163
  · exact B223167
  · exact B223171
  · exact B223175
  · exact B223179
  · exact B223183
  · exact B223187
  · exact B223191
  · exact B223195
  · exact B223199
  · exact B223203
  · exact B223207
  · exact B223211
  · exact B223215
  · exact B223219
  · exact B223223
  · exact B223227
  · exact B223231
  · exact B223235
  · exact B223239
  · exact B223243
  · exact B223247
  · exact B223251
  · exact B223255
  · exact B223259
  · exact B223263
  · exact B223267
  · exact B223271
  · exact B223275
  · exact B223279
  · exact B223283
  · exact B223287
  · exact B223291
  · exact B223295
  · exact B223299
  · exact B223303
  · exact B223307
  · exact B223311
  · exact B223315
  · exact B223319
  · exact B223323
  · exact B223327
  · exact B223331
  · exact B223335
  · exact B223339
  · exact B223343
  · exact B223347
  · exact B223351
  · exact B223355
  · exact B223359
  · exact B223363
  · exact B223367
  · exact B223371
  · exact B223375
  · exact B223379
  · exact B223383
  · exact B223387
  · exact B223391
  · exact B223395
  · exact B223399
  · exact B223403
  · exact B223407
  · exact B223411
  · exact B223415
  · exact B223419
  · exact B223423
  · exact B223427
  · exact B223431
  · exact B223435
  · exact B223439
  · exact B223443
  · exact B223447
  · exact B223451
  · exact B223455
  · exact B223459
  · exact B223463
  · exact B223467
  · exact B223471
  · exact B223475
  · exact B223479
  · exact B223483
  · exact B223487
  · exact B223491
  · exact B223495
  · exact B223499
  · exact B223503
  · exact B223507
  · exact B223511
  · exact B223515
  · exact B223519
  · exact B223523
  · exact B223527
  · exact B223531
  · exact B223535
  · exact B223539
  · exact B223543
  · exact B223547
  · exact B223551
  · exact B223555
  · exact B223559
  · exact B223563
  · exact B223567
  · exact B223571
  · exact B223575
  · exact B223579
  · exact B223583
  · exact B223587
  · exact B223591
  · exact B223595
  · exact B223599
  · exact B223603
  · exact B223607
  · exact B223611
  · exact B223615
  · exact B223619
  · exact B223623
  · exact B223627
  · exact B223631
  · exact B223635
  · exact B223639
  · exact B223643
  · exact B223647
  · exact B223651
  · exact B223655
  · exact B223659
  · exact B223663
  · exact B223667
  · exact B223671
  · exact B223675
  · exact B223679
  · exact B223683
  · exact B223687
  · exact B223691
  · exact B223695
  · exact B223699
  · exact B223703
  · exact B223707
  · exact B223711
  · exact B223715
  · exact B223719
  · exact B223723
  · exact B223727
  · exact B223731
  · exact B223735
  · exact B223739
  · exact B223743
  · exact B223747
  · exact B223751
  · exact B223755
  · exact B223759
  · exact B223763
  · exact B223767
  · exact B223771
  · exact B223775
  · exact B223779
  · exact B223783
  · exact B223787
  · exact B223791
  · exact B223795
  · exact B223799
  · exact B223803
  · exact B223807
  · exact B223811

theorem solution (m : ℕ) (hlo : 219811 ≤ m) (hhi : m ≤ 223811) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 54952 ≤ j := by omega
    have hj2 : j ≤ 55952 := by omega
    have hb : Blo 219811 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 55652 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
