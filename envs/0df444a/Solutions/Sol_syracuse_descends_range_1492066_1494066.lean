-- Prove2me | solution 1 for syracuse_descends_range_1492066_1494066
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:46:57.306708+00:00
-- url     : https://prove2.me/submissions/b18ca731-bb76-441f-a130-0932ee83239b

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


theorem B1679377 : Blo 1492066 1679377 := bbase (se 2 (by rfl) ⟨629766, by rfl⟩ : syracuseStep 1679377 = 1259533) (by norm_num)
theorem B6373397 : Blo 1492066 6373397 := bbase (se 6 (by rfl) ⟨149376, by rfl⟩ : syracuseStep 6373397 = 298753) (by norm_num)
theorem B22986773 : Blo 1492066 22986773 := bbase (se 6 (by rfl) ⟨538752, by rfl⟩ : syracuseStep 22986773 = 1077505) (by norm_num)
theorem B3498013 : Blo 1492066 3498013 := bbase (se 3 (by rfl) ⟨655877, by rfl⟩ : syracuseStep 3498013 = 1311755) (by norm_num)
theorem B1679413 : Blo 1492066 1679413 := bbase (se 5 (by rfl) ⟨78722, by rfl⟩ : syracuseStep 1679413 = 157445) (by norm_num)
theorem B3358781 : Blo 1492066 3358781 := bbase (se 3 (by rfl) ⟨629771, by rfl⟩ : syracuseStep 3358781 = 1259543) (by norm_num)
theorem B9085013 : Blo 1492066 9085013 := bbase (se 8 (by rfl) ⟨53232, by rfl⟩ : syracuseStep 9085013 = 106465) (by norm_num)
theorem B1679449 : Blo 1492066 1679449 := bbase (se 2 (by rfl) ⟨629793, by rfl⟩ : syracuseStep 1679449 = 1259587) (by norm_num)
theorem B1679485 : Blo 1492066 1679485 := bbase (se 3 (by rfl) ⟨314903, by rfl⟩ : syracuseStep 1679485 = 629807) (by norm_num)
theorem B3358853 : Blo 1492066 3358853 := bbase (se 4 (by rfl) ⟨314892, by rfl⟩ : syracuseStep 3358853 = 629785) (by norm_num)
theorem B7561349 : Blo 1492066 7561349 := bbase (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) (by norm_num)
theorem B1679521 : Blo 1492066 1679521 := bbase (se 2 (by rfl) ⟨629820, by rfl⟩ : syracuseStep 1679521 = 1259641) (by norm_num)
theorem B2392229 : Blo 1492066 2392229 := bbase (se 4 (by rfl) ⟨224271, by rfl⟩ : syracuseStep 2392229 = 448543) (by norm_num)
theorem B3186869 : Blo 1492066 3186869 := bbase (se 5 (by rfl) ⟨149384, by rfl⟩ : syracuseStep 3186869 = 298769) (by norm_num)
theorem B1941689 : Blo 1492066 1941689 := bbase (se 2 (by rfl) ⟨728133, by rfl⟩ : syracuseStep 1941689 = 1456267) (by norm_num)
theorem B1679557 : Blo 1492066 1679557 := bbase (se 4 (by rfl) ⟨157458, by rfl⟩ : syracuseStep 1679557 = 314917) (by norm_num)
theorem B5382341 : Blo 1492066 5382341 := bbase (se 4 (by rfl) ⟨504594, by rfl⟩ : syracuseStep 5382341 = 1009189) (by norm_num)
theorem B3358925 : Blo 1492066 3358925 := bbase (se 3 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 3358925 = 1259597) (by norm_num)
theorem B1679593 : Blo 1492066 1679593 := bbase (se 2 (by rfl) ⟨629847, by rfl⟩ : syracuseStep 1679593 = 1259695) (by norm_num)
theorem B1818865 : Blo 1492066 1818865 := bbase (se 2 (by rfl) ⟨682074, by rfl⟩ : syracuseStep 1818865 = 1364149) (by norm_num)
theorem B7176437 : Blo 1492066 7176437 := bbase (se 5 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 7176437 = 672791) (by norm_num)
theorem B1868033 : Blo 1492066 1868033 := bbase (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) (by norm_num)
theorem B6373637 : Blo 1492066 6373637 := bbase (se 4 (by rfl) ⟨597528, by rfl⟩ : syracuseStep 6373637 = 1195057) (by norm_num)
theorem B1679629 : Blo 1492066 1679629 := bbase (se 3 (by rfl) ⟨314930, by rfl⟩ : syracuseStep 1679629 = 629861) (by norm_num)
theorem B3358997 : Blo 1492066 3358997 := bbase (se 6 (by rfl) ⟨78726, by rfl⟩ : syracuseStep 3358997 = 157453) (by norm_num)
theorem B1679665 : Blo 1492066 1679665 := bbase (se 2 (by rfl) ⟨629874, by rfl⟩ : syracuseStep 1679665 = 1259749) (by norm_num)
theorem B4251973 : Blo 1492066 4251973 := bbase (se 4 (by rfl) ⟨398622, by rfl⟩ : syracuseStep 4251973 = 797245) (by norm_num)
theorem B1679701 : Blo 1492066 1679701 := bbase (se 10 (by rfl) ⟨2460, by rfl⟩ : syracuseStep 1679701 = 4921) (by norm_num)
theorem B3359069 : Blo 1492066 3359069 := bbase (se 3 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 3359069 = 1259651) (by norm_num)
theorem B9208181 : Blo 1492066 9208181 := bbase (se 5 (by rfl) ⟨431633, by rfl⟩ : syracuseStep 9208181 = 863267) (by norm_num)
theorem B1794421 : Blo 1492066 1794421 := bbase (se 5 (by rfl) ⟨84113, by rfl⟩ : syracuseStep 1794421 = 168227) (by norm_num)
theorem B1679737 : Blo 1492066 1679737 := bbase (se 2 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 1679737 = 1259803) (by norm_num)
theorem B5038469 : Blo 1492066 5038469 := bbase (se 4 (by rfl) ⟨472356, by rfl⟩ : syracuseStep 5038469 = 944713) (by norm_num)
theorem B2392453 : Blo 1492066 2392453 := bbase (se 4 (by rfl) ⟨224292, by rfl⟩ : syracuseStep 2392453 = 448585) (by norm_num)
theorem B1679773 : Blo 1492066 1679773 := bbase (se 3 (by rfl) ⟨314957, by rfl⟩ : syracuseStep 1679773 = 629915) (by norm_num)
theorem B3187109 : Blo 1492066 3187109 := bbase (se 4 (by rfl) ⟨298791, by rfl⟩ : syracuseStep 3187109 = 597583) (by norm_num)
theorem B3359141 : Blo 1492066 3359141 := bbase (se 4 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 3359141 = 629839) (by norm_num)
theorem B1679809 : Blo 1492066 1679809 := bbase (se 2 (by rfl) ⟨629928, by rfl⟩ : syracuseStep 1679809 = 1259857) (by norm_num)
theorem B1794517 : Blo 1492066 1794517 := bbase (se 7 (by rfl) ⟨21029, by rfl⟩ : syracuseStep 1794517 = 42059) (by norm_num)
theorem B3776989 : Blo 1492066 3776989 := bbase (se 3 (by rfl) ⟨708185, by rfl⟩ : syracuseStep 3776989 = 1416371) (by norm_num)
theorem B1679845 : Blo 1492066 1679845 := bbase (se 4 (by rfl) ⟨157485, by rfl⟩ : syracuseStep 1679845 = 314971) (by norm_num)
theorem B5382629 : Blo 1492066 5382629 := bbase (se 4 (by rfl) ⟨504621, by rfl⟩ : syracuseStep 5382629 = 1009243) (by norm_num)
theorem B1819109 : Blo 1492066 1819109 := bbase (se 4 (by rfl) ⟨170541, by rfl⟩ : syracuseStep 1819109 = 341083) (by norm_num)
theorem B3359213 : Blo 1492066 3359213 := bbase (se 3 (by rfl) ⟨629852, by rfl⟩ : syracuseStep 3359213 = 1259705) (by norm_num)
theorem B1679881 : Blo 1492066 1679881 := bbase (se 2 (by rfl) ⟨629955, by rfl⟩ : syracuseStep 1679881 = 1259911) (by norm_num)
theorem B1679917 : Blo 1492066 1679917 := bbase (se 3 (by rfl) ⟨314984, by rfl⟩ : syracuseStep 1679917 = 629969) (by norm_num)
theorem B3359285 : Blo 1492066 3359285 := bbase (se 5 (by rfl) ⟨157466, by rfl⟩ : syracuseStep 3359285 = 314933) (by norm_num)
theorem B3883589 : Blo 1492066 3883589 := bbase (se 4 (by rfl) ⟨364086, by rfl⟩ : syracuseStep 3883589 = 728173) (by norm_num)
theorem B2835013 : Blo 1492066 2835013 := bbase (se 4 (by rfl) ⟨265782, by rfl⟩ : syracuseStep 2835013 = 531565) (by norm_num)
theorem B3777101 : Blo 1492066 3777101 := bbase (se 3 (by rfl) ⟨708206, by rfl⟩ : syracuseStep 3777101 = 1416413) (by norm_num)
theorem B1679953 : Blo 1492066 1679953 := bbase (se 2 (by rfl) ⟨629982, by rfl⟩ : syracuseStep 1679953 = 1259965) (by norm_num)
theorem B1679989 : Blo 1492066 1679989 := bbase (se 5 (by rfl) ⟨78749, by rfl⟩ : syracuseStep 1679989 = 157499) (by norm_num)
theorem B3359357 : Blo 1492066 3359357 := bbase (se 3 (by rfl) ⟨629879, by rfl⟩ : syracuseStep 3359357 = 1259759) (by norm_num)
theorem B20439701 : Blo 1492066 20439701 := bbase (se 6 (by rfl) ⟨479055, by rfl⟩ : syracuseStep 20439701 = 958111) (by norm_num)
theorem B1680025 : Blo 1492066 1680025 := bbase (se 2 (by rfl) ⟨630009, by rfl⟩ : syracuseStep 1680025 = 1260019) (by norm_num)
theorem B1680061 : Blo 1492066 1680061 := bbase (se 3 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 1680061 = 630023) (by norm_num)
theorem B3359429 : Blo 1492066 3359429 := bbase (se 4 (by rfl) ⟨314946, by rfl⟩ : syracuseStep 3359429 = 629893) (by norm_num)
theorem B2835157 : Blo 1492066 2835157 := bbase (se 7 (by rfl) ⟨33224, by rfl⟩ : syracuseStep 2835157 = 66449) (by norm_num)
theorem B1680097 : Blo 1492066 1680097 := bbase (se 2 (by rfl) ⟨630036, by rfl⟩ : syracuseStep 1680097 = 1260073) (by norm_num)
theorem B1680133 : Blo 1492066 1680133 := bbase (se 4 (by rfl) ⟨157512, by rfl⟩ : syracuseStep 1680133 = 315025) (by norm_num)
theorem B3777293 : Blo 1492066 3777293 := bbase (se 3 (by rfl) ⟨708242, by rfl⟩ : syracuseStep 3777293 = 1416485) (by norm_num)
theorem B3359501 : Blo 1492066 3359501 := bbase (se 3 (by rfl) ⟨629906, by rfl⟩ : syracuseStep 3359501 = 1259813) (by norm_num)
theorem B21521173 : Blo 1492066 21521173 := bbase (se 6 (by rfl) ⟨504402, by rfl⟩ : syracuseStep 21521173 = 1008805) (by norm_num)
theorem B1680169 : Blo 1492066 1680169 := bbase (se 2 (by rfl) ⟨630063, by rfl⟩ : syracuseStep 1680169 = 1260127) (by norm_num)
theorem B5038901 : Blo 1492066 5038901 := bbase (se 5 (by rfl) ⟨236198, by rfl⟩ : syracuseStep 5038901 = 472397) (by norm_num)
theorem B1680205 : Blo 1492066 1680205 := bbase (se 3 (by rfl) ⟨315038, by rfl⟩ : syracuseStep 1680205 = 630077) (by norm_num)
theorem B3359573 : Blo 1492066 3359573 := bbase (se 9 (by rfl) ⟨9842, by rfl⟩ : syracuseStep 3359573 = 19685) (by norm_num)
theorem B8504149 : Blo 1492066 8504149 := bbase (se 9 (by rfl) ⟨24914, by rfl⟩ : syracuseStep 8504149 = 49829) (by norm_num)
theorem B1680241 : Blo 1492066 1680241 := bbase (se 2 (by rfl) ⟨630090, by rfl⟩ : syracuseStep 1680241 = 1260181) (by norm_num)
theorem B2835317 : Blo 1492066 2835317 := bbase (se 5 (by rfl) ⟨132905, by rfl⟩ : syracuseStep 2835317 = 265811) (by norm_num)
theorem B1680277 : Blo 1492066 1680277 := bbase (se 6 (by rfl) ⟨39381, by rfl⟩ : syracuseStep 1680277 = 78763) (by norm_num)
theorem B3187613 : Blo 1492066 3187613 := bbase (se 3 (by rfl) ⟨597677, by rfl⟩ : syracuseStep 3187613 = 1195355) (by norm_num)
theorem B3359645 : Blo 1492066 3359645 := bbase (se 3 (by rfl) ⟨629933, by rfl⟩ : syracuseStep 3359645 = 1259867) (by norm_num)
theorem B3187621 : Blo 1492066 3187621 := bbase (se 4 (by rfl) ⟨298839, by rfl⟩ : syracuseStep 3187621 = 597679) (by norm_num)
theorem B5669797 : Blo 1492066 5669797 := bbase (se 4 (by rfl) ⟨531543, by rfl⟩ : syracuseStep 5669797 = 1063087) (by norm_num)
theorem B1680313 : Blo 1492066 1680313 := bbase (se 2 (by rfl) ⟨630117, by rfl⟩ : syracuseStep 1680313 = 1260235) (by norm_num)
theorem B5530565 : Blo 1492066 5530565 := bbase (se 4 (by rfl) ⟨518490, by rfl⟩ : syracuseStep 5530565 = 1036981) (by norm_num)
theorem B1680349 : Blo 1492066 1680349 := bbase (se 3 (by rfl) ⟨315065, by rfl⟩ : syracuseStep 1680349 = 630131) (by norm_num)
theorem B3359717 : Blo 1492066 3359717 := bbase (se 4 (by rfl) ⟨314973, by rfl⟩ : syracuseStep 3359717 = 629947) (by norm_num)
theorem B1680385 : Blo 1492066 1680385 := bbase (se 2 (by rfl) ⟨630144, by rfl⟩ : syracuseStep 1680385 = 1260289) (by norm_num)
theorem B2835461 : Blo 1492066 2835461 := bbase (se 4 (by rfl) ⟨265824, by rfl⟩ : syracuseStep 2835461 = 531649) (by norm_num)
theorem B1680421 : Blo 1492066 1680421 := bbase (se 4 (by rfl) ⟨157539, by rfl⟩ : syracuseStep 1680421 = 315079) (by norm_num)
theorem B3359789 : Blo 1492066 3359789 := bbase (se 3 (by rfl) ⟨629960, by rfl⟩ : syracuseStep 3359789 = 1259921) (by norm_num)
theorem B1680457 : Blo 1492066 1680457 := bbase (se 2 (by rfl) ⟨630171, by rfl⟩ : syracuseStep 1680457 = 1260343) (by norm_num)
theorem B41976917 : Blo 1492066 41976917 := bbase (se 8 (by rfl) ⟨245958, by rfl⟩ : syracuseStep 41976917 = 491917) (by norm_num)
theorem B3777637 : Blo 1492066 3777637 := bbase (se 4 (by rfl) ⟨354153, by rfl⟩ : syracuseStep 3777637 = 708307) (by norm_num)
theorem B1680493 : Blo 1492066 1680493 := bbase (se 3 (by rfl) ⟨315092, by rfl⟩ : syracuseStep 1680493 = 630185) (by norm_num)
theorem B3359861 : Blo 1492066 3359861 := bbase (se 5 (by rfl) ⟨157493, by rfl⟩ : syracuseStep 3359861 = 314987) (by norm_num)
theorem B1680529 : Blo 1492066 1680529 := bbase (se 2 (by rfl) ⟨630198, by rfl⟩ : syracuseStep 1680529 = 1260397) (by norm_num)
theorem B3884213 : Blo 1492066 3884213 := bbase (se 5 (by rfl) ⟨182072, by rfl⟩ : syracuseStep 3884213 = 364145) (by norm_num)
theorem B1680565 : Blo 1492066 1680565 := bbase (se 5 (by rfl) ⟨78776, by rfl⟩ : syracuseStep 1680565 = 157553) (by norm_num)
theorem B3359933 : Blo 1492066 3359933 := bbase (se 3 (by rfl) ⟨629987, by rfl⟩ : syracuseStep 3359933 = 1259975) (by norm_num)
theorem B3777749 : Blo 1492066 3777749 := bbase (se 7 (by rfl) ⟨44270, by rfl⟩ : syracuseStep 3777749 = 88541) (by norm_num)
theorem B5670101 : Blo 1492066 5670101 := bbase (se 7 (by rfl) ⟨66446, by rfl⟩ : syracuseStep 5670101 = 132893) (by norm_num)
theorem B1680601 : Blo 1492066 1680601 := bbase (se 2 (by rfl) ⟨630225, by rfl⟩ : syracuseStep 1680601 = 1260451) (by norm_num)
theorem B5039333 : Blo 1492066 5039333 := bbase (se 4 (by rfl) ⟨472437, by rfl⟩ : syracuseStep 5039333 = 944875) (by norm_num)
theorem B1680637 : Blo 1492066 1680637 := bbase (se 3 (by rfl) ⟨315119, by rfl⟩ : syracuseStep 1680637 = 630239) (by norm_num)
theorem B3360005 : Blo 1492066 3360005 := bbase (se 4 (by rfl) ⟨315000, by rfl⟩ : syracuseStep 3360005 = 630001) (by norm_num)
theorem B6808853 : Blo 1492066 6808853 := bbase (se 6 (by rfl) ⟨159582, by rfl⟩ : syracuseStep 6808853 = 319165) (by norm_num)
theorem B1680673 : Blo 1492066 1680673 := bbase (se 2 (by rfl) ⟨630252, by rfl⟩ : syracuseStep 1680673 = 1260505) (by norm_num)
theorem B2835749 : Blo 1492066 2835749 := bbase (se 4 (by rfl) ⟨265851, by rfl⟩ : syracuseStep 2835749 = 531703) (by norm_num)
theorem B14345525 : Blo 1492066 14345525 := bbase (se 5 (by rfl) ⟨672446, by rfl⟩ : syracuseStep 14345525 = 1344893) (by norm_num)
theorem B1680709 : Blo 1492066 1680709 := bbase (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) (by norm_num)
theorem B3360077 : Blo 1492066 3360077 := bbase (se 3 (by rfl) ⟨630014, by rfl⟩ : syracuseStep 3360077 = 1260029) (by norm_num)
theorem B1680745 : Blo 1492066 1680745 := bbase (se 2 (by rfl) ⟨630279, by rfl⟩ : syracuseStep 1680745 = 1260559) (by norm_num)
theorem B1680781 : Blo 1492066 1680781 := bbase (se 3 (by rfl) ⟨315146, by rfl⟩ : syracuseStep 1680781 = 630293) (by norm_num)
theorem B3777941 : Blo 1492066 3777941 := bbase (se 6 (by rfl) ⟨88545, by rfl⟩ : syracuseStep 3777941 = 177091) (by norm_num)
theorem B3360149 : Blo 1492066 3360149 := bbase (se 6 (by rfl) ⟨78753, by rfl⟩ : syracuseStep 3360149 = 157507) (by norm_num)
theorem B4253077 : Blo 1492066 4253077 := bbase (se 6 (by rfl) ⟨99681, by rfl⟩ : syracuseStep 4253077 = 199363) (by norm_num)
theorem B7562645 : Blo 1492066 7562645 := bbase (se 6 (by rfl) ⟨177249, by rfl⟩ : syracuseStep 7562645 = 354499) (by norm_num)
theorem B1680817 : Blo 1492066 1680817 := bbase (se 2 (by rfl) ⟨630306, by rfl⟩ : syracuseStep 1680817 = 1260613) (by norm_num)
theorem B2835901 : Blo 1492066 2835901 := bbase (se 3 (by rfl) ⟨531731, by rfl⟩ : syracuseStep 2835901 = 1063463) (by norm_num)
theorem B3360221 : Blo 1492066 3360221 := bbase (se 3 (by rfl) ⟨630041, by rfl⟩ : syracuseStep 3360221 = 1260083) (by norm_num)
theorem B3360293 : Blo 1492066 3360293 := bbase (se 4 (by rfl) ⟨315027, by rfl⟩ : syracuseStep 3360293 = 630055) (by norm_num)
theorem B9561685 : Blo 1492066 9561685 := bbase (se 8 (by rfl) ⟨56025, by rfl⟩ : syracuseStep 9561685 = 112051) (by norm_num)
theorem B8619605 : Blo 1492066 8619605 := bbase (se 8 (by rfl) ⟨50505, by rfl⟩ : syracuseStep 8619605 = 101011) (by norm_num)
theorem B3360365 : Blo 1492066 3360365 := bbase (se 3 (by rfl) ⟨630068, by rfl⟩ : syracuseStep 3360365 = 1260137) (by norm_num)
theorem B2238101 : Blo 1492066 2238101 := bbase (se 6 (by rfl) ⟨52455, by rfl⟩ : syracuseStep 2238101 = 104911) (by norm_num)
theorem B5039765 : Blo 1492066 5039765 := bbase (se 6 (by rfl) ⟨118119, by rfl⟩ : syracuseStep 5039765 = 236239) (by norm_num)
theorem B2238125 : Blo 1492066 2238125 := bbase (se 3 (by rfl) ⟨419648, by rfl⟩ : syracuseStep 2238125 = 839297) (by norm_num)
theorem B3360437 : Blo 1492066 3360437 := bbase (se 5 (by rfl) ⟨157520, by rfl⟩ : syracuseStep 3360437 = 315041) (by norm_num)
theorem B2238149 : Blo 1492066 2238149 := bbase (se 4 (by rfl) ⟨209826, by rfl⟩ : syracuseStep 2238149 = 419653) (by norm_num)
theorem B2238173 : Blo 1492066 2238173 := bbase (se 3 (by rfl) ⟨419657, by rfl⟩ : syracuseStep 2238173 = 839315) (by norm_num)
theorem B3778285 : Blo 1492066 3778285 := bbase (se 3 (by rfl) ⟨708428, by rfl⟩ : syracuseStep 3778285 = 1416857) (by norm_num)
theorem B2836205 : Blo 1492066 2836205 := bbase (se 3 (by rfl) ⟨531788, by rfl⟩ : syracuseStep 2836205 = 1063577) (by norm_num)
theorem B2238197 : Blo 1492066 2238197 := bbase (se 5 (by rfl) ⟨104915, by rfl⟩ : syracuseStep 2238197 = 209831) (by norm_num)
theorem B3360509 : Blo 1492066 3360509 := bbase (se 3 (by rfl) ⟨630095, by rfl⟩ : syracuseStep 3360509 = 1260191) (by norm_num)
theorem B2238221 : Blo 1492066 2238221 := bbase (se 3 (by rfl) ⟨419666, by rfl⟩ : syracuseStep 2238221 = 839333) (by norm_num)
theorem B2238245 : Blo 1492066 2238245 := bbase (se 4 (by rfl) ⟨209835, by rfl⟩ : syracuseStep 2238245 = 419671) (by norm_num)
theorem B7554869 : Blo 1492066 7554869 := bbase (se 5 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 7554869 = 708269) (by norm_num)
theorem B2238269 : Blo 1492066 2238269 := bbase (se 3 (by rfl) ⟨419675, by rfl⟩ : syracuseStep 2238269 = 839351) (by norm_num)
theorem B3360581 : Blo 1492066 3360581 := bbase (se 4 (by rfl) ⟨315054, by rfl⟩ : syracuseStep 3360581 = 630109) (by norm_num)
theorem B2238293 : Blo 1492066 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B3778397 : Blo 1492066 3778397 := bbase (se 3 (by rfl) ⟨708449, by rfl⟩ : syracuseStep 3778397 = 1416899) (by norm_num)
theorem B2238317 : Blo 1492066 2238317 := bbase (se 3 (by rfl) ⟨419684, by rfl⟩ : syracuseStep 2238317 = 839369) (by norm_num)
theorem B2238341 : Blo 1492066 2238341 := bbase (se 4 (by rfl) ⟨209844, by rfl⟩ : syracuseStep 2238341 = 419689) (by norm_num)
theorem B3360653 : Blo 1492066 3360653 := bbase (se 3 (by rfl) ⟨630122, by rfl⟩ : syracuseStep 3360653 = 1260245) (by norm_num)
theorem B2238365 : Blo 1492066 2238365 := bbase (se 3 (by rfl) ⟨419693, by rfl⟩ : syracuseStep 2238365 = 839387) (by norm_num)
theorem B2238389 : Blo 1492066 2238389 := bbase (se 5 (by rfl) ⟨104924, by rfl⟩ : syracuseStep 2238389 = 209849) (by norm_num)
theorem B2238413 : Blo 1492066 2238413 := bbase (se 3 (by rfl) ⟨419702, by rfl⟩ : syracuseStep 2238413 = 839405) (by norm_num)
theorem B3360725 : Blo 1492066 3360725 := bbase (se 7 (by rfl) ⟨39383, by rfl⟩ : syracuseStep 3360725 = 78767) (by norm_num)
theorem B2238437 : Blo 1492066 2238437 := bbase (se 4 (by rfl) ⟨209853, by rfl⟩ : syracuseStep 2238437 = 419707) (by norm_num)
theorem B2238461 : Blo 1492066 2238461 := bbase (se 3 (by rfl) ⟨419711, by rfl⟩ : syracuseStep 2238461 = 839423) (by norm_num)
theorem B3188749 : Blo 1492066 3188749 := bbase (se 3 (by rfl) ⟨597890, by rfl⟩ : syracuseStep 3188749 = 1195781) (by norm_num)
theorem B2238485 : Blo 1492066 2238485 := bbase (se 6 (by rfl) ⟨52464, by rfl⟩ : syracuseStep 2238485 = 104929) (by norm_num)
theorem B12757013 : Blo 1492066 12757013 := bbase (se 6 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 12757013 = 597985) (by norm_num)
theorem B3778589 : Blo 1492066 3778589 := bbase (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) (by norm_num)
theorem B3360797 : Blo 1492066 3360797 := bbase (se 3 (by rfl) ⟨630149, by rfl⟩ : syracuseStep 3360797 = 1260299) (by norm_num)
theorem B2238509 : Blo 1492066 2238509 := bbase (se 3 (by rfl) ⟨419720, by rfl⟩ : syracuseStep 2238509 = 839441) (by norm_num)
theorem B3024965 : Blo 1492066 3024965 := bbase (se 4 (by rfl) ⟨283590, by rfl⟩ : syracuseStep 3024965 = 567181) (by norm_num)
theorem B2238533 : Blo 1492066 2238533 := bbase (se 4 (by rfl) ⟨209862, by rfl⟩ : syracuseStep 2238533 = 419725) (by norm_num)
theorem B5040197 : Blo 1492066 5040197 := bbase (se 4 (by rfl) ⟨472518, by rfl⟩ : syracuseStep 5040197 = 945037) (by norm_num)
theorem B2238557 : Blo 1492066 2238557 := bbase (se 3 (by rfl) ⟨419729, by rfl⟩ : syracuseStep 2238557 = 839459) (by norm_num)
theorem B3360869 : Blo 1492066 3360869 := bbase (se 4 (by rfl) ⟨315081, by rfl⟩ : syracuseStep 3360869 = 630163) (by norm_num)
theorem B2238581 : Blo 1492066 2238581 := bbase (se 5 (by rfl) ⟨104933, by rfl⟩ : syracuseStep 2238581 = 209867) (by norm_num)
theorem B2017405 : Blo 1492066 2017405 := bbase (se 3 (by rfl) ⟨378263, by rfl⟩ : syracuseStep 2017405 = 756527) (by norm_num)
theorem B2238605 : Blo 1492066 2238605 := bbase (se 3 (by rfl) ⟨419738, by rfl⟩ : syracuseStep 2238605 = 839477) (by norm_num)
theorem B2238629 : Blo 1492066 2238629 := bbase (se 4 (by rfl) ⟨209871, by rfl⟩ : syracuseStep 2238629 = 419743) (by norm_num)
theorem B3360941 : Blo 1492066 3360941 := bbase (se 3 (by rfl) ⟨630176, by rfl⟩ : syracuseStep 3360941 = 1260353) (by norm_num)
theorem B2238653 : Blo 1492066 2238653 := bbase (se 3 (by rfl) ⟨419747, by rfl⟩ : syracuseStep 2238653 = 839495) (by norm_num)
theorem B2238677 : Blo 1492066 2238677 := bbase (se 7 (by rfl) ⟨26234, by rfl⟩ : syracuseStep 2238677 = 52469) (by norm_num)
theorem B7178453 : Blo 1492066 7178453 := bbase (se 7 (by rfl) ⟨84122, by rfl⟩ : syracuseStep 7178453 = 168245) (by norm_num)
theorem B2238701 : Blo 1492066 2238701 := bbase (se 3 (by rfl) ⟨419756, by rfl⟩ : syracuseStep 2238701 = 839513) (by norm_num)
theorem B3361013 : Blo 1492066 3361013 := bbase (se 5 (by rfl) ⟨157547, by rfl⟩ : syracuseStep 3361013 = 315095) (by norm_num)
theorem B2238725 : Blo 1492066 2238725 := bbase (se 4 (by rfl) ⟨209880, by rfl⟩ : syracuseStep 2238725 = 419761) (by norm_num)
theorem B2238749 : Blo 1492066 2238749 := bbase (se 3 (by rfl) ⟨419765, by rfl⟩ : syracuseStep 2238749 = 839531) (by norm_num)
theorem B2238773 : Blo 1492066 2238773 := bbase (se 5 (by rfl) ⟨104942, by rfl⟩ : syracuseStep 2238773 = 209885) (by norm_num)
theorem B3361085 : Blo 1492066 3361085 := bbase (se 3 (by rfl) ⟨630203, by rfl⟩ : syracuseStep 3361085 = 1260407) (by norm_num)
theorem B2238797 : Blo 1492066 2238797 := bbase (se 3 (by rfl) ⟨419774, by rfl⟩ : syracuseStep 2238797 = 839549) (by norm_num)
theorem B2238821 : Blo 1492066 2238821 := bbase (se 4 (by rfl) ⟨209889, by rfl⟩ : syracuseStep 2238821 = 419779) (by norm_num)
theorem B3778933 : Blo 1492066 3778933 := bbase (se 5 (by rfl) ⟨177137, by rfl⟩ : syracuseStep 3778933 = 354275) (by norm_num)
theorem B2238845 : Blo 1492066 2238845 := bbase (se 3 (by rfl) ⟨419783, by rfl⟩ : syracuseStep 2238845 = 839567) (by norm_num)
theorem B3189125 : Blo 1492066 3189125 := bbase (se 4 (by rfl) ⟨298980, by rfl⟩ : syracuseStep 3189125 = 597961) (by norm_num)
theorem B3361157 : Blo 1492066 3361157 := bbase (se 4 (by rfl) ⟨315108, by rfl⟩ : syracuseStep 3361157 = 630217) (by norm_num)
theorem B2238869 : Blo 1492066 2238869 := bbase (se 6 (by rfl) ⟨52473, by rfl⟩ : syracuseStep 2238869 = 104947) (by norm_num)
theorem B7178645 : Blo 1492066 7178645 := bbase (se 6 (by rfl) ⟨168249, by rfl⟩ : syracuseStep 7178645 = 336499) (by norm_num)
theorem B2238893 : Blo 1492066 2238893 := bbase (se 3 (by rfl) ⟨419792, by rfl⟩ : syracuseStep 2238893 = 839585) (by norm_num)
theorem B2238917 : Blo 1492066 2238917 := bbase (se 4 (by rfl) ⟨209898, by rfl⟩ : syracuseStep 2238917 = 419797) (by norm_num)
theorem B3361229 : Blo 1492066 3361229 := bbase (se 3 (by rfl) ⟨630230, by rfl⟩ : syracuseStep 3361229 = 1260461) (by norm_num)
theorem B2238941 : Blo 1492066 2238941 := bbase (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) (by norm_num)
theorem B3779045 : Blo 1492066 3779045 := bbase (se 4 (by rfl) ⟨354285, by rfl⟩ : syracuseStep 3779045 = 708571) (by norm_num)
theorem B7662053 : Blo 1492066 7662053 := bbase (se 4 (by rfl) ⟨718317, by rfl⟩ : syracuseStep 7662053 = 1436635) (by norm_num)
theorem B2238965 : Blo 1492066 2238965 := bbase (se 5 (by rfl) ⟨104951, by rfl⟩ : syracuseStep 2238965 = 209903) (by norm_num)
theorem B6375925 : Blo 1492066 6375925 := bbase (se 5 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 6375925 = 597743) (by norm_num)
theorem B5040629 : Blo 1492066 5040629 := bbase (se 5 (by rfl) ⟨236279, by rfl⟩ : syracuseStep 5040629 = 472559) (by norm_num)
theorem B2238989 : Blo 1492066 2238989 := bbase (se 3 (by rfl) ⟨419810, by rfl⟩ : syracuseStep 2238989 = 839621) (by norm_num)
theorem B3361301 : Blo 1492066 3361301 := bbase (se 6 (by rfl) ⟨78780, by rfl⟩ : syracuseStep 3361301 = 157561) (by norm_num)
theorem B2239013 : Blo 1492066 2239013 := bbase (se 4 (by rfl) ⟨209907, by rfl⟩ : syracuseStep 2239013 = 419815) (by norm_num)
theorem B2239037 : Blo 1492066 2239037 := bbase (se 3 (by rfl) ⟨419819, by rfl⟩ : syracuseStep 2239037 = 839639) (by norm_num)
theorem B2239061 : Blo 1492066 2239061 := bbase (se 8 (by rfl) ⟨13119, by rfl⟩ : syracuseStep 2239061 = 26239) (by norm_num)
theorem B3361373 : Blo 1492066 3361373 := bbase (se 3 (by rfl) ⟨630257, by rfl⟩ : syracuseStep 3361373 = 1260515) (by norm_num)
theorem B2239085 : Blo 1492066 2239085 := bbase (se 3 (by rfl) ⟨419828, by rfl⟩ : syracuseStep 2239085 = 839657) (by norm_num)
theorem B2239109 : Blo 1492066 2239109 := bbase (se 4 (by rfl) ⟨209916, by rfl⟩ : syracuseStep 2239109 = 419833) (by norm_num)
theorem B2239133 : Blo 1492066 2239133 := bbase (se 3 (by rfl) ⟨419837, by rfl⟩ : syracuseStep 2239133 = 839675) (by norm_num)
theorem B3779237 : Blo 1492066 3779237 := bbase (se 4 (by rfl) ⟨354303, by rfl⟩ : syracuseStep 3779237 = 708607) (by norm_num)
theorem B3361445 : Blo 1492066 3361445 := bbase (se 4 (by rfl) ⟨315135, by rfl⟩ : syracuseStep 3361445 = 630271) (by norm_num)
theorem B2239157 : Blo 1492066 2239157 := bbase (se 5 (by rfl) ⟨104960, by rfl⟩ : syracuseStep 2239157 = 209921) (by norm_num)
theorem B2239181 : Blo 1492066 2239181 := bbase (se 3 (by rfl) ⟨419846, by rfl⟩ : syracuseStep 2239181 = 839693) (by norm_num)
theorem B3025621 : Blo 1492066 3025621 := bbase (se 7 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 3025621 = 70913) (by norm_num)
theorem B2239205 : Blo 1492066 2239205 := bbase (se 4 (by rfl) ⟨209925, by rfl⟩ : syracuseStep 2239205 = 419851) (by norm_num)
theorem B3361517 : Blo 1492066 3361517 := bbase (se 3 (by rfl) ⟨630284, by rfl⟩ : syracuseStep 3361517 = 1260569) (by norm_num)
theorem B6056693 : Blo 1492066 6056693 := bbase (se 5 (by rfl) ⟨283907, by rfl⟩ : syracuseStep 6056693 = 567815) (by norm_num)
theorem B2239229 : Blo 1492066 2239229 := bbase (se 3 (by rfl) ⟨419855, by rfl⟩ : syracuseStep 2239229 = 839711) (by norm_num)
theorem B3025685 : Blo 1492066 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B2239253 : Blo 1492066 2239253 := bbase (se 6 (by rfl) ⟨52482, by rfl⟩ : syracuseStep 2239253 = 104965) (by norm_num)
theorem B8506133 : Blo 1492066 8506133 := bbase (se 6 (by rfl) ⟨199362, by rfl⟩ : syracuseStep 8506133 = 398725) (by norm_num)
theorem B2239277 : Blo 1492066 2239277 := bbase (se 3 (by rfl) ⟨419864, by rfl⟩ : syracuseStep 2239277 = 839729) (by norm_num)
theorem B6810421 : Blo 1492066 6810421 := bbase (se 5 (by rfl) ⟨319238, by rfl⟩ : syracuseStep 6810421 = 638477) (by norm_num)
theorem B3361589 : Blo 1492066 3361589 := bbase (se 5 (by rfl) ⟨157574, by rfl⟩ : syracuseStep 3361589 = 315149) (by norm_num)
theorem B2239301 : Blo 1492066 2239301 := bbase (se 4 (by rfl) ⟨209934, by rfl⟩ : syracuseStep 2239301 = 419869) (by norm_num)
theorem B2239325 : Blo 1492066 2239325 := bbase (se 3 (by rfl) ⟨419873, by rfl⟩ : syracuseStep 2239325 = 839747) (by norm_num)
theorem B2239349 : Blo 1492066 2239349 := bbase (se 5 (by rfl) ⟨104969, by rfl⟩ : syracuseStep 2239349 = 209939) (by norm_num)
theorem B4254581 : Blo 1492066 4254581 := bbase (se 5 (by rfl) ⟨199433, by rfl⟩ : syracuseStep 4254581 = 398867) (by norm_num)
theorem B2239373 : Blo 1492066 2239373 := bbase (se 3 (by rfl) ⟨419882, by rfl⟩ : syracuseStep 2239373 = 839765) (by norm_num)
theorem B2517925 : Blo 1492066 2517925 := bbase (se 4 (by rfl) ⟨236055, by rfl⟩ : syracuseStep 2517925 = 472111) (by norm_num)
theorem B2239397 : Blo 1492066 2239397 := bbase (se 4 (by rfl) ⟨209943, by rfl⟩ : syracuseStep 2239397 = 419887) (by norm_num)
theorem B5041061 : Blo 1492066 5041061 := bbase (se 4 (by rfl) ⟨472599, by rfl⟩ : syracuseStep 5041061 = 945199) (by norm_num)
theorem B2239421 : Blo 1492066 2239421 := bbase (se 3 (by rfl) ⟨419891, by rfl⟩ : syracuseStep 2239421 = 839783) (by norm_num)
theorem B3828685 : Blo 1492066 3828685 := bbase (se 3 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 3828685 = 1435757) (by norm_num)
theorem B2239445 : Blo 1492066 2239445 := bbase (se 7 (by rfl) ⟨26243, by rfl⟩ : syracuseStep 2239445 = 52487) (by norm_num)
theorem B2239469 : Blo 1492066 2239469 := bbase (se 3 (by rfl) ⟨419900, by rfl⟩ : syracuseStep 2239469 = 839801) (by norm_num)
theorem B2518013 : Blo 1492066 2518013 := bbase (se 3 (by rfl) ⟨472127, by rfl⟩ : syracuseStep 2518013 = 944255) (by norm_num)
theorem B3779581 : Blo 1492066 3779581 := bbase (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) (by norm_num)
theorem B2239493 : Blo 1492066 2239493 := bbase (se 4 (by rfl) ⟨209952, by rfl⟩ : syracuseStep 2239493 = 419905) (by norm_num)
theorem B2239517 : Blo 1492066 2239517 := bbase (se 3 (by rfl) ⟨419909, by rfl⟩ : syracuseStep 2239517 = 839819) (by norm_num)
theorem B2239541 : Blo 1492066 2239541 := bbase (se 5 (by rfl) ⟨104978, by rfl⟩ : syracuseStep 2239541 = 209957) (by norm_num)
theorem B7556165 : Blo 1492066 7556165 := bbase (se 4 (by rfl) ⟨708390, by rfl⟩ : syracuseStep 7556165 = 1416781) (by norm_num)
theorem B2239565 : Blo 1492066 2239565 := bbase (se 3 (by rfl) ⟨419918, by rfl⟩ : syracuseStep 2239565 = 839837) (by norm_num)
theorem B2124893 : Blo 1492066 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B2239589 : Blo 1492066 2239589 := bbase (se 4 (by rfl) ⟨209961, by rfl⟩ : syracuseStep 2239589 = 419923) (by norm_num)
theorem B4090981 : Blo 1492066 4090981 := bbase (se 4 (by rfl) ⟨383529, by rfl⟩ : syracuseStep 4090981 = 767059) (by norm_num)
theorem B3779693 : Blo 1492066 3779693 := bbase (se 3 (by rfl) ⟨708692, by rfl⟩ : syracuseStep 3779693 = 1417385) (by norm_num)
theorem B2518141 : Blo 1492066 2518141 := bbase (se 3 (by rfl) ⟨472151, by rfl⟩ : syracuseStep 2518141 = 944303) (by norm_num)
theorem B2239613 : Blo 1492066 2239613 := bbase (se 3 (by rfl) ⟨419927, by rfl⟩ : syracuseStep 2239613 = 839855) (by norm_num)
theorem B2239637 : Blo 1492066 2239637 := bbase (se 6 (by rfl) ⟨52491, by rfl⟩ : syracuseStep 2239637 = 104983) (by norm_num)
theorem B2239661 : Blo 1492066 2239661 := bbase (se 3 (by rfl) ⟨419936, by rfl⟩ : syracuseStep 2239661 = 839873) (by norm_num)
theorem B2239685 : Blo 1492066 2239685 := bbase (se 4 (by rfl) ⟨209970, by rfl⟩ : syracuseStep 2239685 = 419941) (by norm_num)
theorem B2518229 : Blo 1492066 2518229 := bbase (se 7 (by rfl) ⟨29510, by rfl⟩ : syracuseStep 2518229 = 59021) (by norm_num)
theorem B3230941 : Blo 1492066 3230941 := bbase (se 3 (by rfl) ⟨605801, by rfl⟩ : syracuseStep 3230941 = 1211603) (by norm_num)
theorem B2239709 : Blo 1492066 2239709 := bbase (se 3 (by rfl) ⟨419945, by rfl⟩ : syracuseStep 2239709 = 839891) (by norm_num)
theorem B2239733 : Blo 1492066 2239733 := bbase (se 5 (by rfl) ⟨104987, by rfl⟩ : syracuseStep 2239733 = 209975) (by norm_num)
theorem B3026173 : Blo 1492066 3026173 := bbase (se 3 (by rfl) ⟨567407, by rfl⟩ : syracuseStep 3026173 = 1134815) (by norm_num)
theorem B2239757 : Blo 1492066 2239757 := bbase (se 3 (by rfl) ⟨419954, by rfl⟩ : syracuseStep 2239757 = 839909) (by norm_num)
theorem B5672213 : Blo 1492066 5672213 := bbase (se 6 (by rfl) ⟨132942, by rfl⟩ : syracuseStep 5672213 = 265885) (by norm_num)
theorem B2239781 : Blo 1492066 2239781 := bbase (se 4 (by rfl) ⟨209979, by rfl⟩ : syracuseStep 2239781 = 419959) (by norm_num)
theorem B3779885 : Blo 1492066 3779885 := bbase (se 3 (by rfl) ⟨708728, by rfl⟩ : syracuseStep 3779885 = 1417457) (by norm_num)
theorem B2239805 : Blo 1492066 2239805 := bbase (se 3 (by rfl) ⟨419963, by rfl⟩ : syracuseStep 2239805 = 839927) (by norm_num)
theorem B2518357 : Blo 1492066 2518357 := bbase (se 11 (by rfl) ⟨1844, by rfl⟩ : syracuseStep 2518357 = 3689) (by norm_num)
theorem B2239829 : Blo 1492066 2239829 := bbase (se 11 (by rfl) ⟨1640, by rfl⟩ : syracuseStep 2239829 = 3281) (by norm_num)
theorem B5041493 : Blo 1492066 5041493 := bbase (se 11 (by rfl) ⟨3692, by rfl⟩ : syracuseStep 5041493 = 7385) (by norm_num)
theorem B2239853 : Blo 1492066 2239853 := bbase (se 3 (by rfl) ⟨419972, by rfl⟩ : syracuseStep 2239853 = 839945) (by norm_num)
theorem B2239877 : Blo 1492066 2239877 := bbase (se 4 (by rfl) ⟨209988, by rfl⟩ : syracuseStep 2239877 = 419977) (by norm_num)
theorem B2239901 : Blo 1492066 2239901 := bbase (se 3 (by rfl) ⟨419981, by rfl⟩ : syracuseStep 2239901 = 839963) (by norm_num)
theorem B2518445 : Blo 1492066 2518445 := bbase (se 3 (by rfl) ⟨472208, by rfl⟩ : syracuseStep 2518445 = 944417) (by norm_num)
theorem B2239925 : Blo 1492066 2239925 := bbase (se 5 (by rfl) ⟨104996, by rfl⟩ : syracuseStep 2239925 = 209993) (by norm_num)
theorem B2239949 : Blo 1492066 2239949 := bbase (se 3 (by rfl) ⟨419990, by rfl⟩ : syracuseStep 2239949 = 839981) (by norm_num)
theorem B2239973 : Blo 1492066 2239973 := bbase (se 4 (by rfl) ⟨209997, by rfl⟩ : syracuseStep 2239973 = 419995) (by norm_num)
theorem B2239997 : Blo 1492066 2239997 := bbase (se 3 (by rfl) ⟨419999, by rfl⟩ : syracuseStep 2239997 = 839999) (by norm_num)
theorem B2240021 : Blo 1492066 2240021 := bbase (se 6 (by rfl) ⟨52500, by rfl⟩ : syracuseStep 2240021 = 105001) (by norm_num)
theorem B2518573 : Blo 1492066 2518573 := bbase (se 3 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 2518573 = 944465) (by norm_num)
theorem B2240045 : Blo 1492066 2240045 := bbase (se 3 (by rfl) ⟨420008, by rfl⟩ : syracuseStep 2240045 = 840017) (by norm_num)
theorem B5672501 : Blo 1492066 5672501 := bbase (se 5 (by rfl) ⟨265898, by rfl⟩ : syracuseStep 5672501 = 531797) (by norm_num)
theorem B2240069 : Blo 1492066 2240069 := bbase (se 4 (by rfl) ⟨210006, by rfl⟩ : syracuseStep 2240069 = 420013) (by norm_num)
theorem B2240093 : Blo 1492066 2240093 := bbase (se 3 (by rfl) ⟨420017, by rfl⟩ : syracuseStep 2240093 = 840035) (by norm_num)
theorem B2240117 : Blo 1492066 2240117 := bbase (se 5 (by rfl) ⟨105005, by rfl⟩ : syracuseStep 2240117 = 210011) (by norm_num)
theorem B2518661 : Blo 1492066 2518661 := bbase (se 4 (by rfl) ⟨236124, by rfl⟩ : syracuseStep 2518661 = 472249) (by norm_num)
theorem B2125445 : Blo 1492066 2125445 := bbase (se 4 (by rfl) ⟨199260, by rfl⟩ : syracuseStep 2125445 = 398521) (by norm_num)
theorem B3780229 : Blo 1492066 3780229 := bbase (se 4 (by rfl) ⟨354396, by rfl⟩ : syracuseStep 3780229 = 708793) (by norm_num)
theorem B2240141 : Blo 1492066 2240141 := bbase (se 3 (by rfl) ⟨420026, by rfl⟩ : syracuseStep 2240141 = 840053) (by norm_num)
theorem B2240165 : Blo 1492066 2240165 := bbase (se 4 (by rfl) ⟨210015, by rfl⟩ : syracuseStep 2240165 = 420031) (by norm_num)
theorem B2240189 : Blo 1492066 2240189 := bbase (se 3 (by rfl) ⟨420035, by rfl⟩ : syracuseStep 2240189 = 840071) (by norm_num)
theorem B2240213 : Blo 1492066 2240213 := bbase (se 7 (by rfl) ⟨26252, by rfl⟩ : syracuseStep 2240213 = 52505) (by norm_num)
theorem B2240237 : Blo 1492066 2240237 := bbase (se 3 (by rfl) ⟨420044, by rfl⟩ : syracuseStep 2240237 = 840089) (by norm_num)
theorem B3780341 : Blo 1492066 3780341 := bbase (se 5 (by rfl) ⟨177203, by rfl⟩ : syracuseStep 3780341 = 354407) (by norm_num)
theorem B2518789 : Blo 1492066 2518789 := bbase (se 4 (by rfl) ⟨236136, by rfl⟩ : syracuseStep 2518789 = 472273) (by norm_num)
theorem B2240261 : Blo 1492066 2240261 := bbase (se 4 (by rfl) ⟨210024, by rfl⟩ : syracuseStep 2240261 = 420049) (by norm_num)
theorem B5041925 : Blo 1492066 5041925 := bbase (se 4 (by rfl) ⟨472680, by rfl⟩ : syracuseStep 5041925 = 945361) (by norm_num)
theorem B2240285 : Blo 1492066 2240285 := bbase (se 3 (by rfl) ⟨420053, by rfl⟩ : syracuseStep 2240285 = 840107) (by norm_num)
theorem B2240309 : Blo 1492066 2240309 := bbase (se 5 (by rfl) ⟨105014, by rfl⟩ : syracuseStep 2240309 = 210029) (by norm_num)
theorem B4542277 : Blo 1492066 4542277 := bbase (se 4 (by rfl) ⟨425838, by rfl⟩ : syracuseStep 4542277 = 851677) (by norm_num)
theorem B2240333 : Blo 1492066 2240333 := bbase (se 3 (by rfl) ⟨420062, by rfl⟩ : syracuseStep 2240333 = 840125) (by norm_num)
theorem B2518877 : Blo 1492066 2518877 := bbase (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) (by norm_num)
theorem B2240357 : Blo 1492066 2240357 := bbase (se 4 (by rfl) ⟨210033, by rfl⟩ : syracuseStep 2240357 = 420067) (by norm_num)
theorem B2240381 : Blo 1492066 2240381 := bbase (se 3 (by rfl) ⟨420071, by rfl⟩ : syracuseStep 2240381 = 840143) (by norm_num)
theorem B2240405 : Blo 1492066 2240405 := bbase (se 6 (by rfl) ⟨52509, by rfl⟩ : syracuseStep 2240405 = 105019) (by norm_num)
theorem B2240429 : Blo 1492066 2240429 := bbase (se 3 (by rfl) ⟨420080, by rfl⟩ : syracuseStep 2240429 = 840161) (by norm_num)
theorem B3780533 : Blo 1492066 3780533 := bbase (se 5 (by rfl) ⟨177212, by rfl⟩ : syracuseStep 3780533 = 354425) (by norm_num)
theorem B4599749 : Blo 1492066 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B6377413 : Blo 1492066 6377413 := bbase (se 4 (by rfl) ⟨597882, by rfl⟩ : syracuseStep 6377413 = 1195765) (by norm_num)
theorem B2240453 : Blo 1492066 2240453 := bbase (se 4 (by rfl) ⟨210042, by rfl⟩ : syracuseStep 2240453 = 420085) (by norm_num)
theorem B6377429 : Blo 1492066 6377429 := bbase (se 7 (by rfl) ⟨74735, by rfl⟩ : syracuseStep 6377429 = 149471) (by norm_num)
theorem B11341781 : Blo 1492066 11341781 := bbase (se 7 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 11341781 = 265823) (by norm_num)
theorem B2519005 : Blo 1492066 2519005 := bbase (se 3 (by rfl) ⟨472313, by rfl⟩ : syracuseStep 2519005 = 944627) (by norm_num)
theorem B2240477 : Blo 1492066 2240477 := bbase (se 3 (by rfl) ⟨420089, by rfl⟩ : syracuseStep 2240477 = 840179) (by norm_num)
theorem B3190765 : Blo 1492066 3190765 := bbase (se 3 (by rfl) ⟨598268, by rfl⟩ : syracuseStep 3190765 = 1196537) (by norm_num)
theorem B2240501 : Blo 1492066 2240501 := bbase (se 5 (by rfl) ⟨105023, by rfl⟩ : syracuseStep 2240501 = 210047) (by norm_num)
theorem B2240525 : Blo 1492066 2240525 := bbase (se 3 (by rfl) ⟨420098, by rfl⟩ : syracuseStep 2240525 = 840197) (by norm_num)
theorem B2240549 : Blo 1492066 2240549 := bbase (se 4 (by rfl) ⟨210051, by rfl⟩ : syracuseStep 2240549 = 420103) (by norm_num)
theorem B2519093 : Blo 1492066 2519093 := bbase (se 5 (by rfl) ⟨118082, by rfl⟩ : syracuseStep 2519093 = 236165) (by norm_num)
theorem B2240573 : Blo 1492066 2240573 := bbase (se 3 (by rfl) ⟨420107, by rfl⟩ : syracuseStep 2240573 = 840215) (by norm_num)
theorem B7270469 : Blo 1492066 7270469 := bbase (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) (by norm_num)
theorem B2240597 : Blo 1492066 2240597 := bbase (se 8 (by rfl) ⟨13128, by rfl⟩ : syracuseStep 2240597 = 26257) (by norm_num)
theorem B2240621 : Blo 1492066 2240621 := bbase (se 3 (by rfl) ⟨420116, by rfl⟩ : syracuseStep 2240621 = 840233) (by norm_num)
theorem B1593469 : Blo 1492066 1593469 := bbase (se 3 (by rfl) ⟨298775, by rfl⟩ : syracuseStep 1593469 = 597551) (by norm_num)
theorem B2240645 : Blo 1492066 2240645 := bbase (se 4 (by rfl) ⟨210060, by rfl⟩ : syracuseStep 2240645 = 420121) (by norm_num)
theorem B2240669 : Blo 1492066 2240669 := bbase (se 3 (by rfl) ⟨420125, by rfl⟩ : syracuseStep 2240669 = 840251) (by norm_num)
theorem B1888429 : Blo 1492066 1888429 := bbase (se 3 (by rfl) ⟨354080, by rfl⟩ : syracuseStep 1888429 = 708161) (by norm_num)
theorem B2519221 : Blo 1492066 2519221 := bbase (se 5 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 2519221 = 236177) (by norm_num)
theorem B2240693 : Blo 1492066 2240693 := bbase (se 5 (by rfl) ⟨105032, by rfl⟩ : syracuseStep 2240693 = 210065) (by norm_num)
theorem B5042357 : Blo 1492066 5042357 := bbase (se 5 (by rfl) ⟨236360, by rfl⟩ : syracuseStep 5042357 = 472721) (by norm_num)
theorem B2240717 : Blo 1492066 2240717 := bbase (se 3 (by rfl) ⟨420134, by rfl⟩ : syracuseStep 2240717 = 840269) (by norm_num)
theorem B2691301 : Blo 1492066 2691301 := bbase (se 4 (by rfl) ⟨252309, by rfl⟩ : syracuseStep 2691301 = 504619) (by norm_num)
theorem B2240741 : Blo 1492066 2240741 := bbase (se 4 (by rfl) ⟨210069, by rfl⟩ : syracuseStep 2240741 = 420139) (by norm_num)
theorem B2240765 : Blo 1492066 2240765 := bbase (se 3 (by rfl) ⟨420143, by rfl⟩ : syracuseStep 2240765 = 840287) (by norm_num)
theorem B1888525 : Blo 1492066 1888525 := bbase (se 3 (by rfl) ⟨354098, by rfl⟩ : syracuseStep 1888525 = 708197) (by norm_num)
theorem B2519309 : Blo 1492066 2519309 := bbase (se 3 (by rfl) ⟨472370, by rfl⟩ : syracuseStep 2519309 = 944741) (by norm_num)
theorem B3780877 : Blo 1492066 3780877 := bbase (se 3 (by rfl) ⟨708914, by rfl⟩ : syracuseStep 3780877 = 1417829) (by norm_num)
theorem B2240789 : Blo 1492066 2240789 := bbase (se 6 (by rfl) ⟨52518, by rfl⟩ : syracuseStep 2240789 = 105037) (by norm_num)
theorem B2240813 : Blo 1492066 2240813 := bbase (se 3 (by rfl) ⟨420152, by rfl⟩ : syracuseStep 2240813 = 840305) (by norm_num)
theorem B2240837 : Blo 1492066 2240837 := bbase (se 4 (by rfl) ⟨210078, by rfl⟩ : syracuseStep 2240837 = 420157) (by norm_num)
theorem B7557461 : Blo 1492066 7557461 := bbase (se 10 (by rfl) ⟨11070, by rfl⟩ : syracuseStep 7557461 = 22141) (by norm_num)
theorem B2240861 : Blo 1492066 2240861 := bbase (se 3 (by rfl) ⟨420161, by rfl⟩ : syracuseStep 2240861 = 840323) (by norm_num)
theorem B11334005 : Blo 1492066 11334005 := bbase (se 5 (by rfl) ⟨531281, by rfl⟩ : syracuseStep 11334005 = 1062563) (by norm_num)
theorem B2126197 : Blo 1492066 2126197 := bbase (se 5 (by rfl) ⟨99665, by rfl⟩ : syracuseStep 2126197 = 199331) (by norm_num)
theorem B2240885 : Blo 1492066 2240885 := bbase (se 5 (by rfl) ⟨105041, by rfl⟩ : syracuseStep 2240885 = 210083) (by norm_num)
theorem B3780989 : Blo 1492066 3780989 := bbase (se 3 (by rfl) ⟨708935, by rfl⟩ : syracuseStep 3780989 = 1417871) (by norm_num)
theorem B2519437 : Blo 1492066 2519437 := bbase (se 3 (by rfl) ⟨472394, by rfl⟩ : syracuseStep 2519437 = 944789) (by norm_num)
theorem B2240909 : Blo 1492066 2240909 := bbase (se 3 (by rfl) ⟨420170, by rfl⟩ : syracuseStep 2240909 = 840341) (by norm_num)
theorem B2240933 : Blo 1492066 2240933 := bbase (se 4 (by rfl) ⟨210087, by rfl⟩ : syracuseStep 2240933 = 420175) (by norm_num)
theorem B1888697 : Blo 1492066 1888697 := bbase (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) (by norm_num)
theorem B3027389 : Blo 1492066 3027389 := bbase (se 3 (by rfl) ⟨567635, by rfl⟩ : syracuseStep 3027389 = 1135271) (by norm_num)
theorem B2240957 : Blo 1492066 2240957 := bbase (se 3 (by rfl) ⟨420179, by rfl⟩ : syracuseStep 2240957 = 840359) (by norm_num)
theorem B2240981 : Blo 1492066 2240981 := bbase (se 7 (by rfl) ⟨26261, by rfl⟩ : syracuseStep 2240981 = 52523) (by norm_num)
theorem B2519525 : Blo 1492066 2519525 := bbase (se 4 (by rfl) ⟨236205, by rfl⟩ : syracuseStep 2519525 = 472411) (by norm_num)
theorem B2241005 : Blo 1492066 2241005 := bbase (se 3 (by rfl) ⟨420188, by rfl⟩ : syracuseStep 2241005 = 840377) (by norm_num)
theorem B1888753 : Blo 1492066 1888753 := bbase (se 2 (by rfl) ⟨708282, by rfl⟩ : syracuseStep 1888753 = 1416565) (by norm_num)
theorem B2241029 : Blo 1492066 2241029 := bbase (se 4 (by rfl) ⟨210096, by rfl⟩ : syracuseStep 2241029 = 420193) (by norm_num)
theorem B2241053 : Blo 1492066 2241053 := bbase (se 3 (by rfl) ⟨420197, by rfl⟩ : syracuseStep 2241053 = 840395) (by norm_num)
theorem B10768949 : Blo 1492066 10768949 := bbase (se 5 (by rfl) ⟨504794, by rfl⟩ : syracuseStep 10768949 = 1009589) (by norm_num)
theorem B2241077 : Blo 1492066 2241077 := bbase (se 5 (by rfl) ⟨105050, by rfl⟩ : syracuseStep 2241077 = 210101) (by norm_num)
theorem B3781181 : Blo 1492066 3781181 := bbase (se 3 (by rfl) ⟨708971, by rfl⟩ : syracuseStep 3781181 = 1417943) (by norm_num)
theorem B1888849 : Blo 1492066 1888849 := bbase (se 2 (by rfl) ⟨708318, by rfl⟩ : syracuseStep 1888849 = 1416637) (by norm_num)
theorem B2519653 : Blo 1492066 2519653 := bbase (se 4 (by rfl) ⟨236217, by rfl⟩ : syracuseStep 2519653 = 472435) (by norm_num)
theorem B2552485 : Blo 1492066 2552485 := bbase (se 4 (by rfl) ⟨239295, by rfl⟩ : syracuseStep 2552485 = 478591) (by norm_num)
theorem B2519741 : Blo 1492066 2519741 := bbase (se 3 (by rfl) ⟨472451, by rfl⟩ : syracuseStep 2519741 = 944903) (by norm_num)
theorem B4780741 : Blo 1492066 4780741 := bbase (se 4 (by rfl) ⟨448194, by rfl⟩ : syracuseStep 4780741 = 896389) (by norm_num)
theorem B1889021 : Blo 1492066 1889021 := bbase (se 3 (by rfl) ⟨354191, by rfl⟩ : syracuseStep 1889021 = 708383) (by norm_num)
theorem B1889077 : Blo 1492066 1889077 := bbase (se 5 (by rfl) ⟨88550, by rfl⟩ : syracuseStep 1889077 = 177101) (by norm_num)
theorem B4543285 : Blo 1492066 4543285 := bbase (se 5 (by rfl) ⟨212966, by rfl⟩ : syracuseStep 4543285 = 425933) (by norm_num)
theorem B2519869 : Blo 1492066 2519869 := bbase (se 3 (by rfl) ⟨472475, by rfl⟩ : syracuseStep 2519869 = 944951) (by norm_num)
theorem B1889173 : Blo 1492066 1889173 := bbase (se 6 (by rfl) ⟨44277, by rfl⟩ : syracuseStep 1889173 = 88555) (by norm_num)
theorem B3404693 : Blo 1492066 3404693 := bbase (se 6 (by rfl) ⟨79797, by rfl⟩ : syracuseStep 3404693 = 159595) (by norm_num)
theorem B2519957 : Blo 1492066 2519957 := bbase (se 6 (by rfl) ⟨59061, by rfl⟩ : syracuseStep 2519957 = 118123) (by norm_num)
theorem B3781525 : Blo 1492066 3781525 := bbase (se 6 (by rfl) ⟨88629, by rfl⟩ : syracuseStep 3781525 = 177259) (by norm_num)
theorem B1594289 : Blo 1492066 1594289 := bbase (se 2 (by rfl) ⟨597858, by rfl⟩ : syracuseStep 1594289 = 1195717) (by norm_num)
theorem B8508341 : Blo 1492066 8508341 := bbase (se 5 (by rfl) ⟨398828, by rfl⟩ : syracuseStep 8508341 = 797657) (by norm_num)
theorem B2552813 : Blo 1492066 2552813 := bbase (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) (by norm_num)
theorem B3781637 : Blo 1492066 3781637 := bbase (se 4 (by rfl) ⟨354528, by rfl⟩ : syracuseStep 3781637 = 709057) (by norm_num)
theorem B2692109 : Blo 1492066 2692109 := bbase (se 3 (by rfl) ⟨504770, by rfl⟩ : syracuseStep 2692109 = 1009541) (by norm_num)
theorem B3453965 : Blo 1492066 3453965 := bbase (se 3 (by rfl) ⟨647618, by rfl⟩ : syracuseStep 3453965 = 1295237) (by norm_num)
theorem B2520085 : Blo 1492066 2520085 := bbase (se 6 (by rfl) ⟨59064, by rfl⟩ : syracuseStep 2520085 = 118129) (by norm_num)
theorem B3027989 : Blo 1492066 3027989 := bbase (se 6 (by rfl) ⟨70968, by rfl⟩ : syracuseStep 3027989 = 141937) (by norm_num)
theorem B1889345 : Blo 1492066 1889345 := bbase (se 2 (by rfl) ⟨708504, by rfl⟩ : syracuseStep 1889345 = 1417009) (by norm_num)
theorem B19141717 : Blo 1492066 19141717 := bbase (se 8 (by rfl) ⟨112158, by rfl⟩ : syracuseStep 19141717 = 224317) (by norm_num)
theorem B2520173 : Blo 1492066 2520173 := bbase (se 3 (by rfl) ⟨472532, by rfl⟩ : syracuseStep 2520173 = 945065) (by norm_num)
theorem B5665909 : Blo 1492066 5665909 := bbase (se 5 (by rfl) ⟨265589, by rfl⟩ : syracuseStep 5665909 = 531179) (by norm_num)
theorem B1889401 : Blo 1492066 1889401 := bbase (se 2 (by rfl) ⟨708525, by rfl⟩ : syracuseStep 1889401 = 1417051) (by norm_num)
theorem B2126989 : Blo 1492066 2126989 := bbase (se 3 (by rfl) ⟨398810, by rfl⟩ : syracuseStep 2126989 = 797621) (by norm_num)
theorem B6050981 : Blo 1492066 6050981 := bbase (se 4 (by rfl) ⟨567279, by rfl⟩ : syracuseStep 6050981 = 1134559) (by norm_num)
theorem B2553005 : Blo 1492066 2553005 := bbase (se 3 (by rfl) ⟨478688, by rfl⟩ : syracuseStep 2553005 = 957377) (by norm_num)
theorem B3781829 : Blo 1492066 3781829 := bbase (se 4 (by rfl) ⟨354546, by rfl⟩ : syracuseStep 3781829 = 709093) (by norm_num)
theorem B1889497 : Blo 1492066 1889497 := bbase (se 2 (by rfl) ⟨708561, by rfl⟩ : syracuseStep 1889497 = 1417123) (by norm_num)
theorem B7656677 : Blo 1492066 7656677 := bbase (se 4 (by rfl) ⟨717813, by rfl⟩ : syracuseStep 7656677 = 1435627) (by norm_num)
theorem B2520301 : Blo 1492066 2520301 := bbase (se 3 (by rfl) ⟨472556, by rfl⟩ : syracuseStep 2520301 = 945113) (by norm_num)
theorem B1512713 : Blo 1492066 1512713 := bbase (se 2 (by rfl) ⟨567267, by rfl⟩ : syracuseStep 1512713 = 1134535) (by norm_num)
theorem B2553101 : Blo 1492066 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B3585325 : Blo 1492066 3585325 := bbase (se 3 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 3585325 = 1344497) (by norm_num)
theorem B2520389 : Blo 1492066 2520389 := bbase (se 4 (by rfl) ⟨236286, by rfl⟩ : syracuseStep 2520389 = 472573) (by norm_num)
theorem B1594733 : Blo 1492066 1594733 := bbase (se 3 (by rfl) ⟨299012, by rfl⟩ : syracuseStep 1594733 = 598025) (by norm_num)
theorem B1889669 : Blo 1492066 1889669 := bbase (se 4 (by rfl) ⟨177156, by rfl⟩ : syracuseStep 1889669 = 354313) (by norm_num)
theorem B5666213 : Blo 1492066 5666213 := bbase (se 4 (by rfl) ⟨531207, by rfl⟩ : syracuseStep 5666213 = 1062415) (by norm_num)
theorem B1889725 : Blo 1492066 1889725 := bbase (se 3 (by rfl) ⟨354323, by rfl⟩ : syracuseStep 1889725 = 708647) (by norm_num)
theorem B2520517 : Blo 1492066 2520517 := bbase (se 4 (by rfl) ⟨236298, by rfl⟩ : syracuseStep 2520517 = 472597) (by norm_num)
theorem B1889821 : Blo 1492066 1889821 := bbase (se 3 (by rfl) ⟨354341, by rfl⟩ : syracuseStep 1889821 = 708683) (by norm_num)
theorem B2520605 : Blo 1492066 2520605 := bbase (se 3 (by rfl) ⟨472613, by rfl⟩ : syracuseStep 2520605 = 945227) (by norm_num)
theorem B7558757 : Blo 1492066 7558757 := bbase (se 4 (by rfl) ⟨708633, by rfl⟩ : syracuseStep 7558757 = 1417267) (by norm_num)
theorem B1594981 : Blo 1492066 1594981 := bbase (se 4 (by rfl) ⟨149529, by rfl⟩ : syracuseStep 1594981 = 299059) (by norm_num)
theorem B4249205 : Blo 1492066 4249205 := bbase (se 5 (by rfl) ⟨199181, by rfl⟩ : syracuseStep 4249205 = 398363) (by norm_num)
theorem B2520733 : Blo 1492066 2520733 := bbase (se 3 (by rfl) ⟨472637, by rfl⟩ : syracuseStep 2520733 = 945275) (by norm_num)
theorem B1889993 : Blo 1492066 1889993 := bbase (se 2 (by rfl) ⟨708747, by rfl⟩ : syracuseStep 1889993 = 1417495) (by norm_num)
theorem B13801205 : Blo 1492066 13801205 := bbase (se 5 (by rfl) ⟨646931, by rfl⟩ : syracuseStep 13801205 = 1293863) (by norm_num)
theorem B2520821 : Blo 1492066 2520821 := bbase (se 5 (by rfl) ⟨118163, by rfl⟩ : syracuseStep 2520821 = 236327) (by norm_num)
theorem B1890049 : Blo 1492066 1890049 := bbase (se 2 (by rfl) ⟨708768, by rfl⟩ : syracuseStep 1890049 = 1417537) (by norm_num)
theorem B1701653 : Blo 1492066 1701653 := bbase (se 6 (by rfl) ⟨39882, by rfl⟩ : syracuseStep 1701653 = 79765) (by norm_num)
theorem B1890145 : Blo 1492066 1890145 := bbase (se 2 (by rfl) ⟨708804, by rfl⟩ : syracuseStep 1890145 = 1417609) (by norm_num)
theorem B5035877 : Blo 1492066 5035877 := bbase (se 4 (by rfl) ⟨472113, by rfl⟩ : syracuseStep 5035877 = 944227) (by norm_num)
theorem B2520949 : Blo 1492066 2520949 := bbase (se 5 (by rfl) ⟨118169, by rfl⟩ : syracuseStep 2520949 = 236339) (by norm_num)
theorem B3233677 : Blo 1492066 3233677 := bbase (se 3 (by rfl) ⟨606314, by rfl⟩ : syracuseStep 3233677 = 1212629) (by norm_num)
theorem B3585941 : Blo 1492066 3585941 := bbase (se 6 (by rfl) ⟨84045, by rfl⟩ : syracuseStep 3585941 = 168091) (by norm_num)
theorem B2521037 : Blo 1492066 2521037 := bbase (se 3 (by rfl) ⟨472694, by rfl⟩ : syracuseStep 2521037 = 945389) (by norm_num)
theorem B1890317 : Blo 1492066 1890317 := bbase (se 3 (by rfl) ⟨354434, by rfl⟩ : syracuseStep 1890317 = 708869) (by norm_num)
theorem B8075285 : Blo 1492066 8075285 := bbase (se 6 (by rfl) ⟨189264, by rfl⟩ : syracuseStep 8075285 = 378529) (by norm_num)
theorem B1595413 : Blo 1492066 1595413 := bbase (se 6 (by rfl) ⟨37392, by rfl⟩ : syracuseStep 1595413 = 74785) (by norm_num)
theorem B1890373 : Blo 1492066 1890373 := bbase (se 4 (by rfl) ⟨177222, by rfl⟩ : syracuseStep 1890373 = 354445) (by norm_num)
theorem B2521165 : Blo 1492066 2521165 := bbase (se 3 (by rfl) ⟨472718, by rfl⟩ : syracuseStep 2521165 = 945437) (by norm_num)
theorem B5380181 : Blo 1492066 5380181 := bbase (se 8 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 5380181 = 63049) (by norm_num)
theorem B6379685 : Blo 1492066 6379685 := bbase (se 4 (by rfl) ⟨598095, by rfl⟩ : syracuseStep 6379685 = 1196191) (by norm_num)
theorem B1890469 : Blo 1492066 1890469 := bbase (se 4 (by rfl) ⟨177231, by rfl⟩ : syracuseStep 1890469 = 354463) (by norm_num)
theorem B5036309 : Blo 1492066 5036309 := bbase (se 6 (by rfl) ⟨118038, by rfl⟩ : syracuseStep 5036309 = 236077) (by norm_num)
theorem B3586373 : Blo 1492066 3586373 := bbase (se 4 (by rfl) ⟨336222, by rfl⟩ : syracuseStep 3586373 = 672445) (by norm_num)
theorem B1890641 : Blo 1492066 1890641 := bbase (se 2 (by rfl) ⟨708990, by rfl⟩ : syracuseStep 1890641 = 1417981) (by norm_num)
theorem B2390357 : Blo 1492066 2390357 := bbase (se 10 (by rfl) ⟨3501, by rfl⟩ : syracuseStep 2390357 = 7003) (by norm_num)
theorem B1890697 : Blo 1492066 1890697 := bbase (se 2 (by rfl) ⟨709011, by rfl⟩ : syracuseStep 1890697 = 1418023) (by norm_num)
theorem B1890793 : Blo 1492066 1890793 := bbase (se 2 (by rfl) ⟨709047, by rfl⟩ : syracuseStep 1890793 = 1418095) (by norm_num)
theorem B3357197 : Blo 1492066 3357197 := bbase (se 3 (by rfl) ⟨629474, by rfl⟩ : syracuseStep 3357197 = 1258949) (by norm_num)
theorem B1792537 : Blo 1492066 1792537 := bbase (se 2 (by rfl) ⟨672201, by rfl⟩ : syracuseStep 1792537 = 1344403) (by norm_num)
theorem B2873885 : Blo 1492066 2873885 := bbase (se 3 (by rfl) ⟨538853, by rfl⟩ : syracuseStep 2873885 = 1077707) (by norm_num)
theorem B3357269 : Blo 1492066 3357269 := bbase (se 8 (by rfl) ⟨19671, by rfl⟩ : syracuseStep 3357269 = 39343) (by norm_num)
theorem B1915493 : Blo 1492066 1915493 := bbase (se 4 (by rfl) ⟨179577, by rfl⟩ : syracuseStep 1915493 = 359155) (by norm_num)
theorem B1514137 : Blo 1492066 1514137 := bbase (se 2 (by rfl) ⟨567801, by rfl⟩ : syracuseStep 1514137 = 1135603) (by norm_num)
theorem B3357341 : Blo 1492066 3357341 := bbase (se 3 (by rfl) ⟨629501, by rfl⟩ : syracuseStep 3357341 = 1259003) (by norm_num)
theorem B2833069 : Blo 1492066 2833069 := bbase (se 3 (by rfl) ⟨531200, by rfl⟩ : syracuseStep 2833069 = 1062401) (by norm_num)
theorem B10902197 : Blo 1492066 10902197 := bbase (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) (by norm_num)
theorem B5036741 : Blo 1492066 5036741 := bbase (se 4 (by rfl) ⟨472194, by rfl⟩ : syracuseStep 5036741 = 944389) (by norm_num)
theorem B3357413 : Blo 1492066 3357413 := bbase (se 4 (by rfl) ⟨314757, by rfl⟩ : syracuseStep 3357413 = 629515) (by norm_num)
theorem B12114677 : Blo 1492066 12114677 := bbase (se 5 (by rfl) ⟨567875, by rfl⟩ : syracuseStep 12114677 = 1135751) (by norm_num)
theorem B4250389 : Blo 1492066 4250389 := bbase (se 6 (by rfl) ⟨99618, by rfl⟩ : syracuseStep 4250389 = 199237) (by norm_num)
theorem B2390813 : Blo 1492066 2390813 := bbase (se 3 (by rfl) ⟨448277, by rfl⟩ : syracuseStep 2390813 = 896555) (by norm_num)
theorem B3357485 : Blo 1492066 3357485 := bbase (se 3 (by rfl) ⟨629528, by rfl⟩ : syracuseStep 3357485 = 1259057) (by norm_num)
theorem B2833213 : Blo 1492066 2833213 := bbase (se 3 (by rfl) ⟨531227, by rfl⟩ : syracuseStep 2833213 = 1062455) (by norm_num)
theorem B8624981 : Blo 1492066 8624981 := bbase (se 9 (by rfl) ⟨25268, by rfl⟩ : syracuseStep 8624981 = 50537) (by norm_num)
theorem B3357557 : Blo 1492066 3357557 := bbase (se 5 (by rfl) ⟨157385, by rfl⟩ : syracuseStep 3357557 = 314771) (by norm_num)
theorem B7560053 : Blo 1492066 7560053 := bbase (se 5 (by rfl) ⟨354377, by rfl⟩ : syracuseStep 7560053 = 708755) (by norm_num)
theorem B5110661 : Blo 1492066 5110661 := bbase (se 4 (by rfl) ⟨479124, by rfl⟩ : syracuseStep 5110661 = 958249) (by norm_num)
theorem B4250549 : Blo 1492066 4250549 := bbase (se 5 (by rfl) ⟨199244, by rfl⟩ : syracuseStep 4250549 = 398489) (by norm_num)
theorem B3586997 : Blo 1492066 3586997 := bbase (se 5 (by rfl) ⟨168140, by rfl⟩ : syracuseStep 3586997 = 336281) (by norm_num)
theorem B3357629 : Blo 1492066 3357629 := bbase (se 3 (by rfl) ⟨629555, by rfl⟩ : syracuseStep 3357629 = 1259111) (by norm_num)
theorem B2833373 : Blo 1492066 2833373 := bbase (se 3 (by rfl) ⟨531257, by rfl⟩ : syracuseStep 2833373 = 1062515) (by norm_num)
theorem B3357701 : Blo 1492066 3357701 := bbase (se 4 (by rfl) ⟨314784, by rfl⟩ : syracuseStep 3357701 = 629569) (by norm_num)
theorem B3357773 : Blo 1492066 3357773 := bbase (se 3 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 3357773 = 1259165) (by norm_num)
theorem B2833517 : Blo 1492066 2833517 := bbase (se 3 (by rfl) ⟨531284, by rfl⟩ : syracuseStep 2833517 = 1062569) (by norm_num)
theorem B5037173 : Blo 1492066 5037173 := bbase (se 5 (by rfl) ⟨236117, by rfl⟩ : syracuseStep 5037173 = 472235) (by norm_num)
theorem B12754037 : Blo 1492066 12754037 := bbase (se 5 (by rfl) ⟨597845, by rfl⟩ : syracuseStep 12754037 = 1195691) (by norm_num)
theorem B3832957 : Blo 1492066 3832957 := bbase (se 3 (by rfl) ⟨718679, by rfl⟩ : syracuseStep 3832957 = 1437359) (by norm_num)
theorem B3357845 : Blo 1492066 3357845 := bbase (se 6 (by rfl) ⟨78699, by rfl⟩ : syracuseStep 3357845 = 157399) (by norm_num)
theorem B4250789 : Blo 1492066 4250789 := bbase (se 4 (by rfl) ⟨398511, by rfl⟩ : syracuseStep 4250789 = 797023) (by norm_num)
theorem B3357917 : Blo 1492066 3357917 := bbase (se 3 (by rfl) ⟨629609, by rfl⟩ : syracuseStep 3357917 = 1259219) (by norm_num)
theorem B6053093 : Blo 1492066 6053093 := bbase (se 4 (by rfl) ⟨567477, by rfl⟩ : syracuseStep 6053093 = 1134955) (by norm_num)
theorem B1678585 : Blo 1492066 1678585 := bbase (se 2 (by rfl) ⟨629469, by rfl⟩ : syracuseStep 1678585 = 1258939) (by norm_num)
theorem B1678621 : Blo 1492066 1678621 := bbase (se 3 (by rfl) ⟨314741, by rfl⟩ : syracuseStep 1678621 = 629483) (by norm_num)
theorem B3357989 : Blo 1492066 3357989 := bbase (se 4 (by rfl) ⟨314811, by rfl⟩ : syracuseStep 3357989 = 629623) (by norm_num)
theorem B2424109 : Blo 1492066 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B1678657 : Blo 1492066 1678657 := bbase (se 2 (by rfl) ⟨629496, by rfl⟩ : syracuseStep 1678657 = 1258993) (by norm_num)
theorem B1817929 : Blo 1492066 1817929 := bbase (se 2 (by rfl) ⟨681723, by rfl⟩ : syracuseStep 1817929 = 1363447) (by norm_num)
theorem B1678693 : Blo 1492066 1678693 := bbase (se 4 (by rfl) ⟨157377, by rfl⟩ : syracuseStep 1678693 = 314755) (by norm_num)
theorem B4250981 : Blo 1492066 4250981 := bbase (se 4 (by rfl) ⟨398529, by rfl⟩ : syracuseStep 4250981 = 797059) (by norm_num)
theorem B3358061 : Blo 1492066 3358061 := bbase (se 3 (by rfl) ⟨629636, by rfl⟩ : syracuseStep 3358061 = 1259273) (by norm_num)
theorem B1678729 : Blo 1492066 1678729 := bbase (se 2 (by rfl) ⟨629523, by rfl⟩ : syracuseStep 1678729 = 1259047) (by norm_num)
theorem B2833805 : Blo 1492066 2833805 := bbase (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) (by norm_num)
theorem B1793441 : Blo 1492066 1793441 := bbase (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) (by norm_num)
theorem B1678765 : Blo 1492066 1678765 := bbase (se 3 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 1678765 = 629537) (by norm_num)
theorem B3358133 : Blo 1492066 3358133 := bbase (se 5 (by rfl) ⟨157412, by rfl⟩ : syracuseStep 3358133 = 314825) (by norm_num)
theorem B1678801 : Blo 1492066 1678801 := bbase (se 2 (by rfl) ⟨629550, by rfl⟩ : syracuseStep 1678801 = 1259101) (by norm_num)
theorem B5668325 : Blo 1492066 5668325 := bbase (se 4 (by rfl) ⟨531405, by rfl⟩ : syracuseStep 5668325 = 1062811) (by norm_num)
theorem B1678837 : Blo 1492066 1678837 := bbase (se 5 (by rfl) ⟨78695, by rfl⟩ : syracuseStep 1678837 = 157391) (by norm_num)
theorem B3358205 : Blo 1492066 3358205 := bbase (se 3 (by rfl) ⟨629663, by rfl⟩ : syracuseStep 3358205 = 1259327) (by norm_num)
theorem B4783637 : Blo 1492066 4783637 := bbase (se 6 (by rfl) ⟨112116, by rfl⟩ : syracuseStep 4783637 = 224233) (by norm_num)
theorem B1678873 : Blo 1492066 1678873 := bbase (se 2 (by rfl) ⟨629577, by rfl⟩ : syracuseStep 1678873 = 1259155) (by norm_num)
theorem B5037605 : Blo 1492066 5037605 := bbase (se 4 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 5037605 = 944551) (by norm_num)
theorem B2833957 : Blo 1492066 2833957 := bbase (se 4 (by rfl) ⟨265683, by rfl⟩ : syracuseStep 2833957 = 531367) (by norm_num)
theorem B1678909 : Blo 1492066 1678909 := bbase (se 3 (by rfl) ⟨314795, by rfl⟩ : syracuseStep 1678909 = 629591) (by norm_num)
theorem B3358277 : Blo 1492066 3358277 := bbase (se 4 (by rfl) ⟨314838, by rfl⟩ : syracuseStep 3358277 = 629677) (by norm_num)
theorem B1678945 : Blo 1492066 1678945 := bbase (se 2 (by rfl) ⟨629604, by rfl⟩ : syracuseStep 1678945 = 1259209) (by norm_num)
theorem B1678981 : Blo 1492066 1678981 := bbase (se 4 (by rfl) ⟨157404, by rfl⟩ : syracuseStep 1678981 = 314809) (by norm_num)
theorem B3358349 : Blo 1492066 3358349 := bbase (se 3 (by rfl) ⟨629690, by rfl⟩ : syracuseStep 3358349 = 1259381) (by norm_num)
theorem B1793701 : Blo 1492066 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B1679017 : Blo 1492066 1679017 := bbase (se 2 (by rfl) ⟨629631, by rfl⟩ : syracuseStep 1679017 = 1259263) (by norm_num)
theorem B8502965 : Blo 1492066 8502965 := bbase (se 5 (by rfl) ⟨398576, by rfl⟩ : syracuseStep 8502965 = 797153) (by norm_num)
theorem B1679053 : Blo 1492066 1679053 := bbase (se 3 (by rfl) ⟨314822, by rfl⟩ : syracuseStep 1679053 = 629645) (by norm_num)
theorem B3358421 : Blo 1492066 3358421 := bbase (se 7 (by rfl) ⟨39356, by rfl⟩ : syracuseStep 3358421 = 78713) (by norm_num)
theorem B1679089 : Blo 1492066 1679089 := bbase (se 2 (by rfl) ⟨629658, by rfl⟩ : syracuseStep 1679089 = 1259317) (by norm_num)
theorem B9567989 : Blo 1492066 9567989 := bbase (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) (by norm_num)
theorem B4849397 : Blo 1492066 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B5668613 : Blo 1492066 5668613 := bbase (se 4 (by rfl) ⟨531432, by rfl⟩ : syracuseStep 5668613 = 1062865) (by norm_num)
theorem B1679125 : Blo 1492066 1679125 := bbase (se 6 (by rfl) ⟨39354, by rfl⟩ : syracuseStep 1679125 = 78709) (by norm_num)
theorem B3358493 : Blo 1492066 3358493 := bbase (se 3 (by rfl) ⟨629717, by rfl⟩ : syracuseStep 3358493 = 1259435) (by norm_num)
theorem B1679161 : Blo 1492066 1679161 := bbase (se 2 (by rfl) ⟨629685, by rfl⟩ : syracuseStep 1679161 = 1259371) (by norm_num)
theorem B2834261 : Blo 1492066 2834261 := bbase (se 9 (by rfl) ⟨8303, by rfl⟩ : syracuseStep 2834261 = 16607) (by norm_num)
theorem B1679197 : Blo 1492066 1679197 := bbase (se 3 (by rfl) ⟨314849, by rfl⟩ : syracuseStep 1679197 = 629699) (by norm_num)
theorem B3358565 : Blo 1492066 3358565 := bbase (se 4 (by rfl) ⟨314865, by rfl⟩ : syracuseStep 3358565 = 629731) (by norm_num)
theorem B1793893 : Blo 1492066 1793893 := bbase (se 4 (by rfl) ⟨168177, by rfl⟩ : syracuseStep 1793893 = 336355) (by norm_num)
theorem B1793917 : Blo 1492066 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B1679233 : Blo 1492066 1679233 := bbase (se 2 (by rfl) ⟨629712, by rfl⟩ : syracuseStep 1679233 = 1259425) (by norm_num)
theorem B1793921 : Blo 1492066 1793921 := bbase (se 2 (by rfl) ⟨672720, by rfl⟩ : syracuseStep 1793921 = 1345441) (by norm_num)
theorem B1679269 : Blo 1492066 1679269 := bbase (se 4 (by rfl) ⟨157431, by rfl⟩ : syracuseStep 1679269 = 314863) (by norm_num)
theorem B3358637 : Blo 1492066 3358637 := bbase (se 3 (by rfl) ⟨629744, by rfl⟩ : syracuseStep 3358637 = 1259489) (by norm_num)
theorem B1679305 : Blo 1492066 1679305 := bbase (se 2 (by rfl) ⟨629739, by rfl⟩ : syracuseStep 1679305 = 1259479) (by norm_num)
theorem B5038037 : Blo 1492066 5038037 := bbase (se 7 (by rfl) ⟨59039, by rfl⟩ : syracuseStep 5038037 = 118079) (by norm_num)
theorem B1679341 : Blo 1492066 1679341 := bbase (se 3 (by rfl) ⟨314876, by rfl⟩ : syracuseStep 1679341 = 629753) (by norm_num)
theorem B3358709 : Blo 1492066 3358709 := bbase (se 5 (by rfl) ⟨157439, by rfl⟩ : syracuseStep 3358709 = 314879) (by norm_num)
theorem B4251665 : Blo 1492066 4251665 := bstep (se 2 (by rfl) ⟨1594374, by rfl⟩ : syracuseStep 4251665 = 3188749) B3188749
theorem B1679395 : Blo 1492066 1679395 := bstep (se 1 (by rfl) ⟨1259546, by rfl⟩ : syracuseStep 1679395 = 2519093) B2519093
theorem B3588227 : Blo 1492066 3588227 := bstep (se 1 (by rfl) ⟨2691170, by rfl⟩ : syracuseStep 3588227 = 5382341) B5382341
theorem B9560197 : Blo 1492066 9560197 := bstep (se 4 (by rfl) ⟨896268, by rfl⟩ : syracuseStep 9560197 = 1792537) B1792537
theorem B4784291 : Blo 1492066 4784291 := bstep (se 1 (by rfl) ⟨3588218, by rfl⟩ : syracuseStep 4784291 = 7176437) B7176437
theorem B5038253 : Blo 1492066 5038253 := bstep (se 3 (by rfl) ⟨944672, by rfl⟩ : syracuseStep 5038253 = 1889345) B1889345
theorem B1679539 : Blo 1492066 1679539 := bstep (se 1 (by rfl) ⟨1259654, by rfl⟩ : syracuseStep 1679539 = 2519309) B2519309
theorem B5038307 : Blo 1492066 5038307 := bstep (se 1 (by rfl) ⟨3778730, by rfl⟩ : syracuseStep 5038307 = 7557461) B7557461
theorem B3358961 : Blo 1492066 3358961 := bstep (se 2 (by rfl) ⟨1259610, by rfl⟩ : syracuseStep 3358961 = 2519221) B2519221
theorem B3358979 : Blo 1492066 3358979 := bstep (se 1 (by rfl) ⟨2519234, by rfl⟩ : syracuseStep 3358979 = 5038469) B5038469
theorem B3588401 : Blo 1492066 3588401 := bstep (se 2 (by rfl) ⟨1345650, by rfl⟩ : syracuseStep 3588401 = 2691301) B2691301
theorem B2425153 : Blo 1492066 2425153 := bstep (se 2 (by rfl) ⟨909432, by rfl⟩ : syracuseStep 2425153 = 1818865) B1818865
theorem B1679683 : Blo 1492066 1679683 := bstep (se 1 (by rfl) ⟨1259762, by rfl⟩ : syracuseStep 1679683 = 2519525) B2519525
theorem B3588419 : Blo 1492066 3588419 := bstep (se 1 (by rfl) ⟨2691314, by rfl⟩ : syracuseStep 3588419 = 5382629) B5382629
theorem B2589059 : Blo 1492066 2589059 := bstep (se 1 (by rfl) ⟨1941794, by rfl⟩ : syracuseStep 2589059 = 3883589) B3883589
theorem B5669297 : Blo 1492066 5669297 := bstep (se 2 (by rfl) ⟨2125986, by rfl⟩ : syracuseStep 5669297 = 4251973) B4251973
theorem B6808013 : Blo 1492066 6808013 := bstep (se 3 (by rfl) ⟨1276502, by rfl⟩ : syracuseStep 6808013 = 2553005) B2553005
theorem B1679827 : Blo 1492066 1679827 := bstep (se 1 (by rfl) ⟨1259870, by rfl⟩ : syracuseStep 1679827 = 2519741) B2519741
theorem B5177837 : Blo 1492066 5177837 := bstep (se 3 (by rfl) ⟨970844, by rfl⟩ : syracuseStep 5177837 = 1941689) B1941689
theorem B5038577 : Blo 1492066 5038577 := bstep (se 2 (by rfl) ⟨1889466, by rfl⟩ : syracuseStep 5038577 = 3778933) B3778933
theorem B2834929 : Blo 1492066 2834929 := bstep (se 2 (by rfl) ⟨1063098, by rfl⟩ : syracuseStep 2834929 = 2126197) B2126197
theorem B2392561 : Blo 1492066 2392561 := bstep (se 2 (by rfl) ⟨897210, by rfl⟩ : syracuseStep 2392561 = 1794421) B1794421
theorem B3359249 : Blo 1492066 3359249 := bstep (se 2 (by rfl) ⟨1259718, by rfl⟩ : syracuseStep 3359249 = 2519437) B2519437
theorem B3359267 : Blo 1492066 3359267 := bstep (se 1 (by rfl) ⟨2519450, by rfl⟩ : syracuseStep 3359267 = 5038901) B5038901
theorem B2269795 : Blo 1492066 2269795 := bstep (se 1 (by rfl) ⟨1702346, by rfl⟩ : syracuseStep 2269795 = 3404693) B3404693
theorem B1679971 : Blo 1492066 1679971 := bstep (se 1 (by rfl) ⟨1259978, by rfl⟩ : syracuseStep 1679971 = 2519957) B2519957
theorem B3687043 : Blo 1492066 3687043 := bstep (se 1 (by rfl) ⟨2765282, by rfl⟩ : syracuseStep 3687043 = 5530565) B5530565
theorem B4981421 : Blo 1492066 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B1794739 : Blo 1492066 1794739 := bstep (se 1 (by rfl) ⟨1346054, by rfl⟩ : syracuseStep 1794739 = 2692109) B2692109
theorem B2302643 : Blo 1492066 2302643 := bstep (se 1 (by rfl) ⟨1726982, by rfl⟩ : syracuseStep 2302643 = 3453965) B3453965
theorem B27984611 : Blo 1492066 27984611 := bstep (se 1 (by rfl) ⟨20988458, by rfl⟩ : syracuseStep 27984611 = 41976917) B41976917
theorem B1680115 : Blo 1492066 1680115 := bstep (se 1 (by rfl) ⟨1260086, by rfl⟩ : syracuseStep 1680115 = 2520173) B2520173
theorem B7561997 : Blo 1492066 7561997 := bstep (se 3 (by rfl) ⟨1417874, by rfl⟩ : syracuseStep 7561997 = 2835749) B2835749
theorem B2589475 : Blo 1492066 2589475 := bstep (se 1 (by rfl) ⟨1942106, by rfl⟩ : syracuseStep 2589475 = 3884213) B3884213
theorem B3359537 : Blo 1492066 3359537 := bstep (se 2 (by rfl) ⟨1259826, by rfl⟩ : syracuseStep 3359537 = 2519653) B2519653
theorem B5104451 : Blo 1492066 5104451 := bstep (se 1 (by rfl) ⟨3828338, by rfl⟩ : syracuseStep 5104451 = 7656677) B7656677
theorem B3359555 : Blo 1492066 3359555 := bstep (se 1 (by rfl) ⟨2519666, by rfl⟩ : syracuseStep 3359555 = 5039333) B5039333
theorem B4539235 : Blo 1492066 4539235 := bstep (se 1 (by rfl) ⟨3404426, by rfl⟩ : syracuseStep 4539235 = 6808853) B6808853
theorem B1680259 : Blo 1492066 1680259 := bstep (se 1 (by rfl) ⟨1260194, by rfl⟩ : syracuseStep 1680259 = 2520389) B2520389
theorem B6374285 : Blo 1492066 6374285 := bstep (se 3 (by rfl) ⟨1195178, by rfl⟩ : syracuseStep 6374285 = 2390357) B2390357
theorem B3777425 : Blo 1492066 3777425 := bstep (se 2 (by rfl) ⟨1416534, by rfl⟩ : syracuseStep 3777425 = 2833069) B2833069
theorem B6374321 : Blo 1492066 6374321 := bstep (se 2 (by rfl) ⟨2390370, by rfl⟩ : syracuseStep 6374321 = 4780741) B4780741
theorem B3777475 : Blo 1492066 3777475 := bstep (se 1 (by rfl) ⟨2833106, by rfl⟩ : syracuseStep 3777475 = 5666213) B5666213
theorem B5039117 : Blo 1492066 5039117 := bstep (se 3 (by rfl) ⟨944834, by rfl⟩ : syracuseStep 5039117 = 1889669) B1889669
theorem B1680403 : Blo 1492066 1680403 := bstep (se 1 (by rfl) ⟨1260302, by rfl⟩ : syracuseStep 1680403 = 2520605) B2520605
theorem B5039171 : Blo 1492066 5039171 := bstep (se 1 (by rfl) ⟨3779378, by rfl⟩ : syracuseStep 5039171 = 7558757) B7558757
theorem B3777617 : Blo 1492066 3777617 := bstep (se 2 (by rfl) ⟨1416606, by rfl⟩ : syracuseStep 3777617 = 2833213) B2833213
theorem B3359825 : Blo 1492066 3359825 := bstep (se 2 (by rfl) ⟨1259934, by rfl⟩ : syracuseStep 3359825 = 2519869) B2519869
theorem B1492067 : Blo 1492066 1492067 := bstep (se 1 (by rfl) ⟨1119050, by rfl⟩ : syracuseStep 1492067 = 2238101) B2238101
theorem B3359843 : Blo 1492066 3359843 := bstep (se 1 (by rfl) ⟨2519882, by rfl⟩ : syracuseStep 3359843 = 5039765) B5039765
theorem B11338865 : Blo 1492066 11338865 := bstep (se 2 (by rfl) ⟨4252074, by rfl⟩ : syracuseStep 11338865 = 8504149) B8504149
theorem B1492083 : Blo 1492066 1492083 := bstep (se 1 (by rfl) ⟨1119062, by rfl⟩ : syracuseStep 1492083 = 2238125) B2238125
theorem B1492099 : Blo 1492066 1492099 := bstep (se 1 (by rfl) ⟨1119074, by rfl⟩ : syracuseStep 1492099 = 2238149) B2238149
theorem B1492115 : Blo 1492066 1492115 := bstep (se 1 (by rfl) ⟨1119086, by rfl⟩ : syracuseStep 1492115 = 2238173) B2238173
theorem B1492131 : Blo 1492066 1492131 := bstep (se 1 (by rfl) ⟨1119098, by rfl⟩ : syracuseStep 1492131 = 2238197) B2238197
theorem B1680547 : Blo 1492066 1680547 := bstep (se 1 (by rfl) ⟨1260410, by rfl⟩ : syracuseStep 1680547 = 2520821) B2520821
theorem B1492147 : Blo 1492066 1492147 := bstep (se 1 (by rfl) ⟨1119110, by rfl⟩ : syracuseStep 1492147 = 2238221) B2238221
theorem B1492163 : Blo 1492066 1492163 := bstep (se 1 (by rfl) ⟨1119122, by rfl⟩ : syracuseStep 1492163 = 2238245) B2238245
theorem B1492179 : Blo 1492066 1492179 := bstep (se 1 (by rfl) ⟨1119134, by rfl⟩ : syracuseStep 1492179 = 2238269) B2238269
theorem B1492195 : Blo 1492066 1492195 := bstep (se 1 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 1492195 = 2238293) B2238293
theorem B1492211 : Blo 1492066 1492211 := bstep (se 1 (by rfl) ⟨1119158, by rfl⟩ : syracuseStep 1492211 = 2238317) B2238317
theorem B1492227 : Blo 1492066 1492227 := bstep (se 1 (by rfl) ⟨1119170, by rfl⟩ : syracuseStep 1492227 = 2238341) B2238341
theorem B4850957 : Blo 1492066 4850957 := bstep (se 3 (by rfl) ⟨909554, by rfl⟩ : syracuseStep 4850957 = 1819109) B1819109
theorem B5104913 : Blo 1492066 5104913 := bstep (se 2 (by rfl) ⟨1914342, by rfl⟩ : syracuseStep 5104913 = 3828685) B3828685
theorem B1492243 : Blo 1492066 1492243 := bstep (se 1 (by rfl) ⟨1119182, by rfl⟩ : syracuseStep 1492243 = 2238365) B2238365
theorem B1492259 : Blo 1492066 1492259 := bstep (se 1 (by rfl) ⟨1119194, by rfl⟩ : syracuseStep 1492259 = 2238389) B2238389
theorem B1492275 : Blo 1492066 1492275 := bstep (se 1 (by rfl) ⟨1119206, by rfl⟩ : syracuseStep 1492275 = 2238413) B2238413
theorem B1680691 : Blo 1492066 1680691 := bstep (se 1 (by rfl) ⟨1260518, by rfl⟩ : syracuseStep 1680691 = 2521037) B2521037
theorem B1492291 : Blo 1492066 1492291 := bstep (se 1 (by rfl) ⟨1119218, by rfl⟩ : syracuseStep 1492291 = 2238437) B2238437
theorem B5039441 : Blo 1492066 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B1492307 : Blo 1492066 1492307 := bstep (se 1 (by rfl) ⟨1119230, by rfl⟩ : syracuseStep 1492307 = 2238461) B2238461
theorem B1492323 : Blo 1492066 1492323 := bstep (se 1 (by rfl) ⟨1119242, by rfl⟩ : syracuseStep 1492323 = 2238485) B2238485
theorem B8504675 : Blo 1492066 8504675 := bstep (se 1 (by rfl) ⟨6378506, by rfl⟩ : syracuseStep 8504675 = 12757013) B12757013
theorem B5383523 : Blo 1492066 5383523 := bstep (se 1 (by rfl) ⟨4037642, by rfl⟩ : syracuseStep 5383523 = 8075285) B8075285
theorem B3360113 : Blo 1492066 3360113 := bstep (se 2 (by rfl) ⟨1260042, by rfl⟩ : syracuseStep 3360113 = 2520085) B2520085
theorem B1492339 : Blo 1492066 1492339 := bstep (se 1 (by rfl) ⟨1119254, by rfl⟩ : syracuseStep 1492339 = 2238509) B2238509
theorem B1492355 : Blo 1492066 1492355 := bstep (se 1 (by rfl) ⟨1119266, by rfl⟩ : syracuseStep 1492355 = 2238533) B2238533
theorem B3360131 : Blo 1492066 3360131 := bstep (se 1 (by rfl) ⟨2520098, by rfl⟩ : syracuseStep 3360131 = 5040197) B5040197
theorem B1492371 : Blo 1492066 1492371 := bstep (se 1 (by rfl) ⟨1119278, by rfl⟩ : syracuseStep 1492371 = 2238557) B2238557
theorem B1492387 : Blo 1492066 1492387 := bstep (se 1 (by rfl) ⟨1119290, by rfl⟩ : syracuseStep 1492387 = 2238581) B2238581
theorem B1492403 : Blo 1492066 1492403 := bstep (se 1 (by rfl) ⟨1119302, by rfl⟩ : syracuseStep 1492403 = 2238605) B2238605
theorem B1492419 : Blo 1492066 1492419 := bstep (se 1 (by rfl) ⟨1119314, by rfl⟩ : syracuseStep 1492419 = 2238629) B2238629
theorem B4253123 : Blo 1492066 4253123 := bstep (se 1 (by rfl) ⟨3189842, by rfl⟩ : syracuseStep 4253123 = 6379685) B6379685
theorem B1492435 : Blo 1492066 1492435 := bstep (se 1 (by rfl) ⟨1119326, by rfl⟩ : syracuseStep 1492435 = 2238653) B2238653
theorem B1492451 : Blo 1492066 1492451 := bstep (se 1 (by rfl) ⟨1119338, by rfl⟩ : syracuseStep 1492451 = 2238677) B2238677
theorem B4785635 : Blo 1492066 4785635 := bstep (se 1 (by rfl) ⟨3589226, by rfl⟩ : syracuseStep 4785635 = 7178453) B7178453
theorem B7554545 : Blo 1492066 7554545 := bstep (se 2 (by rfl) ⟨2832954, by rfl⟩ : syracuseStep 7554545 = 5665909) B5665909
theorem B1492467 : Blo 1492066 1492467 := bstep (se 1 (by rfl) ⟨1119350, by rfl⟩ : syracuseStep 1492467 = 2238701) B2238701
theorem B1492483 : Blo 1492066 1492483 := bstep (se 1 (by rfl) ⟨1119362, by rfl⟩ : syracuseStep 1492483 = 2238725) B2238725
theorem B2835985 : Blo 1492066 2835985 := bstep (se 2 (by rfl) ⟨1063494, by rfl⟩ : syracuseStep 2835985 = 2126989) B2126989
theorem B1492499 : Blo 1492066 1492499 := bstep (se 1 (by rfl) ⟨1119374, by rfl⟩ : syracuseStep 1492499 = 2238749) B2238749
theorem B1492515 : Blo 1492066 1492515 := bstep (se 1 (by rfl) ⟨1119386, by rfl⟩ : syracuseStep 1492515 = 2238773) B2238773
theorem B1492531 : Blo 1492066 1492531 := bstep (se 1 (by rfl) ⟨1119398, by rfl⟩ : syracuseStep 1492531 = 2238797) B2238797
theorem B1492547 : Blo 1492066 1492547 := bstep (se 1 (by rfl) ⟨1119410, by rfl⟩ : syracuseStep 1492547 = 2238821) B2238821
theorem B1492563 : Blo 1492066 1492563 := bstep (se 1 (by rfl) ⟨1119422, by rfl⟩ : syracuseStep 1492563 = 2238845) B2238845
theorem B1492579 : Blo 1492066 1492579 := bstep (se 1 (by rfl) ⟨1119434, by rfl⟩ : syracuseStep 1492579 = 2238869) B2238869
theorem B1492595 : Blo 1492066 1492595 := bstep (se 1 (by rfl) ⟨1119446, by rfl⟩ : syracuseStep 1492595 = 2238893) B2238893
theorem B1492611 : Blo 1492066 1492611 := bstep (se 1 (by rfl) ⟨1119458, by rfl⟩ : syracuseStep 1492611 = 2238917) B2238917
theorem B3360401 : Blo 1492066 3360401 := bstep (se 2 (by rfl) ⟨1260150, by rfl⟩ : syracuseStep 3360401 = 2520301) B2520301
theorem B1492627 : Blo 1492066 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B2238113 : Blo 1492066 2238113 := bstep (se 2 (by rfl) ⟨839292, by rfl⟩ : syracuseStep 2238113 = 1678585) B1678585
theorem B1492643 : Blo 1492066 1492643 := bstep (se 1 (by rfl) ⟨1119482, by rfl⟩ : syracuseStep 1492643 = 2238965) B2238965
theorem B3360419 : Blo 1492066 3360419 := bstep (se 1 (by rfl) ⟨2520314, by rfl⟩ : syracuseStep 3360419 = 5040629) B5040629
theorem B2238131 : Blo 1492066 2238131 := bstep (se 1 (by rfl) ⟨1678598, by rfl⟩ : syracuseStep 2238131 = 3357197) B3357197
theorem B1492659 : Blo 1492066 1492659 := bstep (se 1 (by rfl) ⟨1119494, by rfl⟩ : syracuseStep 1492659 = 2238989) B2238989
theorem B1492675 : Blo 1492066 1492675 := bstep (se 1 (by rfl) ⟨1119506, by rfl⟩ : syracuseStep 1492675 = 2239013) B2239013
theorem B2238161 : Blo 1492066 2238161 := bstep (se 2 (by rfl) ⟨839310, by rfl⟩ : syracuseStep 2238161 = 1678621) B1678621
theorem B1492691 : Blo 1492066 1492691 := bstep (se 1 (by rfl) ⟨1119518, by rfl⟩ : syracuseStep 1492691 = 2239037) B2239037
theorem B2238179 : Blo 1492066 2238179 := bstep (se 1 (by rfl) ⟨1678634, by rfl⟩ : syracuseStep 2238179 = 3357269) B3357269
theorem B1492707 : Blo 1492066 1492707 := bstep (se 1 (by rfl) ⟨1119530, by rfl⟩ : syracuseStep 1492707 = 2239061) B2239061
theorem B1492723 : Blo 1492066 1492723 := bstep (se 1 (by rfl) ⟨1119542, by rfl⟩ : syracuseStep 1492723 = 2239085) B2239085
theorem B2238209 : Blo 1492066 2238209 := bstep (se 2 (by rfl) ⟨839328, by rfl⟩ : syracuseStep 2238209 = 1678657) B1678657
theorem B1492739 : Blo 1492066 1492739 := bstep (se 1 (by rfl) ⟨1119554, by rfl⟩ : syracuseStep 1492739 = 2239109) B2239109
theorem B2238227 : Blo 1492066 2238227 := bstep (se 1 (by rfl) ⟨1678670, by rfl⟩ : syracuseStep 2238227 = 3357341) B3357341
theorem B1492755 : Blo 1492066 1492755 := bstep (se 1 (by rfl) ⟨1119566, by rfl⟩ : syracuseStep 1492755 = 2239133) B2239133
theorem B7268131 : Blo 1492066 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B1492771 : Blo 1492066 1492771 := bstep (se 1 (by rfl) ⟨1119578, by rfl⟩ : syracuseStep 1492771 = 2239157) B2239157
theorem B2238257 : Blo 1492066 2238257 := bstep (se 2 (by rfl) ⟨839346, by rfl⟩ : syracuseStep 2238257 = 1678693) B1678693
theorem B1492787 : Blo 1492066 1492787 := bstep (se 1 (by rfl) ⟨1119590, by rfl⟩ : syracuseStep 1492787 = 2239181) B2239181
theorem B2238275 : Blo 1492066 2238275 := bstep (se 1 (by rfl) ⟨1678706, by rfl⟩ : syracuseStep 2238275 = 3357413) B3357413
theorem B1492803 : Blo 1492066 1492803 := bstep (se 1 (by rfl) ⟨1119602, by rfl⟩ : syracuseStep 1492803 = 2239205) B2239205
theorem B1492819 : Blo 1492066 1492819 := bstep (se 1 (by rfl) ⟨1119614, by rfl⟩ : syracuseStep 1492819 = 2239229) B2239229
theorem B2238305 : Blo 1492066 2238305 := bstep (se 2 (by rfl) ⟨839364, by rfl⟩ : syracuseStep 2238305 = 1678729) B1678729
theorem B1492835 : Blo 1492066 1492835 := bstep (se 1 (by rfl) ⟨1119626, by rfl⟩ : syracuseStep 1492835 = 2239253) B2239253
theorem B5670755 : Blo 1492066 5670755 := bstep (se 1 (by rfl) ⟨4253066, by rfl⟩ : syracuseStep 5670755 = 8506133) B8506133
theorem B5039981 : Blo 1492066 5039981 := bstep (se 3 (by rfl) ⟨944996, by rfl⟩ : syracuseStep 5039981 = 1889993) B1889993
theorem B5670769 : Blo 1492066 5670769 := bstep (se 2 (by rfl) ⟨2126538, by rfl⟩ : syracuseStep 5670769 = 4253077) B4253077
theorem B2238323 : Blo 1492066 2238323 := bstep (se 1 (by rfl) ⟨1678742, by rfl⟩ : syracuseStep 2238323 = 3357485) B3357485
theorem B1492851 : Blo 1492066 1492851 := bstep (se 1 (by rfl) ⟨1119638, by rfl⟩ : syracuseStep 1492851 = 2239277) B2239277
theorem B1492867 : Blo 1492066 1492867 := bstep (se 1 (by rfl) ⟨1119650, by rfl⟩ : syracuseStep 1492867 = 2239301) B2239301
theorem B2238353 : Blo 1492066 2238353 := bstep (se 2 (by rfl) ⟨839382, by rfl⟩ : syracuseStep 2238353 = 1678765) B1678765
theorem B1492883 : Blo 1492066 1492883 := bstep (se 1 (by rfl) ⟨1119662, by rfl⟩ : syracuseStep 1492883 = 2239325) B2239325
theorem B2238371 : Blo 1492066 2238371 := bstep (se 1 (by rfl) ⟨1678778, by rfl⟩ : syracuseStep 2238371 = 3357557) B3357557
theorem B1492899 : Blo 1492066 1492899 := bstep (se 1 (by rfl) ⟨1119674, by rfl⟩ : syracuseStep 1492899 = 2239349) B2239349
theorem B5040035 : Blo 1492066 5040035 := bstep (se 1 (by rfl) ⟨3780026, by rfl⟩ : syracuseStep 5040035 = 7560053) B7560053
theorem B2836387 : Blo 1492066 2836387 := bstep (se 1 (by rfl) ⟨2127290, by rfl⟩ : syracuseStep 2836387 = 4254581) B4254581
theorem B3360689 : Blo 1492066 3360689 := bstep (se 2 (by rfl) ⟨1260258, by rfl⟩ : syracuseStep 3360689 = 2520517) B2520517
theorem B1492915 : Blo 1492066 1492915 := bstep (se 1 (by rfl) ⟨1119686, by rfl⟩ : syracuseStep 1492915 = 2239373) B2239373
theorem B2238401 : Blo 1492066 2238401 := bstep (se 2 (by rfl) ⟨839400, by rfl⟩ : syracuseStep 2238401 = 1678801) B1678801
theorem B1492931 : Blo 1492066 1492931 := bstep (se 1 (by rfl) ⟨1119698, by rfl⟩ : syracuseStep 1492931 = 2239397) B2239397
theorem B3360707 : Blo 1492066 3360707 := bstep (se 1 (by rfl) ⟨2520530, by rfl⟩ : syracuseStep 3360707 = 5041061) B5041061
theorem B2238419 : Blo 1492066 2238419 := bstep (se 1 (by rfl) ⟨1678814, by rfl⟩ : syracuseStep 2238419 = 3357629) B3357629
theorem B1492947 : Blo 1492066 1492947 := bstep (se 1 (by rfl) ⟨1119710, by rfl⟩ : syracuseStep 1492947 = 2239421) B2239421
theorem B1492963 : Blo 1492066 1492963 := bstep (se 1 (by rfl) ⟨1119722, by rfl⟩ : syracuseStep 1492963 = 2239445) B2239445
theorem B2238449 : Blo 1492066 2238449 := bstep (se 2 (by rfl) ⟨839418, by rfl⟩ : syracuseStep 2238449 = 1678837) B1678837
theorem B1492979 : Blo 1492066 1492979 := bstep (se 1 (by rfl) ⟨1119734, by rfl⟩ : syracuseStep 1492979 = 2239469) B2239469
theorem B2238467 : Blo 1492066 2238467 := bstep (se 1 (by rfl) ⟨1678850, by rfl⟩ : syracuseStep 2238467 = 3357701) B3357701
theorem B1492995 : Blo 1492066 1492995 := bstep (se 1 (by rfl) ⟨1119746, by rfl⟩ : syracuseStep 1492995 = 2239493) B2239493
theorem B1493011 : Blo 1492066 1493011 := bstep (se 1 (by rfl) ⟨1119758, by rfl⟩ : syracuseStep 1493011 = 2239517) B2239517
theorem B2238497 : Blo 1492066 2238497 := bstep (se 2 (by rfl) ⟨839436, by rfl⟩ : syracuseStep 2238497 = 1678873) B1678873
theorem B1493027 : Blo 1492066 1493027 := bstep (se 1 (by rfl) ⟨1119770, by rfl⟩ : syracuseStep 1493027 = 2239541) B2239541
theorem B3778609 : Blo 1492066 3778609 := bstep (se 2 (by rfl) ⟨1416978, by rfl⟩ : syracuseStep 3778609 = 2833957) B2833957
theorem B2238515 : Blo 1492066 2238515 := bstep (se 1 (by rfl) ⟨1678886, by rfl⟩ : syracuseStep 2238515 = 3357773) B3357773
theorem B1493043 : Blo 1492066 1493043 := bstep (se 1 (by rfl) ⟨1119782, by rfl⟩ : syracuseStep 1493043 = 2239565) B2239565
theorem B1493059 : Blo 1492066 1493059 := bstep (se 1 (by rfl) ⟨1119794, by rfl⟩ : syracuseStep 1493059 = 2239589) B2239589
theorem B2238545 : Blo 1492066 2238545 := bstep (se 2 (by rfl) ⟨839454, by rfl⟩ : syracuseStep 2238545 = 1678909) B1678909
theorem B1493075 : Blo 1492066 1493075 := bstep (se 1 (by rfl) ⟨1119806, by rfl⟩ : syracuseStep 1493075 = 2239613) B2239613
theorem B2238563 : Blo 1492066 2238563 := bstep (se 1 (by rfl) ⟨1678922, by rfl⟩ : syracuseStep 2238563 = 3357845) B3357845
theorem B1493091 : Blo 1492066 1493091 := bstep (se 1 (by rfl) ⟨1119818, by rfl⟩ : syracuseStep 1493091 = 2239637) B2239637
theorem B12748913 : Blo 1492066 12748913 := bstep (se 2 (by rfl) ⟨4780842, by rfl⟩ : syracuseStep 12748913 = 9561685) B9561685
theorem B1493107 : Blo 1492066 1493107 := bstep (se 1 (by rfl) ⟨1119830, by rfl⟩ : syracuseStep 1493107 = 2239661) B2239661
theorem B2238593 : Blo 1492066 2238593 := bstep (se 2 (by rfl) ⟨839472, by rfl⟩ : syracuseStep 2238593 = 1678945) B1678945
theorem B1493123 : Blo 1492066 1493123 := bstep (se 1 (by rfl) ⟨1119842, by rfl⟩ : syracuseStep 1493123 = 2239685) B2239685
theorem B2238611 : Blo 1492066 2238611 := bstep (se 1 (by rfl) ⟨1678958, by rfl⟩ : syracuseStep 2238611 = 3357917) B3357917
theorem B1493139 : Blo 1492066 1493139 := bstep (se 1 (by rfl) ⟨1119854, by rfl⟩ : syracuseStep 1493139 = 2239709) B2239709
theorem B1493155 : Blo 1492066 1493155 := bstep (se 1 (by rfl) ⟨1119866, by rfl⟩ : syracuseStep 1493155 = 2239733) B2239733
theorem B2238641 : Blo 1492066 2238641 := bstep (se 2 (by rfl) ⟨839490, by rfl⟩ : syracuseStep 2238641 = 1678981) B1678981
theorem B5040305 : Blo 1492066 5040305 := bstep (se 2 (by rfl) ⟨1890114, by rfl⟩ : syracuseStep 5040305 = 3780229) B3780229
theorem B1493171 : Blo 1492066 1493171 := bstep (se 1 (by rfl) ⟨1119878, by rfl⟩ : syracuseStep 1493171 = 2239757) B2239757
theorem B2238659 : Blo 1492066 2238659 := bstep (se 1 (by rfl) ⟨1678994, by rfl⟩ : syracuseStep 2238659 = 3357989) B3357989
theorem B1493187 : Blo 1492066 1493187 := bstep (se 1 (by rfl) ⟨1119890, by rfl⟩ : syracuseStep 1493187 = 2239781) B2239781
theorem B3360977 : Blo 1492066 3360977 := bstep (se 2 (by rfl) ⟨1260366, by rfl⟩ : syracuseStep 3360977 = 2520733) B2520733
theorem B1493203 : Blo 1492066 1493203 := bstep (se 1 (by rfl) ⟨1119902, by rfl⟩ : syracuseStep 1493203 = 2239805) B2239805
theorem B2238689 : Blo 1492066 2238689 := bstep (se 2 (by rfl) ⟨839508, by rfl⟩ : syracuseStep 2238689 = 1679017) B1679017
theorem B1493219 : Blo 1492066 1493219 := bstep (se 1 (by rfl) ⟨1119914, by rfl⟩ : syracuseStep 1493219 = 2239829) B2239829
theorem B3360995 : Blo 1492066 3360995 := bstep (se 1 (by rfl) ⟨2520746, by rfl⟩ : syracuseStep 3360995 = 5041493) B5041493
theorem B2238707 : Blo 1492066 2238707 := bstep (se 1 (by rfl) ⟨1679030, by rfl⟩ : syracuseStep 2238707 = 3358061) B3358061
theorem B1493235 : Blo 1492066 1493235 := bstep (se 1 (by rfl) ⟨1119926, by rfl⟩ : syracuseStep 1493235 = 2239853) B2239853
theorem B1493251 : Blo 1492066 1493251 := bstep (se 1 (by rfl) ⟨1119938, by rfl⟩ : syracuseStep 1493251 = 2239877) B2239877
theorem B2238737 : Blo 1492066 2238737 := bstep (se 2 (by rfl) ⟨839526, by rfl⟩ : syracuseStep 2238737 = 1679053) B1679053
theorem B1493267 : Blo 1492066 1493267 := bstep (se 1 (by rfl) ⟨1119950, by rfl⟩ : syracuseStep 1493267 = 2239901) B2239901
theorem B2238755 : Blo 1492066 2238755 := bstep (se 1 (by rfl) ⟨1679066, by rfl⟩ : syracuseStep 2238755 = 3358133) B3358133
theorem B1493283 : Blo 1492066 1493283 := bstep (se 1 (by rfl) ⟨1119962, by rfl⟩ : syracuseStep 1493283 = 2239925) B2239925
theorem B1493299 : Blo 1492066 1493299 := bstep (se 1 (by rfl) ⟨1119974, by rfl⟩ : syracuseStep 1493299 = 2239949) B2239949
theorem B2238785 : Blo 1492066 2238785 := bstep (se 2 (by rfl) ⟨839544, by rfl⟩ : syracuseStep 2238785 = 1679089) B1679089
theorem B3778883 : Blo 1492066 3778883 := bstep (se 1 (by rfl) ⟨2834162, by rfl⟩ : syracuseStep 3778883 = 5668325) B5668325
theorem B1493315 : Blo 1492066 1493315 := bstep (se 1 (by rfl) ⟨1119986, by rfl⟩ : syracuseStep 1493315 = 2239973) B2239973
theorem B2238803 : Blo 1492066 2238803 := bstep (se 1 (by rfl) ⟨1679102, by rfl⟩ : syracuseStep 2238803 = 3358205) B3358205
theorem B1493331 : Blo 1492066 1493331 := bstep (se 1 (by rfl) ⟨1119998, by rfl⟩ : syracuseStep 1493331 = 2239997) B2239997
theorem B3189091 : Blo 1492066 3189091 := bstep (se 1 (by rfl) ⟨2391818, by rfl⟩ : syracuseStep 3189091 = 4783637) B4783637
theorem B1493347 : Blo 1492066 1493347 := bstep (se 1 (by rfl) ⟨1120010, by rfl⟩ : syracuseStep 1493347 = 2240021) B2240021
theorem B2238833 : Blo 1492066 2238833 := bstep (se 2 (by rfl) ⟨839562, by rfl⟩ : syracuseStep 2238833 = 1679125) B1679125
theorem B1493363 : Blo 1492066 1493363 := bstep (se 1 (by rfl) ⟨1120022, by rfl⟩ : syracuseStep 1493363 = 2240045) B2240045
theorem B2238851 : Blo 1492066 2238851 := bstep (se 1 (by rfl) ⟨1679138, by rfl⟩ : syracuseStep 2238851 = 3358277) B3358277
theorem B1493379 : Blo 1492066 1493379 := bstep (se 1 (by rfl) ⟨1120034, by rfl⟩ : syracuseStep 1493379 = 2240069) B2240069
theorem B1493395 : Blo 1492066 1493395 := bstep (se 1 (by rfl) ⟨1120046, by rfl⟩ : syracuseStep 1493395 = 2240093) B2240093
theorem B2238881 : Blo 1492066 2238881 := bstep (se 2 (by rfl) ⟨839580, by rfl⟩ : syracuseStep 2238881 = 1679161) B1679161
theorem B1493411 : Blo 1492066 1493411 := bstep (se 1 (by rfl) ⟨1120058, by rfl⟩ : syracuseStep 1493411 = 2240117) B2240117
theorem B6056369 : Blo 1492066 6056369 := bstep (se 2 (by rfl) ⟨2271138, by rfl⟩ : syracuseStep 6056369 = 4542277) B4542277
theorem B2238899 : Blo 1492066 2238899 := bstep (se 1 (by rfl) ⟨1679174, by rfl⟩ : syracuseStep 2238899 = 3358349) B3358349
theorem B1493427 : Blo 1492066 1493427 := bstep (se 1 (by rfl) ⟨1120070, by rfl⟩ : syracuseStep 1493427 = 2240141) B2240141
theorem B1493443 : Blo 1492066 1493443 := bstep (se 1 (by rfl) ⟨1120082, by rfl⟩ : syracuseStep 1493443 = 2240165) B2240165
theorem B9570757 : Blo 1492066 9570757 := bstep (se 4 (by rfl) ⟨897258, by rfl⟩ : syracuseStep 9570757 = 1794517) B1794517
theorem B2238929 : Blo 1492066 2238929 := bstep (se 2 (by rfl) ⟨839598, by rfl⟩ : syracuseStep 2238929 = 1679197) B1679197
theorem B1493459 : Blo 1492066 1493459 := bstep (se 1 (by rfl) ⟨1120094, by rfl⟩ : syracuseStep 1493459 = 2240189) B2240189
theorem B2238947 : Blo 1492066 2238947 := bstep (se 1 (by rfl) ⟨1679210, by rfl⟩ : syracuseStep 2238947 = 3358421) B3358421
theorem B1493475 : Blo 1492066 1493475 := bstep (se 1 (by rfl) ⟨1120106, by rfl⟩ : syracuseStep 1493475 = 2240213) B2240213
theorem B3361265 : Blo 1492066 3361265 := bstep (se 2 (by rfl) ⟨1260474, by rfl⟩ : syracuseStep 3361265 = 2520949) B2520949
theorem B1493491 : Blo 1492066 1493491 := bstep (se 1 (by rfl) ⟨1120118, by rfl⟩ : syracuseStep 1493491 = 2240237) B2240237
theorem B2238977 : Blo 1492066 2238977 := bstep (se 2 (by rfl) ⟨839616, by rfl⟩ : syracuseStep 2238977 = 1679233) B1679233
theorem B3779075 : Blo 1492066 3779075 := bstep (se 1 (by rfl) ⟨2834306, by rfl⟩ : syracuseStep 3779075 = 5668613) B5668613
theorem B1493507 : Blo 1492066 1493507 := bstep (se 1 (by rfl) ⟨1120130, by rfl⟩ : syracuseStep 1493507 = 2240261) B2240261
theorem B3361283 : Blo 1492066 3361283 := bstep (se 1 (by rfl) ⟨2520962, by rfl⟩ : syracuseStep 3361283 = 5041925) B5041925
theorem B4311569 : Blo 1492066 4311569 := bstep (se 2 (by rfl) ⟨1616838, by rfl⟩ : syracuseStep 4311569 = 3233677) B3233677
theorem B2238995 : Blo 1492066 2238995 := bstep (se 1 (by rfl) ⟨1679246, by rfl⟩ : syracuseStep 2238995 = 3358493) B3358493
theorem B1493523 : Blo 1492066 1493523 := bstep (se 1 (by rfl) ⟨1120142, by rfl⟩ : syracuseStep 1493523 = 2240285) B2240285
theorem B1493539 : Blo 1492066 1493539 := bstep (se 1 (by rfl) ⟨1120154, by rfl⟩ : syracuseStep 1493539 = 2240309) B2240309
theorem B2239025 : Blo 1492066 2239025 := bstep (se 2 (by rfl) ⟨839634, by rfl⟩ : syracuseStep 2239025 = 1679269) B1679269
theorem B1493555 : Blo 1492066 1493555 := bstep (se 1 (by rfl) ⟨1120166, by rfl⟩ : syracuseStep 1493555 = 2240333) B2240333
theorem B2239043 : Blo 1492066 2239043 := bstep (se 1 (by rfl) ⟨1679282, by rfl⟩ : syracuseStep 2239043 = 3358565) B3358565
theorem B1493571 : Blo 1492066 1493571 := bstep (se 1 (by rfl) ⟨1120178, by rfl⟩ : syracuseStep 1493571 = 2240357) B2240357
theorem B1493587 : Blo 1492066 1493587 := bstep (se 1 (by rfl) ⟨1120190, by rfl⟩ : syracuseStep 1493587 = 2240381) B2240381
theorem B2239073 : Blo 1492066 2239073 := bstep (se 2 (by rfl) ⟨839652, by rfl⟩ : syracuseStep 2239073 = 1679305) B1679305
theorem B1493603 : Blo 1492066 1493603 := bstep (se 1 (by rfl) ⟨1120202, by rfl⟩ : syracuseStep 1493603 = 2240405) B2240405
theorem B2239091 : Blo 1492066 2239091 := bstep (se 1 (by rfl) ⟨1679318, by rfl⟩ : syracuseStep 2239091 = 3358637) B3358637
theorem B1493619 : Blo 1492066 1493619 := bstep (se 1 (by rfl) ⟨1120214, by rfl⟩ : syracuseStep 1493619 = 2240429) B2240429
theorem B3066499 : Blo 1492066 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B1493635 : Blo 1492066 1493635 := bstep (se 1 (by rfl) ⟨1120226, by rfl⟩ : syracuseStep 1493635 = 2240453) B2240453
theorem B2239121 : Blo 1492066 2239121 := bstep (se 2 (by rfl) ⟨839670, by rfl⟩ : syracuseStep 2239121 = 1679341) B1679341
theorem B1493651 : Blo 1492066 1493651 := bstep (se 1 (by rfl) ⟨1120238, by rfl⟩ : syracuseStep 1493651 = 2240477) B2240477
theorem B4254353 : Blo 1492066 4254353 := bstep (se 2 (by rfl) ⟨1595382, by rfl⟩ : syracuseStep 4254353 = 3190765) B3190765
theorem B2239139 : Blo 1492066 2239139 := bstep (se 1 (by rfl) ⟨1679354, by rfl⟩ : syracuseStep 2239139 = 3358709) B3358709
theorem B1493667 : Blo 1492066 1493667 := bstep (se 1 (by rfl) ⟨1120250, by rfl⟩ : syracuseStep 1493667 = 2240501) B2240501
theorem B1493683 : Blo 1492066 1493683 := bstep (se 1 (by rfl) ⟨1120262, by rfl⟩ : syracuseStep 1493683 = 2240525) B2240525
theorem B2239169 : Blo 1492066 2239169 := bstep (se 2 (by rfl) ⟨839688, by rfl⟩ : syracuseStep 2239169 = 1679377) B1679377
theorem B1493699 : Blo 1492066 1493699 := bstep (se 1 (by rfl) ⟨1120274, by rfl⟩ : syracuseStep 1493699 = 2240549) B2240549
theorem B5040845 : Blo 1492066 5040845 := bstep (se 3 (by rfl) ⟨945158, by rfl⟩ : syracuseStep 5040845 = 1890317) B1890317
theorem B4664017 : Blo 1492066 4664017 := bstep (se 2 (by rfl) ⟨1749006, by rfl⟩ : syracuseStep 4664017 = 3498013) B3498013
theorem B2239187 : Blo 1492066 2239187 := bstep (se 1 (by rfl) ⟨1679390, by rfl⟩ : syracuseStep 2239187 = 3358781) B3358781
theorem B1493715 : Blo 1492066 1493715 := bstep (se 1 (by rfl) ⟨1120286, by rfl⟩ : syracuseStep 1493715 = 2240573) B2240573
theorem B1493731 : Blo 1492066 1493731 := bstep (se 1 (by rfl) ⟨1120298, by rfl⟩ : syracuseStep 1493731 = 2240597) B2240597
theorem B6056675 : Blo 1492066 6056675 := bstep (se 1 (by rfl) ⟨4542506, by rfl⟩ : syracuseStep 6056675 = 9085013) B9085013
theorem B2239217 : Blo 1492066 2239217 := bstep (se 2 (by rfl) ⟨839706, by rfl⟩ : syracuseStep 2239217 = 1679413) B1679413
theorem B1493747 : Blo 1492066 1493747 := bstep (se 1 (by rfl) ⟨1120310, by rfl⟩ : syracuseStep 1493747 = 2240621) B2240621
theorem B2239235 : Blo 1492066 2239235 := bstep (se 1 (by rfl) ⟨1679426, by rfl⟩ : syracuseStep 2239235 = 3358853) B3358853
theorem B5040899 : Blo 1492066 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B1493763 : Blo 1492066 1493763 := bstep (se 1 (by rfl) ⟨1120322, by rfl⟩ : syracuseStep 1493763 = 2240645) B2240645
theorem B3361553 : Blo 1492066 3361553 := bstep (se 2 (by rfl) ⟨1260582, by rfl⟩ : syracuseStep 3361553 = 2521165) B2521165
theorem B1493779 : Blo 1492066 1493779 := bstep (se 1 (by rfl) ⟨1120334, by rfl⟩ : syracuseStep 1493779 = 2240669) B2240669
theorem B2239265 : Blo 1492066 2239265 := bstep (se 2 (by rfl) ⟨839724, by rfl⟩ : syracuseStep 2239265 = 1679449) B1679449
theorem B1493795 : Blo 1492066 1493795 := bstep (se 1 (by rfl) ⟨1120346, by rfl⟩ : syracuseStep 1493795 = 2240693) B2240693
theorem B3361571 : Blo 1492066 3361571 := bstep (se 1 (by rfl) ⟨2521178, by rfl⟩ : syracuseStep 3361571 = 5042357) B5042357
theorem B2239283 : Blo 1492066 2239283 := bstep (se 1 (by rfl) ⟨1679462, by rfl⟩ : syracuseStep 2239283 = 3358925) B3358925
theorem B1493811 : Blo 1492066 1493811 := bstep (se 1 (by rfl) ⟨1120358, by rfl⟩ : syracuseStep 1493811 = 2240717) B2240717
theorem B1493827 : Blo 1492066 1493827 := bstep (se 1 (by rfl) ⟨1120370, by rfl⟩ : syracuseStep 1493827 = 2240741) B2240741
theorem B2124625 : Blo 1492066 2124625 := bstep (se 2 (by rfl) ⟨796734, by rfl⟩ : syracuseStep 2124625 = 1593469) B1593469
theorem B2239313 : Blo 1492066 2239313 := bstep (se 2 (by rfl) ⟨839742, by rfl⟩ : syracuseStep 2239313 = 1679485) B1679485
theorem B1493843 : Blo 1492066 1493843 := bstep (se 1 (by rfl) ⟨1120382, by rfl⟩ : syracuseStep 1493843 = 2240765) B2240765
theorem B2239331 : Blo 1492066 2239331 := bstep (se 1 (by rfl) ⟨1679498, by rfl⟩ : syracuseStep 2239331 = 3358997) B3358997
theorem B1493859 : Blo 1492066 1493859 := bstep (se 1 (by rfl) ⟨1120394, by rfl⟩ : syracuseStep 1493859 = 2240789) B2240789
theorem B1493875 : Blo 1492066 1493875 := bstep (se 1 (by rfl) ⟨1120406, by rfl⟩ : syracuseStep 1493875 = 2240813) B2240813
theorem B2239361 : Blo 1492066 2239361 := bstep (se 2 (by rfl) ⟨839760, by rfl⟩ : syracuseStep 2239361 = 1679521) B1679521
theorem B1493891 : Blo 1492066 1493891 := bstep (se 1 (by rfl) ⟨1120418, by rfl⟩ : syracuseStep 1493891 = 2240837) B2240837
theorem B2517905 : Blo 1492066 2517905 := bstep (se 2 (by rfl) ⟨944214, by rfl⟩ : syracuseStep 2517905 = 1888429) B1888429
theorem B2239379 : Blo 1492066 2239379 := bstep (se 1 (by rfl) ⟨1679534, by rfl⟩ : syracuseStep 2239379 = 3359069) B3359069
theorem B1493907 : Blo 1492066 1493907 := bstep (se 1 (by rfl) ⟨1120430, by rfl⟩ : syracuseStep 1493907 = 2240861) B2240861
theorem B7556003 : Blo 1492066 7556003 := bstep (se 1 (by rfl) ⟨5667002, by rfl⟩ : syracuseStep 7556003 = 11334005) B11334005
theorem B1493923 : Blo 1492066 1493923 := bstep (se 1 (by rfl) ⟨1120442, by rfl⟩ : syracuseStep 1493923 = 2240885) B2240885
theorem B2239409 : Blo 1492066 2239409 := bstep (se 2 (by rfl) ⟨839778, by rfl⟩ : syracuseStep 2239409 = 1679557) B1679557
theorem B1493939 : Blo 1492066 1493939 := bstep (se 1 (by rfl) ⟨1120454, by rfl⟩ : syracuseStep 1493939 = 2240909) B2240909
theorem B2124739 : Blo 1492066 2124739 := bstep (se 1 (by rfl) ⟨1593554, by rfl⟩ : syracuseStep 2124739 = 3187109) B3187109
theorem B2239427 : Blo 1492066 2239427 := bstep (se 1 (by rfl) ⟨1679570, by rfl⟩ : syracuseStep 2239427 = 3359141) B3359141
theorem B1493955 : Blo 1492066 1493955 := bstep (se 1 (by rfl) ⟨1120466, by rfl⟩ : syracuseStep 1493955 = 2240933) B2240933
theorem B1493971 : Blo 1492066 1493971 := bstep (se 1 (by rfl) ⟨1120478, by rfl⟩ : syracuseStep 1493971 = 2240957) B2240957
theorem B2239457 : Blo 1492066 2239457 := bstep (se 2 (by rfl) ⟨839796, by rfl⟩ : syracuseStep 2239457 = 1679593) B1679593
theorem B1493987 : Blo 1492066 1493987 := bstep (se 1 (by rfl) ⟨1120490, by rfl⟩ : syracuseStep 1493987 = 2240981) B2240981
theorem B2239475 : Blo 1492066 2239475 := bstep (se 1 (by rfl) ⟨1679606, by rfl⟩ : syracuseStep 2239475 = 3359213) B3359213
theorem B1494003 : Blo 1492066 1494003 := bstep (se 1 (by rfl) ⟨1120502, by rfl⟩ : syracuseStep 1494003 = 2241005) B2241005
theorem B1494019 : Blo 1492066 1494019 := bstep (se 1 (by rfl) ⟨1120514, by rfl⟩ : syracuseStep 1494019 = 2241029) B2241029
theorem B2518033 : Blo 1492066 2518033 := bstep (se 2 (by rfl) ⟨944262, by rfl⟩ : syracuseStep 2518033 = 1888525) B1888525
theorem B2239505 : Blo 1492066 2239505 := bstep (se 2 (by rfl) ⟨839814, by rfl⟩ : syracuseStep 2239505 = 1679629) B1679629
theorem B5041169 : Blo 1492066 5041169 := bstep (se 2 (by rfl) ⟨1890438, by rfl⟩ : syracuseStep 5041169 = 3780877) B3780877
theorem B1494035 : Blo 1492066 1494035 := bstep (se 1 (by rfl) ⟨1120526, by rfl⟩ : syracuseStep 1494035 = 2241053) B2241053
theorem B2239523 : Blo 1492066 2239523 := bstep (se 1 (by rfl) ⟨1679642, by rfl⟩ : syracuseStep 2239523 = 3359285) B3359285
theorem B7179299 : Blo 1492066 7179299 := bstep (se 1 (by rfl) ⟨5384474, by rfl⟩ : syracuseStep 7179299 = 10768949) B10768949
theorem B1494051 : Blo 1492066 1494051 := bstep (se 1 (by rfl) ⟨1120538, by rfl⟩ : syracuseStep 1494051 = 2241077) B2241077
theorem B2518067 : Blo 1492066 2518067 := bstep (se 1 (by rfl) ⟨1888550, by rfl⟩ : syracuseStep 2518067 = 3777101) B3777101
theorem B2239553 : Blo 1492066 2239553 := bstep (se 2 (by rfl) ⟨839832, by rfl⟩ : syracuseStep 2239553 = 1679665) B1679665
theorem B2239571 : Blo 1492066 2239571 := bstep (se 1 (by rfl) ⟨1679678, by rfl⟩ : syracuseStep 2239571 = 3359357) B3359357
theorem B13626467 : Blo 1492066 13626467 := bstep (se 1 (by rfl) ⟨10219850, by rfl⟩ : syracuseStep 13626467 = 20439701) B20439701
theorem B2239601 : Blo 1492066 2239601 := bstep (se 2 (by rfl) ⟨839850, by rfl⟩ : syracuseStep 2239601 = 1679701) B1679701
theorem B2239619 : Blo 1492066 2239619 := bstep (se 1 (by rfl) ⟨1679714, by rfl⟩ : syracuseStep 2239619 = 3359429) B3359429
theorem B8498317 : Blo 1492066 8498317 := bstep (se 3 (by rfl) ⟨1593434, by rfl⟩ : syracuseStep 8498317 = 3186869) B3186869
theorem B2239649 : Blo 1492066 2239649 := bstep (se 2 (by rfl) ⟨839868, by rfl⟩ : syracuseStep 2239649 = 1679737) B1679737
theorem B3189937 : Blo 1492066 3189937 := bstep (se 2 (by rfl) ⟨1196226, by rfl⟩ : syracuseStep 3189937 = 2392453) B2392453
theorem B2518195 : Blo 1492066 2518195 := bstep (se 1 (by rfl) ⟨1888646, by rfl⟩ : syracuseStep 2518195 = 3777293) B3777293
theorem B2239667 : Blo 1492066 2239667 := bstep (se 1 (by rfl) ⟨1679750, by rfl⟩ : syracuseStep 2239667 = 3359501) B3359501
theorem B8506565 : Blo 1492066 8506565 := bstep (se 4 (by rfl) ⟨797490, by rfl⟩ : syracuseStep 8506565 = 1594981) B1594981
theorem B2239697 : Blo 1492066 2239697 := bstep (se 2 (by rfl) ⟨839886, by rfl⟩ : syracuseStep 2239697 = 1679773) B1679773
theorem B2239715 : Blo 1492066 2239715 := bstep (se 1 (by rfl) ⟨1679786, by rfl⟩ : syracuseStep 2239715 = 3359573) B3359573
theorem B2239745 : Blo 1492066 2239745 := bstep (se 2 (by rfl) ⟨839904, by rfl⟩ : syracuseStep 2239745 = 1679809) B1679809
theorem B2239763 : Blo 1492066 2239763 := bstep (se 1 (by rfl) ⟨1679822, by rfl⟩ : syracuseStep 2239763 = 3359645) B3359645
theorem B5672227 : Blo 1492066 5672227 := bstep (se 1 (by rfl) ⟨4254170, by rfl⟩ : syracuseStep 5672227 = 8508341) B8508341
theorem B2239793 : Blo 1492066 2239793 := bstep (se 2 (by rfl) ⟨839922, by rfl⟩ : syracuseStep 2239793 = 1679845) B1679845
theorem B2518337 : Blo 1492066 2518337 := bstep (se 2 (by rfl) ⟨944376, by rfl⟩ : syracuseStep 2518337 = 1888753) B1888753
theorem B2239811 : Blo 1492066 2239811 := bstep (se 1 (by rfl) ⟨1679858, by rfl⟩ : syracuseStep 2239811 = 3359717) B3359717
theorem B10759493 : Blo 1492066 10759493 := bstep (se 4 (by rfl) ⟨1008702, by rfl⟩ : syracuseStep 10759493 = 2017405) B2017405
theorem B2239841 : Blo 1492066 2239841 := bstep (se 2 (by rfl) ⟨839940, by rfl⟩ : syracuseStep 2239841 = 1679881) B1679881
theorem B4033901 : Blo 1492066 4033901 := bstep (se 3 (by rfl) ⟨756356, by rfl⟩ : syracuseStep 4033901 = 1512713) B1512713
theorem B2239859 : Blo 1492066 2239859 := bstep (se 1 (by rfl) ⟨1679894, by rfl⟩ : syracuseStep 2239859 = 3359789) B3359789
theorem B2239889 : Blo 1492066 2239889 := bstep (se 2 (by rfl) ⟨839958, by rfl⟩ : syracuseStep 2239889 = 1679917) B1679917
theorem B2239907 : Blo 1492066 2239907 := bstep (se 1 (by rfl) ⟨1679930, by rfl⟩ : syracuseStep 2239907 = 3359861) B3359861
theorem B3780017 : Blo 1492066 3780017 := bstep (se 2 (by rfl) ⟨1417506, by rfl⟩ : syracuseStep 3780017 = 2835013) B2835013
theorem B2518465 : Blo 1492066 2518465 := bstep (se 2 (by rfl) ⟨944424, by rfl⟩ : syracuseStep 2518465 = 1888849) B1888849
theorem B2239937 : Blo 1492066 2239937 := bstep (se 2 (by rfl) ⟨839976, by rfl⟩ : syracuseStep 2239937 = 1679953) B1679953
theorem B2239955 : Blo 1492066 2239955 := bstep (se 1 (by rfl) ⟨1679966, by rfl⟩ : syracuseStep 2239955 = 3359933) B3359933
theorem B2518499 : Blo 1492066 2518499 := bstep (se 1 (by rfl) ⟨1888874, by rfl⟩ : syracuseStep 2518499 = 3777749) B3777749
theorem B3780067 : Blo 1492066 3780067 := bstep (se 1 (by rfl) ⟨2835050, by rfl⟩ : syracuseStep 3780067 = 5670101) B5670101
theorem B2239985 : Blo 1492066 2239985 := bstep (se 2 (by rfl) ⟨839994, by rfl⟩ : syracuseStep 2239985 = 1679989) B1679989
theorem B2240003 : Blo 1492066 2240003 := bstep (se 1 (by rfl) ⟨1680002, by rfl⟩ : syracuseStep 2240003 = 3360005) B3360005
theorem B2240033 : Blo 1492066 2240033 := bstep (se 2 (by rfl) ⟨840012, by rfl⟩ : syracuseStep 2240033 = 1680025) B1680025
theorem B2018849 : Blo 1492066 2018849 := bstep (se 2 (by rfl) ⟨757068, by rfl⟩ : syracuseStep 2018849 = 1514137) B1514137
theorem B9563683 : Blo 1492066 9563683 := bstep (se 1 (by rfl) ⟨7172762, by rfl⟩ : syracuseStep 9563683 = 14345525) B14345525
theorem B5041709 : Blo 1492066 5041709 := bstep (se 3 (by rfl) ⟨945320, by rfl⟩ : syracuseStep 5041709 = 1890641) B1890641
theorem B3403313 : Blo 1492066 3403313 := bstep (se 2 (by rfl) ⟨1276242, by rfl⟩ : syracuseStep 3403313 = 2552485) B2552485
theorem B2240051 : Blo 1492066 2240051 := bstep (se 1 (by rfl) ⟨1680038, by rfl⟩ : syracuseStep 2240051 = 3360077) B3360077
theorem B2240081 : Blo 1492066 2240081 := bstep (se 2 (by rfl) ⟨840030, by rfl⟩ : syracuseStep 2240081 = 1680061) B1680061
theorem B2518627 : Blo 1492066 2518627 := bstep (se 1 (by rfl) ⟨1888970, by rfl⟩ : syracuseStep 2518627 = 3777941) B3777941
theorem B2240099 : Blo 1492066 2240099 := bstep (se 1 (by rfl) ⟨1680074, by rfl⟩ : syracuseStep 2240099 = 3360149) B3360149
theorem B5041763 : Blo 1492066 5041763 := bstep (se 1 (by rfl) ⟨3781322, by rfl⟩ : syracuseStep 5041763 = 7562645) B7562645
theorem B4034161 : Blo 1492066 4034161 := bstep (se 2 (by rfl) ⟨1512810, by rfl⟩ : syracuseStep 4034161 = 3025621) B3025621
theorem B3780209 : Blo 1492066 3780209 := bstep (se 2 (by rfl) ⟨1417578, by rfl⟩ : syracuseStep 3780209 = 2835157) B2835157
theorem B2240129 : Blo 1492066 2240129 := bstep (se 2 (by rfl) ⟨840048, by rfl⟩ : syracuseStep 2240129 = 1680097) B1680097
theorem B24555149 : Blo 1492066 24555149 := bstep (se 3 (by rfl) ⟨4604090, by rfl⟩ : syracuseStep 24555149 = 9208181) B9208181
theorem B2240147 : Blo 1492066 2240147 := bstep (se 1 (by rfl) ⟨1680110, by rfl⟩ : syracuseStep 2240147 = 3360221) B3360221
theorem B2240177 : Blo 1492066 2240177 := bstep (se 2 (by rfl) ⟨840066, by rfl⟩ : syracuseStep 2240177 = 1680133) B1680133
theorem B2240195 : Blo 1492066 2240195 := bstep (se 1 (by rfl) ⟨1680146, by rfl⟩ : syracuseStep 2240195 = 3360293) B3360293
theorem B7556813 : Blo 1492066 7556813 := bstep (se 3 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 7556813 = 2833805) B2833805
theorem B2240225 : Blo 1492066 2240225 := bstep (se 2 (by rfl) ⟨840084, by rfl⟩ : syracuseStep 2240225 = 1680169) B1680169
theorem B5746403 : Blo 1492066 5746403 := bstep (se 1 (by rfl) ⟨4309802, by rfl⟩ : syracuseStep 5746403 = 8619605) B8619605
theorem B2518769 : Blo 1492066 2518769 := bstep (se 2 (by rfl) ⟨944538, by rfl⟩ : syracuseStep 2518769 = 1889077) B1889077
theorem B9080561 : Blo 1492066 9080561 := bstep (se 2 (by rfl) ⟨3405210, by rfl⟩ : syracuseStep 9080561 = 6810421) B6810421
theorem B2240243 : Blo 1492066 2240243 := bstep (se 1 (by rfl) ⟨1680182, by rfl⟩ : syracuseStep 2240243 = 3360365) B3360365
theorem B6057713 : Blo 1492066 6057713 := bstep (se 2 (by rfl) ⟨2271642, by rfl⟩ : syracuseStep 6057713 = 4543285) B4543285
theorem B2240273 : Blo 1492066 2240273 := bstep (se 2 (by rfl) ⟨840102, by rfl⟩ : syracuseStep 2240273 = 1680205) B1680205
theorem B2240291 : Blo 1492066 2240291 := bstep (se 1 (by rfl) ⟨1680218, by rfl⟩ : syracuseStep 2240291 = 3360437) B3360437
theorem B17010485 : Blo 1492066 17010485 := bstep (se 5 (by rfl) ⟨797366, by rfl⟩ : syracuseStep 17010485 = 1594733) B1594733
theorem B2240321 : Blo 1492066 2240321 := bstep (se 2 (by rfl) ⟨840120, by rfl⟩ : syracuseStep 2240321 = 1680241) B1680241
theorem B8073037 : Blo 1492066 8073037 := bstep (se 3 (by rfl) ⟨1513694, by rfl⟩ : syracuseStep 8073037 = 3027389) B3027389
theorem B2240339 : Blo 1492066 2240339 := bstep (se 1 (by rfl) ⟨1680254, by rfl⟩ : syracuseStep 2240339 = 3360509) B3360509
theorem B2518897 : Blo 1492066 2518897 := bstep (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) B1889173
theorem B2240369 : Blo 1492066 2240369 := bstep (se 2 (by rfl) ⟨840138, by rfl⟩ : syracuseStep 2240369 = 1680277) B1680277
theorem B5042033 : Blo 1492066 5042033 := bstep (se 2 (by rfl) ⟨1890762, by rfl⟩ : syracuseStep 5042033 = 3781525) B3781525
theorem B2240387 : Blo 1492066 2240387 := bstep (se 1 (by rfl) ⟨1680290, by rfl⟩ : syracuseStep 2240387 = 3360581) B3360581
theorem B2518931 : Blo 1492066 2518931 := bstep (se 1 (by rfl) ⟨1889198, by rfl⟩ : syracuseStep 2518931 = 3778397) B3778397
theorem B2240417 : Blo 1492066 2240417 := bstep (se 2 (by rfl) ⟨840156, by rfl⟩ : syracuseStep 2240417 = 1680313) B1680313
theorem B2240435 : Blo 1492066 2240435 := bstep (se 1 (by rfl) ⟨1680326, by rfl⟩ : syracuseStep 2240435 = 3360653) B3360653
theorem B2240465 : Blo 1492066 2240465 := bstep (se 2 (by rfl) ⟨840174, by rfl⟩ : syracuseStep 2240465 = 1680349) B1680349
theorem B2240483 : Blo 1492066 2240483 := bstep (se 1 (by rfl) ⟨1680362, by rfl⟩ : syracuseStep 2240483 = 3360725) B3360725
theorem B2240513 : Blo 1492066 2240513 := bstep (se 2 (by rfl) ⟨840192, by rfl⟩ : syracuseStep 2240513 = 1680385) B1680385
theorem B2519059 : Blo 1492066 2519059 := bstep (se 1 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 2519059 = 3778589) B3778589
theorem B2240531 : Blo 1492066 2240531 := bstep (se 1 (by rfl) ⟨1680398, by rfl⟩ : syracuseStep 2240531 = 3360797) B3360797
theorem B2240561 : Blo 1492066 2240561 := bstep (se 2 (by rfl) ⟨840210, by rfl⟩ : syracuseStep 2240561 = 1680421) B1680421
theorem B2240579 : Blo 1492066 2240579 := bstep (se 1 (by rfl) ⟨1680434, by rfl⟩ : syracuseStep 2240579 = 3360869) B3360869
theorem B7663693 : Blo 1492066 7663693 := bstep (se 3 (by rfl) ⟨1436942, by rfl⟩ : syracuseStep 7663693 = 2873885) B2873885
theorem B2240609 : Blo 1492066 2240609 := bstep (se 2 (by rfl) ⟨840228, by rfl⟩ : syracuseStep 2240609 = 1680457) B1680457
theorem B25522289 : Blo 1492066 25522289 := bstep (se 2 (by rfl) ⟨9570858, by rfl⟩ : syracuseStep 25522289 = 19141717) B19141717
theorem B2240627 : Blo 1492066 2240627 := bstep (se 1 (by rfl) ⟨1680470, by rfl⟩ : syracuseStep 2240627 = 3360941) B3360941
theorem B2240657 : Blo 1492066 2240657 := bstep (se 2 (by rfl) ⟨840246, by rfl⟩ : syracuseStep 2240657 = 1680493) B1680493
theorem B2519201 : Blo 1492066 2519201 := bstep (se 2 (by rfl) ⟨944700, by rfl⟩ : syracuseStep 2519201 = 1889401) B1889401
theorem B2240675 : Blo 1492066 2240675 := bstep (se 1 (by rfl) ⟨1680506, by rfl⟩ : syracuseStep 2240675 = 3361013) B3361013
theorem B2240705 : Blo 1492066 2240705 := bstep (se 2 (by rfl) ⟨840264, by rfl⟩ : syracuseStep 2240705 = 1680529) B1680529
theorem B2240723 : Blo 1492066 2240723 := bstep (se 1 (by rfl) ⟨1680542, by rfl⟩ : syracuseStep 2240723 = 3361085) B3361085
theorem B2240753 : Blo 1492066 2240753 := bstep (se 2 (by rfl) ⟨840282, by rfl⟩ : syracuseStep 2240753 = 1680565) B1680565
theorem B2126083 : Blo 1492066 2126083 := bstep (se 1 (by rfl) ⟨1594562, by rfl⟩ : syracuseStep 2126083 = 3189125) B3189125
theorem B2240771 : Blo 1492066 2240771 := bstep (se 1 (by rfl) ⟨1680578, by rfl⟩ : syracuseStep 2240771 = 3361157) B3361157
theorem B5107981 : Blo 1492066 5107981 := bstep (se 3 (by rfl) ⟨957746, by rfl⟩ : syracuseStep 5107981 = 1915493) B1915493
theorem B2519329 : Blo 1492066 2519329 := bstep (se 2 (by rfl) ⟨944748, by rfl⟩ : syracuseStep 2519329 = 1889497) B1889497
theorem B2240801 : Blo 1492066 2240801 := bstep (se 2 (by rfl) ⟨840300, by rfl⟩ : syracuseStep 2240801 = 1680601) B1680601
theorem B2240819 : Blo 1492066 2240819 := bstep (se 1 (by rfl) ⟨1680614, by rfl⟩ : syracuseStep 2240819 = 3361229) B3361229
theorem B2519363 : Blo 1492066 2519363 := bstep (se 1 (by rfl) ⟨1889522, by rfl⟩ : syracuseStep 2519363 = 3779045) B3779045
theorem B5108035 : Blo 1492066 5108035 := bstep (se 1 (by rfl) ⟨3831026, by rfl⟩ : syracuseStep 5108035 = 7662053) B7662053
theorem B4034897 : Blo 1492066 4034897 := bstep (se 2 (by rfl) ⟨1513086, by rfl⟩ : syracuseStep 4034897 = 3026173) B3026173
theorem B2240849 : Blo 1492066 2240849 := bstep (se 2 (by rfl) ⟨840318, by rfl⟩ : syracuseStep 2240849 = 1680637) B1680637
theorem B2240867 : Blo 1492066 2240867 := bstep (se 1 (by rfl) ⟨1680650, by rfl⟩ : syracuseStep 2240867 = 3361301) B3361301
theorem B2240897 : Blo 1492066 2240897 := bstep (se 2 (by rfl) ⟨840336, by rfl⟩ : syracuseStep 2240897 = 1680673) B1680673
theorem B9695621 : Blo 1492066 9695621 := bstep (se 4 (by rfl) ⟨908964, by rfl⟩ : syracuseStep 9695621 = 1817929) B1817929
theorem B4780433 : Blo 1492066 4780433 := bstep (se 2 (by rfl) ⟨1792662, by rfl⟩ : syracuseStep 4780433 = 3585325) B3585325
theorem B3232145 : Blo 1492066 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B2240915 : Blo 1492066 2240915 := bstep (se 1 (by rfl) ⟨1680686, by rfl⟩ : syracuseStep 2240915 = 3361373) B3361373
theorem B2240945 : Blo 1492066 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B2519491 : Blo 1492066 2519491 := bstep (se 1 (by rfl) ⟨1889618, by rfl⟩ : syracuseStep 2519491 = 3779237) B3779237
theorem B2240963 : Blo 1492066 2240963 := bstep (se 1 (by rfl) ⟨1680722, by rfl⟩ : syracuseStep 2240963 = 3361445) B3361445
theorem B2240993 : Blo 1492066 2240993 := bstep (se 2 (by rfl) ⟨840372, by rfl⟩ : syracuseStep 2240993 = 1680745) B1680745
theorem B2241011 : Blo 1492066 2241011 := bstep (se 1 (by rfl) ⟨1680758, by rfl⟩ : syracuseStep 2241011 = 3361517) B3361517
theorem B2241041 : Blo 1492066 2241041 := bstep (se 2 (by rfl) ⟨840390, by rfl⟩ : syracuseStep 2241041 = 1680781) B1680781
theorem B1593875 : Blo 1492066 1593875 := bstep (se 1 (by rfl) ⟨1195406, by rfl⟩ : syracuseStep 1593875 = 2390813) B2390813
theorem B2241059 : Blo 1492066 2241059 := bstep (se 1 (by rfl) ⟨1680794, by rfl⟩ : syracuseStep 2241059 = 3361589) B3361589
theorem B2241089 : Blo 1492066 2241089 := bstep (se 2 (by rfl) ⟨840408, by rfl⟩ : syracuseStep 2241089 = 1680817) B1680817
theorem B2519633 : Blo 1492066 2519633 := bstep (se 2 (by rfl) ⟨944862, by rfl⟩ : syracuseStep 2519633 = 1889725) B1889725
theorem B3781201 : Blo 1492066 3781201 := bstep (se 2 (by rfl) ⟨1417950, by rfl⟩ : syracuseStep 3781201 = 2835901) B2835901
theorem B36803213 : Blo 1492066 36803213 := bstep (se 3 (by rfl) ⟨6900602, by rfl⟩ : syracuseStep 36803213 = 13801205) B13801205
theorem B1888915 : Blo 1492066 1888915 := bstep (se 1 (by rfl) ⟨1416686, by rfl⟩ : syracuseStep 1888915 = 2833373) B2833373
theorem B2519761 : Blo 1492066 2519761 := bstep (se 2 (by rfl) ⟨944910, by rfl⟩ : syracuseStep 2519761 = 1889821) B1889821
theorem B1889011 : Blo 1492066 1889011 := bstep (se 1 (by rfl) ⟨1416758, by rfl⟩ : syracuseStep 1889011 = 2833517) B2833517
theorem B2519795 : Blo 1492066 2519795 := bstep (se 1 (by rfl) ⟨1889846, by rfl⟩ : syracuseStep 2519795 = 3779693) B3779693
theorem B4035395 : Blo 1492066 4035395 := bstep (se 1 (by rfl) ⟨3026546, by rfl⟩ : syracuseStep 4035395 = 6053093) B6053093
theorem B3781475 : Blo 1492066 3781475 := bstep (se 1 (by rfl) ⟨2836106, by rfl⟩ : syracuseStep 3781475 = 5672213) B5672213
theorem B2519923 : Blo 1492066 2519923 := bstep (se 1 (by rfl) ⟨1889942, by rfl⟩ : syracuseStep 2519923 = 3779885) B3779885
theorem B22999949 : Blo 1492066 22999949 := bstep (se 3 (by rfl) ⟨4312490, by rfl⟩ : syracuseStep 22999949 = 8624981) B8624981
theorem B2520065 : Blo 1492066 2520065 := bstep (se 2 (by rfl) ⟨945024, by rfl⟩ : syracuseStep 2520065 = 1890049) B1890049
theorem B3781667 : Blo 1492066 3781667 := bstep (se 1 (by rfl) ⟨2836250, by rfl⟩ : syracuseStep 3781667 = 5672501) B5672501
theorem B8500301 : Blo 1492066 8500301 := bstep (se 3 (by rfl) ⟨1593806, by rfl⟩ : syracuseStep 8500301 = 3187613) B3187613
theorem B2520193 : Blo 1492066 2520193 := bstep (se 2 (by rfl) ⟨945072, by rfl⟩ : syracuseStep 2520193 = 1890145) B1890145
theorem B6378659 : Blo 1492066 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B3232931 : Blo 1492066 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B2520227 : Blo 1492066 2520227 := bstep (se 1 (by rfl) ⟨1890170, by rfl⟩ : syracuseStep 2520227 = 3780341) B3780341
theorem B1889507 : Blo 1492066 1889507 := bstep (se 1 (by rfl) ⟨1417130, by rfl⟩ : syracuseStep 1889507 = 2834261) B2834261
theorem B2520355 : Blo 1492066 2520355 := bstep (se 1 (by rfl) ⟨1890266, by rfl⟩ : syracuseStep 2520355 = 3780533) B3780533
theorem B4248931 : Blo 1492066 4248931 := bstep (se 1 (by rfl) ⟨3186698, by rfl⟩ : syracuseStep 4248931 = 6373397) B6373397
theorem B15324515 : Blo 1492066 15324515 := bstep (se 1 (by rfl) ⟨11493386, by rfl⟩ : syracuseStep 15324515 = 22986773) B22986773
theorem B2127217 : Blo 1492066 2127217 := bstep (se 2 (by rfl) ⟨797706, by rfl⟩ : syracuseStep 2127217 = 1595413) B1595413
theorem B4846979 : Blo 1492066 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B8074637 : Blo 1492066 8074637 := bstep (se 3 (by rfl) ⟨1513994, by rfl⟩ : syracuseStep 8074637 = 3027989) B3027989
theorem B2520497 : Blo 1492066 2520497 := bstep (se 2 (by rfl) ⟨945186, by rfl⟩ : syracuseStep 2520497 = 1890373) B1890373
theorem B1594819 : Blo 1492066 1594819 := bstep (se 1 (by rfl) ⟨1196114, by rfl⟩ : syracuseStep 1594819 = 2392229) B2392229
theorem B4249091 : Blo 1492066 4249091 := bstep (se 1 (by rfl) ⟨3186818, by rfl⟩ : syracuseStep 4249091 = 6373637) B6373637
theorem B8066573 : Blo 1492066 8066573 := bstep (se 3 (by rfl) ⟨1512482, by rfl⟩ : syracuseStep 8066573 = 3024965) B3024965
theorem B2520625 : Blo 1492066 2520625 := bstep (se 2 (by rfl) ⟨945234, by rfl⟩ : syracuseStep 2520625 = 1890469) B1890469
theorem B5666381 : Blo 1492066 5666381 := bstep (se 3 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 5666381 = 2124893) B2124893
theorem B2520659 : Blo 1492066 2520659 := bstep (se 1 (by rfl) ⟨1890494, by rfl⟩ : syracuseStep 2520659 = 3780989) B3780989
theorem B2520787 : Blo 1492066 2520787 := bstep (se 1 (by rfl) ⟨1890590, by rfl⟩ : syracuseStep 2520787 = 3781181) B3781181
theorem B16135949 : Blo 1492066 16135949 := bstep (se 3 (by rfl) ⟨3025490, by rfl⟩ : syracuseStep 16135949 = 6050981) B6050981
theorem B2520929 : Blo 1492066 2520929 := bstep (se 2 (by rfl) ⟨945348, by rfl⟩ : syracuseStep 2520929 = 1890697) B1890697
theorem B1890211 : Blo 1492066 1890211 := bstep (se 1 (by rfl) ⟨1417658, by rfl⟩ : syracuseStep 1890211 = 2835317) B2835317
theorem B5035985 : Blo 1492066 5035985 := bstep (se 2 (by rfl) ⟨1888494, by rfl⟩ : syracuseStep 5035985 = 3776989) B3776989
theorem B2521057 : Blo 1492066 2521057 := bstep (se 2 (by rfl) ⟨945396, by rfl⟩ : syracuseStep 2521057 = 1890793) B1890793
theorem B8501233 : Blo 1492066 8501233 := bstep (se 2 (by rfl) ⟨3187962, by rfl⟩ : syracuseStep 8501233 = 6375925) B6375925
theorem B1701875 : Blo 1492066 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B1890307 : Blo 1492066 1890307 := bstep (se 1 (by rfl) ⟨1417730, by rfl⟩ : syracuseStep 1890307 = 2835461) B2835461
theorem B2521091 : Blo 1492066 2521091 := bstep (se 1 (by rfl) ⟨1890818, by rfl⟩ : syracuseStep 2521091 = 3781637) B3781637
theorem B2521219 : Blo 1492066 2521219 := bstep (se 1 (by rfl) ⟨1890914, by rfl⟩ : syracuseStep 2521219 = 3781829) B3781829
theorem B1702067 : Blo 1492066 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B11335949 : Blo 1492066 11335949 := bstep (se 3 (by rfl) ⟨2125490, by rfl⟩ : syracuseStep 11335949 = 4250981) B4250981
theorem B5667185 : Blo 1492066 5667185 := bstep (se 2 (by rfl) ⟨2125194, by rfl⟩ : syracuseStep 5667185 = 4250389) B4250389
theorem B28694897 : Blo 1492066 28694897 := bstep (se 2 (by rfl) ⟨10760586, by rfl⟩ : syracuseStep 28694897 = 21521173) B21521173
theorem B19143053 : Blo 1492066 19143053 := bstep (se 3 (by rfl) ⟨3589322, by rfl⟩ : syracuseStep 19143053 = 7178645) B7178645
theorem B2832803 : Blo 1492066 2832803 := bstep (se 1 (by rfl) ⟨2124602, by rfl⟩ : syracuseStep 2832803 = 4249205) B4249205
theorem B4782509 : Blo 1492066 4782509 := bstep (se 3 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 4782509 = 1793441) B1793441
theorem B5036525 : Blo 1492066 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B1890803 : Blo 1492066 1890803 := bstep (se 1 (by rfl) ⟨1418102, by rfl⟩ : syracuseStep 1890803 = 2836205) B2836205
theorem B5036579 : Blo 1492066 5036579 := bstep (se 1 (by rfl) ⟨3777434, by rfl⟩ : syracuseStep 5036579 = 7554869) B7554869
theorem B3357233 : Blo 1492066 3357233 := bstep (se 2 (by rfl) ⟨1258962, by rfl⟩ : syracuseStep 3357233 = 2517925) B2517925
theorem B4250161 : Blo 1492066 4250161 := bstep (se 2 (by rfl) ⟨1593810, by rfl⟩ : syracuseStep 4250161 = 3187621) B3187621
theorem B7559729 : Blo 1492066 7559729 := bstep (se 2 (by rfl) ⟨2834898, by rfl⟩ : syracuseStep 7559729 = 5669797) B5669797
theorem B3357251 : Blo 1492066 3357251 := bstep (se 1 (by rfl) ⟨2517938, by rfl⟩ : syracuseStep 3357251 = 5035877) B5035877
theorem B2390627 : Blo 1492066 2390627 := bstep (se 1 (by rfl) ⟨1792970, by rfl⟩ : syracuseStep 2390627 = 3585941) B3585941
theorem B3586787 : Blo 1492066 3586787 := bstep (se 1 (by rfl) ⟨2690090, by rfl⟩ : syracuseStep 3586787 = 5380181) B5380181
theorem B5036849 : Blo 1492066 5036849 := bstep (se 2 (by rfl) ⟨1888818, by rfl⟩ : syracuseStep 5036849 = 3777637) B3777637
theorem B5454641 : Blo 1492066 5454641 := bstep (se 2 (by rfl) ⟨2045490, by rfl⟩ : syracuseStep 5454641 = 4090981) B4090981
theorem B3357521 : Blo 1492066 3357521 := bstep (se 2 (by rfl) ⟨1259070, by rfl⟩ : syracuseStep 3357521 = 2518141) B2518141
theorem B5110609 : Blo 1492066 5110609 := bstep (se 2 (by rfl) ⟨1916478, by rfl⟩ : syracuseStep 5110609 = 3832957) B3832957
theorem B3357539 : Blo 1492066 3357539 := bstep (se 1 (by rfl) ⟨2518154, by rfl⟩ : syracuseStep 3357539 = 5036309) B5036309
theorem B2390915 : Blo 1492066 2390915 := bstep (se 1 (by rfl) ⟨1793186, by rfl⟩ : syracuseStep 2390915 = 3586373) B3586373
theorem B4307921 : Blo 1492066 4307921 := bstep (se 2 (by rfl) ⟨1615470, by rfl⟩ : syracuseStep 4307921 = 3230941) B3230941
theorem B5667853 : Blo 1492066 5667853 := bstep (se 3 (by rfl) ⟨1062722, by rfl⟩ : syracuseStep 5667853 = 2125445) B2125445
theorem B3357809 : Blo 1492066 3357809 := bstep (se 2 (by rfl) ⟨1259178, by rfl⟩ : syracuseStep 3357809 = 2518357) B2518357
theorem B3357827 : Blo 1492066 3357827 := bstep (se 1 (by rfl) ⟨2518370, by rfl⟩ : syracuseStep 3357827 = 5036741) B5036741
theorem B4037795 : Blo 1492066 4037795 := bstep (se 1 (by rfl) ⟨3028346, by rfl⟩ : syracuseStep 4037795 = 6056693) B6056693
theorem B8076451 : Blo 1492066 8076451 := bstep (se 1 (by rfl) ⟨6057338, by rfl⟩ : syracuseStep 8076451 = 12114677) B12114677
theorem B3407107 : Blo 1492066 3407107 := bstep (se 1 (by rfl) ⟨2555330, by rfl⟩ : syracuseStep 3407107 = 5110661) B5110661
theorem B2833699 : Blo 1492066 2833699 := bstep (se 1 (by rfl) ⟨2125274, by rfl⟩ : syracuseStep 2833699 = 4250549) B4250549
theorem B2391331 : Blo 1492066 2391331 := bstep (se 1 (by rfl) ⟨1793498, by rfl⟩ : syracuseStep 2391331 = 3586997) B3586997
theorem B9567557 : Blo 1492066 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B5037389 : Blo 1492066 5037389 := bstep (se 3 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 5037389 = 1889021) B1889021
theorem B1678675 : Blo 1492066 1678675 := bstep (se 1 (by rfl) ⟨1259006, by rfl⟩ : syracuseStep 1678675 = 2518013) B2518013
theorem B5037443 : Blo 1492066 5037443 := bstep (se 1 (by rfl) ⟨3778082, by rfl⟩ : syracuseStep 5037443 = 7556165) B7556165
theorem B4537741 : Blo 1492066 4537741 := bstep (se 3 (by rfl) ⟨850826, by rfl⟩ : syracuseStep 4537741 = 1701653) B1701653
theorem B8068493 : Blo 1492066 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B3358097 : Blo 1492066 3358097 := bstep (se 2 (by rfl) ⟨1259286, by rfl⟩ : syracuseStep 3358097 = 2518573) B2518573
theorem B3358115 : Blo 1492066 3358115 := bstep (se 1 (by rfl) ⟨2518586, by rfl⟩ : syracuseStep 3358115 = 5037173) B5037173
theorem B8502691 : Blo 1492066 8502691 := bstep (se 1 (by rfl) ⟨6377018, by rfl⟩ : syracuseStep 8502691 = 12754037) B12754037
theorem B2833859 : Blo 1492066 2833859 := bstep (se 1 (by rfl) ⟨2125394, by rfl⟩ : syracuseStep 2833859 = 4250789) B4250789
theorem B1678819 : Blo 1492066 1678819 := bstep (se 1 (by rfl) ⟨1259114, by rfl⟩ : syracuseStep 1678819 = 2518229) B2518229
theorem B2391601 : Blo 1492066 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B1678963 : Blo 1492066 1678963 := bstep (se 1 (by rfl) ⟨1259222, by rfl⟩ : syracuseStep 1678963 = 2518445) B2518445
theorem B5037713 : Blo 1492066 5037713 := bstep (se 2 (by rfl) ⟨1889142, by rfl⟩ : syracuseStep 5037713 = 3778285) B3778285
theorem B4783789 : Blo 1492066 4783789 := bstep (se 3 (by rfl) ⟨896960, by rfl⟩ : syracuseStep 4783789 = 1793921) B1793921
theorem B3358385 : Blo 1492066 3358385 := bstep (se 2 (by rfl) ⟨1259394, by rfl⟩ : syracuseStep 3358385 = 2518789) B2518789
theorem B3358403 : Blo 1492066 3358403 := bstep (se 1 (by rfl) ⟨2518802, by rfl⟩ : syracuseStep 3358403 = 5037605) B5037605
theorem B1679107 : Blo 1492066 1679107 := bstep (se 1 (by rfl) ⟨1259330, by rfl⟩ : syracuseStep 1679107 = 2518661) B2518661
theorem B5668643 : Blo 1492066 5668643 := bstep (se 1 (by rfl) ⟨4251482, by rfl⟩ : syracuseStep 5668643 = 8502965) B8502965
theorem B4251437 : Blo 1492066 4251437 := bstep (se 3 (by rfl) ⟨797144, by rfl⟩ : syracuseStep 4251437 = 1594289) B1594289
theorem B2391857 : Blo 1492066 2391857 := bstep (se 2 (by rfl) ⟨896946, by rfl⟩ : syracuseStep 2391857 = 1793893) B1793893
theorem B1679251 : Blo 1492066 1679251 := bstep (se 1 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 1679251 = 2518877) B2518877
theorem B8503217 : Blo 1492066 8503217 := bstep (se 2 (by rfl) ⟨3188706, by rfl⟩ : syracuseStep 8503217 = 6377413) B6377413
theorem B3358673 : Blo 1492066 3358673 := bstep (se 2 (by rfl) ⟨1259502, by rfl⟩ : syracuseStep 3358673 = 2519005) B2519005
theorem B3358691 : Blo 1492066 3358691 := bstep (se 1 (by rfl) ⟨2519018, by rfl⟩ : syracuseStep 3358691 = 5038037) B5038037
theorem B4251619 : Blo 1492066 4251619 := bstep (se 1 (by rfl) ⟨3188714, by rfl⟩ : syracuseStep 4251619 = 6377429) B6377429
theorem B7561187 : Blo 1492066 7561187 := bstep (se 1 (by rfl) ⟨5670890, by rfl⟩ : syracuseStep 7561187 = 11341781) B11341781
theorem B2834443 : Blo 1492066 2834443 := bstep (se 1 (by rfl) ⟨2125832, by rfl⟩ : syracuseStep 2834443 = 4251665) B4251665
theorem B3358745 : Blo 1492066 3358745 := bstep (se 2 (by rfl) ⟨1259529, by rfl⟩ : syracuseStep 3358745 = 2519059) B2519059
theorem B5038145 : Blo 1492066 5038145 := bstep (se 2 (by rfl) ⟨1889304, by rfl⟩ : syracuseStep 5038145 = 3778609) B3778609
theorem B17014859 : Blo 1492066 17014859 := bstep (se 1 (by rfl) ⟨12761144, by rfl⟩ : syracuseStep 17014859 = 25522289) B25522289
theorem B2392151 : Blo 1492066 2392151 := bstep (se 1 (by rfl) ⟨1794113, by rfl⟩ : syracuseStep 2392151 = 3588227) B3588227
theorem B1679467 : Blo 1492066 1679467 := bstep (se 1 (by rfl) ⟨1259600, by rfl⟩ : syracuseStep 1679467 = 2519201) B2519201
theorem B3358835 : Blo 1492066 3358835 := bstep (se 1 (by rfl) ⟨2519126, by rfl⟩ : syracuseStep 3358835 = 5038253) B5038253
theorem B3358871 : Blo 1492066 3358871 := bstep (se 1 (by rfl) ⟨2519153, by rfl⟩ : syracuseStep 3358871 = 5038307) B5038307
theorem B12746929 : Blo 1492066 12746929 := bstep (se 2 (by rfl) ⟨4780098, by rfl⟩ : syracuseStep 12746929 = 9560197) B9560197
theorem B54452405 : Blo 1492066 54452405 := bstep (se 5 (by rfl) ⟨2552456, by rfl⟩ : syracuseStep 54452405 = 5104913) B5104913
theorem B2392267 : Blo 1492066 2392267 := bstep (se 1 (by rfl) ⟨1794200, by rfl⟩ : syracuseStep 2392267 = 3588401) B3588401
theorem B1679575 : Blo 1492066 1679575 := bstep (se 1 (by rfl) ⟨1259681, by rfl⟩ : syracuseStep 1679575 = 2519363) B2519363
theorem B6463747 : Blo 1492066 6463747 := bstep (se 1 (by rfl) ⟨4847810, by rfl⟩ : syracuseStep 6463747 = 9695621) B9695621
theorem B3186955 : Blo 1492066 3186955 := bstep (se 1 (by rfl) ⟨2390216, by rfl⟩ : syracuseStep 3186955 = 4780433) B4780433
theorem B2154763 : Blo 1492066 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B4538675 : Blo 1492066 4538675 := bstep (se 1 (by rfl) ⟨3404006, by rfl⟩ : syracuseStep 4538675 = 6808013) B6808013
theorem B3359051 : Blo 1492066 3359051 := bstep (se 1 (by rfl) ⟨2519288, by rfl⟩ : syracuseStep 3359051 = 5038577) B5038577
theorem B2834777 : Blo 1492066 2834777 := bstep (se 2 (by rfl) ⟨1063041, by rfl⟩ : syracuseStep 2834777 = 2126083) B2126083
theorem B3359105 : Blo 1492066 3359105 := bstep (se 2 (by rfl) ⟨1259664, by rfl⟩ : syracuseStep 3359105 = 2519329) B2519329
theorem B1679755 : Blo 1492066 1679755 := bstep (se 1 (by rfl) ⟨1259816, by rfl⟩ : syracuseStep 1679755 = 2519633) B2519633
theorem B24535475 : Blo 1492066 24535475 := bstep (se 1 (by rfl) ⟨18401606, by rfl⟩ : syracuseStep 24535475 = 36803213) B36803213
theorem B4252121 : Blo 1492066 4252121 := bstep (se 2 (by rfl) ⟨1594545, by rfl⟩ : syracuseStep 4252121 = 3189091) B3189091
theorem B4538845 : Blo 1492066 4538845 := bstep (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) B1702067
theorem B1679863 : Blo 1492066 1679863 := bstep (se 1 (by rfl) ⟨1259897, by rfl⟩ : syracuseStep 1679863 = 2519795) B2519795
theorem B3359321 : Blo 1492066 3359321 := bstep (se 2 (by rfl) ⟨1259745, by rfl⟩ : syracuseStep 3359321 = 2519491) B2519491
theorem B5038685 : Blo 1492066 5038685 := bstep (se 3 (by rfl) ⟨944753, by rfl⟩ : syracuseStep 5038685 = 1889507) B1889507
theorem B1680043 : Blo 1492066 1680043 := bstep (se 1 (by rfl) ⟨1260032, by rfl⟩ : syracuseStep 1680043 = 2520065) B2520065
theorem B3359411 : Blo 1492066 3359411 := bstep (se 1 (by rfl) ⟨2519558, by rfl⟩ : syracuseStep 3359411 = 5039117) B5039117
theorem B3359447 : Blo 1492066 3359447 := bstep (se 1 (by rfl) ⟨2519585, by rfl⟩ : syracuseStep 3359447 = 5039171) B5039171
theorem B4252439 : Blo 1492066 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B1680151 : Blo 1492066 1680151 := bstep (se 1 (by rfl) ⟨1260113, by rfl⟩ : syracuseStep 1680151 = 2520227) B2520227
theorem B4088665 : Blo 1492066 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B4916057 : Blo 1492066 4916057 := bstep (se 2 (by rfl) ⟨1843521, by rfl⟩ : syracuseStep 4916057 = 3687043) B3687043
theorem B9569117 : Blo 1492066 9569117 := bstep (se 3 (by rfl) ⟨1794209, by rfl⟩ : syracuseStep 9569117 = 3588419) B3588419
theorem B3359627 : Blo 1492066 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B10216343 : Blo 1492066 10216343 := bstep (se 1 (by rfl) ⟨7662257, by rfl⟩ : syracuseStep 10216343 = 15324515) B15324515
theorem B5669783 : Blo 1492066 5669783 := bstep (se 1 (by rfl) ⟨4252337, by rfl⟩ : syracuseStep 5669783 = 8504675) B8504675
theorem B2392985 : Blo 1492066 2392985 := bstep (se 2 (by rfl) ⟨897369, by rfl⟩ : syracuseStep 2392985 = 1794739) B1794739
theorem B5383091 : Blo 1492066 5383091 := bstep (se 1 (by rfl) ⟨4037318, by rfl⟩ : syracuseStep 5383091 = 8074637) B8074637
theorem B6218689 : Blo 1492066 6218689 := bstep (se 2 (by rfl) ⟨2332008, by rfl⟩ : syracuseStep 6218689 = 4664017) B4664017
theorem B3359681 : Blo 1492066 3359681 := bstep (se 2 (by rfl) ⟨1259880, by rfl⟩ : syracuseStep 3359681 = 2519761) B2519761
theorem B1680331 : Blo 1492066 1680331 := bstep (se 1 (by rfl) ⟨1260248, by rfl⟩ : syracuseStep 1680331 = 2520497) B2520497
theorem B10757069 : Blo 1492066 10757069 := bstep (se 3 (by rfl) ⟨2016950, by rfl⟩ : syracuseStep 10757069 = 4033901) B4033901
theorem B2835415 : Blo 1492066 2835415 := bstep (se 1 (by rfl) ⟨2126561, by rfl⟩ : syracuseStep 2835415 = 4253123) B4253123
theorem B3777587 : Blo 1492066 3777587 := bstep (se 1 (by rfl) ⟨2833190, by rfl⟩ : syracuseStep 3777587 = 5666381) B5666381
theorem B1680439 : Blo 1492066 1680439 := bstep (se 1 (by rfl) ⟨1260329, by rfl⟩ : syracuseStep 1680439 = 2520659) B2520659
theorem B1492075 : Blo 1492066 1492075 := bstep (se 1 (by rfl) ⟨1119056, by rfl⟩ : syracuseStep 1492075 = 2238113) B2238113
theorem B1492087 : Blo 1492066 1492087 := bstep (se 1 (by rfl) ⟨1119065, by rfl⟩ : syracuseStep 1492087 = 2238131) B2238131
theorem B1492107 : Blo 1492066 1492107 := bstep (se 1 (by rfl) ⟨1119080, by rfl⟩ : syracuseStep 1492107 = 2238161) B2238161
theorem B1492119 : Blo 1492066 1492119 := bstep (se 1 (by rfl) ⟨1119089, by rfl⟩ : syracuseStep 1492119 = 2238179) B2238179
theorem B3359897 : Blo 1492066 3359897 := bstep (se 2 (by rfl) ⟨1259961, by rfl⟩ : syracuseStep 3359897 = 2519923) B2519923
theorem B1492139 : Blo 1492066 1492139 := bstep (se 1 (by rfl) ⟨1119104, by rfl⟩ : syracuseStep 1492139 = 2238209) B2238209
theorem B10757299 : Blo 1492066 10757299 := bstep (se 1 (by rfl) ⟨8067974, by rfl⟩ : syracuseStep 10757299 = 16135949) B16135949
theorem B1492151 : Blo 1492066 1492151 := bstep (se 1 (by rfl) ⟨1119113, by rfl⟩ : syracuseStep 1492151 = 2238227) B2238227
theorem B1492171 : Blo 1492066 1492171 := bstep (se 1 (by rfl) ⟨1119128, by rfl⟩ : syracuseStep 1492171 = 2238257) B2238257
theorem B1492183 : Blo 1492066 1492183 := bstep (se 1 (by rfl) ⟨1119137, by rfl⟩ : syracuseStep 1492183 = 2238275) B2238275
theorem B1492203 : Blo 1492066 1492203 := bstep (se 1 (by rfl) ⟨1119152, by rfl⟩ : syracuseStep 1492203 = 2238305) B2238305
theorem B1680619 : Blo 1492066 1680619 := bstep (se 1 (by rfl) ⟨1260464, by rfl⟩ : syracuseStep 1680619 = 2520929) B2520929
theorem B3359987 : Blo 1492066 3359987 := bstep (se 1 (by rfl) ⟨2519990, by rfl⟩ : syracuseStep 3359987 = 5039981) B5039981
theorem B1492215 : Blo 1492066 1492215 := bstep (se 1 (by rfl) ⟨1119161, by rfl⟩ : syracuseStep 1492215 = 2238323) B2238323
theorem B1492235 : Blo 1492066 1492235 := bstep (se 1 (by rfl) ⟨1119176, by rfl⟩ : syracuseStep 1492235 = 2238353) B2238353
theorem B1492247 : Blo 1492066 1492247 := bstep (se 1 (by rfl) ⟨1119185, by rfl⟩ : syracuseStep 1492247 = 2238371) B2238371
theorem B3360023 : Blo 1492066 3360023 := bstep (se 1 (by rfl) ⟨2520017, by rfl⟩ : syracuseStep 3360023 = 5040035) B5040035
theorem B1492267 : Blo 1492066 1492267 := bstep (se 1 (by rfl) ⟨1119200, by rfl⟩ : syracuseStep 1492267 = 2238401) B2238401
theorem B1492279 : Blo 1492066 1492279 := bstep (se 1 (by rfl) ⟨1119209, by rfl⟩ : syracuseStep 1492279 = 2238419) B2238419
theorem B1492299 : Blo 1492066 1492299 := bstep (se 1 (by rfl) ⟨1119224, by rfl⟩ : syracuseStep 1492299 = 2238449) B2238449
theorem B1492311 : Blo 1492066 1492311 := bstep (se 1 (by rfl) ⟨1119233, by rfl⟩ : syracuseStep 1492311 = 2238467) B2238467
theorem B1680727 : Blo 1492066 1680727 := bstep (se 1 (by rfl) ⟨1260545, by rfl⟩ : syracuseStep 1680727 = 2521091) B2521091
theorem B1492331 : Blo 1492066 1492331 := bstep (se 1 (by rfl) ⟨1119248, by rfl⟩ : syracuseStep 1492331 = 2238497) B2238497
theorem B1492343 : Blo 1492066 1492343 := bstep (se 1 (by rfl) ⟨1119257, by rfl⟩ : syracuseStep 1492343 = 2238515) B2238515
theorem B1492363 : Blo 1492066 1492363 := bstep (se 1 (by rfl) ⟨1119272, by rfl⟩ : syracuseStep 1492363 = 2238545) B2238545
theorem B1492375 : Blo 1492066 1492375 := bstep (se 1 (by rfl) ⟨1119281, by rfl⟩ : syracuseStep 1492375 = 2238563) B2238563
theorem B1492395 : Blo 1492066 1492395 := bstep (se 1 (by rfl) ⟨1119296, by rfl⟩ : syracuseStep 1492395 = 2238593) B2238593
theorem B5383597 : Blo 1492066 5383597 := bstep (se 3 (by rfl) ⟨1009424, by rfl⟩ : syracuseStep 5383597 = 2018849) B2018849
theorem B1492407 : Blo 1492066 1492407 := bstep (se 1 (by rfl) ⟨1119305, by rfl⟩ : syracuseStep 1492407 = 2238611) B2238611
theorem B1492427 : Blo 1492066 1492427 := bstep (se 1 (by rfl) ⟨1119320, by rfl⟩ : syracuseStep 1492427 = 2238641) B2238641
theorem B3360203 : Blo 1492066 3360203 := bstep (se 1 (by rfl) ⟨2520152, by rfl⟩ : syracuseStep 3360203 = 5040305) B5040305
theorem B1492439 : Blo 1492066 1492439 := bstep (se 1 (by rfl) ⟨1119329, by rfl⟩ : syracuseStep 1492439 = 2238659) B2238659
theorem B1492459 : Blo 1492066 1492459 := bstep (se 1 (by rfl) ⟨1119344, by rfl⟩ : syracuseStep 1492459 = 2238689) B2238689
theorem B1492471 : Blo 1492066 1492471 := bstep (se 1 (by rfl) ⟨1119353, by rfl⟩ : syracuseStep 1492471 = 2238707) B2238707
theorem B3360257 : Blo 1492066 3360257 := bstep (se 2 (by rfl) ⟨1260096, by rfl⟩ : syracuseStep 3360257 = 2520193) B2520193
theorem B1492491 : Blo 1492066 1492491 := bstep (se 1 (by rfl) ⟨1119368, by rfl⟩ : syracuseStep 1492491 = 2238737) B2238737
theorem B11331089 : Blo 1492066 11331089 := bstep (se 2 (by rfl) ⟨4249158, by rfl⟩ : syracuseStep 11331089 = 8498317) B8498317
theorem B1492503 : Blo 1492066 1492503 := bstep (se 1 (by rfl) ⟨1119377, by rfl⟩ : syracuseStep 1492503 = 2238755) B2238755
theorem B1492523 : Blo 1492066 1492523 := bstep (se 1 (by rfl) ⟨1119392, by rfl⟩ : syracuseStep 1492523 = 2238785) B2238785
theorem B1492535 : Blo 1492066 1492535 := bstep (se 1 (by rfl) ⟨1119401, by rfl⟩ : syracuseStep 1492535 = 2238803) B2238803
theorem B4253249 : Blo 1492066 4253249 := bstep (se 2 (by rfl) ⟨1594968, by rfl⟩ : syracuseStep 4253249 = 3189937) B3189937
theorem B1492555 : Blo 1492066 1492555 := bstep (se 1 (by rfl) ⟨1119416, by rfl⟩ : syracuseStep 1492555 = 2238833) B2238833
theorem B3778123 : Blo 1492066 3778123 := bstep (se 1 (by rfl) ⟨2833592, by rfl⟩ : syracuseStep 3778123 = 5667185) B5667185
theorem B19129931 : Blo 1492066 19129931 := bstep (se 1 (by rfl) ⟨14347448, by rfl⟩ : syracuseStep 19129931 = 28694897) B28694897
theorem B1492567 : Blo 1492066 1492567 := bstep (se 1 (by rfl) ⟨1119425, by rfl⟩ : syracuseStep 1492567 = 2238851) B2238851
theorem B1492587 : Blo 1492066 1492587 := bstep (se 1 (by rfl) ⟨1119440, by rfl⟩ : syracuseStep 1492587 = 2238881) B2238881
theorem B3188339 : Blo 1492066 3188339 := bstep (se 1 (by rfl) ⟨2391254, by rfl⟩ : syracuseStep 3188339 = 4782509) B4782509
theorem B1492599 : Blo 1492066 1492599 := bstep (se 1 (by rfl) ⟨1119449, by rfl⟩ : syracuseStep 1492599 = 2238899) B2238899
theorem B1492619 : Blo 1492066 1492619 := bstep (se 1 (by rfl) ⟨1119464, by rfl⟩ : syracuseStep 1492619 = 2238929) B2238929
theorem B1492631 : Blo 1492066 1492631 := bstep (se 1 (by rfl) ⟨1119473, by rfl⟩ : syracuseStep 1492631 = 2238947) B2238947
theorem B1492651 : Blo 1492066 1492651 := bstep (se 1 (by rfl) ⟨1119488, by rfl⟩ : syracuseStep 1492651 = 2238977) B2238977
theorem B1492663 : Blo 1492066 1492663 := bstep (se 1 (by rfl) ⟨1119497, by rfl⟩ : syracuseStep 1492663 = 2238995) B2238995
theorem B2238155 : Blo 1492066 2238155 := bstep (se 1 (by rfl) ⟨1678616, by rfl⟩ : syracuseStep 2238155 = 3357233) B3357233
theorem B1492683 : Blo 1492066 1492683 := bstep (se 1 (by rfl) ⟨1119512, by rfl⟩ : syracuseStep 1492683 = 2239025) B2239025
theorem B5039819 : Blo 1492066 5039819 := bstep (se 1 (by rfl) ⟨3779864, by rfl⟩ : syracuseStep 5039819 = 7559729) B7559729
theorem B2238167 : Blo 1492066 2238167 := bstep (se 1 (by rfl) ⟨1678625, by rfl⟩ : syracuseStep 2238167 = 3357251) B3357251
theorem B1492695 : Blo 1492066 1492695 := bstep (se 1 (by rfl) ⟨1119521, by rfl⟩ : syracuseStep 1492695 = 2239043) B2239043
theorem B3778265 : Blo 1492066 3778265 := bstep (se 2 (by rfl) ⟨1416849, by rfl⟩ : syracuseStep 3778265 = 2833699) B2833699
theorem B3188441 : Blo 1492066 3188441 := bstep (se 2 (by rfl) ⟨1195665, by rfl⟩ : syracuseStep 3188441 = 2391331) B2391331
theorem B3360473 : Blo 1492066 3360473 := bstep (se 2 (by rfl) ⟨1260177, by rfl⟩ : syracuseStep 3360473 = 2520355) B2520355
theorem B7562969 : Blo 1492066 7562969 := bstep (se 2 (by rfl) ⟨2836113, by rfl⟩ : syracuseStep 7562969 = 5672227) B5672227
theorem B1492715 : Blo 1492066 1492715 := bstep (se 1 (by rfl) ⟨1119536, by rfl⟩ : syracuseStep 1492715 = 2239073) B2239073
theorem B1492727 : Blo 1492066 1492727 := bstep (se 1 (by rfl) ⟨1119545, by rfl⟩ : syracuseStep 1492727 = 2239091) B2239091
theorem B1492747 : Blo 1492066 1492747 := bstep (se 1 (by rfl) ⟨1119560, by rfl⟩ : syracuseStep 1492747 = 2239121) B2239121
theorem B2836235 : Blo 1492066 2836235 := bstep (se 1 (by rfl) ⟨2127176, by rfl⟩ : syracuseStep 2836235 = 4254353) B4254353
theorem B1492759 : Blo 1492066 1492759 := bstep (se 1 (by rfl) ⟨1119569, by rfl⟩ : syracuseStep 1492759 = 2239139) B2239139
theorem B2238233 : Blo 1492066 2238233 := bstep (se 2 (by rfl) ⟨839337, by rfl⟩ : syracuseStep 2238233 = 1678675) B1678675
theorem B1492779 : Blo 1492066 1492779 := bstep (se 1 (by rfl) ⟨1119584, by rfl⟩ : syracuseStep 1492779 = 2239169) B2239169
theorem B3360563 : Blo 1492066 3360563 := bstep (se 1 (by rfl) ⟨2520422, by rfl⟩ : syracuseStep 3360563 = 5040845) B5040845
theorem B1492791 : Blo 1492066 1492791 := bstep (se 1 (by rfl) ⟨1119593, by rfl⟩ : syracuseStep 1492791 = 2239187) B2239187
theorem B2836289 : Blo 1492066 2836289 := bstep (se 2 (by rfl) ⟨1063608, by rfl⟩ : syracuseStep 2836289 = 2127217) B2127217
theorem B1492811 : Blo 1492066 1492811 := bstep (se 1 (by rfl) ⟨1119608, by rfl⟩ : syracuseStep 1492811 = 2239217) B2239217
theorem B1492823 : Blo 1492066 1492823 := bstep (se 1 (by rfl) ⟨1119617, by rfl⟩ : syracuseStep 1492823 = 2239235) B2239235
theorem B3360599 : Blo 1492066 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B1492843 : Blo 1492066 1492843 := bstep (se 1 (by rfl) ⟨1119632, by rfl⟩ : syracuseStep 1492843 = 2239265) B2239265
theorem B1492855 : Blo 1492066 1492855 := bstep (se 1 (by rfl) ⟨1119641, by rfl⟩ : syracuseStep 1492855 = 2239283) B2239283
theorem B2238347 : Blo 1492066 2238347 := bstep (se 1 (by rfl) ⟨1678760, by rfl⟩ : syracuseStep 2238347 = 3357521) B3357521
theorem B1492875 : Blo 1492066 1492875 := bstep (se 1 (by rfl) ⟨1119656, by rfl⟩ : syracuseStep 1492875 = 2239313) B2239313
theorem B2238359 : Blo 1492066 2238359 := bstep (se 1 (by rfl) ⟨1678769, by rfl⟩ : syracuseStep 2238359 = 3357539) B3357539
theorem B1492887 : Blo 1492066 1492887 := bstep (se 1 (by rfl) ⟨1119665, by rfl⟩ : syracuseStep 1492887 = 2239331) B2239331
theorem B1492907 : Blo 1492066 1492907 := bstep (se 1 (by rfl) ⟨1119680, by rfl⟩ : syracuseStep 1492907 = 2239361) B2239361
theorem B1492919 : Blo 1492066 1492919 := bstep (se 1 (by rfl) ⟨1119689, by rfl⟩ : syracuseStep 1492919 = 2239379) B2239379
theorem B1492939 : Blo 1492066 1492939 := bstep (se 1 (by rfl) ⟨1119704, by rfl⟩ : syracuseStep 1492939 = 2239409) B2239409
theorem B1492951 : Blo 1492066 1492951 := bstep (se 1 (by rfl) ⟨1119713, by rfl⟩ : syracuseStep 1492951 = 2239427) B2239427
theorem B2238425 : Blo 1492066 2238425 := bstep (se 2 (by rfl) ⟨839409, by rfl⟩ : syracuseStep 2238425 = 1678819) B1678819
theorem B5040089 : Blo 1492066 5040089 := bstep (se 2 (by rfl) ⟨1890033, by rfl⟩ : syracuseStep 5040089 = 3780067) B3780067
theorem B1492971 : Blo 1492066 1492971 := bstep (se 1 (by rfl) ⟨1119728, by rfl⟩ : syracuseStep 1492971 = 2239457) B2239457
theorem B1492983 : Blo 1492066 1492983 := bstep (se 1 (by rfl) ⟨1119737, by rfl⟩ : syracuseStep 1492983 = 2239475) B2239475
theorem B1493003 : Blo 1492066 1493003 := bstep (se 1 (by rfl) ⟨1119752, by rfl⟩ : syracuseStep 1493003 = 2239505) B2239505
theorem B3360779 : Blo 1492066 3360779 := bstep (se 1 (by rfl) ⟨2520584, by rfl⟩ : syracuseStep 3360779 = 5041169) B5041169
theorem B1493015 : Blo 1492066 1493015 := bstep (se 1 (by rfl) ⟨1119761, by rfl⟩ : syracuseStep 1493015 = 2239523) B2239523
theorem B4786199 : Blo 1492066 4786199 := bstep (se 1 (by rfl) ⟨3589649, by rfl⟩ : syracuseStep 4786199 = 7179299) B7179299
theorem B1493035 : Blo 1492066 1493035 := bstep (se 1 (by rfl) ⟨1119776, by rfl⟩ : syracuseStep 1493035 = 2239553) B2239553
theorem B1493047 : Blo 1492066 1493047 := bstep (se 1 (by rfl) ⟨1119785, by rfl⟩ : syracuseStep 1493047 = 2239571) B2239571
theorem B3188801 : Blo 1492066 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B3360833 : Blo 1492066 3360833 := bstep (se 2 (by rfl) ⟨1260312, by rfl⟩ : syracuseStep 3360833 = 2520625) B2520625
theorem B2238539 : Blo 1492066 2238539 := bstep (se 1 (by rfl) ⟨1678904, by rfl⟩ : syracuseStep 2238539 = 3357809) B3357809
theorem B1493067 : Blo 1492066 1493067 := bstep (se 1 (by rfl) ⟨1119800, by rfl⟩ : syracuseStep 1493067 = 2239601) B2239601
theorem B2238551 : Blo 1492066 2238551 := bstep (se 1 (by rfl) ⟨1678913, by rfl⟩ : syracuseStep 2238551 = 3357827) B3357827
theorem B1493079 : Blo 1492066 1493079 := bstep (se 1 (by rfl) ⟨1119809, by rfl⟩ : syracuseStep 1493079 = 2239619) B2239619
theorem B1493099 : Blo 1492066 1493099 := bstep (se 1 (by rfl) ⟨1119824, by rfl⟩ : syracuseStep 1493099 = 2239649) B2239649
theorem B1493111 : Blo 1492066 1493111 := bstep (se 1 (by rfl) ⟨1119833, by rfl⟩ : syracuseStep 1493111 = 2239667) B2239667
theorem B5671043 : Blo 1492066 5671043 := bstep (se 1 (by rfl) ⟨4253282, by rfl⟩ : syracuseStep 5671043 = 8506565) B8506565
theorem B1493131 : Blo 1492066 1493131 := bstep (se 1 (by rfl) ⟨1119848, by rfl⟩ : syracuseStep 1493131 = 2239697) B2239697
theorem B1493143 : Blo 1492066 1493143 := bstep (se 1 (by rfl) ⟨1119857, by rfl⟩ : syracuseStep 1493143 = 2239715) B2239715
theorem B2238617 : Blo 1492066 2238617 := bstep (se 2 (by rfl) ⟨839481, by rfl⟩ : syracuseStep 2238617 = 1678963) B1678963
theorem B1493163 : Blo 1492066 1493163 := bstep (se 1 (by rfl) ⟨1119872, by rfl⟩ : syracuseStep 1493163 = 2239745) B2239745
theorem B1493175 : Blo 1492066 1493175 := bstep (se 1 (by rfl) ⟨1119881, by rfl⟩ : syracuseStep 1493175 = 2239763) B2239763
theorem B1493195 : Blo 1492066 1493195 := bstep (se 1 (by rfl) ⟨1119896, by rfl⟩ : syracuseStep 1493195 = 2239793) B2239793
theorem B1493207 : Blo 1492066 1493207 := bstep (se 1 (by rfl) ⟨1119905, by rfl⟩ : syracuseStep 1493207 = 2239811) B2239811
theorem B1493227 : Blo 1492066 1493227 := bstep (se 1 (by rfl) ⟨1119920, by rfl⟩ : syracuseStep 1493227 = 2239841) B2239841
theorem B1493239 : Blo 1492066 1493239 := bstep (se 1 (by rfl) ⟨1119929, by rfl⟩ : syracuseStep 1493239 = 2239859) B2239859
theorem B2238731 : Blo 1492066 2238731 := bstep (se 1 (by rfl) ⟨1679048, by rfl⟩ : syracuseStep 2238731 = 3358097) B3358097
theorem B1493259 : Blo 1492066 1493259 := bstep (se 1 (by rfl) ⟨1119944, by rfl⟩ : syracuseStep 1493259 = 2239889) B2239889
theorem B2238743 : Blo 1492066 2238743 := bstep (se 1 (by rfl) ⟨1679057, by rfl⟩ : syracuseStep 2238743 = 3358115) B3358115
theorem B1493271 : Blo 1492066 1493271 := bstep (se 1 (by rfl) ⟨1119953, by rfl⟩ : syracuseStep 1493271 = 2239907) B2239907
theorem B3361049 : Blo 1492066 3361049 := bstep (se 2 (by rfl) ⟨1260393, by rfl⟩ : syracuseStep 3361049 = 2520787) B2520787
theorem B1493291 : Blo 1492066 1493291 := bstep (se 1 (by rfl) ⟨1119968, by rfl⟩ : syracuseStep 1493291 = 2239937) B2239937
theorem B1493303 : Blo 1492066 1493303 := bstep (se 1 (by rfl) ⟨1119977, by rfl⟩ : syracuseStep 1493303 = 2239955) B2239955
theorem B1493323 : Blo 1492066 1493323 := bstep (se 1 (by rfl) ⟨1119992, by rfl⟩ : syracuseStep 1493323 = 2239985) B2239985
theorem B1493335 : Blo 1492066 1493335 := bstep (se 1 (by rfl) ⟨1120001, by rfl⟩ : syracuseStep 1493335 = 2240003) B2240003
theorem B2238809 : Blo 1492066 2238809 := bstep (se 2 (by rfl) ⟨839553, by rfl⟩ : syracuseStep 2238809 = 1679107) B1679107
theorem B6375773 : Blo 1492066 6375773 := bstep (se 3 (by rfl) ⟨1195457, by rfl⟩ : syracuseStep 6375773 = 2390915) B2390915
theorem B1493355 : Blo 1492066 1493355 := bstep (se 1 (by rfl) ⟨1120016, by rfl⟩ : syracuseStep 1493355 = 2240033) B2240033
theorem B3361139 : Blo 1492066 3361139 := bstep (se 1 (by rfl) ⟨2520854, by rfl⟩ : syracuseStep 3361139 = 5041709) B5041709
theorem B1493367 : Blo 1492066 1493367 := bstep (se 1 (by rfl) ⟨1120025, by rfl⟩ : syracuseStep 1493367 = 2240051) B2240051
theorem B1493387 : Blo 1492066 1493387 := bstep (se 1 (by rfl) ⟨1120040, by rfl⟩ : syracuseStep 1493387 = 2240081) B2240081
theorem B1493399 : Blo 1492066 1493399 := bstep (se 1 (by rfl) ⟨1120049, by rfl⟩ : syracuseStep 1493399 = 2240099) B2240099
theorem B3361175 : Blo 1492066 3361175 := bstep (se 1 (by rfl) ⟨2520881, by rfl⟩ : syracuseStep 3361175 = 5041763) B5041763
theorem B1493419 : Blo 1492066 1493419 := bstep (se 1 (by rfl) ⟨1120064, by rfl⟩ : syracuseStep 1493419 = 2240129) B2240129
theorem B16370099 : Blo 1492066 16370099 := bstep (se 1 (by rfl) ⟨12277574, by rfl⟩ : syracuseStep 16370099 = 24555149) B24555149
theorem B1493431 : Blo 1492066 1493431 := bstep (se 1 (by rfl) ⟨1120073, by rfl⟩ : syracuseStep 1493431 = 2240147) B2240147
theorem B2238923 : Blo 1492066 2238923 := bstep (se 1 (by rfl) ⟨1679192, by rfl⟩ : syracuseStep 2238923 = 3358385) B3358385
theorem B1493451 : Blo 1492066 1493451 := bstep (se 1 (by rfl) ⟨1120088, by rfl⟩ : syracuseStep 1493451 = 2240177) B2240177
theorem B2238935 : Blo 1492066 2238935 := bstep (se 1 (by rfl) ⟨1679201, by rfl⟩ : syracuseStep 2238935 = 3358403) B3358403
theorem B1493463 : Blo 1492066 1493463 := bstep (se 1 (by rfl) ⟨1120097, by rfl⟩ : syracuseStep 1493463 = 2240195) B2240195
theorem B1493483 : Blo 1492066 1493483 := bstep (se 1 (by rfl) ⟨1120112, by rfl⟩ : syracuseStep 1493483 = 2240225) B2240225
theorem B1493495 : Blo 1492066 1493495 := bstep (se 1 (by rfl) ⟨1120121, by rfl⟩ : syracuseStep 1493495 = 2240243) B2240243
theorem B1493515 : Blo 1492066 1493515 := bstep (se 1 (by rfl) ⟨1120136, by rfl⟩ : syracuseStep 1493515 = 2240273) B2240273
theorem B3779095 : Blo 1492066 3779095 := bstep (se 1 (by rfl) ⟨2834321, by rfl⟩ : syracuseStep 3779095 = 5668643) B5668643
theorem B1493527 : Blo 1492066 1493527 := bstep (se 1 (by rfl) ⟨1120145, by rfl⟩ : syracuseStep 1493527 = 2240291) B2240291
theorem B2239001 : Blo 1492066 2239001 := bstep (se 2 (by rfl) ⟨839625, by rfl⟩ : syracuseStep 2239001 = 1679251) B1679251
theorem B11340323 : Blo 1492066 11340323 := bstep (se 1 (by rfl) ⟨8505242, by rfl⟩ : syracuseStep 11340323 = 17010485) B17010485
theorem B1493547 : Blo 1492066 1493547 := bstep (se 1 (by rfl) ⟨1120160, by rfl⟩ : syracuseStep 1493547 = 2240321) B2240321
theorem B1493559 : Blo 1492066 1493559 := bstep (se 1 (by rfl) ⟨1120169, by rfl⟩ : syracuseStep 1493559 = 2240339) B2240339
theorem B1493579 : Blo 1492066 1493579 := bstep (se 1 (by rfl) ⟨1120184, by rfl⟩ : syracuseStep 1493579 = 2240369) B2240369
theorem B3361355 : Blo 1492066 3361355 := bstep (se 1 (by rfl) ⟨2521016, by rfl⟩ : syracuseStep 3361355 = 5042033) B5042033
theorem B1493591 : Blo 1492066 1493591 := bstep (se 1 (by rfl) ⟨1120193, by rfl⟩ : syracuseStep 1493591 = 2240387) B2240387
theorem B1493611 : Blo 1492066 1493611 := bstep (se 1 (by rfl) ⟨1120208, by rfl⟩ : syracuseStep 1493611 = 2240417) B2240417
theorem B1493623 : Blo 1492066 1493623 := bstep (se 1 (by rfl) ⟨1120217, by rfl⟩ : syracuseStep 1493623 = 2240435) B2240435
theorem B3361409 : Blo 1492066 3361409 := bstep (se 2 (by rfl) ⟨1260528, by rfl⟩ : syracuseStep 3361409 = 2521057) B2521057
theorem B2239115 : Blo 1492066 2239115 := bstep (se 1 (by rfl) ⟨1679336, by rfl⟩ : syracuseStep 2239115 = 3358673) B3358673
theorem B1493643 : Blo 1492066 1493643 := bstep (se 1 (by rfl) ⟨1120232, by rfl⟩ : syracuseStep 1493643 = 2240465) B2240465
theorem B2239127 : Blo 1492066 2239127 := bstep (se 1 (by rfl) ⟨1679345, by rfl⟩ : syracuseStep 2239127 = 3358691) B3358691
theorem B5040791 : Blo 1492066 5040791 := bstep (se 1 (by rfl) ⟨3780593, by rfl⟩ : syracuseStep 5040791 = 7561187) B7561187
theorem B1493655 : Blo 1492066 1493655 := bstep (se 1 (by rfl) ⟨1120241, by rfl⟩ : syracuseStep 1493655 = 2240483) B2240483
theorem B1493675 : Blo 1492066 1493675 := bstep (se 1 (by rfl) ⟨1120256, by rfl⟩ : syracuseStep 1493675 = 2240513) B2240513
theorem B1493687 : Blo 1492066 1493687 := bstep (se 1 (by rfl) ⟨1120265, by rfl⟩ : syracuseStep 1493687 = 2240531) B2240531
theorem B1493707 : Blo 1492066 1493707 := bstep (se 1 (by rfl) ⟨1120280, by rfl⟩ : syracuseStep 1493707 = 2240561) B2240561
theorem B1493719 : Blo 1492066 1493719 := bstep (se 1 (by rfl) ⟨1120289, by rfl⟩ : syracuseStep 1493719 = 2240579) B2240579
theorem B2239193 : Blo 1492066 2239193 := bstep (se 2 (by rfl) ⟨839697, by rfl⟩ : syracuseStep 2239193 = 1679395) B1679395
theorem B1493739 : Blo 1492066 1493739 := bstep (se 1 (by rfl) ⟨1120304, by rfl⟩ : syracuseStep 1493739 = 2240609) B2240609
theorem B1493751 : Blo 1492066 1493751 := bstep (se 1 (by rfl) ⟨1120313, by rfl⟩ : syracuseStep 1493751 = 2240627) B2240627
theorem B1493771 : Blo 1492066 1493771 := bstep (se 1 (by rfl) ⟨1120328, by rfl⟩ : syracuseStep 1493771 = 2240657) B2240657
theorem B10218257 : Blo 1492066 10218257 := bstep (se 2 (by rfl) ⟨3831846, by rfl⟩ : syracuseStep 10218257 = 7663693) B7663693
theorem B3189527 : Blo 1492066 3189527 := bstep (se 1 (by rfl) ⟨2392145, by rfl⟩ : syracuseStep 3189527 = 4784291) B4784291
theorem B1493783 : Blo 1492066 1493783 := bstep (se 1 (by rfl) ⟨1120337, by rfl⟩ : syracuseStep 1493783 = 2240675) B2240675
theorem B1493803 : Blo 1492066 1493803 := bstep (se 1 (by rfl) ⟨1120352, by rfl⟩ : syracuseStep 1493803 = 2240705) B2240705
theorem B1493815 : Blo 1492066 1493815 := bstep (se 1 (by rfl) ⟨1120361, by rfl⟩ : syracuseStep 1493815 = 2240723) B2240723
theorem B2239307 : Blo 1492066 2239307 := bstep (se 1 (by rfl) ⟨1679480, by rfl⟩ : syracuseStep 2239307 = 3358961) B3358961
theorem B1493835 : Blo 1492066 1493835 := bstep (se 1 (by rfl) ⟨1120376, by rfl⟩ : syracuseStep 1493835 = 2240753) B2240753
theorem B2239319 : Blo 1492066 2239319 := bstep (se 1 (by rfl) ⟨1679489, by rfl⟩ : syracuseStep 2239319 = 3358979) B3358979
theorem B1493847 : Blo 1492066 1493847 := bstep (se 1 (by rfl) ⟨1120385, by rfl⟩ : syracuseStep 1493847 = 2240771) B2240771
theorem B3361625 : Blo 1492066 3361625 := bstep (se 2 (by rfl) ⟨1260609, by rfl⟩ : syracuseStep 3361625 = 2521219) B2521219
theorem B1493867 : Blo 1492066 1493867 := bstep (se 1 (by rfl) ⟨1120400, by rfl⟩ : syracuseStep 1493867 = 2240801) B2240801
theorem B1493879 : Blo 1492066 1493879 := bstep (se 1 (by rfl) ⟨1120409, by rfl⟩ : syracuseStep 1493879 = 2240819) B2240819
theorem B2689931 : Blo 1492066 2689931 := bstep (se 1 (by rfl) ⟨2017448, by rfl⟩ : syracuseStep 2689931 = 4034897) B4034897
theorem B1493899 : Blo 1492066 1493899 := bstep (se 1 (by rfl) ⟨1120424, by rfl⟩ : syracuseStep 1493899 = 2240849) B2240849
theorem B1493911 : Blo 1492066 1493911 := bstep (se 1 (by rfl) ⟨1120433, by rfl⟩ : syracuseStep 1493911 = 2240867) B2240867
theorem B2239385 : Blo 1492066 2239385 := bstep (se 2 (by rfl) ⟨839769, by rfl⟩ : syracuseStep 2239385 = 1679539) B1679539
theorem B1493931 : Blo 1492066 1493931 := bstep (se 1 (by rfl) ⟨1120448, by rfl⟩ : syracuseStep 1493931 = 2240897) B2240897
theorem B1493943 : Blo 1492066 1493943 := bstep (se 1 (by rfl) ⟨1120457, by rfl⟩ : syracuseStep 1493943 = 2240915) B2240915
theorem B3779531 : Blo 1492066 3779531 := bstep (se 1 (by rfl) ⟨2834648, by rfl⟩ : syracuseStep 3779531 = 5669297) B5669297
theorem B1493963 : Blo 1492066 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B1493975 : Blo 1492066 1493975 := bstep (se 1 (by rfl) ⟨1120481, by rfl⟩ : syracuseStep 1493975 = 2240963) B2240963
theorem B1493995 : Blo 1492066 1493995 := bstep (se 1 (by rfl) ⟨1120496, by rfl⟩ : syracuseStep 1493995 = 2240993) B2240993
theorem B3451891 : Blo 1492066 3451891 := bstep (se 1 (by rfl) ⟨2588918, by rfl⟩ : syracuseStep 3451891 = 5177837) B5177837
theorem B1494007 : Blo 1492066 1494007 := bstep (se 1 (by rfl) ⟨1120505, by rfl⟩ : syracuseStep 1494007 = 2241011) B2241011
theorem B2239499 : Blo 1492066 2239499 := bstep (se 1 (by rfl) ⟨1679624, by rfl⟩ : syracuseStep 2239499 = 3359249) B3359249
theorem B1494027 : Blo 1492066 1494027 := bstep (se 1 (by rfl) ⟨1120520, by rfl⟩ : syracuseStep 1494027 = 2241041) B2241041
theorem B6810641 : Blo 1492066 6810641 := bstep (se 2 (by rfl) ⟨2553990, by rfl⟩ : syracuseStep 6810641 = 5107981) B5107981
theorem B2239511 : Blo 1492066 2239511 := bstep (se 1 (by rfl) ⟨1679633, by rfl⟩ : syracuseStep 2239511 = 3359267) B3359267
theorem B1494039 : Blo 1492066 1494039 := bstep (se 1 (by rfl) ⟨1120529, by rfl⟩ : syracuseStep 1494039 = 2241059) B2241059
theorem B1494059 : Blo 1492066 1494059 := bstep (se 1 (by rfl) ⟨1120544, by rfl⟩ : syracuseStep 1494059 = 2241089) B2241089
theorem B2239577 : Blo 1492066 2239577 := bstep (se 2 (by rfl) ⟨839841, by rfl⟩ : syracuseStep 2239577 = 1679683) B1679683
theorem B6810713 : Blo 1492066 6810713 := bstep (se 2 (by rfl) ⟨2554017, by rfl⟩ : syracuseStep 6810713 = 5108035) B5108035
theorem B8621149 : Blo 1492066 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B3320947 : Blo 1492066 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B1535095 : Blo 1492066 1535095 := bstep (se 1 (by rfl) ⟨1151321, by rfl⟩ : syracuseStep 1535095 = 2302643) B2302643
theorem B18656407 : Blo 1492066 18656407 := bstep (se 1 (by rfl) ⟨13992305, by rfl⟩ : syracuseStep 18656407 = 27984611) B27984611
theorem B5041331 : Blo 1492066 5041331 := bstep (se 1 (by rfl) ⟨3780998, by rfl⟩ : syracuseStep 5041331 = 7561997) B7561997
theorem B2239691 : Blo 1492066 2239691 := bstep (se 1 (by rfl) ⟨1679768, by rfl⟩ : syracuseStep 2239691 = 3359537) B3359537
theorem B3402967 : Blo 1492066 3402967 := bstep (se 1 (by rfl) ⟨2552225, by rfl⟩ : syracuseStep 3402967 = 5104451) B5104451
theorem B2690263 : Blo 1492066 2690263 := bstep (se 1 (by rfl) ⟨2017697, by rfl⟩ : syracuseStep 2690263 = 4035395) B4035395
theorem B2239703 : Blo 1492066 2239703 := bstep (se 1 (by rfl) ⟨1679777, by rfl⟩ : syracuseStep 2239703 = 3359555) B3359555
theorem B2518283 : Blo 1492066 2518283 := bstep (se 1 (by rfl) ⟨1888712, by rfl⟩ : syracuseStep 2518283 = 3777425) B3777425
theorem B2239769 : Blo 1492066 2239769 := bstep (se 2 (by rfl) ⟨839913, by rfl⟩ : syracuseStep 2239769 = 1679827) B1679827
theorem B3779905 : Blo 1492066 3779905 := bstep (se 2 (by rfl) ⟨1417464, by rfl⟩ : syracuseStep 3779905 = 2834929) B2834929
theorem B2518411 : Blo 1492066 2518411 := bstep (se 1 (by rfl) ⟨1888808, by rfl⟩ : syracuseStep 2518411 = 3777617) B3777617
theorem B2239883 : Blo 1492066 2239883 := bstep (se 1 (by rfl) ⟨1679912, by rfl⟩ : syracuseStep 2239883 = 3359825) B3359825
theorem B2239895 : Blo 1492066 2239895 := bstep (se 1 (by rfl) ⟨1679921, by rfl⟩ : syracuseStep 2239895 = 3359843) B3359843
theorem B5041601 : Blo 1492066 5041601 := bstep (se 2 (by rfl) ⟨1890600, by rfl⟩ : syracuseStep 5041601 = 3781201) B3781201
theorem B3026393 : Blo 1492066 3026393 := bstep (se 2 (by rfl) ⟨1134897, by rfl⟩ : syracuseStep 3026393 = 2269795) B2269795
theorem B2239961 : Blo 1492066 2239961 := bstep (se 2 (by rfl) ⟨839985, by rfl⟩ : syracuseStep 2239961 = 1679971) B1679971
theorem B2518553 : Blo 1492066 2518553 := bstep (se 2 (by rfl) ⟨944457, by rfl⟩ : syracuseStep 2518553 = 1888915) B1888915
theorem B25513541 : Blo 1492066 25513541 := bstep (se 4 (by rfl) ⟨2391894, by rfl⟩ : syracuseStep 25513541 = 4783789) B4783789
theorem B2240075 : Blo 1492066 2240075 := bstep (se 1 (by rfl) ⟨1680056, by rfl⟩ : syracuseStep 2240075 = 3360113) B3360113
theorem B2240087 : Blo 1492066 2240087 := bstep (se 1 (by rfl) ⟨1680065, by rfl⟩ : syracuseStep 2240087 = 3360131) B3360131
theorem B14356061 : Blo 1492066 14356061 := bstep (se 3 (by rfl) ⟨2691761, by rfl⟩ : syracuseStep 14356061 = 5383523) B5383523
theorem B3190423 : Blo 1492066 3190423 := bstep (se 1 (by rfl) ⟨2392817, by rfl⟩ : syracuseStep 3190423 = 4785635) B4785635
theorem B2518681 : Blo 1492066 2518681 := bstep (se 2 (by rfl) ⟨944505, by rfl⟩ : syracuseStep 2518681 = 1889011) B1889011
theorem B2240153 : Blo 1492066 2240153 := bstep (se 2 (by rfl) ⟨840057, by rfl⟩ : syracuseStep 2240153 = 1680115) B1680115
theorem B5377715 : Blo 1492066 5377715 := bstep (se 1 (by rfl) ⟨4033286, by rfl⟩ : syracuseStep 5377715 = 8066573) B8066573
theorem B3452633 : Blo 1492066 3452633 := bstep (se 2 (by rfl) ⟨1294737, by rfl⟩ : syracuseStep 3452633 = 2589475) B2589475
theorem B2240267 : Blo 1492066 2240267 := bstep (se 1 (by rfl) ⟨1680200, by rfl⟩ : syracuseStep 2240267 = 3360401) B3360401
theorem B2240279 : Blo 1492066 2240279 := bstep (se 1 (by rfl) ⟨1680209, by rfl⟩ : syracuseStep 2240279 = 3360419) B3360419
theorem B2240345 : Blo 1492066 2240345 := bstep (se 2 (by rfl) ⟨840129, by rfl⟩ : syracuseStep 2240345 = 1680259) B1680259
theorem B3780503 : Blo 1492066 3780503 := bstep (se 1 (by rfl) ⟨2835377, by rfl⟩ : syracuseStep 3780503 = 5670755) B5670755
theorem B2240459 : Blo 1492066 2240459 := bstep (se 1 (by rfl) ⟨1680344, by rfl⟩ : syracuseStep 2240459 = 3360689) B3360689
theorem B2240471 : Blo 1492066 2240471 := bstep (se 1 (by rfl) ⟨1680353, by rfl⟩ : syracuseStep 2240471 = 3360707) B3360707
theorem B5042141 : Blo 1492066 5042141 := bstep (se 3 (by rfl) ⟨945401, by rfl⟩ : syracuseStep 5042141 = 1890803) B1890803
theorem B7557137 : Blo 1492066 7557137 := bstep (se 2 (by rfl) ⟨2833926, by rfl⟩ : syracuseStep 7557137 = 5667853) B5667853
theorem B2240537 : Blo 1492066 2240537 := bstep (se 2 (by rfl) ⟨840201, by rfl⟩ : syracuseStep 2240537 = 1680403) B1680403
theorem B8499275 : Blo 1492066 8499275 := bstep (se 1 (by rfl) ⟨6374456, by rfl⟩ : syracuseStep 8499275 = 12748913) B12748913
theorem B2240651 : Blo 1492066 2240651 := bstep (se 1 (by rfl) ⟨1680488, by rfl⟩ : syracuseStep 2240651 = 3360977) B3360977
theorem B2240663 : Blo 1492066 2240663 := bstep (se 1 (by rfl) ⟨1680497, by rfl⟩ : syracuseStep 2240663 = 3360995) B3360995
theorem B7557299 : Blo 1492066 7557299 := bstep (se 1 (by rfl) ⟨5667974, by rfl⟩ : syracuseStep 7557299 = 11335949) B11335949
theorem B2519255 : Blo 1492066 2519255 := bstep (se 1 (by rfl) ⟨1889441, by rfl⟩ : syracuseStep 2519255 = 3778883) B3778883
theorem B2240729 : Blo 1492066 2240729 := bstep (se 2 (by rfl) ⟨840273, by rfl⟩ : syracuseStep 2240729 = 1680547) B1680547
theorem B10768601 : Blo 1492066 10768601 := bstep (se 2 (by rfl) ⟨4038225, by rfl⟩ : syracuseStep 10768601 = 8076451) B8076451
theorem B1888535 : Blo 1492066 1888535 := bstep (se 1 (by rfl) ⟨1416401, by rfl⟩ : syracuseStep 1888535 = 2832803) B2832803
theorem B2240843 : Blo 1492066 2240843 := bstep (se 1 (by rfl) ⟨1680632, by rfl⟩ : syracuseStep 2240843 = 3361265) B3361265
theorem B2519383 : Blo 1492066 2519383 := bstep (se 1 (by rfl) ⟨1889537, by rfl⟩ : syracuseStep 2519383 = 3779075) B3779075
theorem B2240855 : Blo 1492066 2240855 := bstep (se 1 (by rfl) ⟨1680641, by rfl⟩ : syracuseStep 2240855 = 3361283) B3361283
theorem B4542809 : Blo 1492066 4542809 := bstep (se 2 (by rfl) ⟨1703553, by rfl⟩ : syracuseStep 4542809 = 3407107) B3407107
theorem B1593751 : Blo 1492066 1593751 := bstep (se 1 (by rfl) ⟨1195313, by rfl⟩ : syracuseStep 1593751 = 2390627) B2390627
theorem B2240921 : Blo 1492066 2240921 := bstep (se 2 (by rfl) ⟨840345, by rfl⟩ : syracuseStep 2240921 = 1680691) B1680691
theorem B5665241 : Blo 1492066 5665241 := bstep (se 2 (by rfl) ⟨2124465, by rfl⟩ : syracuseStep 5665241 = 4248931) B4248931
theorem B2241035 : Blo 1492066 2241035 := bstep (se 1 (by rfl) ⟨1680776, by rfl⟩ : syracuseStep 2241035 = 3361553) B3361553
theorem B6050321 : Blo 1492066 6050321 := bstep (se 2 (by rfl) ⟨2268870, by rfl⟩ : syracuseStep 6050321 = 4537741) B4537741
theorem B2241047 : Blo 1492066 2241047 := bstep (se 1 (by rfl) ⟨1680785, by rfl⟩ : syracuseStep 2241047 = 3361571) B3361571
theorem B2126425 : Blo 1492066 2126425 := bstep (se 2 (by rfl) ⟨797409, by rfl⟩ : syracuseStep 2126425 = 1594819) B1594819
theorem B15323741 : Blo 1492066 15323741 := bstep (se 3 (by rfl) ⟨2873201, by rfl⟩ : syracuseStep 15323741 = 5746403) B5746403
theorem B2871947 : Blo 1492066 2871947 := bstep (se 1 (by rfl) ⟨2153960, by rfl⟩ : syracuseStep 2871947 = 4307921) B4307921
theorem B3781313 : Blo 1492066 3781313 := bstep (se 2 (by rfl) ⟨1417992, by rfl⟩ : syracuseStep 3781313 = 2835985) B2835985
theorem B12751577 : Blo 1492066 12751577 := bstep (se 2 (by rfl) ⟨4781841, by rfl⟩ : syracuseStep 12751577 = 9563683) B9563683
theorem B2691863 : Blo 1492066 2691863 := bstep (se 1 (by rfl) ⟨2018897, by rfl⟩ : syracuseStep 2691863 = 4037795) B4037795
theorem B5378881 : Blo 1492066 5378881 := bstep (se 2 (by rfl) ⟨2017080, by rfl⟩ : syracuseStep 5378881 = 4034161) B4034161
theorem B7172995 : Blo 1492066 7172995 := bstep (se 1 (by rfl) ⟨5379746, by rfl⟩ : syracuseStep 7172995 = 10759493) B10759493
theorem B6378371 : Blo 1492066 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B5378995 : Blo 1492066 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B2520011 : Blo 1492066 2520011 := bstep (se 1 (by rfl) ⟨1890008, by rfl⟩ : syracuseStep 2520011 = 3780017) B3780017
theorem B1889239 : Blo 1492066 1889239 := bstep (se 1 (by rfl) ⟨1416929, by rfl⟩ : syracuseStep 1889239 = 2833859) B2833859
theorem B2520139 : Blo 1492066 2520139 := bstep (se 1 (by rfl) ⟨1890104, by rfl⟩ : syracuseStep 2520139 = 3780209) B3780209
theorem B1594571 : Blo 1492066 1594571 := bstep (se 1 (by rfl) ⟨1195928, by rfl⟩ : syracuseStep 1594571 = 2391857) B2391857
theorem B2520281 : Blo 1492066 2520281 := bstep (se 2 (by rfl) ⟨945105, by rfl⟩ : syracuseStep 2520281 = 1890211) B1890211
theorem B3781849 : Blo 1492066 3781849 := bstep (se 2 (by rfl) ⟨1418193, by rfl⟩ : syracuseStep 3781849 = 2836387) B2836387
theorem B12760325 : Blo 1492066 12760325 := bstep (se 4 (by rfl) ⟨1196280, by rfl⟩ : syracuseStep 12760325 = 2392561) B2392561
theorem B11334977 : Blo 1492066 11334977 := bstep (se 2 (by rfl) ⟨4250616, by rfl⟩ : syracuseStep 11334977 = 8501233) B8501233
theorem B2520409 : Blo 1492066 2520409 := bstep (se 2 (by rfl) ⟨945153, by rfl⟩ : syracuseStep 2520409 = 1890307) B1890307
theorem B1726039 : Blo 1492066 1726039 := bstep (se 1 (by rfl) ⟨1294529, by rfl⟩ : syracuseStep 1726039 = 2589059) B2589059
theorem B3233537 : Blo 1492066 3233537 := bstep (se 2 (by rfl) ⟨1212576, by rfl⟩ : syracuseStep 3233537 = 2425153) B2425153
theorem B2520983 : Blo 1492066 2520983 := bstep (se 1 (by rfl) ⟨1890737, by rfl⟩ : syracuseStep 2520983 = 3781475) B3781475
theorem B12761009 : Blo 1492066 12761009 := bstep (se 2 (by rfl) ⟨4785378, by rfl⟩ : syracuseStep 12761009 = 9570757) B9570757
theorem B4249523 : Blo 1492066 4249523 := bstep (se 1 (by rfl) ⟨3187142, by rfl⟩ : syracuseStep 4249523 = 6374285) B6374285
theorem B15333299 : Blo 1492066 15333299 := bstep (se 1 (by rfl) ⟨11499974, by rfl⟩ : syracuseStep 15333299 = 22999949) B22999949
theorem B4249547 : Blo 1492066 4249547 := bstep (se 1 (by rfl) ⟨3187160, by rfl⟩ : syracuseStep 4249547 = 6374321) B6374321
theorem B2521111 : Blo 1492066 2521111 := bstep (se 1 (by rfl) ⟨1890833, by rfl⟩ : syracuseStep 2521111 = 3781667) B3781667
theorem B5666867 : Blo 1492066 5666867 := bstep (se 1 (by rfl) ⟨4250150, by rfl⟩ : syracuseStep 5666867 = 8500301) B8500301
theorem B5666881 : Blo 1492066 5666881 := bstep (se 2 (by rfl) ⟨2125080, by rfl⟩ : syracuseStep 5666881 = 4250161) B4250161
theorem B7559243 : Blo 1492066 7559243 := bstep (se 1 (by rfl) ⟨5669432, by rfl⟩ : syracuseStep 7559243 = 11338865) B11338865
theorem B3233971 : Blo 1492066 3233971 := bstep (se 1 (by rfl) ⟨2425478, by rfl⟩ : syracuseStep 3233971 = 4850957) B4850957
theorem B5036363 : Blo 1492066 5036363 := bstep (se 1 (by rfl) ⟨3777272, by rfl⟩ : syracuseStep 5036363 = 7554545) B7554545
theorem B2832727 : Blo 1492066 2832727 := bstep (se 1 (by rfl) ⟨2124545, by rfl⟩ : syracuseStep 2832727 = 4249091) B4249091
theorem B12925277 : Blo 1492066 12925277 := bstep (se 3 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 12925277 = 4846979) B4846979
theorem B2832833 : Blo 1492066 2832833 := bstep (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) B2124625
theorem B6814145 : Blo 1492066 6814145 := bstep (se 2 (by rfl) ⟨2555304, by rfl⟩ : syracuseStep 6814145 = 5110609) B5110609
theorem B6052313 : Blo 1492066 6052313 := bstep (se 2 (by rfl) ⟨2269617, by rfl⟩ : syracuseStep 6052313 = 4539235) B4539235
theorem B2832985 : Blo 1492066 2832985 := bstep (se 2 (by rfl) ⟨1062369, by rfl⟩ : syracuseStep 2832985 = 2124739) B2124739
theorem B5036633 : Blo 1492066 5036633 := bstep (se 2 (by rfl) ⟨1888737, by rfl⟩ : syracuseStep 5036633 = 3777475) B3777475
theorem B3357323 : Blo 1492066 3357323 := bstep (se 1 (by rfl) ⟨2517992, by rfl⟩ : syracuseStep 3357323 = 5035985) B5035985
theorem B3357377 : Blo 1492066 3357377 := bstep (se 2 (by rfl) ⟨1259016, by rfl⟩ : syracuseStep 3357377 = 2518033) B2518033
theorem B4250333 : Blo 1492066 4250333 := bstep (se 3 (by rfl) ⟨796937, by rfl⟩ : syracuseStep 4250333 = 1593875) B1593875
theorem B3357593 : Blo 1492066 3357593 := bstep (se 2 (by rfl) ⟨1259097, by rfl⟩ : syracuseStep 3357593 = 2518195) B2518195
theorem B12762035 : Blo 1492066 12762035 := bstep (se 1 (by rfl) ⟨9571526, by rfl⟩ : syracuseStep 12762035 = 19143053) B19143053
theorem B4037579 : Blo 1492066 4037579 := bstep (se 1 (by rfl) ⟨3028184, by rfl⟩ : syracuseStep 4037579 = 6056369) B6056369
theorem B3357683 : Blo 1492066 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B2874379 : Blo 1492066 2874379 := bstep (se 1 (by rfl) ⟨2155784, by rfl⟩ : syracuseStep 2874379 = 4311569) B4311569
theorem B3357719 : Blo 1492066 3357719 := bstep (se 1 (by rfl) ⟨2518289, by rfl⟩ : syracuseStep 3357719 = 5036579) B5036579
theorem B2391191 : Blo 1492066 2391191 := bstep (se 1 (by rfl) ⟨1793393, by rfl⟩ : syracuseStep 2391191 = 3586787) B3586787
theorem B4037783 : Blo 1492066 4037783 := bstep (se 1 (by rfl) ⟨3028337, by rfl⟩ : syracuseStep 4037783 = 6056675) B6056675
theorem B3357899 : Blo 1492066 3357899 := bstep (se 1 (by rfl) ⟨2518424, by rfl⟩ : syracuseStep 3357899 = 5036849) B5036849
theorem B3636427 : Blo 1492066 3636427 := bstep (se 1 (by rfl) ⟨2727320, by rfl⟩ : syracuseStep 3636427 = 5454641) B5454641
theorem B11336921 : Blo 1492066 11336921 := bstep (se 2 (by rfl) ⟨4251345, by rfl⟩ : syracuseStep 11336921 = 8502691) B8502691
theorem B3357953 : Blo 1492066 3357953 := bstep (se 2 (by rfl) ⟨1259232, by rfl⟩ : syracuseStep 3357953 = 2518465) B2518465
theorem B1678603 : Blo 1492066 1678603 := bstep (se 1 (by rfl) ⟨1258952, by rfl⟩ : syracuseStep 1678603 = 2517905) B2517905
theorem B5037335 : Blo 1492066 5037335 := bstep (se 1 (by rfl) ⟨3778001, by rfl⟩ : syracuseStep 5037335 = 7556003) B7556003
theorem B16153901 : Blo 1492066 16153901 := bstep (se 3 (by rfl) ⟨3028856, by rfl⟩ : syracuseStep 16153901 = 6057713) B6057713
theorem B1678711 : Blo 1492066 1678711 := bstep (se 1 (by rfl) ⟨1259033, by rfl⟩ : syracuseStep 1678711 = 2518067) B2518067
theorem B9084311 : Blo 1492066 9084311 := bstep (se 1 (by rfl) ⟨6813233, by rfl⟩ : syracuseStep 9084311 = 13626467) B13626467
theorem B3358169 : Blo 1492066 3358169 := bstep (se 2 (by rfl) ⟨1259313, by rfl⟩ : syracuseStep 3358169 = 2518627) B2518627
theorem B1678891 : Blo 1492066 1678891 := bstep (se 1 (by rfl) ⟨1259168, by rfl⟩ : syracuseStep 1678891 = 2518337) B2518337
theorem B3358259 : Blo 1492066 3358259 := bstep (se 1 (by rfl) ⟨2518694, by rfl⟩ : syracuseStep 3358259 = 5037389) B5037389
theorem B3358295 : Blo 1492066 3358295 := bstep (se 1 (by rfl) ⟨2518721, by rfl⟩ : syracuseStep 3358295 = 5037443) B5037443
theorem B1678999 : Blo 1492066 1678999 := bstep (se 1 (by rfl) ⟨1259249, by rfl⟩ : syracuseStep 1678999 = 2518499) B2518499
theorem B2268875 : Blo 1492066 2268875 := bstep (se 1 (by rfl) ⟨1701656, by rfl⟩ : syracuseStep 2268875 = 3403313) B3403313
theorem B9690841 : Blo 1492066 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B3358475 : Blo 1492066 3358475 := bstep (se 1 (by rfl) ⟨2518856, by rfl⟩ : syracuseStep 3358475 = 5037713) B5037713
theorem B10764049 : Blo 1492066 10764049 := bstep (se 2 (by rfl) ⟨4036518, by rfl⟩ : syracuseStep 10764049 = 8073037) B8073037
theorem B5037875 : Blo 1492066 5037875 := bstep (se 1 (by rfl) ⟨3778406, by rfl⟩ : syracuseStep 5037875 = 7556813) B7556813
theorem B3358529 : Blo 1492066 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B7561025 : Blo 1492066 7561025 := bstep (se 2 (by rfl) ⟨2835384, by rfl⟩ : syracuseStep 7561025 = 5670769) B5670769
theorem B1679179 : Blo 1492066 1679179 := bstep (se 1 (by rfl) ⟨1259384, by rfl⟩ : syracuseStep 1679179 = 2518769) B2518769
theorem B6053707 : Blo 1492066 6053707 := bstep (se 1 (by rfl) ⟨4540280, by rfl⟩ : syracuseStep 6053707 = 9080561) B9080561
theorem B2834291 : Blo 1492066 2834291 := bstep (se 1 (by rfl) ⟨2125718, by rfl⟩ : syracuseStep 2834291 = 4251437) B4251437
theorem B1679287 : Blo 1492066 1679287 := bstep (se 1 (by rfl) ⟨1259465, by rfl⟩ : syracuseStep 1679287 = 2518931) B2518931
theorem B5668811 : Blo 1492066 5668811 := bstep (se 1 (by rfl) ⟨4251608, by rfl⟩ : syracuseStep 5668811 = 8503217) B8503217
theorem B5668825 : Blo 1492066 5668825 := bstep (se 2 (by rfl) ⟨2125809, by rfl⟩ : syracuseStep 5668825 = 4251619) B4251619
theorem B4538333 : Blo 1492066 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B5038091 : Blo 1492066 5038091 := bstep (se 1 (by rfl) ⟨3778568, by rfl⟩ : syracuseStep 5038091 = 7557137) B7557137
theorem B3358763 : Blo 1492066 3358763 := bstep (se 1 (by rfl) ⟨2519072, by rfl⟩ : syracuseStep 3358763 = 5038145) B5038145
theorem B5038199 : Blo 1492066 5038199 := bstep (se 1 (by rfl) ⟨3778649, by rfl⟩ : syracuseStep 5038199 = 7557299) B7557299
theorem B1679503 : Blo 1492066 1679503 := bstep (se 1 (by rfl) ⟨1259627, by rfl⟩ : syracuseStep 1679503 = 2519255) B2519255
theorem B3776827 : Blo 1492066 3776827 := bstep (se 1 (by rfl) ⟨2832620, by rfl⟩ : syracuseStep 3776827 = 5665241) B5665241
theorem B2834747 : Blo 1492066 2834747 := bstep (se 1 (by rfl) ⟨2126060, by rfl⟩ : syracuseStep 2834747 = 4252121) B4252121
theorem B8618329 : Blo 1492066 8618329 := bstep (se 2 (by rfl) ⟨3231873, by rfl⟩ : syracuseStep 8618329 = 6463747) B6463747
theorem B3359123 : Blo 1492066 3359123 := bstep (se 1 (by rfl) ⟨2519342, by rfl⟩ : syracuseStep 3359123 = 5038685) B5038685
theorem B10215827 : Blo 1492066 10215827 := bstep (se 1 (by rfl) ⟨7661870, by rfl⟩ : syracuseStep 10215827 = 15323741) B15323741
theorem B3776969 : Blo 1492066 3776969 := bstep (se 2 (by rfl) ⟨1416363, by rfl⟩ : syracuseStep 3776969 = 2832727) B2832727
theorem B3359177 : Blo 1492066 3359177 := bstep (se 2 (by rfl) ⟨1259691, by rfl⟩ : syracuseStep 3359177 = 2519383) B2519383
theorem B1794575 : Blo 1492066 1794575 := bstep (se 1 (by rfl) ⟨1345931, by rfl⟩ : syracuseStep 1794575 = 2691863) B2691863
theorem B4252189 : Blo 1492066 4252189 := bstep (se 3 (by rfl) ⟨797285, by rfl⟩ : syracuseStep 4252189 = 1594571) B1594571
theorem B4252247 : Blo 1492066 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B3588727 : Blo 1492066 3588727 := bstep (se 1 (by rfl) ⟨2691545, by rfl⟩ : syracuseStep 3588727 = 5383091) B5383091
theorem B1680007 : Blo 1492066 1680007 := bstep (se 1 (by rfl) ⟨1260005, by rfl⟩ : syracuseStep 1680007 = 2520011) B2520011
theorem B5038793 : Blo 1492066 5038793 := bstep (se 2 (by rfl) ⟨1889547, by rfl⟩ : syracuseStep 5038793 = 3779095) B3779095
theorem B3777313 : Blo 1492066 3777313 := bstep (se 2 (by rfl) ⟨1416492, by rfl⟩ : syracuseStep 3777313 = 2832985) B2832985
theorem B2835233 : Blo 1492066 2835233 := bstep (se 2 (by rfl) ⟨1063212, by rfl⟩ : syracuseStep 2835233 = 2126425) B2126425
theorem B1680187 : Blo 1492066 1680187 := bstep (se 1 (by rfl) ⟨1260140, by rfl⟩ : syracuseStep 1680187 = 2520281) B2520281
theorem B52437941 : Blo 1492066 52437941 := bstep (se 5 (by rfl) ⟨2458028, by rfl⟩ : syracuseStep 52437941 = 4916057) B4916057
theorem B48456629 : Blo 1492066 48456629 := bstep (se 5 (by rfl) ⟨2271404, by rfl⟩ : syracuseStep 48456629 = 4542809) B4542809
theorem B7554059 : Blo 1492066 7554059 := bstep (se 1 (by rfl) ⟨5665544, by rfl⟩ : syracuseStep 7554059 = 11331089) B11331089
theorem B2835499 : Blo 1492066 2835499 := bstep (se 1 (by rfl) ⟨2126624, by rfl⟩ : syracuseStep 2835499 = 4253249) B4253249
theorem B1492103 : Blo 1492066 1492103 := bstep (se 1 (by rfl) ⟨1119077, by rfl⟩ : syracuseStep 1492103 = 2238155) B2238155
theorem B3359879 : Blo 1492066 3359879 := bstep (se 1 (by rfl) ⟨2519909, by rfl⟩ : syracuseStep 3359879 = 5039819) B5039819
theorem B1492111 : Blo 1492066 1492111 := bstep (se 1 (by rfl) ⟨1119083, by rfl⟩ : syracuseStep 1492111 = 2238167) B2238167
theorem B7554221 : Blo 1492066 7554221 := bstep (se 3 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 7554221 = 2832833) B2832833
theorem B2155691 : Blo 1492066 2155691 := bstep (se 1 (by rfl) ⟨1616768, by rfl⟩ : syracuseStep 2155691 = 3233537) B3233537
theorem B18171053 : Blo 1492066 18171053 := bstep (se 3 (by rfl) ⟨3407072, by rfl⟩ : syracuseStep 18171053 = 6814145) B6814145
theorem B1492155 : Blo 1492066 1492155 := bstep (se 1 (by rfl) ⟨1119116, by rfl⟩ : syracuseStep 1492155 = 2238233) B2238233
theorem B8291585 : Blo 1492066 8291585 := bstep (se 2 (by rfl) ⟨3109344, by rfl⟩ : syracuseStep 8291585 = 6218689) B6218689
theorem B1492231 : Blo 1492066 1492231 := bstep (se 1 (by rfl) ⟨1119173, by rfl⟩ : syracuseStep 1492231 = 2238347) B2238347
theorem B1492239 : Blo 1492066 1492239 := bstep (se 1 (by rfl) ⟨1119179, by rfl⟩ : syracuseStep 1492239 = 2238359) B2238359
theorem B1680655 : Blo 1492066 1680655 := bstep (se 1 (by rfl) ⟨1260491, by rfl⟩ : syracuseStep 1680655 = 2520983) B2520983
theorem B1492283 : Blo 1492066 1492283 := bstep (se 1 (by rfl) ⟨1119212, by rfl⟩ : syracuseStep 1492283 = 2238425) B2238425
theorem B3360059 : Blo 1492066 3360059 := bstep (se 1 (by rfl) ⟨2520044, by rfl⟩ : syracuseStep 3360059 = 5040089) B5040089
theorem B3777911 : Blo 1492066 3777911 := bstep (se 1 (by rfl) ⟨2833433, by rfl⟩ : syracuseStep 3777911 = 5666867) B5666867
theorem B1492359 : Blo 1492066 1492359 := bstep (se 1 (by rfl) ⟨1119269, by rfl⟩ : syracuseStep 1492359 = 2238539) B2238539
theorem B5039495 : Blo 1492066 5039495 := bstep (se 1 (by rfl) ⟨3779621, by rfl⟩ : syracuseStep 5039495 = 7559243) B7559243
theorem B1492367 : Blo 1492066 1492367 := bstep (se 1 (by rfl) ⟨1119275, by rfl⟩ : syracuseStep 1492367 = 2238551) B2238551
theorem B3360185 : Blo 1492066 3360185 := bstep (se 2 (by rfl) ⟨1260069, by rfl⟩ : syracuseStep 3360185 = 2520139) B2520139
theorem B1492411 : Blo 1492066 1492411 := bstep (se 1 (by rfl) ⟨1119308, by rfl⟩ : syracuseStep 1492411 = 2238617) B2238617
theorem B11494865 : Blo 1492066 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B1492487 : Blo 1492066 1492487 := bstep (se 1 (by rfl) ⟨1119365, by rfl⟩ : syracuseStep 1492487 = 2238731) B2238731
theorem B1492495 : Blo 1492066 1492495 := bstep (se 1 (by rfl) ⟨1119371, by rfl⟩ : syracuseStep 1492495 = 2238743) B2238743
theorem B1492539 : Blo 1492066 1492539 := bstep (se 1 (by rfl) ⟨1119404, by rfl⟩ : syracuseStep 1492539 = 2238809) B2238809
theorem B10913399 : Blo 1492066 10913399 := bstep (se 1 (by rfl) ⟨8185049, by rfl⟩ : syracuseStep 10913399 = 16370099) B16370099
theorem B1492615 : Blo 1492066 1492615 := bstep (se 1 (by rfl) ⟨1119461, by rfl⟩ : syracuseStep 1492615 = 2238923) B2238923
theorem B1492623 : Blo 1492066 1492623 := bstep (se 1 (by rfl) ⟨1119467, by rfl⟩ : syracuseStep 1492623 = 2238935) B2238935
theorem B2238137 : Blo 1492066 2238137 := bstep (se 2 (by rfl) ⟨839301, by rfl⟩ : syracuseStep 2238137 = 1678603) B1678603
theorem B1492667 : Blo 1492066 1492667 := bstep (se 1 (by rfl) ⟨1119500, by rfl⟩ : syracuseStep 1492667 = 2239001) B2239001
theorem B5039873 : Blo 1492066 5039873 := bstep (se 2 (by rfl) ⟨1889952, by rfl⟩ : syracuseStep 5039873 = 3779905) B3779905
theorem B2238215 : Blo 1492066 2238215 := bstep (se 1 (by rfl) ⟨1678661, by rfl⟩ : syracuseStep 2238215 = 3357323) B3357323
theorem B1492743 : Blo 1492066 1492743 := bstep (se 1 (by rfl) ⟨1119557, by rfl⟩ : syracuseStep 1492743 = 2239115) B2239115
theorem B1492751 : Blo 1492066 1492751 := bstep (se 1 (by rfl) ⟨1119563, by rfl⟩ : syracuseStep 1492751 = 2239127) B2239127
theorem B3360527 : Blo 1492066 3360527 := bstep (se 1 (by rfl) ⟨2520395, by rfl⟩ : syracuseStep 3360527 = 5040791) B5040791
theorem B3360545 : Blo 1492066 3360545 := bstep (se 2 (by rfl) ⟨1260204, by rfl⟩ : syracuseStep 3360545 = 2520409) B2520409
theorem B2238251 : Blo 1492066 2238251 := bstep (se 1 (by rfl) ⟨1678688, by rfl⟩ : syracuseStep 2238251 = 3357377) B3357377
theorem B1492795 : Blo 1492066 1492795 := bstep (se 1 (by rfl) ⟨1119596, by rfl⟩ : syracuseStep 1492795 = 2239193) B2239193
theorem B2238281 : Blo 1492066 2238281 := bstep (se 2 (by rfl) ⟨839355, by rfl⟩ : syracuseStep 2238281 = 1678711) B1678711
theorem B1492871 : Blo 1492066 1492871 := bstep (se 1 (by rfl) ⟨1119653, by rfl⟩ : syracuseStep 1492871 = 2239307) B2239307
theorem B1492879 : Blo 1492066 1492879 := bstep (se 1 (by rfl) ⟨1119659, by rfl⟩ : syracuseStep 1492879 = 2239319) B2239319
theorem B7178129 : Blo 1492066 7178129 := bstep (se 2 (by rfl) ⟨2691798, by rfl⟩ : syracuseStep 7178129 = 5383597) B5383597
theorem B2238395 : Blo 1492066 2238395 := bstep (se 1 (by rfl) ⟨1678796, by rfl⟩ : syracuseStep 2238395 = 3357593) B3357593
theorem B1492923 : Blo 1492066 1492923 := bstep (se 1 (by rfl) ⟨1119692, by rfl⟩ : syracuseStep 1492923 = 2239385) B2239385
theorem B2238455 : Blo 1492066 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B1492999 : Blo 1492066 1492999 := bstep (se 1 (by rfl) ⟨1119749, by rfl⟩ : syracuseStep 1492999 = 2239499) B2239499
theorem B4540427 : Blo 1492066 4540427 := bstep (se 1 (by rfl) ⟨3405320, by rfl⟩ : syracuseStep 4540427 = 6810641) B6810641
theorem B2238479 : Blo 1492066 2238479 := bstep (se 1 (by rfl) ⟨1678859, by rfl⟩ : syracuseStep 2238479 = 3357719) B3357719
theorem B1493007 : Blo 1492066 1493007 := bstep (se 1 (by rfl) ⟨1119755, by rfl⟩ : syracuseStep 1493007 = 2239511) B2239511
theorem B7563293 : Blo 1492066 7563293 := bstep (se 3 (by rfl) ⟨1418117, by rfl⟩ : syracuseStep 7563293 = 2836235) B2836235
theorem B2238521 : Blo 1492066 2238521 := bstep (se 2 (by rfl) ⟨839445, by rfl⟩ : syracuseStep 2238521 = 1678891) B1678891
theorem B1493051 : Blo 1492066 1493051 := bstep (se 1 (by rfl) ⟨1119788, by rfl⟩ : syracuseStep 1493051 = 2239577) B2239577
theorem B4540475 : Blo 1492066 4540475 := bstep (se 1 (by rfl) ⟨3405356, by rfl⟩ : syracuseStep 4540475 = 6810713) B6810713
theorem B11339837 : Blo 1492066 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B3360887 : Blo 1492066 3360887 := bstep (se 1 (by rfl) ⟨2520665, by rfl⟩ : syracuseStep 3360887 = 5041331) B5041331
theorem B2238599 : Blo 1492066 2238599 := bstep (se 1 (by rfl) ⟨1678949, by rfl⟩ : syracuseStep 2238599 = 3357899) B3357899
theorem B1493127 : Blo 1492066 1493127 := bstep (se 1 (by rfl) ⟨1119845, by rfl⟩ : syracuseStep 1493127 = 2239691) B2239691
theorem B1493135 : Blo 1492066 1493135 := bstep (se 1 (by rfl) ⟨1119851, by rfl⟩ : syracuseStep 1493135 = 2239703) B2239703
theorem B2238635 : Blo 1492066 2238635 := bstep (se 1 (by rfl) ⟨1678976, by rfl⟩ : syracuseStep 2238635 = 3357953) B3357953
theorem B1493179 : Blo 1492066 1493179 := bstep (se 1 (by rfl) ⟨1119884, by rfl⟩ : syracuseStep 1493179 = 2239769) B2239769
theorem B2238665 : Blo 1492066 2238665 := bstep (se 2 (by rfl) ⟨839499, by rfl⟩ : syracuseStep 2238665 = 1678999) B1678999
theorem B4253897 : Blo 1492066 4253897 := bstep (se 2 (by rfl) ⟨1595211, by rfl⟩ : syracuseStep 4253897 = 3190423) B3190423
theorem B1493255 : Blo 1492066 1493255 := bstep (se 1 (by rfl) ⟨1119941, by rfl⟩ : syracuseStep 1493255 = 2239883) B2239883
theorem B1493263 : Blo 1492066 1493263 := bstep (se 1 (by rfl) ⟨1119947, by rfl⟩ : syracuseStep 1493263 = 2239895) B2239895
theorem B6056207 : Blo 1492066 6056207 := bstep (se 1 (by rfl) ⟨4542155, by rfl⟩ : syracuseStep 6056207 = 9084311) B9084311
theorem B12921121 : Blo 1492066 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B3361067 : Blo 1492066 3361067 := bstep (se 1 (by rfl) ⟨2520800, by rfl⟩ : syracuseStep 3361067 = 5041601) B5041601
theorem B2238779 : Blo 1492066 2238779 := bstep (se 1 (by rfl) ⟨1679084, by rfl⟩ : syracuseStep 2238779 = 3358169) B3358169
theorem B2017595 : Blo 1492066 2017595 := bstep (se 1 (by rfl) ⟨1513196, by rfl⟩ : syracuseStep 2017595 = 3026393) B3026393
theorem B1493307 : Blo 1492066 1493307 := bstep (se 1 (by rfl) ⟨1119980, by rfl⟩ : syracuseStep 1493307 = 2239961) B2239961
theorem B2238839 : Blo 1492066 2238839 := bstep (se 1 (by rfl) ⟨1679129, by rfl⟩ : syracuseStep 2238839 = 3358259) B3358259
theorem B17009027 : Blo 1492066 17009027 := bstep (se 1 (by rfl) ⟨12756770, by rfl⟩ : syracuseStep 17009027 = 25513541) B25513541
theorem B1493383 : Blo 1492066 1493383 := bstep (se 1 (by rfl) ⟨1120037, by rfl⟩ : syracuseStep 1493383 = 2240075) B2240075
theorem B2238863 : Blo 1492066 2238863 := bstep (se 1 (by rfl) ⟨1679147, by rfl⟩ : syracuseStep 2238863 = 3358295) B3358295
theorem B1493391 : Blo 1492066 1493391 := bstep (se 1 (by rfl) ⟨1120043, by rfl⟩ : syracuseStep 1493391 = 2240087) B2240087
theorem B9570707 : Blo 1492066 9570707 := bstep (se 1 (by rfl) ⟨7178030, by rfl⟩ : syracuseStep 9570707 = 14356061) B14356061
theorem B2238905 : Blo 1492066 2238905 := bstep (se 2 (by rfl) ⟨839589, by rfl⟩ : syracuseStep 2238905 = 1679179) B1679179
theorem B8071609 : Blo 1492066 8071609 := bstep (se 2 (by rfl) ⟨3026853, by rfl⟩ : syracuseStep 8071609 = 6053707) B6053707
theorem B1493435 : Blo 1492066 1493435 := bstep (se 1 (by rfl) ⟨1120076, by rfl⟩ : syracuseStep 1493435 = 2240153) B2240153
theorem B11332061 : Blo 1492066 11332061 := bstep (se 3 (by rfl) ⟨2124761, by rfl⟩ : syracuseStep 11332061 = 4249523) B4249523
theorem B2238983 : Blo 1492066 2238983 := bstep (se 1 (by rfl) ⟨1679237, by rfl⟩ : syracuseStep 2238983 = 3358475) B3358475
theorem B1493511 : Blo 1492066 1493511 := bstep (se 1 (by rfl) ⟨1120133, by rfl⟩ : syracuseStep 1493511 = 2240267) B2240267
theorem B1493519 : Blo 1492066 1493519 := bstep (se 1 (by rfl) ⟨1120139, by rfl⟩ : syracuseStep 1493519 = 2240279) B2240279
theorem B2239019 : Blo 1492066 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B5040683 : Blo 1492066 5040683 := bstep (se 1 (by rfl) ⟨3780512, by rfl⟩ : syracuseStep 5040683 = 7561025) B7561025
theorem B1493563 : Blo 1492066 1493563 := bstep (se 1 (by rfl) ⟨1120172, by rfl⟩ : syracuseStep 1493563 = 2240345) B2240345
theorem B2239049 : Blo 1492066 2239049 := bstep (se 2 (by rfl) ⟨839643, by rfl⟩ : syracuseStep 2239049 = 1679287) B1679287
theorem B3779207 : Blo 1492066 3779207 := bstep (se 1 (by rfl) ⟨2834405, by rfl⟩ : syracuseStep 3779207 = 5668811) B5668811
theorem B1493639 : Blo 1492066 1493639 := bstep (se 1 (by rfl) ⟨1120229, by rfl⟩ : syracuseStep 1493639 = 2240459) B2240459
theorem B1493647 : Blo 1492066 1493647 := bstep (se 1 (by rfl) ⟨1120235, by rfl⟩ : syracuseStep 1493647 = 2240471) B2240471
theorem B3025555 : Blo 1492066 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B3361427 : Blo 1492066 3361427 := bstep (se 1 (by rfl) ⟨2521070, by rfl⟩ : syracuseStep 3361427 = 5042141) B5042141
theorem B3779257 : Blo 1492066 3779257 := bstep (se 2 (by rfl) ⟨1417221, by rfl⟩ : syracuseStep 3779257 = 2834443) B2834443
theorem B2239163 : Blo 1492066 2239163 := bstep (se 1 (by rfl) ⟨1679372, by rfl⟩ : syracuseStep 2239163 = 3358745) B3358745
theorem B1493691 : Blo 1492066 1493691 := bstep (se 1 (by rfl) ⟨1120268, by rfl⟩ : syracuseStep 1493691 = 2240537) B2240537
theorem B3361481 : Blo 1492066 3361481 := bstep (se 2 (by rfl) ⟨1260555, by rfl⟩ : syracuseStep 3361481 = 2521111) B2521111
theorem B2239223 : Blo 1492066 2239223 := bstep (se 1 (by rfl) ⟨1679417, by rfl⟩ : syracuseStep 2239223 = 3358835) B3358835
theorem B7555841 : Blo 1492066 7555841 := bstep (se 2 (by rfl) ⟨2833440, by rfl⟩ : syracuseStep 7555841 = 5666881) B5666881
theorem B1493767 : Blo 1492066 1493767 := bstep (se 1 (by rfl) ⟨1120325, by rfl⟩ : syracuseStep 1493767 = 2240651) B2240651
theorem B2239247 : Blo 1492066 2239247 := bstep (se 1 (by rfl) ⟨1679435, by rfl⟩ : syracuseStep 2239247 = 3358871) B3358871
theorem B1493775 : Blo 1492066 1493775 := bstep (se 1 (by rfl) ⟨1120331, by rfl⟩ : syracuseStep 1493775 = 2240663) B2240663
theorem B36301603 : Blo 1492066 36301603 := bstep (se 1 (by rfl) ⟨27226202, by rfl⟩ : syracuseStep 36301603 = 54452405) B54452405
theorem B2239289 : Blo 1492066 2239289 := bstep (se 2 (by rfl) ⟨839733, by rfl⟩ : syracuseStep 2239289 = 1679467) B1679467
theorem B1493819 : Blo 1492066 1493819 := bstep (se 1 (by rfl) ⟨1120364, by rfl⟩ : syracuseStep 1493819 = 2240729) B2240729
theorem B7179067 : Blo 1492066 7179067 := bstep (se 1 (by rfl) ⟨5384300, by rfl⟩ : syracuseStep 7179067 = 10768601) B10768601
theorem B3025783 : Blo 1492066 3025783 := bstep (se 1 (by rfl) ⟨2269337, by rfl⟩ : syracuseStep 3025783 = 4538675) B4538675
theorem B2239367 : Blo 1492066 2239367 := bstep (se 1 (by rfl) ⟨1679525, by rfl⟩ : syracuseStep 2239367 = 3359051) B3359051
theorem B1493895 : Blo 1492066 1493895 := bstep (se 1 (by rfl) ⟨1120421, by rfl⟩ : syracuseStep 1493895 = 2240843) B2240843
theorem B1493903 : Blo 1492066 1493903 := bstep (se 1 (by rfl) ⟨1120427, by rfl⟩ : syracuseStep 1493903 = 2240855) B2240855
theorem B4311961 : Blo 1492066 4311961 := bstep (se 2 (by rfl) ⟨1616985, by rfl⟩ : syracuseStep 4311961 = 3233971) B3233971
theorem B2239403 : Blo 1492066 2239403 := bstep (se 1 (by rfl) ⟨1679552, by rfl⟩ : syracuseStep 2239403 = 3359105) B3359105
theorem B3189689 : Blo 1492066 3189689 := bstep (se 2 (by rfl) ⟨1196133, by rfl⟩ : syracuseStep 3189689 = 2392267) B2392267
theorem B1493947 : Blo 1492066 1493947 := bstep (se 1 (by rfl) ⟨1120460, by rfl⟩ : syracuseStep 1493947 = 2240921) B2240921
theorem B2239433 : Blo 1492066 2239433 := bstep (se 2 (by rfl) ⟨839787, by rfl⟩ : syracuseStep 2239433 = 1679575) B1679575
theorem B1494023 : Blo 1492066 1494023 := bstep (se 1 (by rfl) ⟨1120517, by rfl⟩ : syracuseStep 1494023 = 2241035) B2241035
theorem B4033547 : Blo 1492066 4033547 := bstep (se 1 (by rfl) ⟨3025160, by rfl⟩ : syracuseStep 4033547 = 6050321) B6050321
theorem B1494031 : Blo 1492066 1494031 := bstep (se 1 (by rfl) ⟨1120523, by rfl⟩ : syracuseStep 1494031 = 2241047) B2241047
theorem B2239547 : Blo 1492066 2239547 := bstep (se 1 (by rfl) ⟨1679660, by rfl⟩ : syracuseStep 2239547 = 3359321) B3359321
theorem B10767421 : Blo 1492066 10767421 := bstep (se 3 (by rfl) ⟨2018891, by rfl⟩ : syracuseStep 10767421 = 4037783) B4037783
theorem B2239607 : Blo 1492066 2239607 := bstep (se 1 (by rfl) ⟨1679705, by rfl⟩ : syracuseStep 2239607 = 3359411) B3359411
theorem B2239631 : Blo 1492066 2239631 := bstep (se 1 (by rfl) ⟨1679723, by rfl⟩ : syracuseStep 2239631 = 3359447) B3359447
theorem B2239673 : Blo 1492066 2239673 := bstep (se 2 (by rfl) ⟨839877, by rfl⟩ : syracuseStep 2239673 = 1679755) B1679755
theorem B2125001 : Blo 1492066 2125001 := bstep (se 2 (by rfl) ⟨796875, by rfl⟩ : syracuseStep 2125001 = 1593751) B1593751
theorem B2239751 : Blo 1492066 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B6810895 : Blo 1492066 6810895 := bstep (se 1 (by rfl) ⟨5108171, by rfl⟩ : syracuseStep 6810895 = 10216343) B10216343
theorem B3779855 : Blo 1492066 3779855 := bstep (se 1 (by rfl) ⟨2834891, by rfl⟩ : syracuseStep 3779855 = 5669783) B5669783
theorem B2239787 : Blo 1492066 2239787 := bstep (se 1 (by rfl) ⟨1679840, by rfl⟩ : syracuseStep 2239787 = 3359681) B3359681
theorem B7171379 : Blo 1492066 7171379 := bstep (se 1 (by rfl) ⟨5378534, by rfl⟩ : syracuseStep 7171379 = 10757069) B10757069
theorem B2239817 : Blo 1492066 2239817 := bstep (se 2 (by rfl) ⟨839931, by rfl⟩ : syracuseStep 2239817 = 1679863) B1679863
theorem B2518391 : Blo 1492066 2518391 := bstep (se 1 (by rfl) ⟨1888793, by rfl⟩ : syracuseStep 2518391 = 3777587) B3777587
theorem B2239931 : Blo 1492066 2239931 := bstep (se 1 (by rfl) ⟨1679948, by rfl⟩ : syracuseStep 2239931 = 3359897) B3359897
theorem B2239991 : Blo 1492066 2239991 := bstep (se 1 (by rfl) ⟨1679993, by rfl⟩ : syracuseStep 2239991 = 3359987) B3359987
theorem B8506883 : Blo 1492066 8506883 := bstep (se 1 (by rfl) ⟨6380162, by rfl⟩ : syracuseStep 8506883 = 12760325) B12760325
theorem B2240015 : Blo 1492066 2240015 := bstep (se 1 (by rfl) ⟨1680011, by rfl⟩ : syracuseStep 2240015 = 3360023) B3360023
theorem B7556651 : Blo 1492066 7556651 := bstep (se 1 (by rfl) ⟨5667488, by rfl⟩ : syracuseStep 7556651 = 11334977) B11334977
theorem B2240057 : Blo 1492066 2240057 := bstep (se 2 (by rfl) ⟨840021, by rfl⟩ : syracuseStep 2240057 = 1680043) B1680043
theorem B2240135 : Blo 1492066 2240135 := bstep (se 1 (by rfl) ⟨1680101, by rfl⟩ : syracuseStep 2240135 = 3360203) B3360203
theorem B2240171 : Blo 1492066 2240171 := bstep (se 1 (by rfl) ⟨1680128, by rfl⟩ : syracuseStep 2240171 = 3360257) B3360257
theorem B2240201 : Blo 1492066 2240201 := bstep (se 2 (by rfl) ⟨840075, by rfl⟩ : syracuseStep 2240201 = 1680151) B1680151
theorem B2125559 : Blo 1492066 2125559 := bstep (se 1 (by rfl) ⟨1594169, by rfl⟩ : syracuseStep 2125559 = 3188339) B3188339
theorem B7171841 : Blo 1492066 7171841 := bstep (se 2 (by rfl) ⟨2689440, by rfl⟩ : syracuseStep 7171841 = 5378881) B5378881
theorem B5451553 : Blo 1492066 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B2518843 : Blo 1492066 2518843 := bstep (se 1 (by rfl) ⟨1889132, by rfl⟩ : syracuseStep 2518843 = 3778265) B3778265
theorem B2240315 : Blo 1492066 2240315 := bstep (se 1 (by rfl) ⟨1680236, by rfl⟩ : syracuseStep 2240315 = 3360473) B3360473
theorem B5041979 : Blo 1492066 5041979 := bstep (se 1 (by rfl) ⟨3781484, by rfl⟩ : syracuseStep 5041979 = 7562969) B7562969
theorem B9563993 : Blo 1492066 9563993 := bstep (se 2 (by rfl) ⟨3586497, by rfl⟩ : syracuseStep 9563993 = 7172995) B7172995
theorem B2240375 : Blo 1492066 2240375 := bstep (se 1 (by rfl) ⟨1680281, by rfl⟩ : syracuseStep 2240375 = 3360563) B3360563
theorem B2240399 : Blo 1492066 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B7171993 : Blo 1492066 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B2240441 : Blo 1492066 2240441 := bstep (se 2 (by rfl) ⟨840165, by rfl⟩ : syracuseStep 2240441 = 1680331) B1680331
theorem B2518985 : Blo 1492066 2518985 := bstep (se 2 (by rfl) ⟨944619, by rfl⟩ : syracuseStep 2518985 = 1889239) B1889239
theorem B3780553 : Blo 1492066 3780553 := bstep (se 2 (by rfl) ⟨1417707, by rfl⟩ : syracuseStep 3780553 = 2835415) B2835415
theorem B8507339 : Blo 1492066 8507339 := bstep (se 1 (by rfl) ⟨6380504, by rfl⟩ : syracuseStep 8507339 = 12761009) B12761009
theorem B2240519 : Blo 1492066 2240519 := bstep (se 1 (by rfl) ⟨1680389, by rfl⟩ : syracuseStep 2240519 = 3360779) B3360779
theorem B3190799 : Blo 1492066 3190799 := bstep (se 1 (by rfl) ⟨2393099, by rfl⟩ : syracuseStep 3190799 = 4786199) B4786199
theorem B2125867 : Blo 1492066 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B2240555 : Blo 1492066 2240555 := bstep (se 1 (by rfl) ⟨1680416, by rfl⟩ : syracuseStep 2240555 = 3360833) B3360833
theorem B2240585 : Blo 1492066 2240585 := bstep (se 2 (by rfl) ⟨840219, by rfl⟩ : syracuseStep 2240585 = 1680439) B1680439
theorem B3780695 : Blo 1492066 3780695 := bstep (se 1 (by rfl) ⟨2835521, by rfl⟩ : syracuseStep 3780695 = 5671043) B5671043
theorem B4427929 : Blo 1492066 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B2240699 : Blo 1492066 2240699 := bstep (se 1 (by rfl) ⟨1680524, by rfl⟩ : syracuseStep 2240699 = 3361049) B3361049
theorem B24875209 : Blo 1492066 24875209 := bstep (se 2 (by rfl) ⟨9328203, by rfl⟩ : syracuseStep 24875209 = 18656407) B18656407
theorem B2240759 : Blo 1492066 2240759 := bstep (se 1 (by rfl) ⟨1680569, by rfl⟩ : syracuseStep 2240759 = 3361139) B3361139
theorem B2240783 : Blo 1492066 2240783 := bstep (se 1 (by rfl) ⟨1680587, by rfl⟩ : syracuseStep 2240783 = 3361175) B3361175
theorem B5042465 : Blo 1492066 5042465 := bstep (se 2 (by rfl) ⟨1890924, by rfl⟩ : syracuseStep 5042465 = 3781849) B3781849
theorem B2240825 : Blo 1492066 2240825 := bstep (se 2 (by rfl) ⟨840309, by rfl⟩ : syracuseStep 2240825 = 1680619) B1680619
theorem B4034875 : Blo 1492066 4034875 := bstep (se 1 (by rfl) ⟨3026156, by rfl⟩ : syracuseStep 4034875 = 6052313) B6052313
theorem B2240903 : Blo 1492066 2240903 := bstep (se 1 (by rfl) ⟨1680677, by rfl⟩ : syracuseStep 2240903 = 3361355) B3361355
theorem B2240939 : Blo 1492066 2240939 := bstep (se 1 (by rfl) ⟨1680704, by rfl⟩ : syracuseStep 2240939 = 3361409) B3361409
theorem B2240969 : Blo 1492066 2240969 := bstep (se 2 (by rfl) ⟨840363, by rfl⟩ : syracuseStep 2240969 = 1680727) B1680727
theorem B6812171 : Blo 1492066 6812171 := bstep (se 1 (by rfl) ⟨5109128, by rfl⟩ : syracuseStep 6812171 = 10218257) B10218257
theorem B2126351 : Blo 1492066 2126351 := bstep (se 1 (by rfl) ⟨1594763, by rfl⟩ : syracuseStep 2126351 = 3189527) B3189527
theorem B2241083 : Blo 1492066 2241083 := bstep (se 1 (by rfl) ⟨1680812, by rfl⟩ : syracuseStep 2241083 = 3361625) B3361625
theorem B8508023 : Blo 1492066 8508023 := bstep (se 1 (by rfl) ⟨6381017, by rfl⟩ : syracuseStep 8508023 = 12762035) B12762035
theorem B2519687 : Blo 1492066 2519687 := bstep (se 1 (by rfl) ⟨1889765, by rfl⟩ : syracuseStep 2519687 = 3779531) B3779531
theorem B2691719 : Blo 1492066 2691719 := bstep (se 1 (by rfl) ⟨2018789, by rfl⟩ : syracuseStep 2691719 = 4037579) B4037579
theorem B1594127 : Blo 1492066 1594127 := bstep (se 1 (by rfl) ⟨1195595, by rfl⟩ : syracuseStep 1594127 = 2391191) B2391191
theorem B7557947 : Blo 1492066 7557947 := bstep (se 1 (by rfl) ⟨5668460, by rfl⟩ : syracuseStep 7557947 = 11336921) B11336921
theorem B10769267 : Blo 1492066 10769267 := bstep (se 1 (by rfl) ⟨8076950, by rfl⟩ : syracuseStep 10769267 = 16153901) B16153901
theorem B7558109 : Blo 1492066 7558109 := bstep (se 3 (by rfl) ⟨1417145, by rfl⟩ : syracuseStep 7558109 = 2834291) B2834291
theorem B3585143 : Blo 1492066 3585143 := bstep (se 1 (by rfl) ⟨2688857, by rfl⟩ : syracuseStep 3585143 = 5377715) B5377715
theorem B1512583 : Blo 1492066 1512583 := bstep (se 1 (by rfl) ⟨1134437, by rfl⟩ : syracuseStep 1512583 = 2268875) B2268875
theorem B2520335 : Blo 1492066 2520335 := bstep (se 1 (by rfl) ⟨1890251, by rfl⟩ : syracuseStep 2520335 = 3780503) B3780503
theorem B7558433 : Blo 1492066 7558433 := bstep (se 2 (by rfl) ⟨2834412, by rfl⟩ : syracuseStep 7558433 = 5668825) B5668825
theorem B5666183 : Blo 1492066 5666183 := bstep (se 1 (by rfl) ⟨4249637, by rfl⟩ : syracuseStep 5666183 = 8499275) B8499275
theorem B11343239 : Blo 1492066 11343239 := bstep (se 1 (by rfl) ⟨8507429, by rfl⟩ : syracuseStep 11343239 = 17014859) B17014859
theorem B6379069 : Blo 1492066 6379069 := bstep (se 3 (by rfl) ⟨1196075, by rfl⟩ : syracuseStep 6379069 = 2392151) B2392151
theorem B16995905 : Blo 1492066 16995905 := bstep (se 2 (by rfl) ⟨6373464, by rfl⟩ : syracuseStep 16995905 = 12746929) B12746929
theorem B16356983 : Blo 1492066 16356983 := bstep (se 1 (by rfl) ⟨12267737, by rfl⟩ : syracuseStep 16356983 = 24535475) B24535475
theorem B4249273 : Blo 1492066 4249273 := bstep (se 2 (by rfl) ⟨1593477, by rfl⟩ : syracuseStep 4249273 = 3186955) B3186955
theorem B2873017 : Blo 1492066 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B2520875 : Blo 1492066 2520875 := bstep (se 1 (by rfl) ⟨1890656, by rfl⟩ : syracuseStep 2520875 = 3781313) B3781313
theorem B8501051 : Blo 1492066 8501051 := bstep (se 1 (by rfl) ⟨6375788, by rfl⟩ : syracuseStep 8501051 = 12751577) B12751577
theorem B6379411 : Blo 1492066 6379411 := bstep (se 1 (by rfl) ⟨4784558, by rfl⟩ : syracuseStep 6379411 = 9569117) B9569117
theorem B1595323 : Blo 1492066 1595323 := bstep (se 1 (by rfl) ⟨1196492, by rfl⟩ : syracuseStep 1595323 = 2392985) B2392985
theorem B5036093 : Blo 1492066 5036093 := bstep (se 3 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 5036093 = 1888535) B1888535
theorem B7559405 : Blo 1492066 7559405 := bstep (se 3 (by rfl) ⟨1417388, by rfl⟩ : syracuseStep 7559405 = 2834777) B2834777
theorem B12753287 : Blo 1492066 12753287 := bstep (se 1 (by rfl) ⟨9564965, by rfl⟩ : syracuseStep 12753287 = 19129931) B19129931
theorem B1890859 : Blo 1492066 1890859 := bstep (se 1 (by rfl) ⟨1418144, by rfl⟩ : syracuseStep 1890859 = 2836289) B2836289
theorem B10222199 : Blo 1492066 10222199 := bstep (se 1 (by rfl) ⟨7666649, by rfl⟩ : syracuseStep 10222199 = 15333299) B15333299
theorem B2833031 : Blo 1492066 2833031 := bstep (se 1 (by rfl) ⟨2124773, by rfl⟩ : syracuseStep 2833031 = 4249547) B4249547
theorem B4602521 : Blo 1492066 4602521 := bstep (se 2 (by rfl) ⟨1725945, by rfl⟩ : syracuseStep 4602521 = 3451891) B3451891
theorem B3832505 : Blo 1492066 3832505 := bstep (se 2 (by rfl) ⟨1437189, by rfl⟩ : syracuseStep 3832505 = 2874379) B2874379
theorem B2046793 : Blo 1492066 2046793 := bstep (se 2 (by rfl) ⟨767547, by rfl⟩ : syracuseStep 2046793 = 1535095) B1535095
theorem B3357575 : Blo 1492066 3357575 := bstep (se 1 (by rfl) ⟨2518181, by rfl⟩ : syracuseStep 3357575 = 5036363) B5036363
theorem B8616851 : Blo 1492066 8616851 := bstep (se 1 (by rfl) ⟨6462638, by rfl⟩ : syracuseStep 8616851 = 12925277) B12925277
theorem B4250515 : Blo 1492066 4250515 := bstep (se 1 (by rfl) ⟨3187886, by rfl⟩ : syracuseStep 4250515 = 6375773) B6375773
theorem B14343065 : Blo 1492066 14343065 := bstep (se 2 (by rfl) ⟨5378649, by rfl⟩ : syracuseStep 14343065 = 10757299) B10757299
theorem B4848569 : Blo 1492066 4848569 := bstep (se 2 (by rfl) ⟨1818213, by rfl⟩ : syracuseStep 4848569 = 3636427) B3636427
theorem B4537289 : Blo 1492066 4537289 := bstep (se 2 (by rfl) ⟨1701483, by rfl⟩ : syracuseStep 4537289 = 3402967) B3402967
theorem B3587017 : Blo 1492066 3587017 := bstep (se 2 (by rfl) ⟨1345131, by rfl⟩ : syracuseStep 3587017 = 2690263) B2690263
theorem B7560215 : Blo 1492066 7560215 := bstep (se 1 (by rfl) ⟨5670161, by rfl⟩ : syracuseStep 7560215 = 11340323) B11340323
theorem B7658525 : Blo 1492066 7658525 := bstep (se 3 (by rfl) ⟨1435973, by rfl⟩ : syracuseStep 7658525 = 2871947) B2871947
theorem B3357755 : Blo 1492066 3357755 := bstep (se 1 (by rfl) ⟨2518316, by rfl⟩ : syracuseStep 3357755 = 5036633) B5036633
theorem B2833555 : Blo 1492066 2833555 := bstep (se 1 (by rfl) ⟨2125166, by rfl⟩ : syracuseStep 2833555 = 4250333) B4250333
theorem B3357881 : Blo 1492066 3357881 := bstep (se 2 (by rfl) ⟨1259205, by rfl⟩ : syracuseStep 3357881 = 2518411) B2518411
theorem B8502509 : Blo 1492066 8502509 := bstep (se 3 (by rfl) ⟨1594220, by rfl⟩ : syracuseStep 8502509 = 3188441) B3188441
theorem B1793287 : Blo 1492066 1793287 := bstep (se 1 (by rfl) ⟨1344965, by rfl⟩ : syracuseStep 1793287 = 2689931) B2689931
theorem B5037497 : Blo 1492066 5037497 := bstep (se 2 (by rfl) ⟨1889061, by rfl⟩ : syracuseStep 5037497 = 3778123) B3778123
theorem B2301385 : Blo 1492066 2301385 := bstep (se 2 (by rfl) ⟨863019, by rfl⟩ : syracuseStep 2301385 = 1726039) B1726039
theorem B1678855 : Blo 1492066 1678855 := bstep (se 1 (by rfl) ⟨1259141, by rfl⟩ : syracuseStep 1678855 = 2518283) B2518283
theorem B3358223 : Blo 1492066 3358223 := bstep (se 1 (by rfl) ⟨2518667, by rfl⟩ : syracuseStep 3358223 = 5037335) B5037335
theorem B3358241 : Blo 1492066 3358241 := bstep (se 2 (by rfl) ⟨1259340, by rfl⟩ : syracuseStep 3358241 = 2518681) B2518681
theorem B1679035 : Blo 1492066 1679035 := bstep (se 1 (by rfl) ⟨1259276, by rfl⟩ : syracuseStep 1679035 = 2518553) B2518553
theorem B14352065 : Blo 1492066 14352065 := bstep (se 2 (by rfl) ⟨5382024, by rfl⟩ : syracuseStep 14352065 = 10764049) B10764049
theorem B2301755 : Blo 1492066 2301755 := bstep (se 1 (by rfl) ⟨1726316, by rfl⟩ : syracuseStep 2301755 = 3452633) B3452633
theorem B24207173 : Blo 1492066 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B3358583 : Blo 1492066 3358583 := bstep (se 1 (by rfl) ⟨2518937, by rfl⟩ : syracuseStep 3358583 = 5037875) B5037875
theorem B3358727 : Blo 1492066 3358727 := bstep (se 1 (by rfl) ⟨2519045, by rfl⟩ : syracuseStep 3358727 = 5038091) B5038091
theorem B2834489 : Blo 1492066 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B3358799 : Blo 1492066 3358799 := bstep (se 1 (by rfl) ⟨2519099, by rfl⟩ : syracuseStep 3358799 = 5038199) B5038199
theorem B17228161 : Blo 1492066 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B2834831 : Blo 1492066 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B64545173 : Blo 1492066 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B1679791 : Blo 1492066 1679791 := bstep (se 1 (by rfl) ⟨1259843, by rfl⟩ : syracuseStep 1679791 = 2519687) B2519687
theorem B1794479 : Blo 1492066 1794479 := bstep (se 1 (by rfl) ⟨1345859, by rfl⟩ : syracuseStep 1794479 = 2691719) B2691719
theorem B3359195 : Blo 1492066 3359195 := bstep (se 1 (by rfl) ⟨2519396, by rfl⟩ : syracuseStep 3359195 = 5038793) B5038793
theorem B5038631 : Blo 1492066 5038631 := bstep (se 1 (by rfl) ⟨3778973, by rfl⟩ : syracuseStep 5038631 = 7557947) B7557947
theorem B5038739 : Blo 1492066 5038739 := bstep (se 1 (by rfl) ⟨3779054, by rfl⟩ : syracuseStep 5038739 = 7558109) B7558109
theorem B5669585 : Blo 1492066 5669585 := bstep (se 2 (by rfl) ⟨2126094, by rfl⟩ : syracuseStep 5669585 = 4252189) B4252189
theorem B4784969 : Blo 1492066 4784969 := bstep (se 2 (by rfl) ⟨1794363, by rfl⟩ : syracuseStep 4784969 = 3588727) B3588727
theorem B1680223 : Blo 1492066 1680223 := bstep (se 1 (by rfl) ⟨1260167, by rfl⟩ : syracuseStep 1680223 = 2520335) B2520335
theorem B5038955 : Blo 1492066 5038955 := bstep (se 1 (by rfl) ⟨3779216, by rfl⟩ : syracuseStep 5038955 = 7558433) B7558433
theorem B5039009 : Blo 1492066 5039009 := bstep (se 2 (by rfl) ⟨1889628, by rfl⟩ : syracuseStep 5039009 = 3779257) B3779257
theorem B3777455 : Blo 1492066 3777455 := bstep (se 1 (by rfl) ⟨2833091, by rfl⟩ : syracuseStep 3777455 = 5666183) B5666183
theorem B3359663 : Blo 1492066 3359663 := bstep (se 1 (by rfl) ⟨2519747, by rfl⟩ : syracuseStep 3359663 = 5039495) B5039495
theorem B7562159 : Blo 1492066 7562159 := bstep (se 1 (by rfl) ⟨5671619, by rfl⟩ : syracuseStep 7562159 = 11343239) B11343239
theorem B11330603 : Blo 1492066 11330603 := bstep (se 1 (by rfl) ⟨8497952, by rfl⟩ : syracuseStep 11330603 = 16995905) B16995905
theorem B7275599 : Blo 1492066 7275599 := bstep (se 1 (by rfl) ⟨5456699, by rfl⟩ : syracuseStep 7275599 = 10913399) B10913399
theorem B2729057 : Blo 1492066 2729057 := bstep (se 2 (by rfl) ⟨1023396, by rfl⟩ : syracuseStep 2729057 = 2046793) B2046793
theorem B1492091 : Blo 1492066 1492091 := bstep (se 1 (by rfl) ⟨1119068, by rfl⟩ : syracuseStep 1492091 = 2238137) B2238137
theorem B3359915 : Blo 1492066 3359915 := bstep (se 1 (by rfl) ⟨2519936, by rfl⟩ : syracuseStep 3359915 = 5039873) B5039873
theorem B1492143 : Blo 1492066 1492143 := bstep (se 1 (by rfl) ⟨1119107, by rfl⟩ : syracuseStep 1492143 = 2238215) B2238215
theorem B1492167 : Blo 1492066 1492167 := bstep (se 1 (by rfl) ⟨1119125, by rfl⟩ : syracuseStep 1492167 = 2238251) B2238251
theorem B1680583 : Blo 1492066 1680583 := bstep (se 1 (by rfl) ⟨1260437, by rfl⟩ : syracuseStep 1680583 = 2520875) B2520875
theorem B1492187 : Blo 1492066 1492187 := bstep (se 1 (by rfl) ⟨1119140, by rfl⟩ : syracuseStep 1492187 = 2238281) B2238281
theorem B4785419 : Blo 1492066 4785419 := bstep (se 1 (by rfl) ⟨3589064, by rfl⟩ : syracuseStep 4785419 = 7178129) B7178129
theorem B1492263 : Blo 1492066 1492263 := bstep (se 1 (by rfl) ⟨1119197, by rfl⟩ : syracuseStep 1492263 = 2238395) B2238395
theorem B1492303 : Blo 1492066 1492303 := bstep (se 1 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 1492303 = 2238455) B2238455
theorem B1492319 : Blo 1492066 1492319 := bstep (se 1 (by rfl) ⟨1119239, by rfl⟩ : syracuseStep 1492319 = 2238479) B2238479
theorem B1492347 : Blo 1492066 1492347 := bstep (se 1 (by rfl) ⟨1119260, by rfl⟩ : syracuseStep 1492347 = 2238521) B2238521
theorem B5670269 : Blo 1492066 5670269 := bstep (se 3 (by rfl) ⟨1063175, by rfl⟩ : syracuseStep 5670269 = 2126351) B2126351
theorem B4785533 : Blo 1492066 4785533 := bstep (se 3 (by rfl) ⟨897287, by rfl⟩ : syracuseStep 4785533 = 1794575) B1794575
theorem B36324773 : Blo 1492066 36324773 := bstep (se 4 (by rfl) ⟨3405447, by rfl⟩ : syracuseStep 36324773 = 6810895) B6810895
theorem B1492399 : Blo 1492066 1492399 := bstep (se 1 (by rfl) ⟨1119299, by rfl⟩ : syracuseStep 1492399 = 2238599) B2238599
theorem B1492423 : Blo 1492066 1492423 := bstep (se 1 (by rfl) ⟨1119317, by rfl⟩ : syracuseStep 1492423 = 2238635) B2238635
theorem B1492443 : Blo 1492066 1492443 := bstep (se 1 (by rfl) ⟨1119332, by rfl⟩ : syracuseStep 1492443 = 2238665) B2238665
theorem B5039603 : Blo 1492066 5039603 := bstep (se 1 (by rfl) ⟨3779702, by rfl⟩ : syracuseStep 5039603 = 7559405) B7559405
theorem B3778073 : Blo 1492066 3778073 := bstep (se 2 (by rfl) ⟨1416777, by rfl⟩ : syracuseStep 3778073 = 2833555) B2833555
theorem B1492519 : Blo 1492066 1492519 := bstep (se 1 (by rfl) ⟨1119389, by rfl⟩ : syracuseStep 1492519 = 2238779) B2238779
theorem B1492559 : Blo 1492066 1492559 := bstep (se 1 (by rfl) ⟨1119419, by rfl⟩ : syracuseStep 1492559 = 2238839) B2238839
theorem B11339351 : Blo 1492066 11339351 := bstep (se 1 (by rfl) ⟨8504513, by rfl⟩ : syracuseStep 11339351 = 17009027) B17009027
theorem B1492575 : Blo 1492066 1492575 := bstep (se 1 (by rfl) ⟨1119431, by rfl⟩ : syracuseStep 1492575 = 2238863) B2238863
theorem B1492603 : Blo 1492066 1492603 := bstep (se 1 (by rfl) ⟨1119452, by rfl⟩ : syracuseStep 1492603 = 2238905) B2238905
theorem B7554707 : Blo 1492066 7554707 := bstep (se 1 (by rfl) ⟨5666030, by rfl⟩ : syracuseStep 7554707 = 11332061) B11332061
theorem B1492655 : Blo 1492066 1492655 := bstep (se 1 (by rfl) ⟨1119491, by rfl⟩ : syracuseStep 1492655 = 2238983) B2238983
theorem B1492679 : Blo 1492066 1492679 := bstep (se 1 (by rfl) ⟨1119509, by rfl⟩ : syracuseStep 1492679 = 2239019) B2239019
theorem B3360455 : Blo 1492066 3360455 := bstep (se 1 (by rfl) ⟨2520341, by rfl⟩ : syracuseStep 3360455 = 5040683) B5040683
theorem B1492699 : Blo 1492066 1492699 := bstep (se 1 (by rfl) ⟨1119524, by rfl⟩ : syracuseStep 1492699 = 2239049) B2239049
theorem B12273389 : Blo 1492066 12273389 := bstep (se 3 (by rfl) ⟨2301260, by rfl⟩ : syracuseStep 12273389 = 4602521) B4602521
theorem B1492775 : Blo 1492066 1492775 := bstep (se 1 (by rfl) ⟨1119581, by rfl⟩ : syracuseStep 1492775 = 2239163) B2239163
theorem B1492815 : Blo 1492066 1492815 := bstep (se 1 (by rfl) ⟨1119611, by rfl⟩ : syracuseStep 1492815 = 2239223) B2239223
theorem B1492831 : Blo 1492066 1492831 := bstep (se 1 (by rfl) ⟨1119623, by rfl⟩ : syracuseStep 1492831 = 2239247) B2239247
theorem B1492859 : Blo 1492066 1492859 := bstep (se 1 (by rfl) ⟨1119644, by rfl⟩ : syracuseStep 1492859 = 2239289) B2239289
theorem B2238383 : Blo 1492066 2238383 := bstep (se 1 (by rfl) ⟨1678787, by rfl⟩ : syracuseStep 2238383 = 3357575) B3357575
theorem B1492911 : Blo 1492066 1492911 := bstep (se 1 (by rfl) ⟨1119683, by rfl⟩ : syracuseStep 1492911 = 2239367) B2239367
theorem B5744567 : Blo 1492066 5744567 := bstep (se 1 (by rfl) ⟨4308425, by rfl⟩ : syracuseStep 5744567 = 8616851) B8616851
theorem B9562043 : Blo 1492066 9562043 := bstep (se 1 (by rfl) ⟨7171532, by rfl⟩ : syracuseStep 9562043 = 14343065) B14343065
theorem B1492935 : Blo 1492066 1492935 := bstep (se 1 (by rfl) ⟨1119701, by rfl⟩ : syracuseStep 1492935 = 2239403) B2239403
theorem B3024859 : Blo 1492066 3024859 := bstep (se 1 (by rfl) ⟨2268644, by rfl⟩ : syracuseStep 3024859 = 4537289) B4537289
theorem B1492955 : Blo 1492066 1492955 := bstep (se 1 (by rfl) ⟨1119716, by rfl⟩ : syracuseStep 1492955 = 2239433) B2239433
theorem B2689031 : Blo 1492066 2689031 := bstep (se 1 (by rfl) ⟨2016773, by rfl⟩ : syracuseStep 2689031 = 4033547) B4033547
theorem B2238473 : Blo 1492066 2238473 := bstep (se 2 (by rfl) ⟨839427, by rfl⟩ : syracuseStep 2238473 = 1678855) B1678855
theorem B5040143 : Blo 1492066 5040143 := bstep (se 1 (by rfl) ⟨3780107, by rfl⟩ : syracuseStep 5040143 = 7560215) B7560215
theorem B5105683 : Blo 1492066 5105683 := bstep (se 1 (by rfl) ⟨3829262, by rfl⟩ : syracuseStep 5105683 = 7658525) B7658525
theorem B2238503 : Blo 1492066 2238503 := bstep (se 1 (by rfl) ⟨1678877, by rfl⟩ : syracuseStep 2238503 = 3357755) B3357755
theorem B1493031 : Blo 1492066 1493031 := bstep (se 1 (by rfl) ⟨1119773, by rfl⟩ : syracuseStep 1493031 = 2239547) B2239547
theorem B1493071 : Blo 1492066 1493071 := bstep (se 1 (by rfl) ⟨1119803, by rfl⟩ : syracuseStep 1493071 = 2239607) B2239607
theorem B8505425 : Blo 1492066 8505425 := bstep (se 2 (by rfl) ⟨3189534, by rfl⟩ : syracuseStep 8505425 = 6379069) B6379069
theorem B1493087 : Blo 1492066 1493087 := bstep (se 1 (by rfl) ⟨1119815, by rfl⟩ : syracuseStep 1493087 = 2239631) B2239631
theorem B2238587 : Blo 1492066 2238587 := bstep (se 1 (by rfl) ⟨1678940, by rfl⟩ : syracuseStep 2238587 = 3357881) B3357881
theorem B1493115 : Blo 1492066 1493115 := bstep (se 1 (by rfl) ⟨1119836, by rfl⟩ : syracuseStep 1493115 = 2239673) B2239673
theorem B38250629 : Blo 1492066 38250629 := bstep (se 4 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 38250629 = 7171993) B7171993
theorem B22997125 : Blo 1492066 22997125 := bstep (se 4 (by rfl) ⟨2155980, by rfl⟩ : syracuseStep 22997125 = 4311961) B4311961
theorem B6138013 : Blo 1492066 6138013 := bstep (se 3 (by rfl) ⟨1150877, by rfl⟩ : syracuseStep 6138013 = 2301755) B2301755
theorem B1493167 : Blo 1492066 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B1493191 : Blo 1492066 1493191 := bstep (se 1 (by rfl) ⟨1119893, by rfl⟩ : syracuseStep 1493191 = 2239787) B2239787
theorem B1493211 : Blo 1492066 1493211 := bstep (se 1 (by rfl) ⟨1119908, by rfl⟩ : syracuseStep 1493211 = 2239817) B2239817
theorem B2238713 : Blo 1492066 2238713 := bstep (se 2 (by rfl) ⟨839517, by rfl⟩ : syracuseStep 2238713 = 1679035) B1679035
theorem B1493287 : Blo 1492066 1493287 := bstep (se 1 (by rfl) ⟨1119965, by rfl⟩ : syracuseStep 1493287 = 2239931) B2239931
theorem B1493327 : Blo 1492066 1493327 := bstep (se 1 (by rfl) ⟨1119995, by rfl⟩ : syracuseStep 1493327 = 2239991) B2239991
theorem B5671255 : Blo 1492066 5671255 := bstep (se 1 (by rfl) ⟨4253441, by rfl⟩ : syracuseStep 5671255 = 8506883) B8506883
theorem B2238815 : Blo 1492066 2238815 := bstep (se 1 (by rfl) ⟨1679111, by rfl⟩ : syracuseStep 2238815 = 3358223) B3358223
theorem B1493343 : Blo 1492066 1493343 := bstep (se 1 (by rfl) ⟨1120007, by rfl⟩ : syracuseStep 1493343 = 2240015) B2240015
theorem B2238827 : Blo 1492066 2238827 := bstep (se 1 (by rfl) ⟨1679120, by rfl⟩ : syracuseStep 2238827 = 3358241) B3358241
theorem B1493371 : Blo 1492066 1493371 := bstep (se 1 (by rfl) ⟨1120028, by rfl⟩ : syracuseStep 1493371 = 2240057) B2240057
theorem B7268737 : Blo 1492066 7268737 := bstep (se 2 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 7268737 = 5451553) B5451553
theorem B1493423 : Blo 1492066 1493423 := bstep (se 1 (by rfl) ⟨1120067, by rfl⟩ : syracuseStep 1493423 = 2240135) B2240135
theorem B1493447 : Blo 1492066 1493447 := bstep (se 1 (by rfl) ⟨1120085, by rfl⟩ : syracuseStep 1493447 = 2240171) B2240171
theorem B1493467 : Blo 1492066 1493467 := bstep (se 1 (by rfl) ⟨1120100, by rfl⟩ : syracuseStep 1493467 = 2240201) B2240201
theorem B8505881 : Blo 1492066 8505881 := bstep (se 2 (by rfl) ⟨3189705, by rfl⟩ : syracuseStep 8505881 = 6379411) B6379411
theorem B1493543 : Blo 1492066 1493543 := bstep (se 1 (by rfl) ⟨1120157, by rfl⟩ : syracuseStep 1493543 = 2240315) B2240315
theorem B3361319 : Blo 1492066 3361319 := bstep (se 1 (by rfl) ⟨2520989, by rfl⟩ : syracuseStep 3361319 = 5041979) B5041979
theorem B6375995 : Blo 1492066 6375995 := bstep (se 1 (by rfl) ⟨4781996, by rfl⟩ : syracuseStep 6375995 = 9563993) B9563993
theorem B2239055 : Blo 1492066 2239055 := bstep (se 1 (by rfl) ⟨1679291, by rfl⟩ : syracuseStep 2239055 = 3358583) B3358583
theorem B1493583 : Blo 1492066 1493583 := bstep (se 1 (by rfl) ⟨1120187, by rfl⟩ : syracuseStep 1493583 = 2240375) B2240375
theorem B5040737 : Blo 1492066 5040737 := bstep (se 2 (by rfl) ⟨1890276, by rfl⟩ : syracuseStep 5040737 = 3780553) B3780553
theorem B1493599 : Blo 1492066 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B1493627 : Blo 1492066 1493627 := bstep (se 1 (by rfl) ⟨1120220, by rfl⟩ : syracuseStep 1493627 = 2240441) B2240441
theorem B5671559 : Blo 1492066 5671559 := bstep (se 1 (by rfl) ⟨4253669, by rfl⟩ : syracuseStep 5671559 = 8507339) B8507339
theorem B1493679 : Blo 1492066 1493679 := bstep (se 1 (by rfl) ⟨1120259, by rfl⟩ : syracuseStep 1493679 = 2240519) B2240519
theorem B2239175 : Blo 1492066 2239175 := bstep (se 1 (by rfl) ⟨1679381, by rfl⟩ : syracuseStep 2239175 = 3358763) B3358763
theorem B1493703 : Blo 1492066 1493703 := bstep (se 1 (by rfl) ⟨1120277, by rfl⟩ : syracuseStep 1493703 = 2240555) B2240555
theorem B1493723 : Blo 1492066 1493723 := bstep (se 1 (by rfl) ⟨1120292, by rfl⟩ : syracuseStep 1493723 = 2240585) B2240585
theorem B1493799 : Blo 1492066 1493799 := bstep (se 1 (by rfl) ⟨1120349, by rfl⟩ : syracuseStep 1493799 = 2240699) B2240699
theorem B1493839 : Blo 1492066 1493839 := bstep (se 1 (by rfl) ⟨1120379, by rfl⟩ : syracuseStep 1493839 = 2240759) B2240759
theorem B1493855 : Blo 1492066 1493855 := bstep (se 1 (by rfl) ⟨1120391, by rfl⟩ : syracuseStep 1493855 = 2240783) B2240783
theorem B2239337 : Blo 1492066 2239337 := bstep (se 2 (by rfl) ⟨839751, by rfl⟩ : syracuseStep 2239337 = 1679503) B1679503
theorem B3361643 : Blo 1492066 3361643 := bstep (se 1 (by rfl) ⟨2521232, by rfl⟩ : syracuseStep 3361643 = 5042465) B5042465
theorem B1493883 : Blo 1492066 1493883 := bstep (se 1 (by rfl) ⟨1120412, by rfl⟩ : syracuseStep 1493883 = 2240825) B2240825
theorem B1493935 : Blo 1492066 1493935 := bstep (se 1 (by rfl) ⟨1120451, by rfl⟩ : syracuseStep 1493935 = 2240903) B2240903
theorem B2239415 : Blo 1492066 2239415 := bstep (se 1 (by rfl) ⟨1679561, by rfl⟩ : syracuseStep 2239415 = 3359123) B3359123
theorem B6810551 : Blo 1492066 6810551 := bstep (se 1 (by rfl) ⟨5107913, by rfl⟩ : syracuseStep 6810551 = 10215827) B10215827
theorem B1493959 : Blo 1492066 1493959 := bstep (se 1 (by rfl) ⟨1120469, by rfl⟩ : syracuseStep 1493959 = 2240939) B2240939
theorem B2517979 : Blo 1492066 2517979 := bstep (se 1 (by rfl) ⟨1888484, by rfl⟩ : syracuseStep 2517979 = 3776969) B3776969
theorem B2239451 : Blo 1492066 2239451 := bstep (se 1 (by rfl) ⟨1679588, by rfl⟩ : syracuseStep 2239451 = 3359177) B3359177
theorem B1493979 : Blo 1492066 1493979 := bstep (se 1 (by rfl) ⟨1120484, by rfl⟩ : syracuseStep 1493979 = 2240969) B2240969
theorem B4541447 : Blo 1492066 4541447 := bstep (se 1 (by rfl) ⟨3406085, by rfl⟩ : syracuseStep 4541447 = 6812171) B6812171
theorem B1494055 : Blo 1492066 1494055 := bstep (se 1 (by rfl) ⟨1120541, by rfl⟩ : syracuseStep 1494055 = 2241083) B2241083
theorem B5672015 : Blo 1492066 5672015 := bstep (se 1 (by rfl) ⟨4254011, by rfl⟩ : syracuseStep 5672015 = 8508023) B8508023
theorem B7179511 : Blo 1492066 7179511 := bstep (se 1 (by rfl) ⟨5384633, by rfl⟩ : syracuseStep 7179511 = 10769267) B10769267
theorem B34958627 : Blo 1492066 34958627 := bstep (se 1 (by rfl) ⟨26218970, by rfl⟩ : syracuseStep 34958627 = 52437941) B52437941
theorem B32304419 : Blo 1492066 32304419 := bstep (se 1 (by rfl) ⟨24228314, by rfl⟩ : syracuseStep 32304419 = 48456629) B48456629
theorem B2239919 : Blo 1492066 2239919 := bstep (se 1 (by rfl) ⟨1679939, by rfl⟩ : syracuseStep 2239919 = 3359879) B3359879
theorem B2240009 : Blo 1492066 2240009 := bstep (se 2 (by rfl) ⟨840003, by rfl⟩ : syracuseStep 2240009 = 1680007) B1680007
theorem B2240039 : Blo 1492066 2240039 := bstep (se 1 (by rfl) ⟨1680029, by rfl⟩ : syracuseStep 2240039 = 3360059) B3360059
theorem B2518607 : Blo 1492066 2518607 := bstep (se 1 (by rfl) ⟨1888955, by rfl⟩ : syracuseStep 2518607 = 3777911) B3777911
theorem B2240123 : Blo 1492066 2240123 := bstep (se 1 (by rfl) ⟨1680092, by rfl⟩ : syracuseStep 2240123 = 3360185) B3360185
theorem B7663243 : Blo 1492066 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B48402137 : Blo 1492066 48402137 := bstep (se 2 (by rfl) ⟨18150801, by rfl⟩ : syracuseStep 48402137 = 36301603) B36301603
theorem B2240249 : Blo 1492066 2240249 := bstep (se 2 (by rfl) ⟨840093, by rfl⟩ : syracuseStep 2240249 = 1680187) B1680187
theorem B9572089 : Blo 1492066 9572089 := bstep (se 2 (by rfl) ⟨3589533, by rfl⟩ : syracuseStep 9572089 = 7179067) B7179067
theorem B4034377 : Blo 1492066 4034377 := bstep (se 2 (by rfl) ⟨1512891, by rfl⟩ : syracuseStep 4034377 = 3025783) B3025783
theorem B2240351 : Blo 1492066 2240351 := bstep (se 1 (by rfl) ⟨1680263, by rfl⟩ : syracuseStep 2240351 = 3360527) B3360527
theorem B2240363 : Blo 1492066 2240363 := bstep (se 1 (by rfl) ⟨1680272, by rfl⟩ : syracuseStep 2240363 = 3360545) B3360545
theorem B3026951 : Blo 1492066 3026951 := bstep (se 1 (by rfl) ⟨2270213, by rfl⟩ : syracuseStep 3026951 = 4540427) B4540427
theorem B5042195 : Blo 1492066 5042195 := bstep (se 1 (by rfl) ⟨3781646, by rfl⟩ : syracuseStep 5042195 = 7563293) B7563293
theorem B3026983 : Blo 1492066 3026983 := bstep (se 1 (by rfl) ⟨2270237, by rfl⟩ : syracuseStep 3026983 = 4540475) B4540475
theorem B3780665 : Blo 1492066 3780665 := bstep (se 2 (by rfl) ⟨1417749, by rfl⟩ : syracuseStep 3780665 = 2835499) B2835499
theorem B2240591 : Blo 1492066 2240591 := bstep (se 1 (by rfl) ⟨1680443, by rfl⟩ : syracuseStep 2240591 = 3360887) B3360887
theorem B14356561 : Blo 1492066 14356561 := bstep (se 2 (by rfl) ⟨5383710, by rfl⟩ : syracuseStep 14356561 = 10767421) B10767421
theorem B2240711 : Blo 1492066 2240711 := bstep (se 1 (by rfl) ⟨1680533, by rfl⟩ : syracuseStep 2240711 = 3361067) B3361067
theorem B43618621 : Blo 1492066 43618621 := bstep (se 3 (by rfl) ⟨8178491, by rfl⟩ : syracuseStep 43618621 = 16356983) B16356983
theorem B2240873 : Blo 1492066 2240873 := bstep (se 2 (by rfl) ⟨840327, by rfl⟩ : syracuseStep 2240873 = 1680655) B1680655
theorem B1888687 : Blo 1492066 1888687 := bstep (se 1 (by rfl) ⟨1416515, by rfl⟩ : syracuseStep 1888687 = 2833031) B2833031
theorem B2519471 : Blo 1492066 2519471 := bstep (se 1 (by rfl) ⟨1889603, by rfl⟩ : syracuseStep 2519471 = 3779207) B3779207
theorem B2240951 : Blo 1492066 2240951 := bstep (se 1 (by rfl) ⟨1680713, by rfl⟩ : syracuseStep 2240951 = 3361427) B3361427
theorem B2240987 : Blo 1492066 2240987 := bstep (se 1 (by rfl) ⟨1680740, by rfl⟩ : syracuseStep 2240987 = 3361481) B3361481
theorem B3068513 : Blo 1492066 3068513 := bstep (se 2 (by rfl) ⟨1150692, by rfl⟩ : syracuseStep 3068513 = 2301385) B2301385
theorem B3232379 : Blo 1492066 3232379 := bstep (se 1 (by rfl) ⟨2424284, by rfl⟩ : syracuseStep 3232379 = 4848569) B4848569
theorem B2126459 : Blo 1492066 2126459 := bstep (se 1 (by rfl) ⟨1594844, by rfl⟩ : syracuseStep 2126459 = 3189689) B3189689
theorem B2519903 : Blo 1492066 2519903 := bstep (se 1 (by rfl) ⟨1889927, by rfl⟩ : syracuseStep 2519903 = 3779855) B3779855
theorem B4780919 : Blo 1492066 4780919 := bstep (se 1 (by rfl) ⟨3585689, by rfl⟩ : syracuseStep 4780919 = 7171379) B7171379
theorem B5665697 : Blo 1492066 5665697 := bstep (se 2 (by rfl) ⟨2124636, by rfl⟩ : syracuseStep 5665697 = 4249273) B4249273
theorem B3830689 : Blo 1492066 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B4781227 : Blo 1492066 4781227 := bstep (se 1 (by rfl) ⟨3585920, by rfl⟩ : syracuseStep 4781227 = 7171841) B7171841
theorem B2127097 : Blo 1492066 2127097 := bstep (se 2 (by rfl) ⟨797661, by rfl⟩ : syracuseStep 2127097 = 1595323) B1595323
theorem B8508797 : Blo 1492066 8508797 := bstep (se 3 (by rfl) ⟨1595399, by rfl⟩ : syracuseStep 8508797 = 3190799) B3190799
theorem B2520463 : Blo 1492066 2520463 := bstep (se 1 (by rfl) ⟨1890347, by rfl⟩ : syracuseStep 2520463 = 3780695) B3780695
theorem B1889831 : Blo 1492066 1889831 := bstep (se 1 (by rfl) ⟨1417373, by rfl⟩ : syracuseStep 1889831 = 2834747) B2834747
theorem B33166945 : Blo 1492066 33166945 := bstep (se 2 (by rfl) ⟨12437604, by rfl⟩ : syracuseStep 33166945 = 24875209) B24875209
theorem B5035769 : Blo 1492066 5035769 := bstep (se 2 (by rfl) ⟨1888413, by rfl⟩ : syracuseStep 5035769 = 3776827) B3776827
theorem B5379833 : Blo 1492066 5379833 := bstep (se 2 (by rfl) ⟨2017437, by rfl⟩ : syracuseStep 5379833 = 4034875) B4034875
theorem B5748509 : Blo 1492066 5748509 := bstep (se 3 (by rfl) ⟨1077845, by rfl⟩ : syracuseStep 5748509 = 2155691) B2155691
theorem B1890155 : Blo 1492066 1890155 := bstep (se 1 (by rfl) ⟨1417616, by rfl⟩ : syracuseStep 1890155 = 2835233) B2835233
theorem B5666669 : Blo 1492066 5666669 := bstep (se 3 (by rfl) ⟨1062500, by rfl⟩ : syracuseStep 5666669 = 2125001) B2125001
theorem B11343725 : Blo 1492066 11343725 := bstep (se 3 (by rfl) ⟨2126948, by rfl⟩ : syracuseStep 11343725 = 4253897) B4253897
theorem B10762145 : Blo 1492066 10762145 := bstep (se 2 (by rfl) ⟨4035804, by rfl⟩ : syracuseStep 10762145 = 8071609) B8071609
theorem B5036039 : Blo 1492066 5036039 := bstep (se 1 (by rfl) ⟨3777029, by rfl⟩ : syracuseStep 5036039 = 7554059) B7554059
theorem B8067109 : Blo 1492066 8067109 := bstep (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) B1512583
theorem B2521145 : Blo 1492066 2521145 := bstep (se 2 (by rfl) ⟨945429, by rfl⟩ : syracuseStep 2521145 = 1890859) B1890859
theorem B2390095 : Blo 1492066 2390095 := bstep (se 1 (by rfl) ⟨1792571, by rfl⟩ : syracuseStep 2390095 = 3585143) B3585143
theorem B5036147 : Blo 1492066 5036147 := bstep (se 1 (by rfl) ⟨3777110, by rfl⟩ : syracuseStep 5036147 = 7554221) B7554221
theorem B12114035 : Blo 1492066 12114035 := bstep (se 1 (by rfl) ⟨9085526, by rfl⟩ : syracuseStep 12114035 = 18171053) B18171053
theorem B23615621 : Blo 1492066 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B5380253 : Blo 1492066 5380253 := bstep (se 3 (by rfl) ⟨1008797, by rfl⟩ : syracuseStep 5380253 = 2017595) B2017595
theorem B5527723 : Blo 1492066 5527723 := bstep (se 1 (by rfl) ⟨4145792, by rfl⟩ : syracuseStep 5527723 = 8291585) B8291585
theorem B5036417 : Blo 1492066 5036417 := bstep (se 2 (by rfl) ⟨1888656, by rfl⟩ : syracuseStep 5036417 = 3777313) B3777313
theorem B5667353 : Blo 1492066 5667353 := bstep (se 2 (by rfl) ⟨2125257, by rfl⟩ : syracuseStep 5667353 = 4250515) B4250515
theorem B5667367 : Blo 1492066 5667367 := bstep (se 1 (by rfl) ⟨4250525, by rfl⟩ : syracuseStep 5667367 = 8501051) B8501051
theorem B4782689 : Blo 1492066 4782689 := bstep (se 2 (by rfl) ⟨1793508, by rfl⟩ : syracuseStep 4782689 = 3587017) B3587017
theorem B3357395 : Blo 1492066 3357395 := bstep (se 1 (by rfl) ⟨2518046, by rfl⟩ : syracuseStep 3357395 = 5036093) B5036093
theorem B7559891 : Blo 1492066 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B4037471 : Blo 1492066 4037471 := bstep (se 1 (by rfl) ⟨3028103, by rfl⟩ : syracuseStep 4037471 = 6056207) B6056207
theorem B8502191 : Blo 1492066 8502191 := bstep (se 1 (by rfl) ⟨6376643, by rfl⟩ : syracuseStep 8502191 = 12753287) B12753287
theorem B6380471 : Blo 1492066 6380471 := bstep (se 1 (by rfl) ⟨4785353, by rfl⟩ : syracuseStep 6380471 = 9570707) B9570707
theorem B2391049 : Blo 1492066 2391049 := bstep (se 2 (by rfl) ⟨896643, by rfl⟩ : syracuseStep 2391049 = 1793287) B1793287
theorem B6814799 : Blo 1492066 6814799 := bstep (se 1 (by rfl) ⟨5111099, by rfl⟩ : syracuseStep 6814799 = 10222199) B10222199
theorem B2555003 : Blo 1492066 2555003 := bstep (se 1 (by rfl) ⟨1916252, by rfl⟩ : syracuseStep 2555003 = 3832505) B3832505
theorem B45964421 : Blo 1492066 45964421 := bstep (se 4 (by rfl) ⟨4309164, by rfl⟩ : syracuseStep 45964421 = 8618329) B8618329
theorem B5037227 : Blo 1492066 5037227 := bstep (se 1 (by rfl) ⟨3777920, by rfl⟩ : syracuseStep 5037227 = 7555841) B7555841
theorem B5668157 : Blo 1492066 5668157 := bstep (se 3 (by rfl) ⟨1062779, by rfl⟩ : syracuseStep 5668157 = 2125559) B2125559
theorem B4251005 : Blo 1492066 4251005 := bstep (se 3 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 4251005 = 1594127) B1594127
theorem B5668339 : Blo 1492066 5668339 := bstep (se 1 (by rfl) ⟨4251254, by rfl⟩ : syracuseStep 5668339 = 8502509) B8502509
theorem B1678927 : Blo 1492066 1678927 := bstep (se 1 (by rfl) ⟨1259195, by rfl⟩ : syracuseStep 1678927 = 2518391) B2518391
theorem B3358331 : Blo 1492066 3358331 := bstep (se 1 (by rfl) ⟨2518748, by rfl⟩ : syracuseStep 3358331 = 5037497) B5037497
theorem B5037767 : Blo 1492066 5037767 := bstep (se 1 (by rfl) ⟨3778325, by rfl⟩ : syracuseStep 5037767 = 7556651) B7556651
theorem B3358457 : Blo 1492066 3358457 := bstep (se 2 (by rfl) ⟨1259421, by rfl⟩ : syracuseStep 3358457 = 2518843) B2518843
theorem B9568043 : Blo 1492066 9568043 := bstep (se 1 (by rfl) ⟨7176032, by rfl⟩ : syracuseStep 9568043 = 14352065) B14352065
theorem B16138115 : Blo 1492066 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B1679323 : Blo 1492066 1679323 := bstep (se 1 (by rfl) ⟨1259492, by rfl⟩ : syracuseStep 1679323 = 2518985) B2518985
theorem B6807577 : Blo 1492066 6807577 := bstep (se 2 (by rfl) ⟨2552841, by rfl⟩ : syracuseStep 6807577 = 5105683) B5105683
theorem B10756145 : Blo 1492066 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B3186793 : Blo 1492066 3186793 := bstep (se 2 (by rfl) ⟨1195047, by rfl⟩ : syracuseStep 3186793 = 2390095) B2390095
theorem B30662833 : Blo 1492066 30662833 := bstep (se 2 (by rfl) ⟨11498562, by rfl⟩ : syracuseStep 30662833 = 22997125) B22997125
theorem B8184017 : Blo 1492066 8184017 := bstep (se 2 (by rfl) ⟨3069006, by rfl⟩ : syracuseStep 8184017 = 6138013) B6138013
theorem B1679647 : Blo 1492066 1679647 := bstep (se 1 (by rfl) ⟨1259735, by rfl⟩ : syracuseStep 1679647 = 2519471) B2519471
theorem B3359087 : Blo 1492066 3359087 := bstep (se 1 (by rfl) ⟨2519315, by rfl⟩ : syracuseStep 3359087 = 5038631) B5038631
theorem B2154919 : Blo 1492066 2154919 := bstep (se 1 (by rfl) ⟨1616189, by rfl⟩ : syracuseStep 2154919 = 3232379) B3232379
theorem B3359159 : Blo 1492066 3359159 := bstep (se 1 (by rfl) ⟨2519369, by rfl⟩ : syracuseStep 3359159 = 5038739) B5038739
theorem B7561673 : Blo 1492066 7561673 := bstep (se 2 (by rfl) ⟨2835627, by rfl⟩ : syracuseStep 7561673 = 5671255) B5671255
theorem B22970881 : Blo 1492066 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B9691649 : Blo 1492066 9691649 := bstep (se 2 (by rfl) ⟨3634368, by rfl⟩ : syracuseStep 9691649 = 7268737) B7268737
theorem B1679935 : Blo 1492066 1679935 := bstep (se 1 (by rfl) ⟨1259951, by rfl⟩ : syracuseStep 1679935 = 2519903) B2519903
theorem B3359303 : Blo 1492066 3359303 := bstep (se 1 (by rfl) ⟨2519477, by rfl⟩ : syracuseStep 3359303 = 5038955) B5038955
theorem B3187279 : Blo 1492066 3187279 := bstep (se 1 (by rfl) ⟨2390459, by rfl⟩ : syracuseStep 3187279 = 4780919) B4780919
theorem B3777131 : Blo 1492066 3777131 := bstep (se 1 (by rfl) ⟨2832848, by rfl⟩ : syracuseStep 3777131 = 5665697) B5665697
theorem B3359339 : Blo 1492066 3359339 := bstep (se 1 (by rfl) ⟨2519504, by rfl⟩ : syracuseStep 3359339 = 5039009) B5039009
theorem B7553735 : Blo 1492066 7553735 := bstep (se 1 (by rfl) ⟨5665301, by rfl⟩ : syracuseStep 7553735 = 11330603) B11330603
theorem B4850399 : Blo 1492066 4850399 := bstep (se 1 (by rfl) ⟨3637799, by rfl⟩ : syracuseStep 4850399 = 7275599) B7275599
theorem B24216515 : Blo 1492066 24216515 := bstep (se 1 (by rfl) ⟨18162386, by rfl⟩ : syracuseStep 24216515 = 36324773) B36324773
theorem B3359735 : Blo 1492066 3359735 := bstep (se 1 (by rfl) ⟨2519801, by rfl⟩ : syracuseStep 3359735 = 5039603) B5039603
theorem B4785277 : Blo 1492066 4785277 := bstep (se 3 (by rfl) ⟨897239, by rfl⟩ : syracuseStep 4785277 = 1794479) B1794479
theorem B3777779 : Blo 1492066 3777779 := bstep (se 1 (by rfl) ⟨2833334, by rfl⟩ : syracuseStep 3777779 = 5666669) B5666669
theorem B7562483 : Blo 1492066 7562483 := bstep (se 1 (by rfl) ⟨5671862, by rfl⟩ : syracuseStep 7562483 = 11343725) B11343725
theorem B1492255 : Blo 1492066 1492255 := bstep (se 1 (by rfl) ⟨1119191, by rfl⟩ : syracuseStep 1492255 = 2238383) B2238383
theorem B6374695 : Blo 1492066 6374695 := bstep (se 1 (by rfl) ⟨4781021, by rfl⟩ : syracuseStep 6374695 = 9562043) B9562043
theorem B1492315 : Blo 1492066 1492315 := bstep (se 1 (by rfl) ⟨1119236, by rfl⟩ : syracuseStep 1492315 = 2238473) B2238473
theorem B3360095 : Blo 1492066 3360095 := bstep (se 1 (by rfl) ⟨2520071, by rfl⟩ : syracuseStep 3360095 = 5040143) B5040143
theorem B1492335 : Blo 1492066 1492335 := bstep (se 1 (by rfl) ⟨1119251, by rfl⟩ : syracuseStep 1492335 = 2238503) B2238503
theorem B1680763 : Blo 1492066 1680763 := bstep (se 1 (by rfl) ⟨1260572, by rfl⟩ : syracuseStep 1680763 = 2521145) B2521145
theorem B5670283 : Blo 1492066 5670283 := bstep (se 1 (by rfl) ⟨4252712, by rfl⟩ : syracuseStep 5670283 = 8505425) B8505425
theorem B1492391 : Blo 1492066 1492391 := bstep (se 1 (by rfl) ⟨1119293, by rfl⟩ : syracuseStep 1492391 = 2238587) B2238587
theorem B5039549 : Blo 1492066 5039549 := bstep (se 3 (by rfl) ⟨944915, by rfl⟩ : syracuseStep 5039549 = 1889831) B1889831
theorem B1492475 : Blo 1492066 1492475 := bstep (se 1 (by rfl) ⟨1119356, by rfl⟩ : syracuseStep 1492475 = 2238713) B2238713
theorem B6374969 : Blo 1492066 6374969 := bstep (se 2 (by rfl) ⟨2390613, by rfl⟩ : syracuseStep 6374969 = 4781227) B4781227
theorem B1492543 : Blo 1492066 1492543 := bstep (se 1 (by rfl) ⟨1119407, by rfl⟩ : syracuseStep 1492543 = 2238815) B2238815
theorem B1492551 : Blo 1492066 1492551 := bstep (se 1 (by rfl) ⟨1119413, by rfl⟩ : syracuseStep 1492551 = 2238827) B2238827
theorem B5670557 : Blo 1492066 5670557 := bstep (se 3 (by rfl) ⟨1063229, by rfl⟩ : syracuseStep 5670557 = 2126459) B2126459
theorem B2836129 : Blo 1492066 2836129 := bstep (se 2 (by rfl) ⟨1063548, by rfl⟩ : syracuseStep 2836129 = 2127097) B2127097
theorem B3778235 : Blo 1492066 3778235 := bstep (se 1 (by rfl) ⟨2833676, by rfl⟩ : syracuseStep 3778235 = 5667353) B5667353
theorem B5670587 : Blo 1492066 5670587 := bstep (se 1 (by rfl) ⟨4252940, by rfl⟩ : syracuseStep 5670587 = 8505881) B8505881
theorem B1492703 : Blo 1492066 1492703 := bstep (se 1 (by rfl) ⟨1119527, by rfl⟩ : syracuseStep 1492703 = 2239055) B2239055
theorem B3188459 : Blo 1492066 3188459 := bstep (se 1 (by rfl) ⟨2391344, by rfl⟩ : syracuseStep 3188459 = 4782689) B4782689
theorem B3360491 : Blo 1492066 3360491 := bstep (se 1 (by rfl) ⟨2520368, by rfl⟩ : syracuseStep 3360491 = 5040737) B5040737
theorem B1492783 : Blo 1492066 1492783 := bstep (se 1 (by rfl) ⟨1119587, by rfl⟩ : syracuseStep 1492783 = 2239175) B2239175
theorem B2238263 : Blo 1492066 2238263 := bstep (se 1 (by rfl) ⟨1678697, by rfl⟩ : syracuseStep 2238263 = 3357395) B3357395
theorem B5039927 : Blo 1492066 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B3360617 : Blo 1492066 3360617 := bstep (se 2 (by rfl) ⟨1260231, by rfl⟩ : syracuseStep 3360617 = 2520463) B2520463
theorem B1492891 : Blo 1492066 1492891 := bstep (se 1 (by rfl) ⟨1119668, by rfl⟩ : syracuseStep 1492891 = 2239337) B2239337
theorem B1492943 : Blo 1492066 1492943 := bstep (se 1 (by rfl) ⟨1119707, by rfl⟩ : syracuseStep 1492943 = 2239415) B2239415
theorem B4540367 : Blo 1492066 4540367 := bstep (se 1 (by rfl) ⟨3405275, by rfl⟩ : syracuseStep 4540367 = 6810551) B6810551
theorem B4253647 : Blo 1492066 4253647 := bstep (se 1 (by rfl) ⟨3190235, by rfl⟩ : syracuseStep 4253647 = 6380471) B6380471
theorem B1492967 : Blo 1492066 1492967 := bstep (se 1 (by rfl) ⟨1119725, by rfl⟩ : syracuseStep 1492967 = 2239451) B2239451
theorem B15329357 : Blo 1492066 15329357 := bstep (se 3 (by rfl) ⟨2874254, by rfl⟩ : syracuseStep 15329357 = 5748509) B5748509
theorem B2238569 : Blo 1492066 2238569 := bstep (se 2 (by rfl) ⟨839463, by rfl⟩ : syracuseStep 2238569 = 1678927) B1678927
theorem B44222593 : Blo 1492066 44222593 := bstep (se 2 (by rfl) ⟨16583472, by rfl⟩ : syracuseStep 44222593 = 33166945) B33166945
theorem B10217657 : Blo 1492066 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B3778771 : Blo 1492066 3778771 := bstep (se 1 (by rfl) ⟨2834078, by rfl⟩ : syracuseStep 3778771 = 5668157) B5668157
theorem B5040413 : Blo 1492066 5040413 := bstep (se 3 (by rfl) ⟨945077, by rfl⟩ : syracuseStep 5040413 = 1890155) B1890155
theorem B1493279 : Blo 1492066 1493279 := bstep (se 1 (by rfl) ⟨1119959, by rfl⟩ : syracuseStep 1493279 = 2239919) B2239919
theorem B1493339 : Blo 1492066 1493339 := bstep (se 1 (by rfl) ⟨1120004, by rfl⟩ : syracuseStep 1493339 = 2240009) B2240009
theorem B1493359 : Blo 1492066 1493359 := bstep (se 1 (by rfl) ⟨1120019, by rfl⟩ : syracuseStep 1493359 = 2240039) B2240039
theorem B2238887 : Blo 1492066 2238887 := bstep (se 1 (by rfl) ⟨1679165, by rfl⟩ : syracuseStep 2238887 = 3358331) B3358331
theorem B1493415 : Blo 1492066 1493415 := bstep (se 1 (by rfl) ⟨1120061, by rfl⟩ : syracuseStep 1493415 = 2240123) B2240123
theorem B2238971 : Blo 1492066 2238971 := bstep (se 1 (by rfl) ⟨1679228, by rfl⟩ : syracuseStep 2238971 = 3358457) B3358457
theorem B1493499 : Blo 1492066 1493499 := bstep (se 1 (by rfl) ⟨1120124, by rfl⟩ : syracuseStep 1493499 = 2240249) B2240249
theorem B1493567 : Blo 1492066 1493567 := bstep (se 1 (by rfl) ⟨1120175, by rfl⟩ : syracuseStep 1493567 = 2240351) B2240351
theorem B1493575 : Blo 1492066 1493575 := bstep (se 1 (by rfl) ⟨1120181, by rfl⟩ : syracuseStep 1493575 = 2240363) B2240363
theorem B10758743 : Blo 1492066 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B4033145 : Blo 1492066 4033145 := bstep (se 2 (by rfl) ⟨1512429, by rfl⟩ : syracuseStep 4033145 = 3024859) B3024859
theorem B2239097 : Blo 1492066 2239097 := bstep (se 2 (by rfl) ⟨839661, by rfl⟩ : syracuseStep 2239097 = 1679323) B1679323
theorem B2239151 : Blo 1492066 2239151 := bstep (se 1 (by rfl) ⟨1679363, by rfl⟩ : syracuseStep 2239151 = 3358727) B3358727
theorem B2017967 : Blo 1492066 2017967 := bstep (se 1 (by rfl) ⟨1513475, by rfl⟩ : syracuseStep 2017967 = 3026951) B3026951
theorem B3361463 : Blo 1492066 3361463 := bstep (se 1 (by rfl) ⟨2521097, by rfl⟩ : syracuseStep 3361463 = 5042195) B5042195
theorem B12110525 : Blo 1492066 12110525 := bstep (se 3 (by rfl) ⟨2270723, by rfl⟩ : syracuseStep 12110525 = 4541447) B4541447
theorem B2239199 : Blo 1492066 2239199 := bstep (se 1 (by rfl) ⟨1679399, by rfl⟩ : syracuseStep 2239199 = 3358799) B3358799
theorem B1493727 : Blo 1492066 1493727 := bstep (se 1 (by rfl) ⟨1120295, by rfl⟩ : syracuseStep 1493727 = 2240591) B2240591
theorem B1493807 : Blo 1492066 1493807 := bstep (se 1 (by rfl) ⟨1120355, by rfl⟩ : syracuseStep 1493807 = 2240711) B2240711
theorem B1493915 : Blo 1492066 1493915 := bstep (se 1 (by rfl) ⟨1120436, by rfl⟩ : syracuseStep 1493915 = 2240873) B2240873
theorem B1493967 : Blo 1492066 1493967 := bstep (se 1 (by rfl) ⟨1120475, by rfl⟩ : syracuseStep 1493967 = 2240951) B2240951
theorem B2239463 : Blo 1492066 2239463 := bstep (se 1 (by rfl) ⟨1679597, by rfl⟩ : syracuseStep 2239463 = 3359195) B3359195
theorem B1493991 : Blo 1492066 1493991 := bstep (se 1 (by rfl) ⟨1120493, by rfl⟩ : syracuseStep 1493991 = 2240987) B2240987
theorem B58158161 : Blo 1492066 58158161 := bstep (se 2 (by rfl) ⟨21809310, by rfl⟩ : syracuseStep 58158161 = 43618621) B43618621
theorem B3779723 : Blo 1492066 3779723 := bstep (se 1 (by rfl) ⟨2834792, by rfl⟩ : syracuseStep 3779723 = 5669585) B5669585
theorem B3189979 : Blo 1492066 3189979 := bstep (se 1 (by rfl) ⟨2392484, by rfl⟩ : syracuseStep 3189979 = 4784969) B4784969
theorem B2518249 : Blo 1492066 2518249 := bstep (se 2 (by rfl) ⟨944343, by rfl⟩ : syracuseStep 2518249 = 1888687) B1888687
theorem B2239721 : Blo 1492066 2239721 := bstep (se 2 (by rfl) ⟨839895, by rfl⟩ : syracuseStep 2239721 = 1679791) B1679791
theorem B2518303 : Blo 1492066 2518303 := bstep (se 1 (by rfl) ⟨1888727, by rfl⟩ : syracuseStep 2518303 = 3777455) B3777455
theorem B2239775 : Blo 1492066 2239775 := bstep (se 1 (by rfl) ⟨1679831, by rfl⟩ : syracuseStep 2239775 = 3359663) B3359663
theorem B5041439 : Blo 1492066 5041439 := bstep (se 1 (by rfl) ⟨3781079, by rfl⟩ : syracuseStep 5041439 = 7562159) B7562159
theorem B7556489 : Blo 1492066 7556489 := bstep (se 2 (by rfl) ⟨2833683, by rfl⟩ : syracuseStep 7556489 = 5667367) B5667367
theorem B2239943 : Blo 1492066 2239943 := bstep (se 1 (by rfl) ⟨1679957, by rfl⟩ : syracuseStep 2239943 = 3359915) B3359915
theorem B3190279 : Blo 1492066 3190279 := bstep (se 1 (by rfl) ⟨2392709, by rfl⟩ : syracuseStep 3190279 = 4785419) B4785419
theorem B3780179 : Blo 1492066 3780179 := bstep (se 1 (by rfl) ⟨2835134, by rfl⟩ : syracuseStep 3780179 = 5670269) B5670269
theorem B3190355 : Blo 1492066 3190355 := bstep (se 1 (by rfl) ⟨2392766, by rfl⟩ : syracuseStep 3190355 = 4785533) B4785533
theorem B5672531 : Blo 1492066 5672531 := bstep (se 1 (by rfl) ⟨4254398, by rfl⟩ : syracuseStep 5672531 = 8508797) B8508797
theorem B29109941 : Blo 1492066 29109941 := bstep (se 5 (by rfl) ⟨1364528, by rfl⟩ : syracuseStep 29109941 = 2729057) B2729057
theorem B2518715 : Blo 1492066 2518715 := bstep (se 1 (by rfl) ⟨1889036, by rfl⟩ : syracuseStep 2518715 = 3778073) B3778073
theorem B2240297 : Blo 1492066 2240297 := bstep (se 2 (by rfl) ⟨840111, by rfl⟩ : syracuseStep 2240297 = 1680223) B1680223
theorem B2240303 : Blo 1492066 2240303 := bstep (se 1 (by rfl) ⟨1680227, by rfl⟩ : syracuseStep 2240303 = 3360455) B3360455
theorem B5107585 : Blo 1492066 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B2240777 : Blo 1492066 2240777 := bstep (se 2 (by rfl) ⟨840291, by rfl⟩ : syracuseStep 2240777 = 1680583) B1680583
theorem B9572681 : Blo 1492066 9572681 := bstep (se 2 (by rfl) ⟨3589755, by rfl⟩ : syracuseStep 9572681 = 7179511) B7179511
theorem B2240879 : Blo 1492066 2240879 := bstep (se 1 (by rfl) ⟨1680659, by rfl⟩ : syracuseStep 2240879 = 3361319) B3361319
theorem B21516677 : Blo 1492066 21516677 := bstep (se 4 (by rfl) ⟨2017188, by rfl⟩ : syracuseStep 21516677 = 4034377) B4034377
theorem B3781039 : Blo 1492066 3781039 := bstep (se 1 (by rfl) ⟨2835779, by rfl⟩ : syracuseStep 3781039 = 5671559) B5671559
theorem B2691647 : Blo 1492066 2691647 := bstep (se 1 (by rfl) ⟨2018735, by rfl⟩ : syracuseStep 2691647 = 4037471) B4037471
theorem B2241095 : Blo 1492066 2241095 := bstep (se 1 (by rfl) ⟨1680821, by rfl⟩ : syracuseStep 2241095 = 3361643) B3361643
theorem B7557785 : Blo 1492066 7557785 := bstep (se 2 (by rfl) ⟨2834169, by rfl⟩ : syracuseStep 7557785 = 5668339) B5668339
theorem B3781343 : Blo 1492066 3781343 := bstep (se 1 (by rfl) ⟨2836007, by rfl⟩ : syracuseStep 3781343 = 5672015) B5672015
theorem B4543199 : Blo 1492066 4543199 := bstep (se 1 (by rfl) ⟨3407399, by rfl⟩ : syracuseStep 4543199 = 6814799) B6814799
theorem B30642947 : Blo 1492066 30642947 := bstep (se 1 (by rfl) ⟨22982210, by rfl⟩ : syracuseStep 30642947 = 45964421) B45964421
theorem B6378695 : Blo 1492066 6378695 := bstep (se 1 (by rfl) ⟨4784021, by rfl⟩ : syracuseStep 6378695 = 9568043) B9568043
theorem B1889659 : Blo 1492066 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B2520443 : Blo 1492066 2520443 := bstep (se 1 (by rfl) ⟨1890332, by rfl⟩ : syracuseStep 2520443 = 3780665) B3780665
theorem B12752261 : Blo 1492066 12752261 := bstep (se 4 (by rfl) ⟨1195524, by rfl⟩ : syracuseStep 12752261 = 2391049) B2391049
theorem B4035977 : Blo 1492066 4035977 := bstep (se 2 (by rfl) ⟨1513491, by rfl⟩ : syracuseStep 4035977 = 3026983) B3026983
theorem B19142081 : Blo 1492066 19142081 := bstep (se 2 (by rfl) ⟨7178280, by rfl⟩ : syracuseStep 19142081 = 14356561) B14356561
theorem B7370297 : Blo 1492066 7370297 := bstep (se 2 (by rfl) ⟨2763861, by rfl⟩ : syracuseStep 7370297 = 5527723) B5527723
theorem B1889887 : Blo 1492066 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B43030115 : Blo 1492066 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B6813341 : Blo 1492066 6813341 := bstep (se 3 (by rfl) ⟨1277501, by rfl⟩ : syracuseStep 6813341 = 2555003) B2555003
theorem B2045675 : Blo 1492066 2045675 := bstep (se 1 (by rfl) ⟨1534256, by rfl⟩ : syracuseStep 2045675 = 3068513) B3068513
theorem B7559567 : Blo 1492066 7559567 := bstep (se 1 (by rfl) ⟨5669675, by rfl⟩ : syracuseStep 7559567 = 11339351) B11339351
theorem B5036471 : Blo 1492066 5036471 := bstep (se 1 (by rfl) ⟨3777353, by rfl⟩ : syracuseStep 5036471 = 7554707) B7554707
theorem B8182259 : Blo 1492066 8182259 := bstep (se 1 (by rfl) ⟨6136694, by rfl⟩ : syracuseStep 8182259 = 12273389) B12273389
theorem B3357179 : Blo 1492066 3357179 := bstep (se 1 (by rfl) ⟨2517884, by rfl⟩ : syracuseStep 3357179 = 5035769) B5035769
theorem B3586555 : Blo 1492066 3586555 := bstep (se 1 (by rfl) ⟨2689916, by rfl⟩ : syracuseStep 3586555 = 5379833) B5379833
theorem B7174763 : Blo 1492066 7174763 := bstep (se 1 (by rfl) ⟨5381072, by rfl⟩ : syracuseStep 7174763 = 10762145) B10762145
theorem B3357305 : Blo 1492066 3357305 := bstep (se 2 (by rfl) ⟨1258989, by rfl⟩ : syracuseStep 3357305 = 2517979) B2517979
theorem B1792687 : Blo 1492066 1792687 := bstep (se 1 (by rfl) ⟨1344515, by rfl⟩ : syracuseStep 1792687 = 2689031) B2689031
theorem B3357359 : Blo 1492066 3357359 := bstep (se 1 (by rfl) ⟨2518019, by rfl⟩ : syracuseStep 3357359 = 5036039) B5036039
theorem B3357431 : Blo 1492066 3357431 := bstep (se 1 (by rfl) ⟨2518073, by rfl⟩ : syracuseStep 3357431 = 5036147) B5036147
theorem B8076023 : Blo 1492066 8076023 := bstep (se 1 (by rfl) ⟨6057017, by rfl⟩ : syracuseStep 8076023 = 12114035) B12114035
theorem B25500419 : Blo 1492066 25500419 := bstep (se 1 (by rfl) ⟨19125314, by rfl⟩ : syracuseStep 25500419 = 38250629) B38250629
theorem B15743747 : Blo 1492066 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B3586835 : Blo 1492066 3586835 := bstep (se 1 (by rfl) ⟨2690126, by rfl⟩ : syracuseStep 3586835 = 5380253) B5380253
theorem B3357611 : Blo 1492066 3357611 := bstep (se 1 (by rfl) ⟨2518208, by rfl⟩ : syracuseStep 3357611 = 5036417) B5036417
theorem B4250663 : Blo 1492066 4250663 := bstep (se 1 (by rfl) ⟨3187997, by rfl⟩ : syracuseStep 4250663 = 6375995) B6375995
theorem B5668127 : Blo 1492066 5668127 := bstep (se 1 (by rfl) ⟨4251095, by rfl⟩ : syracuseStep 5668127 = 8502191) B8502191
theorem B3358151 : Blo 1492066 3358151 := bstep (se 1 (by rfl) ⟨2518613, by rfl⟩ : syracuseStep 3358151 = 5037227) B5037227
theorem B23305751 : Blo 1492066 23305751 := bstep (se 1 (by rfl) ⟨17479313, by rfl⟩ : syracuseStep 23305751 = 34958627) B34958627
theorem B21536279 : Blo 1492066 21536279 := bstep (se 1 (by rfl) ⟨16152209, by rfl⟩ : syracuseStep 21536279 = 32304419) B32304419
theorem B2834003 : Blo 1492066 2834003 := bstep (se 1 (by rfl) ⟨2125502, by rfl⟩ : syracuseStep 2834003 = 4251005) B4251005
theorem B12762785 : Blo 1492066 12762785 := bstep (se 2 (by rfl) ⟨4786044, by rfl⟩ : syracuseStep 12762785 = 9572089) B9572089
theorem B1679071 : Blo 1492066 1679071 := bstep (se 1 (by rfl) ⟨1259303, by rfl⟩ : syracuseStep 1679071 = 2518607) B2518607
theorem B3358511 : Blo 1492066 3358511 := bstep (se 1 (by rfl) ⟨2518883, by rfl⟩ : syracuseStep 3358511 = 5037767) B5037767
theorem B32268091 : Blo 1492066 32268091 := bstep (se 1 (by rfl) ⟨24201068, by rfl⟩ : syracuseStep 32268091 = 48402137) B48402137
theorem B15318845 : Blo 1492066 15318845 := bstep (se 3 (by rfl) ⟨2872283, by rfl⟩ : syracuseStep 15318845 = 5744567) B5744567
theorem B9076769 : Blo 1492066 9076769 := bstep (se 2 (by rfl) ⟨3403788, by rfl⟩ : syracuseStep 9076769 = 6807577) B6807577
theorem B5456011 : Blo 1492066 5456011 := bstep (se 1 (by rfl) ⟨4092008, by rfl⟩ : syracuseStep 5456011 = 8184017) B8184017
theorem B6381787 : Blo 1492066 6381787 := bstep (se 1 (by rfl) ⟨4786340, by rfl⟩ : syracuseStep 6381787 = 9572681) B9572681
theorem B14344451 : Blo 1492066 14344451 := bstep (se 1 (by rfl) ⟨10758338, by rfl⟩ : syracuseStep 14344451 = 21516677) B21516677
theorem B5038361 : Blo 1492066 5038361 := bstep (se 2 (by rfl) ⟨1889385, by rfl⟩ : syracuseStep 5038361 = 3778771) B3778771
theorem B1794431 : Blo 1492066 1794431 := bstep (se 1 (by rfl) ⟨1345823, by rfl⟩ : syracuseStep 1794431 = 2691647) B2691647
theorem B16998821 : Blo 1492066 16998821 := bstep (se 4 (by rfl) ⟨1593639, by rfl⟩ : syracuseStep 16998821 = 3187279) B3187279
theorem B5038523 : Blo 1492066 5038523 := bstep (se 1 (by rfl) ⟨3778892, by rfl⟩ : syracuseStep 5038523 = 7557785) B7557785
theorem B4252463 : Blo 1492066 4252463 := bstep (se 1 (by rfl) ⟨3189347, by rfl⟩ : syracuseStep 4252463 = 6378695) B6378695
theorem B1680295 : Blo 1492066 1680295 := bstep (se 1 (by rfl) ⟨1260221, by rfl⟩ : syracuseStep 1680295 = 2520443) B2520443
theorem B3359699 : Blo 1492066 3359699 := bstep (se 1 (by rfl) ⟨2519774, by rfl⟩ : syracuseStep 3359699 = 5039549) B5039549
theorem B1492175 : Blo 1492066 1492175 := bstep (se 1 (by rfl) ⟨1119131, by rfl⟩ : syracuseStep 1492175 = 2238263) B2238263
theorem B3359951 : Blo 1492066 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B1492379 : Blo 1492066 1492379 := bstep (se 1 (by rfl) ⟨1119284, by rfl⟩ : syracuseStep 1492379 = 2238569) B2238569
theorem B3360275 : Blo 1492066 3360275 := bstep (se 1 (by rfl) ⟨2520206, by rfl⟩ : syracuseStep 3360275 = 5040413) B5040413
theorem B5039711 : Blo 1492066 5039711 := bstep (se 1 (by rfl) ⟨3779783, by rfl⟩ : syracuseStep 5039711 = 7559567) B7559567
theorem B1492591 : Blo 1492066 1492591 := bstep (se 1 (by rfl) ⟨1119443, by rfl⟩ : syracuseStep 1492591 = 2238887) B2238887
theorem B4253305 : Blo 1492066 4253305 := bstep (se 2 (by rfl) ⟨1594989, by rfl⟩ : syracuseStep 4253305 = 3189979) B3189979
theorem B2238119 : Blo 1492066 2238119 := bstep (se 1 (by rfl) ⟨1678589, by rfl⟩ : syracuseStep 2238119 = 3357179) B3357179
theorem B1492647 : Blo 1492066 1492647 := bstep (se 1 (by rfl) ⟨1119485, by rfl⟩ : syracuseStep 1492647 = 2238971) B2238971
theorem B2688763 : Blo 1492066 2688763 := bstep (se 1 (by rfl) ⟨2016572, by rfl⟩ : syracuseStep 2688763 = 4033145) B4033145
theorem B2238203 : Blo 1492066 2238203 := bstep (se 1 (by rfl) ⟨1678652, by rfl⟩ : syracuseStep 2238203 = 3357305) B3357305
theorem B1492731 : Blo 1492066 1492731 := bstep (se 1 (by rfl) ⟨1119548, by rfl⟩ : syracuseStep 1492731 = 2239097) B2239097
theorem B2238239 : Blo 1492066 2238239 := bstep (se 1 (by rfl) ⟨1678679, by rfl⟩ : syracuseStep 2238239 = 3357359) B3357359
theorem B1492767 : Blo 1492066 1492767 := bstep (se 1 (by rfl) ⟨1119575, by rfl⟩ : syracuseStep 1492767 = 2239151) B2239151
theorem B1492799 : Blo 1492066 1492799 := bstep (se 1 (by rfl) ⟨1119599, by rfl⟩ : syracuseStep 1492799 = 2239199) B2239199
theorem B2238287 : Blo 1492066 2238287 := bstep (se 1 (by rfl) ⟨1678715, by rfl⟩ : syracuseStep 2238287 = 3357431) B3357431
theorem B5384015 : Blo 1492066 5384015 := bstep (se 1 (by rfl) ⟨4038011, by rfl⟩ : syracuseStep 5384015 = 8076023) B8076023
theorem B17000279 : Blo 1492066 17000279 := bstep (se 1 (by rfl) ⟨12750209, by rfl⟩ : syracuseStep 17000279 = 25500419) B25500419
theorem B10495831 : Blo 1492066 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B2238407 : Blo 1492066 2238407 := bstep (se 1 (by rfl) ⟨1678805, by rfl⟩ : syracuseStep 2238407 = 3357611) B3357611
theorem B1492975 : Blo 1492066 1492975 := bstep (se 1 (by rfl) ⟨1119731, by rfl⟩ : syracuseStep 1492975 = 2239463) B2239463
theorem B4253705 : Blo 1492066 4253705 := bstep (se 2 (by rfl) ⟨1595139, by rfl⟩ : syracuseStep 4253705 = 3190279) B3190279
theorem B1493147 : Blo 1492066 1493147 := bstep (se 1 (by rfl) ⟨1119860, by rfl⟩ : syracuseStep 1493147 = 2239721) B2239721
theorem B3778751 : Blo 1492066 3778751 := bstep (se 1 (by rfl) ⟨2834063, by rfl⟩ : syracuseStep 3778751 = 5668127) B5668127
theorem B1493183 : Blo 1492066 1493183 := bstep (se 1 (by rfl) ⟨1119887, by rfl⟩ : syracuseStep 1493183 = 2239775) B2239775
theorem B3360959 : Blo 1492066 3360959 := bstep (se 1 (by rfl) ⟨2520719, by rfl⟩ : syracuseStep 3360959 = 5041439) B5041439
theorem B2238761 : Blo 1492066 2238761 := bstep (se 2 (by rfl) ⟨839535, by rfl⟩ : syracuseStep 2238761 = 1679071) B1679071
theorem B2238767 : Blo 1492066 2238767 := bstep (se 1 (by rfl) ⟨1679075, by rfl⟩ : syracuseStep 2238767 = 3358151) B3358151
theorem B1493295 : Blo 1492066 1493295 := bstep (se 1 (by rfl) ⟨1119971, by rfl⟩ : syracuseStep 1493295 = 2239943) B2239943
theorem B6810113 : Blo 1492066 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B1493531 : Blo 1492066 1493531 := bstep (se 1 (by rfl) ⟨1120148, by rfl⟩ : syracuseStep 1493531 = 2240297) B2240297
theorem B2239007 : Blo 1492066 2239007 := bstep (se 1 (by rfl) ⟨1679255, by rfl⟩ : syracuseStep 2239007 = 3358511) B3358511
theorem B1493535 : Blo 1492066 1493535 := bstep (se 1 (by rfl) ⟨1120151, by rfl⟩ : syracuseStep 1493535 = 2240303) B2240303
theorem B5671529 : Blo 1492066 5671529 := bstep (se 2 (by rfl) ⟨2126823, by rfl⟩ : syracuseStep 5671529 = 4253647) B4253647
theorem B7170763 : Blo 1492066 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B1493851 : Blo 1492066 1493851 := bstep (se 1 (by rfl) ⟨1120388, by rfl⟩ : syracuseStep 1493851 = 2240777) B2240777
theorem B2239391 : Blo 1492066 2239391 := bstep (se 1 (by rfl) ⟨1679543, by rfl⟩ : syracuseStep 2239391 = 3359087) B3359087
theorem B1493919 : Blo 1492066 1493919 := bstep (se 1 (by rfl) ⟨1120439, by rfl⟩ : syracuseStep 1493919 = 2240879) B2240879
theorem B2239439 : Blo 1492066 2239439 := bstep (se 1 (by rfl) ⟨1679579, by rfl⟩ : syracuseStep 2239439 = 3359159) B3359159
theorem B5041115 : Blo 1492066 5041115 := bstep (se 1 (by rfl) ⟨3780836, by rfl⟩ : syracuseStep 5041115 = 7561673) B7561673
theorem B2239529 : Blo 1492066 2239529 := bstep (se 2 (by rfl) ⟨839823, by rfl⟩ : syracuseStep 2239529 = 1679647) B1679647
theorem B2239535 : Blo 1492066 2239535 := bstep (se 1 (by rfl) ⟨1679651, by rfl⟩ : syracuseStep 2239535 = 3359303) B3359303
theorem B1494063 : Blo 1492066 1494063 := bstep (se 1 (by rfl) ⟨1120547, by rfl⟩ : syracuseStep 1494063 = 2241095) B2241095
theorem B2518087 : Blo 1492066 2518087 := bstep (se 1 (by rfl) ⟨1888565, by rfl⟩ : syracuseStep 2518087 = 3777131) B3777131
theorem B2239559 : Blo 1492066 2239559 := bstep (se 1 (by rfl) ⟨1679669, by rfl⟩ : syracuseStep 2239559 = 3359339) B3359339
theorem B5041385 : Blo 1492066 5041385 := bstep (se 2 (by rfl) ⟨1890519, by rfl⟩ : syracuseStep 5041385 = 3781039) B3781039
theorem B2239823 : Blo 1492066 2239823 := bstep (se 1 (by rfl) ⟨1679867, by rfl⟩ : syracuseStep 2239823 = 3359735) B3359735
theorem B2239913 : Blo 1492066 2239913 := bstep (se 2 (by rfl) ⟨839967, by rfl⟩ : syracuseStep 2239913 = 1679935) B1679935
theorem B2518519 : Blo 1492066 2518519 := bstep (se 1 (by rfl) ⟨1888889, by rfl⟩ : syracuseStep 2518519 = 3777779) B3777779
theorem B5041655 : Blo 1492066 5041655 := bstep (se 1 (by rfl) ⟨3781241, by rfl⟩ : syracuseStep 5041655 = 7562483) B7562483
theorem B2240063 : Blo 1492066 2240063 := bstep (se 1 (by rfl) ⟨1680047, by rfl⟩ : syracuseStep 2240063 = 3360095) B3360095
theorem B2690651 : Blo 1492066 2690651 := bstep (se 1 (by rfl) ⟨2017988, by rfl⟩ : syracuseStep 2690651 = 4035977) B4035977
theorem B3780371 : Blo 1492066 3780371 := bstep (se 1 (by rfl) ⟨2835278, by rfl⟩ : syracuseStep 3780371 = 5670557) B5670557
theorem B4542227 : Blo 1492066 4542227 := bstep (se 1 (by rfl) ⟨3406670, by rfl⟩ : syracuseStep 4542227 = 6813341) B6813341
theorem B2518823 : Blo 1492066 2518823 := bstep (se 1 (by rfl) ⟨1889117, by rfl⟩ : syracuseStep 2518823 = 3778235) B3778235
theorem B3780391 : Blo 1492066 3780391 := bstep (se 1 (by rfl) ⟨2835293, by rfl⟩ : syracuseStep 3780391 = 5670587) B5670587
theorem B2125639 : Blo 1492066 2125639 := bstep (se 1 (by rfl) ⟨1594229, by rfl⟩ : syracuseStep 2125639 = 3188459) B3188459
theorem B2240327 : Blo 1492066 2240327 := bstep (se 1 (by rfl) ⟨1680245, by rfl⟩ : syracuseStep 2240327 = 3360491) B3360491
theorem B2240411 : Blo 1492066 2240411 := bstep (se 1 (by rfl) ⟨1680308, by rfl⟩ : syracuseStep 2240411 = 3360617) B3360617
theorem B3026911 : Blo 1492066 3026911 := bstep (se 1 (by rfl) ⟨2270183, by rfl⟩ : syracuseStep 3026911 = 4540367) B4540367
theorem B10219571 : Blo 1492066 10219571 := bstep (se 1 (by rfl) ⟨7664678, by rfl⟩ : syracuseStep 10219571 = 15329357) B15329357
theorem B6811771 : Blo 1492066 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B8499593 : Blo 1492066 8499593 := bstep (se 2 (by rfl) ⟨3187347, by rfl⟩ : syracuseStep 8499593 = 6374695) B6374695
theorem B7172495 : Blo 1492066 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B2240975 : Blo 1492066 2240975 := bstep (se 1 (by rfl) ⟨1680731, by rfl⟩ : syracuseStep 2240975 = 3361463) B3361463
theorem B8073683 : Blo 1492066 8073683 := bstep (se 1 (by rfl) ⟨6055262, by rfl⟩ : syracuseStep 8073683 = 12110525) B12110525
theorem B2519545 : Blo 1492066 2519545 := bstep (se 2 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 2519545 = 1889659) B1889659
theorem B2241017 : Blo 1492066 2241017 := bstep (se 2 (by rfl) ⟨840381, by rfl⟩ : syracuseStep 2241017 = 1680763) B1680763
theorem B2519815 : Blo 1492066 2519815 := bstep (se 1 (by rfl) ⟨1889861, by rfl⟩ : syracuseStep 2519815 = 3779723) B3779723
theorem B2519849 : Blo 1492066 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B3781505 : Blo 1492066 3781505 := bstep (se 2 (by rfl) ⟨1418064, by rfl⟩ : syracuseStep 3781505 = 2836129) B2836129
theorem B15537167 : Blo 1492066 15537167 := bstep (se 1 (by rfl) ⟨11652875, by rfl⟩ : syracuseStep 15537167 = 23305751) B23305751
theorem B14357519 : Blo 1492066 14357519 := bstep (se 1 (by rfl) ⟨10768139, by rfl⟩ : syracuseStep 14357519 = 21536279) B21536279
theorem B1889335 : Blo 1492066 1889335 := bstep (se 1 (by rfl) ⟨1417001, by rfl⟩ : syracuseStep 1889335 = 2834003) B2834003
theorem B2520119 : Blo 1492066 2520119 := bstep (se 1 (by rfl) ⟨1890089, by rfl⟩ : syracuseStep 2520119 = 3780179) B3780179
theorem B2126903 : Blo 1492066 2126903 := bstep (se 1 (by rfl) ⟨1595177, by rfl⟩ : syracuseStep 2126903 = 3190355) B3190355
theorem B3781687 : Blo 1492066 3781687 := bstep (se 1 (by rfl) ⟨2836265, by rfl⟩ : syracuseStep 3781687 = 5672531) B5672531
theorem B8508523 : Blo 1492066 8508523 := bstep (se 1 (by rfl) ⟨6381392, by rfl⟩ : syracuseStep 8508523 = 12762785) B12762785
theorem B10212563 : Blo 1492066 10212563 := bstep (se 1 (by rfl) ⟨7659422, by rfl⟩ : syracuseStep 10212563 = 15318845) B15318845
theorem B4249057 : Blo 1492066 4249057 := bstep (se 2 (by rfl) ⟨1593396, by rfl⟩ : syracuseStep 4249057 = 3186793) B3186793
theorem B58963457 : Blo 1492066 58963457 := bstep (se 2 (by rfl) ⟨22111296, by rfl⟩ : syracuseStep 58963457 = 44222593) B44222593
theorem B40883777 : Blo 1492066 40883777 := bstep (se 2 (by rfl) ⟨15331416, by rfl⟩ : syracuseStep 40883777 = 30662833) B30662833
theorem B6461099 : Blo 1492066 6461099 := bstep (se 1 (by rfl) ⟨4845824, by rfl⟩ : syracuseStep 6461099 = 9691649) B9691649
theorem B5035823 : Blo 1492066 5035823 := bstep (se 1 (by rfl) ⟨3776867, by rfl⟩ : syracuseStep 5035823 = 7553735) B7553735
theorem B2520895 : Blo 1492066 2520895 := bstep (se 1 (by rfl) ⟨1890671, by rfl⟩ : syracuseStep 2520895 = 3781343) B3781343
theorem B3028799 : Blo 1492066 3028799 := bstep (se 1 (by rfl) ⟨2271599, by rfl⟩ : syracuseStep 3028799 = 4543199) B4543199
theorem B20428631 : Blo 1492066 20428631 := bstep (se 1 (by rfl) ⟨15321473, by rfl⟩ : syracuseStep 20428631 = 30642947) B30642947
theorem B2873225 : Blo 1492066 2873225 := bstep (se 2 (by rfl) ⟨1077459, by rfl⟩ : syracuseStep 2873225 = 2154919) B2154919
theorem B16144343 : Blo 1492066 16144343 := bstep (se 1 (by rfl) ⟨12108257, by rfl⟩ : syracuseStep 16144343 = 24216515) B24216515
theorem B4782073 : Blo 1492066 4782073 := bstep (se 2 (by rfl) ⟨1793277, by rfl⟩ : syracuseStep 4782073 = 3586555) B3586555
theorem B30627841 : Blo 1492066 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B2390249 : Blo 1492066 2390249 := bstep (se 2 (by rfl) ⟨896343, by rfl⟩ : syracuseStep 2390249 = 1792687) B1792687
theorem B8501507 : Blo 1492066 8501507 := bstep (se 1 (by rfl) ⟨6376130, by rfl⟩ : syracuseStep 8501507 = 12752261) B12752261
theorem B12761387 : Blo 1492066 12761387 := bstep (se 1 (by rfl) ⟨9571040, by rfl⟩ : syracuseStep 12761387 = 19142081) B19142081
theorem B4249979 : Blo 1492066 4249979 := bstep (se 1 (by rfl) ⟨3187484, by rfl⟩ : syracuseStep 4249979 = 6374969) B6374969
theorem B4913531 : Blo 1492066 4913531 := bstep (se 1 (by rfl) ⟨3685148, by rfl⟩ : syracuseStep 4913531 = 7370297) B7370297
theorem B28686743 : Blo 1492066 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B6380369 : Blo 1492066 6380369 := bstep (se 2 (by rfl) ⟨2392638, by rfl⟩ : syracuseStep 6380369 = 4785277) B4785277
theorem B3357647 : Blo 1492066 3357647 := bstep (se 1 (by rfl) ⟨2518235, by rfl⟩ : syracuseStep 3357647 = 5036471) B5036471
theorem B3357665 : Blo 1492066 3357665 := bstep (se 2 (by rfl) ⟨1259124, by rfl⟩ : syracuseStep 3357665 = 2518249) B2518249
theorem B5454839 : Blo 1492066 5454839 := bstep (se 1 (by rfl) ⟨4091129, by rfl⟩ : syracuseStep 5454839 = 8182259) B8182259
theorem B3357737 : Blo 1492066 3357737 := bstep (se 2 (by rfl) ⟨1259151, by rfl⟩ : syracuseStep 3357737 = 2518303) B2518303
theorem B4783175 : Blo 1492066 4783175 := bstep (se 1 (by rfl) ⟨3587381, by rfl⟩ : syracuseStep 4783175 = 7174763) B7174763
theorem B5381245 : Blo 1492066 5381245 := bstep (se 3 (by rfl) ⟨1008983, by rfl⟩ : syracuseStep 5381245 = 2017967) B2017967
theorem B2391223 : Blo 1492066 2391223 := bstep (se 1 (by rfl) ⟨1793417, by rfl⟩ : syracuseStep 2391223 = 3586835) B3586835
theorem B7560377 : Blo 1492066 7560377 := bstep (se 2 (by rfl) ⟨2835141, by rfl⟩ : syracuseStep 7560377 = 5670283) B5670283
theorem B12934397 : Blo 1492066 12934397 := bstep (se 3 (by rfl) ⟨2425199, by rfl⟩ : syracuseStep 12934397 = 4850399) B4850399
theorem B5455133 : Blo 1492066 5455133 := bstep (se 3 (by rfl) ⟨1022837, by rfl⟩ : syracuseStep 5455133 = 2045675) B2045675
theorem B2833775 : Blo 1492066 2833775 := bstep (se 1 (by rfl) ⟨2125331, by rfl⟩ : syracuseStep 2833775 = 4250663) B4250663
theorem B38772107 : Blo 1492066 38772107 := bstep (se 1 (by rfl) ⟨29079080, by rfl⟩ : syracuseStep 38772107 = 58158161) B58158161
theorem B5037659 : Blo 1492066 5037659 := bstep (se 1 (by rfl) ⟨3778244, by rfl⟩ : syracuseStep 5037659 = 7556489) B7556489
theorem B43024121 : Blo 1492066 43024121 := bstep (se 2 (by rfl) ⟨16134045, by rfl⟩ : syracuseStep 43024121 = 32268091) B32268091
theorem B19406627 : Blo 1492066 19406627 := bstep (se 1 (by rfl) ⟨14554970, by rfl⟩ : syracuseStep 19406627 = 29109941) B29109941
theorem B1679143 : Blo 1492066 1679143 := bstep (se 1 (by rfl) ⟨1259357, by rfl⟩ : syracuseStep 1679143 = 2518715) B2518715
theorem B40837121 : Blo 1492066 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B7274681 : Blo 1492066 7274681 := bstep (se 2 (by rfl) ⟨2728005, by rfl⟩ : syracuseStep 7274681 = 5456011) B5456011
theorem B3358907 : Blo 1492066 3358907 := bstep (se 1 (by rfl) ⟨2519180, by rfl⟩ : syracuseStep 3358907 = 5038361) B5038361
theorem B3359015 : Blo 1492066 3359015 := bstep (se 1 (by rfl) ⟨2519261, by rfl⟩ : syracuseStep 3359015 = 5038523) B5038523
theorem B5382455 : Blo 1492066 5382455 := bstep (se 1 (by rfl) ⟨4036841, by rfl⟩ : syracuseStep 5382455 = 8073683) B8073683
theorem B1679899 : Blo 1492066 1679899 := bstep (se 1 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 1679899 = 2519849) B2519849
theorem B2834975 : Blo 1492066 2834975 := bstep (se 1 (by rfl) ⟨2126231, by rfl⟩ : syracuseStep 2834975 = 4252463) B4252463
theorem B6373997 : Blo 1492066 6373997 := bstep (se 3 (by rfl) ⟨1195124, by rfl⟩ : syracuseStep 6373997 = 2390249) B2390249
theorem B3359393 : Blo 1492066 3359393 := bstep (se 2 (by rfl) ⟨1259772, by rfl⟩ : syracuseStep 3359393 = 2519545) B2519545
theorem B1680079 : Blo 1492066 1680079 := bstep (se 1 (by rfl) ⟨1260059, by rfl⟩ : syracuseStep 1680079 = 2520119) B2520119
theorem B6808375 : Blo 1492066 6808375 := bstep (se 1 (by rfl) ⟨5106281, by rfl⟩ : syracuseStep 6808375 = 10212563) B10212563
theorem B9561017 : Blo 1492066 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B4785149 : Blo 1492066 4785149 := bstep (se 3 (by rfl) ⟨897215, by rfl⟩ : syracuseStep 4785149 = 1794431) B1794431
theorem B3359753 : Blo 1492066 3359753 := bstep (se 2 (by rfl) ⟨1259907, by rfl⟩ : syracuseStep 3359753 = 2519815) B2519815
theorem B27255851 : Blo 1492066 27255851 := bstep (se 1 (by rfl) ⟨20441888, by rfl⟩ : syracuseStep 27255851 = 40883777) B40883777
theorem B3359807 : Blo 1492066 3359807 := bstep (se 1 (by rfl) ⟨2519855, by rfl⟩ : syracuseStep 3359807 = 5039711) B5039711
theorem B1492079 : Blo 1492066 1492079 := bstep (se 1 (by rfl) ⟨1119059, by rfl⟩ : syracuseStep 1492079 = 2238119) B2238119
theorem B1492135 : Blo 1492066 1492135 := bstep (se 1 (by rfl) ⟨1119101, by rfl⟩ : syracuseStep 1492135 = 2238203) B2238203
theorem B1492159 : Blo 1492066 1492159 := bstep (se 1 (by rfl) ⟨1119119, by rfl⟩ : syracuseStep 1492159 = 2238239) B2238239
theorem B1492191 : Blo 1492066 1492191 := bstep (se 1 (by rfl) ⟨1119143, by rfl⟩ : syracuseStep 1492191 = 2238287) B2238287
theorem B3589343 : Blo 1492066 3589343 := bstep (se 1 (by rfl) ⟨2692007, by rfl⟩ : syracuseStep 3589343 = 5384015) B5384015
theorem B1492271 : Blo 1492066 1492271 := bstep (se 1 (by rfl) ⟨1119203, by rfl⟩ : syracuseStep 1492271 = 2238407) B2238407
theorem B2835803 : Blo 1492066 2835803 := bstep (se 1 (by rfl) ⟨2126852, by rfl⟩ : syracuseStep 2835803 = 4253705) B4253705
theorem B1492507 : Blo 1492066 1492507 := bstep (se 1 (by rfl) ⟨1119380, by rfl⟩ : syracuseStep 1492507 = 2238761) B2238761
theorem B1492511 : Blo 1492066 1492511 := bstep (se 1 (by rfl) ⟨1119383, by rfl⟩ : syracuseStep 1492511 = 2238767) B2238767
theorem B3188297 : Blo 1492066 3188297 := bstep (se 2 (by rfl) ⟨1195611, by rfl⟩ : syracuseStep 3188297 = 2391223) B2391223
theorem B1492671 : Blo 1492066 1492671 := bstep (se 1 (by rfl) ⟨1119503, by rfl⟩ : syracuseStep 1492671 = 2239007) B2239007
theorem B4253579 : Blo 1492066 4253579 := bstep (se 1 (by rfl) ⟨3190184, by rfl⟩ : syracuseStep 4253579 = 6380369) B6380369
theorem B1492927 : Blo 1492066 1492927 := bstep (se 1 (by rfl) ⟨1119695, by rfl⟩ : syracuseStep 1492927 = 2239391) B2239391
theorem B2238431 : Blo 1492066 2238431 := bstep (se 1 (by rfl) ⟨1678823, by rfl⟩ : syracuseStep 2238431 = 3357647) B3357647
theorem B1492959 : Blo 1492066 1492959 := bstep (se 1 (by rfl) ⟨1119719, by rfl⟩ : syracuseStep 1492959 = 2239439) B2239439
theorem B3360743 : Blo 1492066 3360743 := bstep (se 1 (by rfl) ⟨2520557, by rfl⟩ : syracuseStep 3360743 = 5041115) B5041115
theorem B2238443 : Blo 1492066 2238443 := bstep (se 1 (by rfl) ⟨1678832, by rfl⟩ : syracuseStep 2238443 = 3357665) B3357665
theorem B2238491 : Blo 1492066 2238491 := bstep (se 1 (by rfl) ⟨1678868, by rfl⟩ : syracuseStep 2238491 = 3357737) B3357737
theorem B1493019 : Blo 1492066 1493019 := bstep (se 1 (by rfl) ⟨1119764, by rfl⟩ : syracuseStep 1493019 = 2239529) B2239529
theorem B1493023 : Blo 1492066 1493023 := bstep (se 1 (by rfl) ⟨1119767, by rfl⟩ : syracuseStep 1493023 = 2239535) B2239535
theorem B1493039 : Blo 1492066 1493039 := bstep (se 1 (by rfl) ⟨1119779, by rfl⟩ : syracuseStep 1493039 = 2239559) B2239559
theorem B3188783 : Blo 1492066 3188783 := bstep (se 1 (by rfl) ⟨2391587, by rfl⟩ : syracuseStep 3188783 = 4783175) B4783175
theorem B5040251 : Blo 1492066 5040251 := bstep (se 1 (by rfl) ⟨3780188, by rfl⟩ : syracuseStep 5040251 = 7560377) B7560377
theorem B3360923 : Blo 1492066 3360923 := bstep (se 1 (by rfl) ⟨2520692, by rfl⟩ : syracuseStep 3360923 = 5041385) B5041385
theorem B5671073 : Blo 1492066 5671073 := bstep (se 2 (by rfl) ⟨2126652, by rfl⟩ : syracuseStep 5671073 = 4253305) B4253305
theorem B1493215 : Blo 1492066 1493215 := bstep (se 1 (by rfl) ⟨1119911, by rfl⟩ : syracuseStep 1493215 = 2239823) B2239823
theorem B25848071 : Blo 1492066 25848071 := bstep (se 1 (by rfl) ⟨19386053, by rfl⟩ : syracuseStep 25848071 = 38772107) B38772107
theorem B1493275 : Blo 1492066 1493275 := bstep (se 1 (by rfl) ⟨1119956, by rfl⟩ : syracuseStep 1493275 = 2239913) B2239913
theorem B3361103 : Blo 1492066 3361103 := bstep (se 1 (by rfl) ⟨2520827, by rfl⟩ : syracuseStep 3361103 = 5041655) B5041655
theorem B1493375 : Blo 1492066 1493375 := bstep (se 1 (by rfl) ⟨1120031, by rfl⟩ : syracuseStep 1493375 = 2240063) B2240063
theorem B2238857 : Blo 1492066 2238857 := bstep (se 2 (by rfl) ⟨839571, by rfl⟩ : syracuseStep 2238857 = 1679143) B1679143
theorem B5040521 : Blo 1492066 5040521 := bstep (se 2 (by rfl) ⟨1890195, by rfl⟩ : syracuseStep 5040521 = 3780391) B3780391
theorem B3361193 : Blo 1492066 3361193 := bstep (se 2 (by rfl) ⟨1260447, by rfl⟩ : syracuseStep 3361193 = 2520895) B2520895
theorem B13994441 : Blo 1492066 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B28682747 : Blo 1492066 28682747 := bstep (se 1 (by rfl) ⟨21512060, by rfl⟩ : syracuseStep 28682747 = 43024121) B43024121
theorem B12937751 : Blo 1492066 12937751 := bstep (se 1 (by rfl) ⟨9703313, by rfl⟩ : syracuseStep 12937751 = 19406627) B19406627
theorem B1493551 : Blo 1492066 1493551 := bstep (se 1 (by rfl) ⟨1120163, by rfl⟩ : syracuseStep 1493551 = 2240327) B2240327
theorem B1493607 : Blo 1492066 1493607 := bstep (se 1 (by rfl) ⟨1120205, by rfl⟩ : syracuseStep 1493607 = 2240411) B2240411
theorem B6376097 : Blo 1492066 6376097 := bstep (se 2 (by rfl) ⟨2391036, by rfl⟩ : syracuseStep 6376097 = 4782073) B4782073
theorem B5671741 : Blo 1492066 5671741 := bstep (se 3 (by rfl) ⟨1063451, by rfl⟩ : syracuseStep 5671741 = 2126903) B2126903
theorem B9562967 : Blo 1492066 9562967 := bstep (se 1 (by rfl) ⟨7172225, by rfl⟩ : syracuseStep 9562967 = 14344451) B14344451
theorem B11332547 : Blo 1492066 11332547 := bstep (se 1 (by rfl) ⟨8499410, by rfl⟩ : syracuseStep 11332547 = 16998821) B16998821
theorem B1493983 : Blo 1492066 1493983 := bstep (se 1 (by rfl) ⟨1120487, by rfl⟩ : syracuseStep 1493983 = 2240975) B2240975
theorem B1494011 : Blo 1492066 1494011 := bstep (se 1 (by rfl) ⟨1120508, by rfl⟩ : syracuseStep 1494011 = 2241017) B2241017
theorem B2239799 : Blo 1492066 2239799 := bstep (se 1 (by rfl) ⟨1679849, by rfl⟩ : syracuseStep 2239799 = 3359699) B3359699
theorem B10358111 : Blo 1492066 10358111 := bstep (se 1 (by rfl) ⟨7768583, by rfl⟩ : syracuseStep 10358111 = 15537167) B15537167
theorem B9571679 : Blo 1492066 9571679 := bstep (se 1 (by rfl) ⟨7178759, by rfl⟩ : syracuseStep 9571679 = 14357519) B14357519
theorem B2239967 : Blo 1492066 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B39308971 : Blo 1492066 39308971 := bstep (se 1 (by rfl) ⟨29481728, by rfl⟩ : syracuseStep 39308971 = 58963457) B58963457
theorem B2240183 : Blo 1492066 2240183 := bstep (se 1 (by rfl) ⟨1680137, by rfl⟩ : syracuseStep 2240183 = 3360275) B3360275
theorem B2019199 : Blo 1492066 2019199 := bstep (se 1 (by rfl) ⟨1514399, by rfl⟩ : syracuseStep 2019199 = 3028799) B3028799
theorem B2240393 : Blo 1492066 2240393 := bstep (se 2 (by rfl) ⟨840147, by rfl⟩ : syracuseStep 2240393 = 1680295) B1680295
theorem B11333519 : Blo 1492066 11333519 := bstep (se 1 (by rfl) ⟨8500139, by rfl⟩ : syracuseStep 11333519 = 17000279) B17000279
theorem B13619087 : Blo 1492066 13619087 := bstep (se 1 (by rfl) ⟨10214315, by rfl⟩ : syracuseStep 13619087 = 20428631) B20428631
theorem B2519113 : Blo 1492066 2519113 := bstep (se 2 (by rfl) ⟨944667, by rfl⟩ : syracuseStep 2519113 = 1889335) B1889335
theorem B5042249 : Blo 1492066 5042249 := bstep (se 2 (by rfl) ⟨1890843, by rfl⟩ : syracuseStep 5042249 = 3781687) B3781687
theorem B2519167 : Blo 1492066 2519167 := bstep (se 1 (by rfl) ⟨1889375, by rfl⟩ : syracuseStep 2519167 = 3778751) B3778751
theorem B2240639 : Blo 1492066 2240639 := bstep (se 1 (by rfl) ⟨1680479, by rfl⟩ : syracuseStep 2240639 = 3360959) B3360959
theorem B8507591 : Blo 1492066 8507591 := bstep (se 1 (by rfl) ⟨6380693, by rfl⟩ : syracuseStep 8507591 = 12761387) B12761387
theorem B19124495 : Blo 1492066 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B3781019 : Blo 1492066 3781019 := bstep (se 1 (by rfl) ⟨2835764, by rfl⟩ : syracuseStep 3781019 = 5671529) B5671529
theorem B5665409 : Blo 1492066 5665409 := bstep (se 2 (by rfl) ⟨2124528, by rfl⟩ : syracuseStep 5665409 = 4249057) B4249057
theorem B8622931 : Blo 1492066 8622931 := bstep (se 1 (by rfl) ⟨6467198, by rfl⟩ : syracuseStep 8622931 = 12934397) B12934397
theorem B1889183 : Blo 1492066 1889183 := bstep (se 1 (by rfl) ⟨1416887, by rfl⟩ : syracuseStep 1889183 = 2833775) B2833775
theorem B3585017 : Blo 1492066 3585017 := bstep (se 2 (by rfl) ⟨1344381, by rfl⟩ : syracuseStep 3585017 = 2688763) B2688763
theorem B2520247 : Blo 1492066 2520247 := bstep (se 1 (by rfl) ⟨1890185, by rfl⟩ : syracuseStep 2520247 = 3780371) B3780371
theorem B3028151 : Blo 1492066 3028151 := bstep (se 1 (by rfl) ⟨2271113, by rfl⟩ : syracuseStep 3028151 = 4542227) B4542227
theorem B4035881 : Blo 1492066 4035881 := bstep (se 2 (by rfl) ⟨1513455, by rfl⟩ : syracuseStep 4035881 = 3026911) B3026911
theorem B6051179 : Blo 1492066 6051179 := bstep (se 1 (by rfl) ⟨4538384, by rfl⟩ : syracuseStep 6051179 = 9076769) B9076769
theorem B6813047 : Blo 1492066 6813047 := bstep (se 1 (by rfl) ⟨5109785, by rfl⟩ : syracuseStep 6813047 = 10219571) B10219571
theorem B9082361 : Blo 1492066 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B5666395 : Blo 1492066 5666395 := bstep (se 1 (by rfl) ⟨4249796, by rfl⟩ : syracuseStep 5666395 = 8499593) B8499593
theorem B4781663 : Blo 1492066 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B8509049 : Blo 1492066 8509049 := bstep (se 2 (by rfl) ⟨3190893, by rfl⟩ : syracuseStep 8509049 = 6381787) B6381787
theorem B2521003 : Blo 1492066 2521003 := bstep (se 1 (by rfl) ⟨1890752, by rfl⟩ : syracuseStep 2521003 = 3781505) B3781505
theorem B4307399 : Blo 1492066 4307399 := bstep (se 1 (by rfl) ⟨3230549, by rfl⟩ : syracuseStep 4307399 = 6461099) B6461099
theorem B3357215 : Blo 1492066 3357215 := bstep (se 1 (by rfl) ⟨2517911, by rfl⟩ : syracuseStep 3357215 = 5035823) B5035823
theorem B1915483 : Blo 1492066 1915483 := bstep (se 1 (by rfl) ⟨1436612, by rfl⟩ : syracuseStep 1915483 = 2873225) B2873225
theorem B10762895 : Blo 1492066 10762895 := bstep (se 1 (by rfl) ⟨8072171, by rfl⟩ : syracuseStep 10762895 = 16144343) B16144343
theorem B18160301 : Blo 1492066 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B3357449 : Blo 1492066 3357449 := bstep (se 2 (by rfl) ⟨1259043, by rfl⟩ : syracuseStep 3357449 = 2518087) B2518087
theorem B11344697 : Blo 1492066 11344697 := bstep (se 2 (by rfl) ⟨4254261, by rfl⟩ : syracuseStep 11344697 = 8508523) B8508523
theorem B7174993 : Blo 1492066 7174993 := bstep (se 2 (by rfl) ⟨2690622, by rfl⟩ : syracuseStep 7174993 = 5381245) B5381245
theorem B5667671 : Blo 1492066 5667671 := bstep (se 1 (by rfl) ⟨4250753, by rfl⟩ : syracuseStep 5667671 = 8501507) B8501507
theorem B7175069 : Blo 1492066 7175069 := bstep (se 3 (by rfl) ⟨1345325, by rfl⟩ : syracuseStep 7175069 = 2690651) B2690651
theorem B2833319 : Blo 1492066 2833319 := bstep (se 1 (by rfl) ⟨2124989, by rfl⟩ : syracuseStep 2833319 = 4249979) B4249979
theorem B3275687 : Blo 1492066 3275687 := bstep (se 1 (by rfl) ⟨2456765, by rfl⟩ : syracuseStep 3275687 = 4913531) B4913531
theorem B3358025 : Blo 1492066 3358025 := bstep (se 2 (by rfl) ⟨1259259, by rfl⟩ : syracuseStep 3358025 = 2518519) B2518519
theorem B3636559 : Blo 1492066 3636559 := bstep (se 1 (by rfl) ⟨2727419, by rfl⟩ : syracuseStep 3636559 = 5454839) B5454839
theorem B3636755 : Blo 1492066 3636755 := bstep (se 1 (by rfl) ⟨2727566, by rfl⟩ : syracuseStep 3636755 = 5455133) B5455133
theorem B3358439 : Blo 1492066 3358439 := bstep (se 1 (by rfl) ⟨2518829, by rfl⟩ : syracuseStep 3358439 = 5037659) B5037659
theorem B2834185 : Blo 1492066 2834185 := bstep (se 2 (by rfl) ⟨1062819, by rfl⟩ : syracuseStep 2834185 = 2125639) B2125639
theorem B1679215 : Blo 1492066 1679215 := bstep (se 1 (by rfl) ⟨1259411, by rfl⟩ : syracuseStep 1679215 = 2518823) B2518823
theorem B3358817 : Blo 1492066 3358817 := bstep (se 2 (by rfl) ⟨1259556, by rfl⟩ : syracuseStep 3358817 = 2519113) B2519113
theorem B4849787 : Blo 1492066 4849787 := bstep (se 1 (by rfl) ⟨3637340, by rfl⟩ : syracuseStep 4849787 = 7274681) B7274681
theorem B3358889 : Blo 1492066 3358889 := bstep (se 2 (by rfl) ⟨1259583, by rfl⟩ : syracuseStep 3358889 = 2519167) B2519167
theorem B3776939 : Blo 1492066 3776939 := bstep (se 1 (by rfl) ⟨2832704, by rfl⟩ : syracuseStep 3776939 = 5665409) B5665409
theorem B18170567 : Blo 1492066 18170567 := bstep (se 1 (by rfl) ⟨13627925, by rfl⟩ : syracuseStep 18170567 = 27255851) B27255851
theorem B14353213 : Blo 1492066 14353213 := bstep (se 3 (by rfl) ⟨2691227, by rfl⟩ : syracuseStep 14353213 = 5382455) B5382455
theorem B2392895 : Blo 1492066 2392895 := bstep (se 1 (by rfl) ⟨1794671, by rfl⟩ : syracuseStep 2392895 = 3589343) B3589343
theorem B6054907 : Blo 1492066 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B3187775 : Blo 1492066 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B9077833 : Blo 1492066 9077833 := bstep (se 2 (by rfl) ⟨3404187, by rfl⟩ : syracuseStep 9077833 = 6808375) B6808375
theorem B7562321 : Blo 1492066 7562321 := bstep (se 2 (by rfl) ⟨2835870, by rfl⟩ : syracuseStep 7562321 = 5671741) B5671741
theorem B2835719 : Blo 1492066 2835719 := bstep (se 1 (by rfl) ⟨2126789, by rfl⟩ : syracuseStep 2835719 = 4253579) B4253579
theorem B1492287 : Blo 1492066 1492287 := bstep (se 1 (by rfl) ⟨1119215, by rfl⟩ : syracuseStep 1492287 = 2238431) B2238431
theorem B1492295 : Blo 1492066 1492295 := bstep (se 1 (by rfl) ⟨1119221, by rfl⟩ : syracuseStep 1492295 = 2238443) B2238443
theorem B1492327 : Blo 1492066 1492327 := bstep (se 1 (by rfl) ⟨1119245, by rfl⟩ : syracuseStep 1492327 = 2238491) B2238491
theorem B3360167 : Blo 1492066 3360167 := bstep (se 1 (by rfl) ⟨2520125, by rfl⟩ : syracuseStep 3360167 = 5040251) B5040251
theorem B3360329 : Blo 1492066 3360329 := bstep (se 2 (by rfl) ⟨1260123, by rfl⟩ : syracuseStep 3360329 = 2520247) B2520247
theorem B1492571 : Blo 1492066 1492571 := bstep (se 1 (by rfl) ⟨1119428, by rfl⟩ : syracuseStep 1492571 = 2238857) B2238857
theorem B3360347 : Blo 1492066 3360347 := bstep (se 1 (by rfl) ⟨2520260, by rfl⟩ : syracuseStep 3360347 = 5040521) B5040521
theorem B19121831 : Blo 1492066 19121831 := bstep (se 1 (by rfl) ⟨14341373, by rfl⟩ : syracuseStep 19121831 = 28682747) B28682747
theorem B2238143 : Blo 1492066 2238143 := bstep (se 1 (by rfl) ⟨1678607, by rfl⟩ : syracuseStep 2238143 = 3357215) B3357215
theorem B2238299 : Blo 1492066 2238299 := bstep (se 1 (by rfl) ⟨1678724, by rfl⟩ : syracuseStep 2238299 = 3357449) B3357449
theorem B7563131 : Blo 1492066 7563131 := bstep (se 1 (by rfl) ⟨5672348, by rfl⟩ : syracuseStep 7563131 = 11344697) B11344697
theorem B6375311 : Blo 1492066 6375311 := bstep (se 1 (by rfl) ⟨4781483, by rfl⟩ : syracuseStep 6375311 = 9562967) B9562967
theorem B3778447 : Blo 1492066 3778447 := bstep (se 1 (by rfl) ⟨2833835, by rfl⟩ : syracuseStep 3778447 = 5667671) B5667671
theorem B7555031 : Blo 1492066 7555031 := bstep (se 1 (by rfl) ⟨5666273, by rfl⟩ : syracuseStep 7555031 = 11332547) B11332547
theorem B7555193 : Blo 1492066 7555193 := bstep (se 2 (by rfl) ⟨2833197, by rfl⟩ : syracuseStep 7555193 = 5666395) B5666395
theorem B1493199 : Blo 1492066 1493199 := bstep (se 1 (by rfl) ⟨1119899, by rfl⟩ : syracuseStep 1493199 = 2239799) B2239799
theorem B2238683 : Blo 1492066 2238683 := bstep (se 1 (by rfl) ⟨1679012, by rfl⟩ : syracuseStep 2238683 = 3358025) B3358025
theorem B1493311 : Blo 1492066 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B3778913 : Blo 1492066 3778913 := bstep (se 2 (by rfl) ⟨1417092, by rfl⟩ : syracuseStep 3778913 = 2834185) B2834185
theorem B7555517 : Blo 1492066 7555517 := bstep (se 3 (by rfl) ⟨1416659, by rfl⟩ : syracuseStep 7555517 = 2833319) B2833319
theorem B1493455 : Blo 1492066 1493455 := bstep (se 1 (by rfl) ⟨1120091, by rfl⟩ : syracuseStep 1493455 = 2240183) B2240183
theorem B2238953 : Blo 1492066 2238953 := bstep (se 2 (by rfl) ⟨839607, by rfl⟩ : syracuseStep 2238953 = 1679215) B1679215
theorem B25496045 : Blo 1492066 25496045 := bstep (se 3 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 25496045 = 9561017) B9561017
theorem B2238959 : Blo 1492066 2238959 := bstep (se 1 (by rfl) ⟨1679219, by rfl⟩ : syracuseStep 2238959 = 3358439) B3358439
theorem B3361337 : Blo 1492066 3361337 := bstep (se 2 (by rfl) ⟨1260501, by rfl⟩ : syracuseStep 3361337 = 2521003) B2521003
theorem B1493595 : Blo 1492066 1493595 := bstep (se 1 (by rfl) ⟨1120196, by rfl⟩ : syracuseStep 1493595 = 2240393) B2240393
theorem B7555679 : Blo 1492066 7555679 := bstep (se 1 (by rfl) ⟨5666759, by rfl⟩ : syracuseStep 7555679 = 11333519) B11333519
theorem B9079391 : Blo 1492066 9079391 := bstep (se 1 (by rfl) ⟨6809543, by rfl⟩ : syracuseStep 9079391 = 13619087) B13619087
theorem B43076245 : Blo 1492066 43076245 := bstep (se 6 (by rfl) ⟨1009599, by rfl⟩ : syracuseStep 43076245 = 2019199) B2019199
theorem B27224747 : Blo 1492066 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B3361499 : Blo 1492066 3361499 := bstep (se 1 (by rfl) ⟨2521124, by rfl⟩ : syracuseStep 3361499 = 5042249) B5042249
theorem B1493759 : Blo 1492066 1493759 := bstep (se 1 (by rfl) ⟨1120319, by rfl⟩ : syracuseStep 1493759 = 2240639) B2240639
theorem B2239271 : Blo 1492066 2239271 := bstep (se 1 (by rfl) ⟨1679453, by rfl⟩ : syracuseStep 2239271 = 3358907) B3358907
theorem B5671727 : Blo 1492066 5671727 := bstep (se 1 (by rfl) ⟨4253795, by rfl⟩ : syracuseStep 5671727 = 8507591) B8507591
theorem B12749663 : Blo 1492066 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B2239343 : Blo 1492066 2239343 := bstep (se 1 (by rfl) ⟨1679507, by rfl⟩ : syracuseStep 2239343 = 3359015) B3359015
theorem B2239595 : Blo 1492066 2239595 := bstep (se 1 (by rfl) ⟨1679696, by rfl⟩ : syracuseStep 2239595 = 3359393) B3359393
theorem B3190099 : Blo 1492066 3190099 := bstep (se 1 (by rfl) ⟨2392574, by rfl⟩ : syracuseStep 3190099 = 4785149) B4785149
theorem B2239835 : Blo 1492066 2239835 := bstep (se 1 (by rfl) ⟨1679876, by rfl⟩ : syracuseStep 2239835 = 3359753) B3359753
theorem B2239865 : Blo 1492066 2239865 := bstep (se 2 (by rfl) ⟨839949, by rfl⟩ : syracuseStep 2239865 = 1679899) B1679899
theorem B2239871 : Blo 1492066 2239871 := bstep (se 1 (by rfl) ⟨1679903, by rfl⟩ : syracuseStep 2239871 = 3359807) B3359807
theorem B2018767 : Blo 1492066 2018767 := bstep (se 1 (by rfl) ⟨1514075, by rfl⟩ : syracuseStep 2018767 = 3028151) B3028151
theorem B2690587 : Blo 1492066 2690587 := bstep (se 1 (by rfl) ⟨2017940, by rfl⟩ : syracuseStep 2690587 = 4035881) B4035881
theorem B4034119 : Blo 1492066 4034119 := bstep (se 1 (by rfl) ⟨3025589, by rfl⟩ : syracuseStep 4034119 = 6051179) B6051179
theorem B4542031 : Blo 1492066 4542031 := bstep (se 1 (by rfl) ⟨3406523, by rfl⟩ : syracuseStep 4542031 = 6813047) B6813047
theorem B2240105 : Blo 1492066 2240105 := bstep (se 2 (by rfl) ⟨840039, by rfl⟩ : syracuseStep 2240105 = 1680079) B1680079
theorem B2125531 : Blo 1492066 2125531 := bstep (se 1 (by rfl) ⟨1594148, by rfl⟩ : syracuseStep 2125531 = 3188297) B3188297
theorem B5672699 : Blo 1492066 5672699 := bstep (se 1 (by rfl) ⟨4254524, by rfl⟩ : syracuseStep 5672699 = 8509049) B8509049
theorem B11497241 : Blo 1492066 11497241 := bstep (se 2 (by rfl) ⟨4311465, by rfl⟩ : syracuseStep 11497241 = 8622931) B8622931
theorem B2240495 : Blo 1492066 2240495 := bstep (se 1 (by rfl) ⟨1680371, by rfl⟩ : syracuseStep 2240495 = 3360743) B3360743
theorem B2125855 : Blo 1492066 2125855 := bstep (se 1 (by rfl) ⟨1594391, by rfl⟩ : syracuseStep 2125855 = 3188783) B3188783
theorem B2240615 : Blo 1492066 2240615 := bstep (se 1 (by rfl) ⟨1680461, by rfl⟩ : syracuseStep 2240615 = 3360923) B3360923
theorem B3780715 : Blo 1492066 3780715 := bstep (se 1 (by rfl) ⟨2835536, by rfl⟩ : syracuseStep 3780715 = 5671073) B5671073
theorem B17232047 : Blo 1492066 17232047 := bstep (se 1 (by rfl) ⟨12924035, by rfl⟩ : syracuseStep 17232047 = 25848071) B25848071
theorem B2240735 : Blo 1492066 2240735 := bstep (se 1 (by rfl) ⟨1680551, by rfl⟩ : syracuseStep 2240735 = 3361103) B3361103
theorem B2240795 : Blo 1492066 2240795 := bstep (se 1 (by rfl) ⟨1680596, by rfl⟩ : syracuseStep 2240795 = 3361193) B3361193
theorem B2871599 : Blo 1492066 2871599 := bstep (se 1 (by rfl) ⟨2153699, by rfl⟩ : syracuseStep 2871599 = 4307399) B4307399
theorem B2183791 : Blo 1492066 2183791 := bstep (se 1 (by rfl) ⟨1637843, by rfl⟩ : syracuseStep 2183791 = 3275687) B3275687
theorem B2520679 : Blo 1492066 2520679 := bstep (se 1 (by rfl) ⟨1890509, by rfl⟩ : syracuseStep 2520679 = 3781019) B3781019
theorem B1889983 : Blo 1492066 1889983 := bstep (se 1 (by rfl) ⟨1417487, by rfl⟩ : syracuseStep 1889983 = 2834975) B2834975
theorem B4249331 : Blo 1492066 4249331 := bstep (se 1 (by rfl) ⟨3186998, by rfl⟩ : syracuseStep 4249331 = 6373997) B6373997
theorem B2553977 : Blo 1492066 2553977 := bstep (se 2 (by rfl) ⟨957741, by rfl⟩ : syracuseStep 2553977 = 1915483) B1915483
theorem B1890535 : Blo 1492066 1890535 := bstep (se 1 (by rfl) ⟨1417901, by rfl⟩ : syracuseStep 1890535 = 2835803) B2835803
theorem B9566657 : Blo 1492066 9566657 := bstep (se 2 (by rfl) ⟨3587496, by rfl⟩ : syracuseStep 9566657 = 7174993) B7174993
theorem B9329627 : Blo 1492066 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B8625167 : Blo 1492066 8625167 := bstep (se 1 (by rfl) ⟨6468875, by rfl⟩ : syracuseStep 8625167 = 12937751) B12937751
theorem B7175263 : Blo 1492066 7175263 := bstep (se 1 (by rfl) ⟨5381447, by rfl⟩ : syracuseStep 7175263 = 10762895) B10762895
theorem B4848745 : Blo 1492066 4848745 := bstep (se 2 (by rfl) ⟨1818279, by rfl⟩ : syracuseStep 4848745 = 3636559) B3636559
theorem B4250731 : Blo 1492066 4250731 := bstep (se 1 (by rfl) ⟨3188048, by rfl⟩ : syracuseStep 4250731 = 6376097) B6376097
theorem B12106867 : Blo 1492066 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B4783379 : Blo 1492066 4783379 := bstep (se 1 (by rfl) ⟨3587534, by rfl⟩ : syracuseStep 4783379 = 7175069) B7175069
theorem B52411961 : Blo 1492066 52411961 := bstep (se 2 (by rfl) ⟨19654485, by rfl⟩ : syracuseStep 52411961 = 39308971) B39308971
theorem B6905407 : Blo 1492066 6905407 := bstep (se 1 (by rfl) ⟨5179055, by rfl⟩ : syracuseStep 6905407 = 10358111) B10358111
theorem B6381119 : Blo 1492066 6381119 := bstep (se 1 (by rfl) ⟨4785839, by rfl⟩ : syracuseStep 6381119 = 9571679) B9571679
theorem B2424503 : Blo 1492066 2424503 := bstep (se 1 (by rfl) ⟨1818377, by rfl⟩ : syracuseStep 2424503 = 3636755) B3636755
theorem B5037821 : Blo 1492066 5037821 := bstep (se 3 (by rfl) ⟨944591, by rfl⟩ : syracuseStep 5037821 = 1889183) B1889183
theorem B9560045 : Blo 1492066 9560045 := bstep (se 3 (by rfl) ⟨1792508, by rfl⟩ : syracuseStep 9560045 = 3585017) B3585017
theorem B11337893 : Blo 1492066 11337893 := bstep (se 4 (by rfl) ⟨1062927, by rfl⟩ : syracuseStep 11337893 = 2125855) B2125855
theorem B12755677 : Blo 1492066 12755677 := bstep (se 3 (by rfl) ⟨2391689, by rfl⟩ : syracuseStep 12755677 = 4783379) B4783379
theorem B57434993 : Blo 1492066 57434993 := bstep (se 2 (by rfl) ⟨21538122, by rfl⟩ : syracuseStep 57434993 = 43076245) B43076245
theorem B19137617 : Blo 1492066 19137617 := bstep (se 2 (by rfl) ⟨7176606, by rfl⟩ : syracuseStep 19137617 = 14353213) B14353213
theorem B12747887 : Blo 1492066 12747887 := bstep (se 1 (by rfl) ⟨9560915, by rfl⟩ : syracuseStep 12747887 = 19121831) B19121831
theorem B1492095 : Blo 1492066 1492095 := bstep (se 1 (by rfl) ⟨1119071, by rfl⟩ : syracuseStep 1492095 = 2238143) B2238143
theorem B1492199 : Blo 1492066 1492199 := bstep (se 1 (by rfl) ⟨1119149, by rfl⟩ : syracuseStep 1492199 = 2238299) B2238299
theorem B6464993 : Blo 1492066 6464993 := bstep (se 2 (by rfl) ⟨2424372, by rfl⟩ : syracuseStep 6464993 = 4848745) B4848745
theorem B1492455 : Blo 1492066 1492455 := bstep (se 1 (by rfl) ⟨1119341, by rfl⟩ : syracuseStep 1492455 = 2238683) B2238683
theorem B17016317 : Blo 1492066 17016317 := bstep (se 3 (by rfl) ⟨3190559, by rfl⟩ : syracuseStep 17016317 = 6381119) B6381119
theorem B1492635 : Blo 1492066 1492635 := bstep (se 1 (by rfl) ⟨1119476, by rfl⟩ : syracuseStep 1492635 = 2238953) B2238953
theorem B1492639 : Blo 1492066 1492639 := bstep (se 1 (by rfl) ⟨1119479, by rfl⟩ : syracuseStep 1492639 = 2238959) B2238959
theorem B4253465 : Blo 1492066 4253465 := bstep (se 2 (by rfl) ⟨1595049, by rfl⟩ : syracuseStep 4253465 = 3190099) B3190099
theorem B1492847 : Blo 1492066 1492847 := bstep (se 1 (by rfl) ⟨1119635, by rfl⟩ : syracuseStep 1492847 = 2239271) B2239271
theorem B1492895 : Blo 1492066 1492895 := bstep (se 1 (by rfl) ⟨1119671, by rfl⟩ : syracuseStep 1492895 = 2239343) B2239343
theorem B1493063 : Blo 1492066 1493063 := bstep (se 1 (by rfl) ⟨1119797, by rfl⟩ : syracuseStep 1493063 = 2239595) B2239595
theorem B6056041 : Blo 1492066 6056041 := bstep (se 2 (by rfl) ⟨2271015, by rfl⟩ : syracuseStep 6056041 = 4542031) B4542031
theorem B3360905 : Blo 1492066 3360905 := bstep (se 2 (by rfl) ⟨1260339, by rfl⟩ : syracuseStep 3360905 = 2520679) B2520679
theorem B1493223 : Blo 1492066 1493223 := bstep (se 1 (by rfl) ⟨1119917, by rfl⟩ : syracuseStep 1493223 = 2239835) B2239835
theorem B1493243 : Blo 1492066 1493243 := bstep (se 1 (by rfl) ⟨1119932, by rfl⟩ : syracuseStep 1493243 = 2239865) B2239865
theorem B1493247 : Blo 1492066 1493247 := bstep (se 1 (by rfl) ⟨1119935, by rfl⟩ : syracuseStep 1493247 = 2239871) B2239871
theorem B34941307 : Blo 1492066 34941307 := bstep (se 1 (by rfl) ⟨26205980, by rfl⟩ : syracuseStep 34941307 = 52411961) B52411961
theorem B1493403 : Blo 1492066 1493403 := bstep (se 1 (by rfl) ⟨1120052, by rfl⟩ : syracuseStep 1493403 = 2240105) B2240105
theorem B1616335 : Blo 1492066 1616335 := bstep (se 1 (by rfl) ⟨1212251, by rfl⟩ : syracuseStep 1616335 = 2424503) B2424503
theorem B1493663 : Blo 1492066 1493663 := bstep (se 1 (by rfl) ⟨1120247, by rfl⟩ : syracuseStep 1493663 = 2240495) B2240495
theorem B2239211 : Blo 1492066 2239211 := bstep (se 1 (by rfl) ⟨1679408, by rfl⟩ : syracuseStep 2239211 = 3358817) B3358817
theorem B1493743 : Blo 1492066 1493743 := bstep (se 1 (by rfl) ⟨1120307, by rfl⟩ : syracuseStep 1493743 = 2240615) B2240615
theorem B2239259 : Blo 1492066 2239259 := bstep (se 1 (by rfl) ⟨1679444, by rfl⟩ : syracuseStep 2239259 = 3358889) B3358889
theorem B11488031 : Blo 1492066 11488031 := bstep (se 1 (by rfl) ⟨8616023, by rfl⟩ : syracuseStep 11488031 = 17232047) B17232047
theorem B5040953 : Blo 1492066 5040953 := bstep (se 2 (by rfl) ⟨1890357, by rfl⟩ : syracuseStep 5040953 = 3780715) B3780715
theorem B1493823 : Blo 1492066 1493823 := bstep (se 1 (by rfl) ⟨1120367, by rfl⟩ : syracuseStep 1493823 = 2240735) B2240735
theorem B1493863 : Blo 1492066 1493863 := bstep (se 1 (by rfl) ⟨1120397, by rfl⟩ : syracuseStep 1493863 = 2240795) B2240795
theorem B2517959 : Blo 1492066 2517959 := bstep (se 1 (by rfl) ⟨1888469, by rfl⟩ : syracuseStep 2517959 = 3776939) B3776939
theorem B5041547 : Blo 1492066 5041547 := bstep (se 1 (by rfl) ⟨3781160, by rfl⟩ : syracuseStep 5041547 = 7562321) B7562321
theorem B2911721 : Blo 1492066 2911721 := bstep (se 2 (by rfl) ⟨1091895, by rfl⟩ : syracuseStep 2911721 = 2183791) B2183791
theorem B2240111 : Blo 1492066 2240111 := bstep (se 1 (by rfl) ⟨1680083, by rfl⟩ : syracuseStep 2240111 = 3360167) B3360167
theorem B2240219 : Blo 1492066 2240219 := bstep (se 1 (by rfl) ⟨1680164, by rfl⟩ : syracuseStep 2240219 = 3360329) B3360329
theorem B2240231 : Blo 1492066 2240231 := bstep (se 1 (by rfl) ⟨1680173, by rfl⟩ : syracuseStep 2240231 = 3360347) B3360347
theorem B5042087 : Blo 1492066 5042087 := bstep (se 1 (by rfl) ⟨3781565, by rfl⟩ : syracuseStep 5042087 = 7563131) B7563131
theorem B8073209 : Blo 1492066 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B12103777 : Blo 1492066 12103777 := bstep (se 2 (by rfl) ⟨4538916, by rfl⟩ : syracuseStep 12103777 = 9077833) B9077833
theorem B16142489 : Blo 1492066 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B2519275 : Blo 1492066 2519275 := bstep (se 1 (by rfl) ⟨1889456, by rfl⟩ : syracuseStep 2519275 = 3778913) B3778913
theorem B24211709 : Blo 1492066 24211709 := bstep (se 3 (by rfl) ⟨4539695, by rfl⟩ : syracuseStep 24211709 = 9079391) B9079391
theorem B6377771 : Blo 1492066 6377771 := bstep (se 1 (by rfl) ⟨4783328, by rfl⟩ : syracuseStep 6377771 = 9566657) B9566657
theorem B2240891 : Blo 1492066 2240891 := bstep (se 1 (by rfl) ⟨1680668, by rfl⟩ : syracuseStep 2240891 = 3361337) B3361337
theorem B18149831 : Blo 1492066 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B2240999 : Blo 1492066 2240999 := bstep (se 1 (by rfl) ⟨1680749, by rfl⟩ : syracuseStep 2240999 = 3361499) B3361499
theorem B3781151 : Blo 1492066 3781151 := bstep (se 1 (by rfl) ⟨2835863, by rfl⟩ : syracuseStep 3781151 = 5671727) B5671727
theorem B8499775 : Blo 1492066 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B2691689 : Blo 1492066 2691689 := bstep (se 2 (by rfl) ⟨1009383, by rfl⟩ : syracuseStep 2691689 = 2018767) B2018767
theorem B5378825 : Blo 1492066 5378825 := bstep (se 2 (by rfl) ⟨2017059, by rfl⟩ : syracuseStep 5378825 = 4034119) B4034119
theorem B2519977 : Blo 1492066 2519977 := bstep (se 2 (by rfl) ⟨944991, by rfl⟩ : syracuseStep 2519977 = 1889983) B1889983
theorem B3781799 : Blo 1492066 3781799 := bstep (se 1 (by rfl) ⟨2836349, by rfl⟩ : syracuseStep 3781799 = 5672699) B5672699
theorem B7664827 : Blo 1492066 7664827 := bstep (se 1 (by rfl) ⟨5748620, by rfl⟩ : syracuseStep 7664827 = 11497241) B11497241
theorem B3233191 : Blo 1492066 3233191 := bstep (se 1 (by rfl) ⟨2424893, by rfl⟩ : syracuseStep 3233191 = 4849787) B4849787
theorem B14349797 : Blo 1492066 14349797 := bstep (se 4 (by rfl) ⟨1345293, by rfl⟩ : syracuseStep 14349797 = 2690587) B2690587
theorem B8500733 : Blo 1492066 8500733 := bstep (se 3 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 8500733 = 3187775) B3187775
theorem B2520713 : Blo 1492066 2520713 := bstep (se 2 (by rfl) ⟨945267, by rfl⟩ : syracuseStep 2520713 = 1890535) B1890535
theorem B12113711 : Blo 1492066 12113711 := bstep (se 1 (by rfl) ⟨9085283, by rfl⟩ : syracuseStep 12113711 = 18170567) B18170567
theorem B1595263 : Blo 1492066 1595263 := bstep (se 1 (by rfl) ⟨1196447, by rfl⟩ : syracuseStep 1595263 = 2392895) B2392895
theorem B7657597 : Blo 1492066 7657597 := bstep (se 3 (by rfl) ⟨1435799, by rfl⟩ : syracuseStep 7657597 = 2871599) B2871599
theorem B1890479 : Blo 1492066 1890479 := bstep (se 1 (by rfl) ⟨1417859, by rfl⟩ : syracuseStep 1890479 = 2835719) B2835719
theorem B2832887 : Blo 1492066 2832887 := bstep (se 1 (by rfl) ⟨2124665, by rfl⟩ : syracuseStep 2832887 = 4249331) B4249331
theorem B4250207 : Blo 1492066 4250207 := bstep (se 1 (by rfl) ⟨3187655, by rfl⟩ : syracuseStep 4250207 = 6375311) B6375311
theorem B5036687 : Blo 1492066 5036687 := bstep (se 1 (by rfl) ⟨3777515, by rfl⟩ : syracuseStep 5036687 = 7555031) B7555031
theorem B5036795 : Blo 1492066 5036795 := bstep (se 1 (by rfl) ⟨3777596, by rfl⟩ : syracuseStep 5036795 = 7555193) B7555193
theorem B1702651 : Blo 1492066 1702651 := bstep (se 1 (by rfl) ⟨1276988, by rfl⟩ : syracuseStep 1702651 = 2553977) B2553977
theorem B9567017 : Blo 1492066 9567017 := bstep (se 2 (by rfl) ⟨3587631, by rfl⟩ : syracuseStep 9567017 = 7175263) B7175263
theorem B5667641 : Blo 1492066 5667641 := bstep (se 2 (by rfl) ⟨2125365, by rfl⟩ : syracuseStep 5667641 = 4250731) B4250731
theorem B5037011 : Blo 1492066 5037011 := bstep (se 1 (by rfl) ⟨3777758, by rfl⟩ : syracuseStep 5037011 = 7555517) B7555517
theorem B16997363 : Blo 1492066 16997363 := bstep (se 1 (by rfl) ⟨12748022, by rfl⟩ : syracuseStep 16997363 = 25496045) B25496045
theorem B5037119 : Blo 1492066 5037119 := bstep (se 1 (by rfl) ⟨3777839, by rfl⟩ : syracuseStep 5037119 = 7555679) B7555679
theorem B5750111 : Blo 1492066 5750111 := bstep (se 1 (by rfl) ⟨4312583, by rfl⟩ : syracuseStep 5750111 = 8625167) B8625167
theorem B9207209 : Blo 1492066 9207209 := bstep (se 2 (by rfl) ⟨3452703, by rfl⟩ : syracuseStep 9207209 = 6905407) B6905407
theorem B2834041 : Blo 1492066 2834041 := bstep (se 2 (by rfl) ⟨1062765, by rfl⟩ : syracuseStep 2834041 = 2125531) B2125531
theorem B3358547 : Blo 1492066 3358547 := bstep (se 1 (by rfl) ⟨2518910, by rfl⟩ : syracuseStep 3358547 = 5037821) B5037821
theorem B5037929 : Blo 1492066 5037929 := bstep (se 2 (by rfl) ⟨1889223, by rfl⟩ : syracuseStep 5037929 = 3778447) B3778447
theorem B24879005 : Blo 1492066 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B6373363 : Blo 1492066 6373363 := bstep (se 1 (by rfl) ⟨4780022, by rfl⟩ : syracuseStep 6373363 = 9560045) B9560045
theorem B16138369 : Blo 1492066 16138369 := bstep (se 2 (by rfl) ⟨6051888, by rfl⟩ : syracuseStep 16138369 = 12103777) B12103777
theorem B4251847 : Blo 1492066 4251847 := bstep (se 1 (by rfl) ⟨3188885, by rfl⟩ : syracuseStep 4251847 = 6377771) B6377771
theorem B12099887 : Blo 1492066 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B3359033 : Blo 1492066 3359033 := bstep (se 2 (by rfl) ⟨1259637, by rfl⟩ : syracuseStep 3359033 = 2519275) B2519275
theorem B46588409 : Blo 1492066 46588409 := bstep (se 2 (by rfl) ⟨17470653, by rfl⟩ : syracuseStep 46588409 = 34941307) B34941307
theorem B38289995 : Blo 1492066 38289995 := bstep (se 1 (by rfl) ⟨28717496, by rfl⟩ : syracuseStep 38289995 = 57434993) B57434993
theorem B17007569 : Blo 1492066 17007569 := bstep (se 2 (by rfl) ⟨6377838, by rfl⟩ : syracuseStep 17007569 = 12755677) B12755677
theorem B2270201 : Blo 1492066 2270201 := bstep (se 2 (by rfl) ⟨851325, by rfl⟩ : syracuseStep 2270201 = 1702651) B1702651
theorem B1680475 : Blo 1492066 1680475 := bstep (se 1 (by rfl) ⟨1260356, by rfl⟩ : syracuseStep 1680475 = 2520713) B2520713
theorem B24552557 : Blo 1492066 24552557 := bstep (se 3 (by rfl) ⟨4603604, by rfl⟩ : syracuseStep 24552557 = 9207209) B9207209
theorem B2835643 : Blo 1492066 2835643 := bstep (se 1 (by rfl) ⟨2126732, by rfl⟩ : syracuseStep 2835643 = 4253465) B4253465
theorem B3359969 : Blo 1492066 3359969 := bstep (se 2 (by rfl) ⟨1259988, by rfl⟩ : syracuseStep 3359969 = 2519977) B2519977
theorem B7177837 : Blo 1492066 7177837 := bstep (se 3 (by rfl) ⟨1345844, by rfl⟩ : syracuseStep 7177837 = 2691689) B2691689
theorem B1492807 : Blo 1492066 1492807 := bstep (se 1 (by rfl) ⟨1119605, by rfl⟩ : syracuseStep 1492807 = 2239211) B2239211
theorem B1492839 : Blo 1492066 1492839 := bstep (se 1 (by rfl) ⟨1119629, by rfl⟩ : syracuseStep 1492839 = 2239259) B2239259
theorem B3778427 : Blo 1492066 3778427 := bstep (se 1 (by rfl) ⟨2833820, by rfl⟩ : syracuseStep 3778427 = 5667641) B5667641
theorem B3360635 : Blo 1492066 3360635 := bstep (se 1 (by rfl) ⟨2520476, by rfl⟩ : syracuseStep 3360635 = 5040953) B5040953
theorem B4310921 : Blo 1492066 4310921 := bstep (se 2 (by rfl) ⟨1616595, by rfl⟩ : syracuseStep 4310921 = 3233191) B3233191
theorem B11331575 : Blo 1492066 11331575 := bstep (se 1 (by rfl) ⟨8498681, by rfl⟩ : syracuseStep 11331575 = 16997363) B16997363
theorem B3778721 : Blo 1492066 3778721 := bstep (se 2 (by rfl) ⟨1417020, by rfl⟩ : syracuseStep 3778721 = 2834041) B2834041
theorem B3361031 : Blo 1492066 3361031 := bstep (se 1 (by rfl) ⟨2520773, by rfl⟩ : syracuseStep 3361031 = 5041547) B5041547
theorem B1493407 : Blo 1492066 1493407 := bstep (se 1 (by rfl) ⟨1120055, by rfl⟩ : syracuseStep 1493407 = 2240111) B2240111
theorem B8620453 : Blo 1492066 8620453 := bstep (se 4 (by rfl) ⟨808167, by rfl⟩ : syracuseStep 8620453 = 1616335) B1616335
theorem B1493479 : Blo 1492066 1493479 := bstep (se 1 (by rfl) ⟨1120109, by rfl⟩ : syracuseStep 1493479 = 2240219) B2240219
theorem B1493487 : Blo 1492066 1493487 := bstep (se 1 (by rfl) ⟨1120115, by rfl⟩ : syracuseStep 1493487 = 2240231) B2240231
theorem B2239031 : Blo 1492066 2239031 := bstep (se 1 (by rfl) ⟨1679273, by rfl⟩ : syracuseStep 2239031 = 3358547) B3358547
theorem B3361391 : Blo 1492066 3361391 := bstep (se 1 (by rfl) ⟨2521043, by rfl⟩ : syracuseStep 3361391 = 5042087) B5042087
theorem B8497817 : Blo 1492066 8497817 := bstep (se 2 (by rfl) ⟨3186681, by rfl⟩ : syracuseStep 8497817 = 6373363) B6373363
theorem B16141139 : Blo 1492066 16141139 := bstep (se 1 (by rfl) ⟨12105854, by rfl⟩ : syracuseStep 16141139 = 24211709) B24211709
theorem B1493927 : Blo 1492066 1493927 := bstep (se 1 (by rfl) ⟨1120445, by rfl⟩ : syracuseStep 1493927 = 2240891) B2240891
theorem B1493999 : Blo 1492066 1493999 := bstep (se 1 (by rfl) ⟨1120499, by rfl⟩ : syracuseStep 1493999 = 2240999) B2240999
theorem B5041277 : Blo 1492066 5041277 := bstep (se 3 (by rfl) ⟨945239, by rfl⟩ : syracuseStep 5041277 = 1890479) B1890479
theorem B40840517 : Blo 1492066 40840517 := bstep (se 4 (by rfl) ⟨3828798, by rfl⟩ : syracuseStep 40840517 = 7657597) B7657597
theorem B12758411 : Blo 1492066 12758411 := bstep (se 1 (by rfl) ⟨9568808, by rfl⟩ : syracuseStep 12758411 = 19137617) B19137617
theorem B8498591 : Blo 1492066 8498591 := bstep (se 1 (by rfl) ⟨6373943, by rfl⟩ : syracuseStep 8498591 = 12747887) B12747887
theorem B11333033 : Blo 1492066 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B17239981 : Blo 1492066 17239981 := bstep (se 3 (by rfl) ⟨3232496, by rfl⟩ : syracuseStep 17239981 = 6464993) B6464993
theorem B2240603 : Blo 1492066 2240603 := bstep (se 1 (by rfl) ⟨1680452, by rfl⟩ : syracuseStep 2240603 = 3360905) B3360905
theorem B5382139 : Blo 1492066 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B10219769 : Blo 1492066 10219769 := bstep (se 2 (by rfl) ⟨3832413, by rfl⟩ : syracuseStep 10219769 = 7664827) B7664827
theorem B1888591 : Blo 1492066 1888591 := bstep (se 1 (by rfl) ⟨1416443, by rfl⟩ : syracuseStep 1888591 = 2832887) B2832887
theorem B6378011 : Blo 1492066 6378011 := bstep (se 1 (by rfl) ⟨4783508, by rfl⟩ : syracuseStep 6378011 = 9567017) B9567017
theorem B2127017 : Blo 1492066 2127017 := bstep (se 2 (by rfl) ⟨797631, by rfl⟩ : syracuseStep 2127017 = 1595263) B1595263
theorem B16586003 : Blo 1492066 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B10761659 : Blo 1492066 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B7558595 : Blo 1492066 7558595 := bstep (se 1 (by rfl) ⟨5668946, by rfl⟩ : syracuseStep 7558595 = 11337893) B11337893
theorem B8074721 : Blo 1492066 8074721 := bstep (se 2 (by rfl) ⟨3028020, by rfl⟩ : syracuseStep 8074721 = 6056041) B6056041
theorem B2520767 : Blo 1492066 2520767 := bstep (se 1 (by rfl) ⟨1890575, by rfl⟩ : syracuseStep 2520767 = 3781151) B3781151
theorem B3585883 : Blo 1492066 3585883 := bstep (se 1 (by rfl) ⟨2689412, by rfl⟩ : syracuseStep 3585883 = 5378825) B5378825
theorem B2521199 : Blo 1492066 2521199 := bstep (se 1 (by rfl) ⟨1890899, by rfl⟩ : syracuseStep 2521199 = 3781799) B3781799
theorem B9566531 : Blo 1492066 9566531 := bstep (se 1 (by rfl) ⟨7174898, by rfl⟩ : syracuseStep 9566531 = 14349797) B14349797
theorem B5667155 : Blo 1492066 5667155 := bstep (se 1 (by rfl) ⟨4250366, by rfl⟩ : syracuseStep 5667155 = 8500733) B8500733
theorem B11344211 : Blo 1492066 11344211 := bstep (se 1 (by rfl) ⟨8508158, by rfl⟩ : syracuseStep 11344211 = 17016317) B17016317
theorem B8075807 : Blo 1492066 8075807 := bstep (se 1 (by rfl) ⟨6056855, by rfl⟩ : syracuseStep 8075807 = 12113711) B12113711
theorem B7764589 : Blo 1492066 7764589 := bstep (se 3 (by rfl) ⟨1455860, by rfl⟩ : syracuseStep 7764589 = 2911721) B2911721
theorem B2833471 : Blo 1492066 2833471 := bstep (se 1 (by rfl) ⟨2125103, by rfl⟩ : syracuseStep 2833471 = 4250207) B4250207
theorem B3357791 : Blo 1492066 3357791 := bstep (se 1 (by rfl) ⟨2518343, by rfl⟩ : syracuseStep 3357791 = 5036687) B5036687
theorem B3357863 : Blo 1492066 3357863 := bstep (se 1 (by rfl) ⟨2518397, by rfl⟩ : syracuseStep 3357863 = 5036795) B5036795
theorem B7658687 : Blo 1492066 7658687 := bstep (se 1 (by rfl) ⟨5744015, by rfl⟩ : syracuseStep 7658687 = 11488031) B11488031
theorem B1678639 : Blo 1492066 1678639 := bstep (se 1 (by rfl) ⟨1258979, by rfl⟩ : syracuseStep 1678639 = 2517959) B2517959
theorem B3358007 : Blo 1492066 3358007 := bstep (se 1 (by rfl) ⟨2518505, by rfl⟩ : syracuseStep 3358007 = 5037011) B5037011
theorem B3358079 : Blo 1492066 3358079 := bstep (se 1 (by rfl) ⟨2518559, by rfl⟩ : syracuseStep 3358079 = 5037119) B5037119
theorem B3833407 : Blo 1492066 3833407 := bstep (se 1 (by rfl) ⟨2875055, by rfl⟩ : syracuseStep 3833407 = 5750111) B5750111
theorem B3358619 : Blo 1492066 3358619 := bstep (se 1 (by rfl) ⟨2518964, by rfl⟩ : syracuseStep 3358619 = 5037929) B5037929
theorem B5669129 : Blo 1492066 5669129 := bstep (se 2 (by rfl) ⟨2125923, by rfl⟩ : syracuseStep 5669129 = 4251847) B4251847
theorem B4252007 : Blo 1492066 4252007 := bstep (se 1 (by rfl) ⟨3189005, by rfl⟩ : syracuseStep 4252007 = 6378011) B6378011
theorem B25526663 : Blo 1492066 25526663 := bstep (se 1 (by rfl) ⟨19144997, by rfl⟩ : syracuseStep 25526663 = 38289995) B38289995
theorem B11493937 : Blo 1492066 11493937 := bstep (se 2 (by rfl) ⟨4310226, by rfl⟩ : syracuseStep 11493937 = 8620453) B8620453
theorem B11338379 : Blo 1492066 11338379 := bstep (se 1 (by rfl) ⟨8503784, by rfl⟩ : syracuseStep 11338379 = 17007569) B17007569
theorem B44229341 : Blo 1492066 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B16368371 : Blo 1492066 16368371 := bstep (se 1 (by rfl) ⟨12276278, by rfl⟩ : syracuseStep 16368371 = 24552557) B24552557
theorem B5039063 : Blo 1492066 5039063 := bstep (se 1 (by rfl) ⟨3779297, by rfl⟩ : syracuseStep 5039063 = 7558595) B7558595
theorem B5383147 : Blo 1492066 5383147 := bstep (se 1 (by rfl) ⟨4037360, by rfl⟩ : syracuseStep 5383147 = 8074721) B8074721
theorem B1680511 : Blo 1492066 1680511 := bstep (se 1 (by rfl) ⟨1260383, by rfl⟩ : syracuseStep 1680511 = 2520767) B2520767
theorem B7554383 : Blo 1492066 7554383 := bstep (se 1 (by rfl) ⟨5665787, by rfl⟩ : syracuseStep 7554383 = 11331575) B11331575
theorem B1680799 : Blo 1492066 1680799 := bstep (se 1 (by rfl) ⟨1260599, by rfl⟩ : syracuseStep 1680799 = 2521199) B2521199
theorem B3777961 : Blo 1492066 3777961 := bstep (se 2 (by rfl) ⟨1416735, by rfl⟩ : syracuseStep 3777961 = 2833471) B2833471
theorem B3778103 : Blo 1492066 3778103 := bstep (se 1 (by rfl) ⟨2833577, by rfl⟩ : syracuseStep 3778103 = 5667155) B5667155
theorem B7562807 : Blo 1492066 7562807 := bstep (se 1 (by rfl) ⟨5672105, by rfl⟩ : syracuseStep 7562807 = 11344211) B11344211
theorem B5383871 : Blo 1492066 5383871 := bstep (se 1 (by rfl) ⟨4037903, by rfl⟩ : syracuseStep 5383871 = 8075807) B8075807
theorem B1492687 : Blo 1492066 1492687 := bstep (se 1 (by rfl) ⟨1119515, by rfl⟩ : syracuseStep 1492687 = 2239031) B2239031
theorem B2238185 : Blo 1492066 2238185 := bstep (se 2 (by rfl) ⟨839319, by rfl⟩ : syracuseStep 2238185 = 1678639) B1678639
theorem B2238527 : Blo 1492066 2238527 := bstep (se 1 (by rfl) ⟨1678895, by rfl⟩ : syracuseStep 2238527 = 3357791) B3357791
theorem B3360851 : Blo 1492066 3360851 := bstep (se 1 (by rfl) ⟨2520638, by rfl⟩ : syracuseStep 3360851 = 5041277) B5041277
theorem B2238575 : Blo 1492066 2238575 := bstep (se 1 (by rfl) ⟨1678931, by rfl⟩ : syracuseStep 2238575 = 3357863) B3357863
theorem B5105791 : Blo 1492066 5105791 := bstep (se 1 (by rfl) ⟨3829343, by rfl⟩ : syracuseStep 5105791 = 7658687) B7658687
theorem B9570449 : Blo 1492066 9570449 := bstep (se 2 (by rfl) ⟨3588918, by rfl⟩ : syracuseStep 9570449 = 7177837) B7177837
theorem B2238671 : Blo 1492066 2238671 := bstep (se 1 (by rfl) ⟨1679003, by rfl⟩ : syracuseStep 2238671 = 3358007) B3358007
theorem B2238719 : Blo 1492066 2238719 := bstep (se 1 (by rfl) ⟨1679039, by rfl⟩ : syracuseStep 2238719 = 3358079) B3358079
theorem B8505607 : Blo 1492066 8505607 := bstep (se 1 (by rfl) ⟨6379205, by rfl⟩ : syracuseStep 8505607 = 12758411) B12758411
theorem B7555355 : Blo 1492066 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B11495789 : Blo 1492066 11495789 := bstep (se 3 (by rfl) ⟨2155460, by rfl⟩ : syracuseStep 11495789 = 4310921) B4310921
theorem B2239079 : Blo 1492066 2239079 := bstep (se 1 (by rfl) ⟨1679309, by rfl⟩ : syracuseStep 2239079 = 3358619) B3358619
theorem B1493735 : Blo 1492066 1493735 := bstep (se 1 (by rfl) ⟨1120301, by rfl⟩ : syracuseStep 1493735 = 2240603) B2240603
theorem B2239355 : Blo 1492066 2239355 := bstep (se 1 (by rfl) ⟨1679516, by rfl⟩ : syracuseStep 2239355 = 3359033) B3359033
theorem B7176185 : Blo 1492066 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B31058939 : Blo 1492066 31058939 := bstep (se 1 (by rfl) ⟨23294204, by rfl⟩ : syracuseStep 31058939 = 46588409) B46588409
theorem B2518121 : Blo 1492066 2518121 := bstep (se 2 (by rfl) ⟨944295, by rfl⟩ : syracuseStep 2518121 = 1888591) B1888591
theorem B5672045 : Blo 1492066 5672045 := bstep (se 3 (by rfl) ⟨1063508, by rfl⟩ : syracuseStep 5672045 = 2127017) B2127017
theorem B2239979 : Blo 1492066 2239979 := bstep (se 1 (by rfl) ⟨1679984, by rfl⟩ : syracuseStep 2239979 = 3359969) B3359969
theorem B2518951 : Blo 1492066 2518951 := bstep (se 1 (by rfl) ⟨1889213, by rfl⟩ : syracuseStep 2518951 = 3778427) B3778427
theorem B2240423 : Blo 1492066 2240423 := bstep (se 1 (by rfl) ⟨1680317, by rfl⟩ : syracuseStep 2240423 = 3360635) B3360635
theorem B2519147 : Blo 1492066 2519147 := bstep (se 1 (by rfl) ⟨1889360, by rfl⟩ : syracuseStep 2519147 = 3778721) B3778721
theorem B2240633 : Blo 1492066 2240633 := bstep (se 2 (by rfl) ⟨840237, by rfl⟩ : syracuseStep 2240633 = 1680475) B1680475
theorem B2240687 : Blo 1492066 2240687 := bstep (se 1 (by rfl) ⟨1680515, by rfl⟩ : syracuseStep 2240687 = 3361031) B3361031
theorem B6377687 : Blo 1492066 6377687 := bstep (se 1 (by rfl) ⟨4783265, by rfl⟩ : syracuseStep 6377687 = 9566531) B9566531
theorem B3780857 : Blo 1492066 3780857 := bstep (se 2 (by rfl) ⟨1417821, by rfl⟩ : syracuseStep 3780857 = 2835643) B2835643
theorem B2240927 : Blo 1492066 2240927 := bstep (se 1 (by rfl) ⟨1680695, by rfl⟩ : syracuseStep 2240927 = 3361391) B3361391
theorem B5665211 : Blo 1492066 5665211 := bstep (se 1 (by rfl) ⟨4248908, by rfl⟩ : syracuseStep 5665211 = 8497817) B8497817
theorem B10760759 : Blo 1492066 10760759 := bstep (se 1 (by rfl) ⟨8070569, by rfl⟩ : syracuseStep 10760759 = 16141139) B16141139
theorem B27227011 : Blo 1492066 27227011 := bstep (se 1 (by rfl) ⟨20420258, by rfl⟩ : syracuseStep 27227011 = 40840517) B40840517
theorem B5665727 : Blo 1492066 5665727 := bstep (se 1 (by rfl) ⟨4249295, by rfl⟩ : syracuseStep 5665727 = 8498591) B8498591
theorem B4781177 : Blo 1492066 4781177 := bstep (se 2 (by rfl) ⟨1792941, by rfl⟩ : syracuseStep 4781177 = 3585883) B3585883
theorem B6813179 : Blo 1492066 6813179 := bstep (se 1 (by rfl) ⟨5109884, by rfl⟩ : syracuseStep 6813179 = 10219769) B10219769
theorem B21517825 : Blo 1492066 21517825 := bstep (se 2 (by rfl) ⟨8069184, by rfl⟩ : syracuseStep 21517825 = 16138369) B16138369
theorem B8066591 : Blo 1492066 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B10352785 : Blo 1492066 10352785 := bstep (se 2 (by rfl) ⟨3882294, by rfl⟩ : syracuseStep 10352785 = 7764589) B7764589
theorem B7174439 : Blo 1492066 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B5111209 : Blo 1492066 5111209 := bstep (se 2 (by rfl) ⟨1916703, by rfl⟩ : syracuseStep 5111209 = 3833407) B3833407
theorem B22986641 : Blo 1492066 22986641 := bstep (se 2 (by rfl) ⟨8619990, by rfl⟩ : syracuseStep 22986641 = 17239981) B17239981
theorem B6053869 : Blo 1492066 6053869 := bstep (se 3 (by rfl) ⟨1135100, by rfl⟩ : syracuseStep 6053869 = 2270201) B2270201
theorem B1679431 : Blo 1492066 1679431 := bstep (se 1 (by rfl) ⟨1259573, by rfl⟩ : syracuseStep 1679431 = 2519147) B2519147
theorem B4251791 : Blo 1492066 4251791 := bstep (se 1 (by rfl) ⟨3188843, by rfl⟩ : syracuseStep 4251791 = 6377687) B6377687
theorem B6807721 : Blo 1492066 6807721 := bstep (se 2 (by rfl) ⟨2552895, by rfl⟩ : syracuseStep 6807721 = 5105791) B5105791
theorem B13803713 : Blo 1492066 13803713 := bstep (se 2 (by rfl) ⟨5176392, by rfl⟩ : syracuseStep 13803713 = 10352785) B10352785
theorem B2834671 : Blo 1492066 2834671 := bstep (se 1 (by rfl) ⟨2126003, by rfl⟩ : syracuseStep 2834671 = 4252007) B4252007
theorem B3776807 : Blo 1492066 3776807 := bstep (se 1 (by rfl) ⟨2832605, by rfl⟩ : syracuseStep 3776807 = 5665211) B5665211
theorem B10912247 : Blo 1492066 10912247 := bstep (se 1 (by rfl) ⟨8184185, by rfl⟩ : syracuseStep 10912247 = 16368371) B16368371
theorem B3777151 : Blo 1492066 3777151 := bstep (se 1 (by rfl) ⟨2832863, by rfl⟩ : syracuseStep 3777151 = 5665727) B5665727
theorem B3359375 : Blo 1492066 3359375 := bstep (se 1 (by rfl) ⟨2519531, by rfl⟩ : syracuseStep 3359375 = 5039063) B5039063
theorem B3187451 : Blo 1492066 3187451 := bstep (se 1 (by rfl) ⟨2390588, by rfl⟩ : syracuseStep 3187451 = 4781177) B4781177
theorem B3589247 : Blo 1492066 3589247 := bstep (se 1 (by rfl) ⟨2691935, by rfl⟩ : syracuseStep 3589247 = 5383871) B5383871
theorem B1492123 : Blo 1492066 1492123 := bstep (se 1 (by rfl) ⟨1119092, by rfl⟩ : syracuseStep 1492123 = 2238185) B2238185
theorem B7177529 : Blo 1492066 7177529 := bstep (se 2 (by rfl) ⟨2691573, by rfl⟩ : syracuseStep 7177529 = 5383147) B5383147
theorem B1492351 : Blo 1492066 1492351 := bstep (se 1 (by rfl) ⟨1119263, by rfl⟩ : syracuseStep 1492351 = 2238527) B2238527
theorem B1492383 : Blo 1492066 1492383 := bstep (se 1 (by rfl) ⟨1119287, by rfl⟩ : syracuseStep 1492383 = 2238575) B2238575
theorem B1492447 : Blo 1492066 1492447 := bstep (se 1 (by rfl) ⟨1119335, by rfl⟩ : syracuseStep 1492447 = 2238671) B2238671
theorem B1492479 : Blo 1492066 1492479 := bstep (se 1 (by rfl) ⟨1119359, by rfl⟩ : syracuseStep 1492479 = 2238719) B2238719
theorem B1492719 : Blo 1492066 1492719 := bstep (se 1 (by rfl) ⟨1119539, by rfl⟩ : syracuseStep 1492719 = 2239079) B2239079
theorem B1492903 : Blo 1492066 1492903 := bstep (se 1 (by rfl) ⟨1119677, by rfl⟩ : syracuseStep 1492903 = 2239355) B2239355
theorem B4784123 : Blo 1492066 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B28690433 : Blo 1492066 28690433 := bstep (se 2 (by rfl) ⟨10758912, by rfl⟩ : syracuseStep 28690433 = 21517825) B21517825
theorem B1493319 : Blo 1492066 1493319 := bstep (se 1 (by rfl) ⟨1119989, by rfl⟩ : syracuseStep 1493319 = 2239979) B2239979
theorem B1493615 : Blo 1492066 1493615 := bstep (se 1 (by rfl) ⟨1120211, by rfl⟩ : syracuseStep 1493615 = 2240423) B2240423
theorem B8071825 : Blo 1492066 8071825 := bstep (se 2 (by rfl) ⟨3026934, by rfl⟩ : syracuseStep 8071825 = 6053869) B6053869
theorem B1493755 : Blo 1492066 1493755 := bstep (se 1 (by rfl) ⟨1120316, by rfl⟩ : syracuseStep 1493755 = 2240633) B2240633
theorem B1493791 : Blo 1492066 1493791 := bstep (se 1 (by rfl) ⟨1120343, by rfl⟩ : syracuseStep 1493791 = 2240687) B2240687
theorem B3779419 : Blo 1492066 3779419 := bstep (se 1 (by rfl) ⟨2834564, by rfl⟩ : syracuseStep 3779419 = 5669129) B5669129
theorem B17017775 : Blo 1492066 17017775 := bstep (se 1 (by rfl) ⟨12763331, by rfl⟩ : syracuseStep 17017775 = 25526663) B25526663
theorem B1493951 : Blo 1492066 1493951 := bstep (se 1 (by rfl) ⟨1120463, by rfl⟩ : syracuseStep 1493951 = 2240927) B2240927
theorem B11340809 : Blo 1492066 11340809 := bstep (se 2 (by rfl) ⟨4252803, by rfl⟩ : syracuseStep 11340809 = 8505607) B8505607
theorem B29486227 : Blo 1492066 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B4542119 : Blo 1492066 4542119 := bstep (se 1 (by rfl) ⟨3406589, by rfl⟩ : syracuseStep 4542119 = 6813179) B6813179
theorem B5377727 : Blo 1492066 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B2518735 : Blo 1492066 2518735 := bstep (se 1 (by rfl) ⟨1889051, by rfl⟩ : syracuseStep 2518735 = 3778103) B3778103
theorem B5041871 : Blo 1492066 5041871 := bstep (se 1 (by rfl) ⟨3781403, by rfl⟩ : syracuseStep 5041871 = 7562807) B7562807
theorem B36302681 : Blo 1492066 36302681 := bstep (se 2 (by rfl) ⟨13613505, by rfl⟩ : syracuseStep 36302681 = 27227011) B27227011
theorem B2240567 : Blo 1492066 2240567 := bstep (se 1 (by rfl) ⟨1680425, by rfl⟩ : syracuseStep 2240567 = 3360851) B3360851
theorem B2240681 : Blo 1492066 2240681 := bstep (se 2 (by rfl) ⟨840255, by rfl⟩ : syracuseStep 2240681 = 1680511) B1680511
theorem B7663859 : Blo 1492066 7663859 := bstep (se 1 (by rfl) ⟨5747894, by rfl⟩ : syracuseStep 7663859 = 11495789) B11495789
theorem B2241065 : Blo 1492066 2241065 := bstep (se 2 (by rfl) ⟨840399, by rfl⟩ : syracuseStep 2241065 = 1680799) B1680799
theorem B20705959 : Blo 1492066 20705959 := bstep (se 1 (by rfl) ⟨15529469, by rfl⟩ : syracuseStep 20705959 = 31058939) B31058939
theorem B3781363 : Blo 1492066 3781363 := bstep (se 1 (by rfl) ⟨2836022, by rfl⟩ : syracuseStep 3781363 = 5672045) B5672045
theorem B15324427 : Blo 1492066 15324427 := bstep (se 1 (by rfl) ⟨11493320, by rfl⟩ : syracuseStep 15324427 = 22986641) B22986641
theorem B2520571 : Blo 1492066 2520571 := bstep (se 1 (by rfl) ⟨1890428, by rfl⟩ : syracuseStep 2520571 = 3780857) B3780857
theorem B7173839 : Blo 1492066 7173839 := bstep (se 1 (by rfl) ⟨5380379, by rfl⟩ : syracuseStep 7173839 = 10760759) B10760759
theorem B7558919 : Blo 1492066 7558919 := bstep (se 1 (by rfl) ⟨5669189, by rfl⟩ : syracuseStep 7558919 = 11338379) B11338379
theorem B15325249 : Blo 1492066 15325249 := bstep (se 2 (by rfl) ⟨5746968, by rfl⟩ : syracuseStep 15325249 = 11493937) B11493937
theorem B5036255 : Blo 1492066 5036255 := bstep (se 1 (by rfl) ⟨3777191, by rfl⟩ : syracuseStep 5036255 = 7554383) B7554383
theorem B6380299 : Blo 1492066 6380299 := bstep (se 1 (by rfl) ⟨4785224, by rfl⟩ : syracuseStep 6380299 = 9570449) B9570449
theorem B5036903 : Blo 1492066 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B4782959 : Blo 1492066 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B5037281 : Blo 1492066 5037281 := bstep (se 2 (by rfl) ⟨1888980, by rfl⟩ : syracuseStep 5037281 = 3777961) B3777961
theorem B6814945 : Blo 1492066 6814945 := bstep (se 2 (by rfl) ⟨2555604, by rfl⟩ : syracuseStep 6814945 = 5111209) B5111209
theorem B1678747 : Blo 1492066 1678747 := bstep (se 1 (by rfl) ⟨1259060, by rfl⟩ : syracuseStep 1678747 = 2518121) B2518121
theorem B3358601 : Blo 1492066 3358601 := bstep (se 2 (by rfl) ⟨1259475, by rfl⟩ : syracuseStep 3358601 = 2518951) B2518951
theorem B2834527 : Blo 1492066 2834527 := bstep (se 1 (by rfl) ⟨2125895, by rfl⟩ : syracuseStep 2834527 = 4251791) B4251791
theorem B9076961 : Blo 1492066 9076961 := bstep (se 2 (by rfl) ⟨3403860, by rfl⟩ : syracuseStep 9076961 = 6807721) B6807721
theorem B7274831 : Blo 1492066 7274831 := bstep (se 1 (by rfl) ⟨5456123, by rfl⟩ : syracuseStep 7274831 = 10912247) B10912247
theorem B2392831 : Blo 1492066 2392831 := bstep (se 1 (by rfl) ⟨1794623, by rfl⟩ : syracuseStep 2392831 = 3589247) B3589247
theorem B27607945 : Blo 1492066 27607945 := bstep (se 2 (by rfl) ⟨10352979, by rfl⟩ : syracuseStep 27607945 = 20705959) B20705959
theorem B5039225 : Blo 1492066 5039225 := bstep (se 2 (by rfl) ⟨1889709, by rfl⟩ : syracuseStep 5039225 = 3779419) B3779419
theorem B5039279 : Blo 1492066 5039279 := bstep (se 1 (by rfl) ⟨3779459, by rfl⟩ : syracuseStep 5039279 = 7558919) B7558919
theorem B39314969 : Blo 1492066 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B9086593 : Blo 1492066 9086593 := bstep (se 2 (by rfl) ⟨3407472, by rfl⟩ : syracuseStep 9086593 = 6814945) B6814945
theorem B20432569 : Blo 1492066 20432569 := bstep (se 2 (by rfl) ⟨7662213, by rfl⟩ : syracuseStep 20432569 = 15324427) B15324427
theorem B2238329 : Blo 1492066 2238329 := bstep (se 2 (by rfl) ⟨839373, by rfl⟩ : syracuseStep 2238329 = 1678747) B1678747
theorem B3188639 : Blo 1492066 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B3360761 : Blo 1492066 3360761 := bstep (se 2 (by rfl) ⟨1260285, by rfl⟩ : syracuseStep 3360761 = 2520571) B2520571
theorem B3361247 : Blo 1492066 3361247 := bstep (se 1 (by rfl) ⟨2520935, by rfl⟩ : syracuseStep 3361247 = 5041871) B5041871
theorem B24201787 : Blo 1492066 24201787 := bstep (se 1 (by rfl) ⟨18151340, by rfl⟩ : syracuseStep 24201787 = 36302681) B36302681
theorem B2239067 : Blo 1492066 2239067 := bstep (se 1 (by rfl) ⟨1679300, by rfl⟩ : syracuseStep 2239067 = 3358601) B3358601
theorem B12757661 : Blo 1492066 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B1493711 : Blo 1492066 1493711 := bstep (se 1 (by rfl) ⟨1120283, by rfl⟩ : syracuseStep 1493711 = 2240567) B2240567
theorem B20433665 : Blo 1492066 20433665 := bstep (se 2 (by rfl) ⟨7662624, by rfl⟩ : syracuseStep 20433665 = 15325249) B15325249
theorem B2239241 : Blo 1492066 2239241 := bstep (se 2 (by rfl) ⟨839715, by rfl⟩ : syracuseStep 2239241 = 1679431) B1679431
theorem B1493787 : Blo 1492066 1493787 := bstep (se 1 (by rfl) ⟨1120340, by rfl⟩ : syracuseStep 1493787 = 2240681) B2240681
theorem B9202475 : Blo 1492066 9202475 := bstep (se 1 (by rfl) ⟨6901856, by rfl⟩ : syracuseStep 9202475 = 13803713) B13803713
theorem B2517871 : Blo 1492066 2517871 := bstep (se 1 (by rfl) ⟨1888403, by rfl⟩ : syracuseStep 2517871 = 3776807) B3776807
theorem B3779561 : Blo 1492066 3779561 := bstep (se 2 (by rfl) ⟨1417335, by rfl⟩ : syracuseStep 3779561 = 2834671) B2834671
theorem B1494043 : Blo 1492066 1494043 := bstep (se 1 (by rfl) ⟨1120532, by rfl⟩ : syracuseStep 1494043 = 2241065) B2241065
theorem B2239583 : Blo 1492066 2239583 := bstep (se 1 (by rfl) ⟨1679687, by rfl⟩ : syracuseStep 2239583 = 3359375) B3359375
theorem B2124967 : Blo 1492066 2124967 := bstep (se 1 (by rfl) ⟨1593725, by rfl⟩ : syracuseStep 2124967 = 3187451) B3187451
theorem B19140077 : Blo 1492066 19140077 := bstep (se 3 (by rfl) ⟨3588764, by rfl⟩ : syracuseStep 19140077 = 7177529) B7177529
theorem B5041817 : Blo 1492066 5041817 := bstep (se 2 (by rfl) ⟨1890681, by rfl⟩ : syracuseStep 5041817 = 3781363) B3781363
theorem B8507065 : Blo 1492066 8507065 := bstep (se 2 (by rfl) ⟨3190149, by rfl⟩ : syracuseStep 8507065 = 6380299) B6380299
theorem B3028079 : Blo 1492066 3028079 := bstep (se 1 (by rfl) ⟨2271059, by rfl⟩ : syracuseStep 3028079 = 4542119) B4542119
theorem B3585151 : Blo 1492066 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B5109239 : Blo 1492066 5109239 := bstep (se 1 (by rfl) ⟨3831929, by rfl⟩ : syracuseStep 5109239 = 7663859) B7663859
theorem B5036201 : Blo 1492066 5036201 := bstep (se 2 (by rfl) ⟨1888575, by rfl⟩ : syracuseStep 5036201 = 3777151) B3777151
theorem B10762433 : Blo 1492066 10762433 := bstep (se 2 (by rfl) ⟨4035912, by rfl⟩ : syracuseStep 10762433 = 8071825) B8071825
theorem B4782559 : Blo 1492066 4782559 := bstep (se 1 (by rfl) ⟨3586919, by rfl⟩ : syracuseStep 4782559 = 7173839) B7173839
theorem B19126955 : Blo 1492066 19126955 := bstep (se 1 (by rfl) ⟨14345216, by rfl⟩ : syracuseStep 19126955 = 28690433) B28690433
theorem B3357503 : Blo 1492066 3357503 := bstep (se 1 (by rfl) ⟨2518127, by rfl⟩ : syracuseStep 3357503 = 5036255) B5036255
theorem B3357935 : Blo 1492066 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B11345183 : Blo 1492066 11345183 := bstep (se 1 (by rfl) ⟨8508887, by rfl⟩ : syracuseStep 11345183 = 17017775) B17017775
theorem B7560539 : Blo 1492066 7560539 := bstep (se 1 (by rfl) ⟨5670404, by rfl⟩ : syracuseStep 7560539 = 11340809) B11340809
theorem B3358187 : Blo 1492066 3358187 := bstep (se 1 (by rfl) ⟨2518640, by rfl⟩ : syracuseStep 3358187 = 5037281) B5037281
theorem B3358313 : Blo 1492066 3358313 := bstep (se 2 (by rfl) ⟨1259367, by rfl⟩ : syracuseStep 3358313 = 2518735) B2518735
theorem B19120805 : Blo 1492066 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B32269049 : Blo 1492066 32269049 := bstep (se 2 (by rfl) ⟨12100893, by rfl⟩ : syracuseStep 32269049 = 24201787) B24201787
theorem B3359483 : Blo 1492066 3359483 := bstep (se 1 (by rfl) ⟨2519612, by rfl⟩ : syracuseStep 3359483 = 5039225) B5039225
theorem B3359519 : Blo 1492066 3359519 := bstep (se 1 (by rfl) ⟨2519639, by rfl⟩ : syracuseStep 3359519 = 5039279) B5039279
theorem B19399549 : Blo 1492066 19399549 := bstep (se 3 (by rfl) ⟨3637415, by rfl⟩ : syracuseStep 19399549 = 7274831) B7274831
theorem B1492219 : Blo 1492066 1492219 := bstep (se 1 (by rfl) ⟨1119164, by rfl⟩ : syracuseStep 1492219 = 2238329) B2238329
theorem B1492711 : Blo 1492066 1492711 := bstep (se 1 (by rfl) ⟨1119533, by rfl⟩ : syracuseStep 1492711 = 2239067) B2239067
theorem B8505107 : Blo 1492066 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B1492827 : Blo 1492066 1492827 := bstep (se 1 (by rfl) ⟨1119620, by rfl⟩ : syracuseStep 1492827 = 2239241) B2239241
theorem B2238335 : Blo 1492066 2238335 := bstep (se 1 (by rfl) ⟨1678751, by rfl⟩ : syracuseStep 2238335 = 3357503) B3357503
theorem B1493055 : Blo 1492066 1493055 := bstep (se 1 (by rfl) ⟨1119791, by rfl⟩ : syracuseStep 1493055 = 2239583) B2239583
theorem B2238623 : Blo 1492066 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B7563455 : Blo 1492066 7563455 := bstep (se 1 (by rfl) ⟨5672591, by rfl⟩ : syracuseStep 7563455 = 11345183) B11345183
theorem B5040359 : Blo 1492066 5040359 := bstep (se 1 (by rfl) ⟨3780269, by rfl⟩ : syracuseStep 5040359 = 7560539) B7560539
theorem B2238791 : Blo 1492066 2238791 := bstep (se 1 (by rfl) ⟨1679093, by rfl⟩ : syracuseStep 2238791 = 3358187) B3358187
theorem B2238875 : Blo 1492066 2238875 := bstep (se 1 (by rfl) ⟨1679156, by rfl⟩ : syracuseStep 2238875 = 3358313) B3358313
theorem B3361211 : Blo 1492066 3361211 := bstep (se 1 (by rfl) ⟨2520908, by rfl⟩ : syracuseStep 3361211 = 5041817) B5041817
theorem B3779369 : Blo 1492066 3779369 := bstep (se 2 (by rfl) ⟨1417263, by rfl⟩ : syracuseStep 3779369 = 2834527) B2834527
theorem B6376745 : Blo 1492066 6376745 := bstep (se 2 (by rfl) ⟨2391279, by rfl⟩ : syracuseStep 6376745 = 4782559) B4782559
theorem B2018719 : Blo 1492066 2018719 := bstep (se 1 (by rfl) ⟨1514039, by rfl⟩ : syracuseStep 2018719 = 3028079) B3028079
theorem B3190441 : Blo 1492066 3190441 := bstep (se 2 (by rfl) ⟨1196415, by rfl⟩ : syracuseStep 3190441 = 2392831) B2392831
theorem B26209979 : Blo 1492066 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B36810593 : Blo 1492066 36810593 := bstep (se 2 (by rfl) ⟨13803972, by rfl⟩ : syracuseStep 36810593 = 27607945) B27607945
theorem B2125759 : Blo 1492066 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B2240507 : Blo 1492066 2240507 := bstep (se 1 (by rfl) ⟨1680380, by rfl⟩ : syracuseStep 2240507 = 3360761) B3360761
theorem B2240831 : Blo 1492066 2240831 := bstep (se 1 (by rfl) ⟨1680623, by rfl⟩ : syracuseStep 2240831 = 3361247) B3361247
theorem B12751303 : Blo 1492066 12751303 := bstep (se 1 (by rfl) ⟨9563477, by rfl⟩ : syracuseStep 12751303 = 19126955) B19126955
theorem B2519707 : Blo 1492066 2519707 := bstep (se 1 (by rfl) ⟨1889780, by rfl⟩ : syracuseStep 2519707 = 3779561) B3779561
theorem B54489773 : Blo 1492066 54489773 := bstep (se 3 (by rfl) ⟨10216832, by rfl⟩ : syracuseStep 54489773 = 20433665) B20433665
theorem B27243425 : Blo 1492066 27243425 := bstep (se 2 (by rfl) ⟨10216284, by rfl⟩ : syracuseStep 27243425 = 20432569) B20432569
theorem B11342753 : Blo 1492066 11342753 := bstep (se 2 (by rfl) ⟨4253532, by rfl⟩ : syracuseStep 11342753 = 8507065) B8507065
theorem B12760051 : Blo 1492066 12760051 := bstep (se 1 (by rfl) ⟨9570038, by rfl⟩ : syracuseStep 12760051 = 19140077) B19140077
theorem B6051307 : Blo 1492066 6051307 := bstep (se 1 (by rfl) ⟨4538480, by rfl⟩ : syracuseStep 6051307 = 9076961) B9076961
theorem B3406159 : Blo 1492066 3406159 := bstep (se 1 (by rfl) ⟨2554619, by rfl⟩ : syracuseStep 3406159 = 5109239) B5109239
theorem B3357161 : Blo 1492066 3357161 := bstep (se 2 (by rfl) ⟨1258935, by rfl⟩ : syracuseStep 3357161 = 2517871) B2517871
theorem B3357467 : Blo 1492066 3357467 := bstep (se 1 (by rfl) ⟨2518100, by rfl⟩ : syracuseStep 3357467 = 5036201) B5036201
theorem B7174955 : Blo 1492066 7174955 := bstep (se 1 (by rfl) ⟨5381216, by rfl⟩ : syracuseStep 7174955 = 10762433) B10762433
theorem B2833289 : Blo 1492066 2833289 := bstep (se 2 (by rfl) ⟨1062483, by rfl⟩ : syracuseStep 2833289 = 2124967) B2124967
theorem B6134983 : Blo 1492066 6134983 := bstep (se 1 (by rfl) ⟨4601237, by rfl⟩ : syracuseStep 6134983 = 9202475) B9202475
theorem B12115457 : Blo 1492066 12115457 := bstep (se 2 (by rfl) ⟨4543296, by rfl⟩ : syracuseStep 12115457 = 9086593) B9086593
theorem B12747203 : Blo 1492066 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B21512699 : Blo 1492066 21512699 := bstep (se 1 (by rfl) ⟨16134524, by rfl⟩ : syracuseStep 21512699 = 32269049) B32269049
theorem B7561835 : Blo 1492066 7561835 := bstep (se 1 (by rfl) ⟨5671376, by rfl⟩ : syracuseStep 7561835 = 11342753) B11342753
theorem B3359609 : Blo 1492066 3359609 := bstep (se 2 (by rfl) ⟨1259853, by rfl⟩ : syracuseStep 3359609 = 2519707) B2519707
theorem B32719909 : Blo 1492066 32719909 := bstep (se 4 (by rfl) ⟨3067491, by rfl⟩ : syracuseStep 32719909 = 6134983) B6134983
theorem B5670071 : Blo 1492066 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B1492223 : Blo 1492066 1492223 := bstep (se 1 (by rfl) ⟨1119167, by rfl⟩ : syracuseStep 1492223 = 2238335) B2238335
theorem B1492415 : Blo 1492066 1492415 := bstep (se 1 (by rfl) ⟨1119311, by rfl⟩ : syracuseStep 1492415 = 2238623) B2238623
theorem B3360239 : Blo 1492066 3360239 := bstep (se 1 (by rfl) ⟨2520179, by rfl⟩ : syracuseStep 3360239 = 5040359) B5040359
theorem B1492527 : Blo 1492066 1492527 := bstep (se 1 (by rfl) ⟨1119395, by rfl⟩ : syracuseStep 1492527 = 2238791) B2238791
theorem B1492583 : Blo 1492066 1492583 := bstep (se 1 (by rfl) ⟨1119437, by rfl⟩ : syracuseStep 1492583 = 2238875) B2238875
theorem B2238107 : Blo 1492066 2238107 := bstep (se 1 (by rfl) ⟨1678580, by rfl⟩ : syracuseStep 2238107 = 3357161) B3357161
theorem B2238311 : Blo 1492066 2238311 := bstep (se 1 (by rfl) ⟨1678733, by rfl⟩ : syracuseStep 2238311 = 3357467) B3357467
theorem B4253921 : Blo 1492066 4253921 := bstep (se 2 (by rfl) ⟨1595220, by rfl⟩ : syracuseStep 4253921 = 3190441) B3190441
theorem B72649133 : Blo 1492066 72649133 := bstep (se 3 (by rfl) ⟨13621712, by rfl⟩ : syracuseStep 72649133 = 27243425) B27243425
theorem B1493671 : Blo 1492066 1493671 := bstep (se 1 (by rfl) ⟨1120253, by rfl⟩ : syracuseStep 1493671 = 2240507) B2240507
theorem B1493887 : Blo 1492066 1493887 := bstep (se 1 (by rfl) ⟨1120415, by rfl⟩ : syracuseStep 1493887 = 2240831) B2240831
theorem B4541545 : Blo 1492066 4541545 := bstep (se 2 (by rfl) ⟨1703079, by rfl⟩ : syracuseStep 4541545 = 3406159) B3406159
theorem B36326515 : Blo 1492066 36326515 := bstep (se 1 (by rfl) ⟨27244886, by rfl⟩ : syracuseStep 36326515 = 54489773) B54489773
theorem B2239655 : Blo 1492066 2239655 := bstep (se 1 (by rfl) ⟨1679741, by rfl⟩ : syracuseStep 2239655 = 3359483) B3359483
theorem B2239679 : Blo 1492066 2239679 := bstep (se 1 (by rfl) ⟨1679759, by rfl⟩ : syracuseStep 2239679 = 3359519) B3359519
theorem B17001737 : Blo 1492066 17001737 := bstep (se 2 (by rfl) ⟨6375651, by rfl⟩ : syracuseStep 17001737 = 12751303) B12751303
theorem B25866065 : Blo 1492066 25866065 := bstep (se 2 (by rfl) ⟨9699774, by rfl⟩ : syracuseStep 25866065 = 19399549) B19399549
theorem B5042303 : Blo 1492066 5042303 := bstep (se 1 (by rfl) ⟨3781727, by rfl⟩ : syracuseStep 5042303 = 7563455) B7563455
theorem B2240807 : Blo 1492066 2240807 := bstep (se 1 (by rfl) ⟨1680605, by rfl⟩ : syracuseStep 2240807 = 3361211) B3361211
theorem B2519579 : Blo 1492066 2519579 := bstep (se 1 (by rfl) ⟨1889684, by rfl⟩ : syracuseStep 2519579 = 3779369) B3779369
theorem B2691625 : Blo 1492066 2691625 := bstep (se 2 (by rfl) ⟨1009359, by rfl⟩ : syracuseStep 2691625 = 2018719) B2018719
theorem B1888859 : Blo 1492066 1888859 := bstep (se 1 (by rfl) ⟨1416644, by rfl⟩ : syracuseStep 1888859 = 2833289) B2833289
theorem B24540395 : Blo 1492066 24540395 := bstep (se 1 (by rfl) ⟨18405296, by rfl⟩ : syracuseStep 24540395 = 36810593) B36810593
theorem B17004653 : Blo 1492066 17004653 := bstep (se 3 (by rfl) ⟨3188372, by rfl⟩ : syracuseStep 17004653 = 6376745) B6376745
theorem B17013401 : Blo 1492066 17013401 := bstep (se 2 (by rfl) ⟨6380025, by rfl⟩ : syracuseStep 17013401 = 12760051) B12760051
theorem B4783303 : Blo 1492066 4783303 := bstep (se 1 (by rfl) ⟨3587477, by rfl⟩ : syracuseStep 4783303 = 7174955) B7174955
theorem B8068409 : Blo 1492066 8068409 := bstep (se 2 (by rfl) ⟨3025653, by rfl⟩ : syracuseStep 8068409 = 6051307) B6051307
theorem B8076971 : Blo 1492066 8076971 := bstep (se 1 (by rfl) ⟨6057728, by rfl⟩ : syracuseStep 8076971 = 12115457) B12115457
theorem B17473319 : Blo 1492066 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B2834345 : Blo 1492066 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B1679719 : Blo 1492066 1679719 := bstep (se 1 (by rfl) ⟨1259789, by rfl⟩ : syracuseStep 1679719 = 2519579) B2519579
theorem B3588833 : Blo 1492066 3588833 := bstep (se 2 (by rfl) ⟨1345812, by rfl⟩ : syracuseStep 3588833 = 2691625) B2691625
theorem B1492071 : Blo 1492066 1492071 := bstep (se 1 (by rfl) ⟨1119053, by rfl⟩ : syracuseStep 1492071 = 2238107) B2238107
theorem B1492207 : Blo 1492066 1492207 := bstep (se 1 (by rfl) ⟨1119155, by rfl⟩ : syracuseStep 1492207 = 2238311) B2238311
theorem B6055393 : Blo 1492066 6055393 := bstep (se 2 (by rfl) ⟨2270772, by rfl⟩ : syracuseStep 6055393 = 4541545) B4541545
theorem B2835947 : Blo 1492066 2835947 := bstep (se 1 (by rfl) ⟨2126960, by rfl⟩ : syracuseStep 2835947 = 4253921) B4253921
theorem B48432755 : Blo 1492066 48432755 := bstep (se 1 (by rfl) ⟨36324566, by rfl⟩ : syracuseStep 48432755 = 72649133) B72649133
theorem B1493103 : Blo 1492066 1493103 := bstep (se 1 (by rfl) ⟨1119827, by rfl⟩ : syracuseStep 1493103 = 2239655) B2239655
theorem B1493119 : Blo 1492066 1493119 := bstep (se 1 (by rfl) ⟨1119839, by rfl⟩ : syracuseStep 1493119 = 2239679) B2239679
theorem B5384647 : Blo 1492066 5384647 := bstep (se 1 (by rfl) ⟨4038485, by rfl⟩ : syracuseStep 5384647 = 8076971) B8076971
theorem B3361535 : Blo 1492066 3361535 := bstep (se 1 (by rfl) ⟨2521151, by rfl⟩ : syracuseStep 3361535 = 5042303) B5042303
theorem B1493871 : Blo 1492066 1493871 := bstep (se 1 (by rfl) ⟨1120403, by rfl⟩ : syracuseStep 1493871 = 2240807) B2240807
theorem B8498135 : Blo 1492066 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B5041223 : Blo 1492066 5041223 := bstep (se 1 (by rfl) ⟨3780917, by rfl⟩ : syracuseStep 5041223 = 7561835) B7561835
theorem B2239739 : Blo 1492066 2239739 := bstep (se 1 (by rfl) ⟨1679804, by rfl⟩ : syracuseStep 2239739 = 3359609) B3359609
theorem B65441053 : Blo 1492066 65441053 := bstep (se 3 (by rfl) ⟨12270197, by rfl⟩ : syracuseStep 65441053 = 24540395) B24540395
theorem B3780047 : Blo 1492066 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B2240159 : Blo 1492066 2240159 := bstep (se 1 (by rfl) ⟨1680119, by rfl⟩ : syracuseStep 2240159 = 3360239) B3360239
theorem B43626545 : Blo 1492066 43626545 := bstep (se 2 (by rfl) ⟨16359954, by rfl⟩ : syracuseStep 43626545 = 32719909) B32719909
theorem B48435353 : Blo 1492066 48435353 := bstep (se 2 (by rfl) ⟨18163257, by rfl⟩ : syracuseStep 48435353 = 36326515) B36326515
theorem B6377737 : Blo 1492066 6377737 := bstep (se 2 (by rfl) ⟨2391651, by rfl⟩ : syracuseStep 6377737 = 4783303) B4783303
theorem B11342267 : Blo 1492066 11342267 := bstep (se 1 (by rfl) ⟨8506700, by rfl⟩ : syracuseStep 11342267 = 17013401) B17013401
theorem B11334491 : Blo 1492066 11334491 := bstep (se 1 (by rfl) ⟨8500868, by rfl⟩ : syracuseStep 11334491 = 17001737) B17001737
theorem B5378939 : Blo 1492066 5378939 := bstep (se 1 (by rfl) ⟨4034204, by rfl⟩ : syracuseStep 5378939 = 8068409) B8068409
theorem B1889563 : Blo 1492066 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B14341799 : Blo 1492066 14341799 := bstep (se 1 (by rfl) ⟨10756349, by rfl⟩ : syracuseStep 14341799 = 21512699) B21512699
theorem B11336435 : Blo 1492066 11336435 := bstep (se 1 (by rfl) ⟨8502326, by rfl⟩ : syracuseStep 11336435 = 17004653) B17004653
theorem B5036957 : Blo 1492066 5036957 := bstep (se 3 (by rfl) ⟨944429, by rfl⟩ : syracuseStep 5036957 = 1888859) B1888859
theorem B68976173 : Blo 1492066 68976173 := bstep (se 3 (by rfl) ⟨12933032, by rfl⟩ : syracuseStep 68976173 = 25866065) B25866065
theorem B11648879 : Blo 1492066 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B7561511 : Blo 1492066 7561511 := bstep (se 1 (by rfl) ⟨5671133, by rfl⟩ : syracuseStep 7561511 = 11342267) B11342267
theorem B8503649 : Blo 1492066 8503649 := bstep (se 2 (by rfl) ⟨3188868, by rfl⟩ : syracuseStep 8503649 = 6377737) B6377737
theorem B9561199 : Blo 1492066 9561199 := bstep (se 1 (by rfl) ⟨7170899, by rfl⟩ : syracuseStep 9561199 = 14341799) B14341799
theorem B9570221 : Blo 1492066 9570221 := bstep (se 3 (by rfl) ⟨1794416, by rfl⟩ : syracuseStep 9570221 = 3588833) B3588833
theorem B3360815 : Blo 1492066 3360815 := bstep (se 1 (by rfl) ⟨2520611, by rfl⟩ : syracuseStep 3360815 = 5041223) B5041223
theorem B1493159 : Blo 1492066 1493159 := bstep (se 1 (by rfl) ⟨1119869, by rfl⟩ : syracuseStep 1493159 = 2239739) B2239739
theorem B45984115 : Blo 1492066 45984115 := bstep (se 1 (by rfl) ⟨34488086, by rfl⟩ : syracuseStep 45984115 = 68976173) B68976173
theorem B1493439 : Blo 1492066 1493439 := bstep (se 1 (by rfl) ⟨1120079, by rfl⟩ : syracuseStep 1493439 = 2240159) B2240159
theorem B29084363 : Blo 1492066 29084363 := bstep (se 1 (by rfl) ⟨21813272, by rfl⟩ : syracuseStep 29084363 = 43626545) B43626545
theorem B2239625 : Blo 1492066 2239625 := bstep (se 2 (by rfl) ⟨839859, by rfl⟩ : syracuseStep 2239625 = 1679719) B1679719
theorem B7556327 : Blo 1492066 7556327 := bstep (se 1 (by rfl) ⟨5667245, by rfl⟩ : syracuseStep 7556327 = 11334491) B11334491
theorem B7179529 : Blo 1492066 7179529 := bstep (se 2 (by rfl) ⟨2692323, by rfl⟩ : syracuseStep 7179529 = 5384647) B5384647
theorem B32288503 : Blo 1492066 32288503 := bstep (se 1 (by rfl) ⟨24216377, by rfl⟩ : syracuseStep 32288503 = 48432755) B48432755
theorem B2519417 : Blo 1492066 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B7557623 : Blo 1492066 7557623 := bstep (se 1 (by rfl) ⟨5668217, by rfl⟩ : syracuseStep 7557623 = 11336435) B11336435
theorem B2241023 : Blo 1492066 2241023 := bstep (se 1 (by rfl) ⟨1680767, by rfl⟩ : syracuseStep 2241023 = 3361535) B3361535
theorem B8073857 : Blo 1492066 8073857 := bstep (se 2 (by rfl) ⟨3027696, by rfl⟩ : syracuseStep 8073857 = 6055393) B6055393
theorem B5665423 : Blo 1492066 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B2520031 : Blo 1492066 2520031 := bstep (se 1 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 2520031 = 3780047) B3780047
theorem B32290235 : Blo 1492066 32290235 := bstep (se 1 (by rfl) ⟨24217676, by rfl⟩ : syracuseStep 32290235 = 48435353) B48435353
theorem B3585959 : Blo 1492066 3585959 := bstep (se 1 (by rfl) ⟨2689469, by rfl⟩ : syracuseStep 3585959 = 5378939) B5378939
theorem B1890631 : Blo 1492066 1890631 := bstep (se 1 (by rfl) ⟨1417973, by rfl⟩ : syracuseStep 1890631 = 2835947) B2835947
theorem B349018949 : Blo 1492066 349018949 := bstep (se 4 (by rfl) ⟨32720526, by rfl⟩ : syracuseStep 349018949 = 65441053) B65441053
theorem B3357971 : Blo 1492066 3357971 := bstep (se 1 (by rfl) ⟨2518478, by rfl⟩ : syracuseStep 3357971 = 5036957) B5036957
theorem B7765919 : Blo 1492066 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B5669099 : Blo 1492066 5669099 := bstep (se 1 (by rfl) ⟨4251824, by rfl⟩ : syracuseStep 5669099 = 8503649) B8503649
theorem B1679611 : Blo 1492066 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B5038415 : Blo 1492066 5038415 := bstep (se 1 (by rfl) ⟨3778811, by rfl⟩ : syracuseStep 5038415 = 7557623) B7557623
theorem B7553897 : Blo 1492066 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B3360041 : Blo 1492066 3360041 := bstep (se 2 (by rfl) ⟨1260015, by rfl⟩ : syracuseStep 3360041 = 2520031) B2520031
theorem B12748265 : Blo 1492066 12748265 := bstep (se 2 (by rfl) ⟨4780599, by rfl⟩ : syracuseStep 12748265 = 9561199) B9561199
theorem B21530285 : Blo 1492066 21530285 := bstep (se 3 (by rfl) ⟨4036928, by rfl⟩ : syracuseStep 21530285 = 8073857) B8073857
theorem B232679299 : Blo 1492066 232679299 := bstep (se 1 (by rfl) ⟨174509474, by rfl⟩ : syracuseStep 232679299 = 349018949) B349018949
theorem B1493083 : Blo 1492066 1493083 := bstep (se 1 (by rfl) ⟨1119812, by rfl⟩ : syracuseStep 1493083 = 2239625) B2239625
theorem B2238647 : Blo 1492066 2238647 := bstep (se 1 (by rfl) ⟨1678985, by rfl⟩ : syracuseStep 2238647 = 3357971) B3357971
theorem B43051337 : Blo 1492066 43051337 := bstep (se 2 (by rfl) ⟨16144251, by rfl⟩ : syracuseStep 43051337 = 32288503) B32288503
theorem B5041007 : Blo 1492066 5041007 := bstep (se 1 (by rfl) ⟨3780755, by rfl⟩ : syracuseStep 5041007 = 7561511) B7561511
theorem B1494015 : Blo 1492066 1494015 := bstep (se 1 (by rfl) ⟨1120511, by rfl⟩ : syracuseStep 1494015 = 2241023) B2241023
theorem B61312153 : Blo 1492066 61312153 := bstep (se 2 (by rfl) ⟨22992057, by rfl⟩ : syracuseStep 61312153 = 45984115) B45984115
theorem B2240543 : Blo 1492066 2240543 := bstep (se 1 (by rfl) ⟨1680407, by rfl⟩ : syracuseStep 2240543 = 3360815) B3360815
theorem B9572705 : Blo 1492066 9572705 := bstep (se 2 (by rfl) ⟨3589764, by rfl⟩ : syracuseStep 9572705 = 7179529) B7179529
theorem B2520841 : Blo 1492066 2520841 := bstep (se 2 (by rfl) ⟨945315, by rfl⟩ : syracuseStep 2520841 = 1890631) B1890631
theorem B21526823 : Blo 1492066 21526823 := bstep (se 1 (by rfl) ⟨16145117, by rfl⟩ : syracuseStep 21526823 = 32290235) B32290235
theorem B2390639 : Blo 1492066 2390639 := bstep (se 1 (by rfl) ⟨1792979, by rfl⟩ : syracuseStep 2390639 = 3585959) B3585959
theorem B6380147 : Blo 1492066 6380147 := bstep (se 1 (by rfl) ⟨4785110, by rfl⟩ : syracuseStep 6380147 = 9570221) B9570221
theorem B19389575 : Blo 1492066 19389575 := bstep (se 1 (by rfl) ⟨14542181, by rfl⟩ : syracuseStep 19389575 = 29084363) B29084363
theorem B5037551 : Blo 1492066 5037551 := bstep (se 1 (by rfl) ⟨3778163, by rfl⟩ : syracuseStep 5037551 = 7556327) B7556327
theorem B5177279 : Blo 1492066 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B3358943 : Blo 1492066 3358943 := bstep (se 1 (by rfl) ⟨2519207, by rfl⟩ : syracuseStep 3358943 = 5038415) B5038415
theorem B6381803 : Blo 1492066 6381803 := bstep (se 1 (by rfl) ⟨4786352, by rfl⟩ : syracuseStep 6381803 = 9572705) B9572705
theorem B14353523 : Blo 1492066 14353523 := bstep (se 1 (by rfl) ⟨10765142, by rfl⟩ : syracuseStep 14353523 = 21530285) B21530285
theorem B1492431 : Blo 1492066 1492431 := bstep (se 1 (by rfl) ⟨1119323, by rfl⟩ : syracuseStep 1492431 = 2238647) B2238647
theorem B81749537 : Blo 1492066 81749537 := bstep (se 2 (by rfl) ⟨30656076, by rfl⟩ : syracuseStep 81749537 = 61312153) B61312153
theorem B6375037 : Blo 1492066 6375037 := bstep (se 3 (by rfl) ⟨1195319, by rfl⟩ : syracuseStep 6375037 = 2390639) B2390639
theorem B4253431 : Blo 1492066 4253431 := bstep (se 1 (by rfl) ⟨3190073, by rfl⟩ : syracuseStep 4253431 = 6380147) B6380147
theorem B3360671 : Blo 1492066 3360671 := bstep (se 1 (by rfl) ⟨2520503, by rfl⟩ : syracuseStep 3360671 = 5041007) B5041007
theorem B3361121 : Blo 1492066 3361121 := bstep (se 2 (by rfl) ⟨1260420, by rfl⟩ : syracuseStep 3361121 = 2520841) B2520841
theorem B13806077 : Blo 1492066 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B1493695 : Blo 1492066 1493695 := bstep (se 1 (by rfl) ⟨1120271, by rfl⟩ : syracuseStep 1493695 = 2240543) B2240543
theorem B3779399 : Blo 1492066 3779399 := bstep (se 1 (by rfl) ⟨2834549, by rfl⟩ : syracuseStep 3779399 = 5669099) B5669099
theorem B2239481 : Blo 1492066 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B2240027 : Blo 1492066 2240027 := bstep (se 1 (by rfl) ⟨1680020, by rfl⟩ : syracuseStep 2240027 = 3360041) B3360041
theorem B8498843 : Blo 1492066 8498843 := bstep (se 1 (by rfl) ⟨6374132, by rfl⟩ : syracuseStep 8498843 = 12748265) B12748265
theorem B28700891 : Blo 1492066 28700891 := bstep (se 1 (by rfl) ⟨21525668, by rfl⟩ : syracuseStep 28700891 = 43051337) B43051337
theorem B51705533 : Blo 1492066 51705533 := bstep (se 3 (by rfl) ⟨9694787, by rfl⟩ : syracuseStep 51705533 = 19389575) B19389575
theorem B5035931 : Blo 1492066 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B14351215 : Blo 1492066 14351215 := bstep (se 1 (by rfl) ⟨10763411, by rfl⟩ : syracuseStep 14351215 = 21526823) B21526823
theorem B3358367 : Blo 1492066 3358367 := bstep (se 1 (by rfl) ⟨2518775, by rfl⟩ : syracuseStep 3358367 = 5037551) B5037551
theorem B310239065 : Blo 1492066 310239065 := bstep (se 2 (by rfl) ⟨116339649, by rfl⟩ : syracuseStep 310239065 = 232679299) B232679299
theorem B9569015 : Blo 1492066 9569015 := bstep (se 1 (by rfl) ⟨7176761, by rfl⟩ : syracuseStep 9569015 = 14353523) B14353523
theorem B36816205 : Blo 1492066 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B1492987 : Blo 1492066 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B5671241 : Blo 1492066 5671241 := bstep (se 2 (by rfl) ⟨2126715, by rfl⟩ : syracuseStep 5671241 = 4253431) B4253431
theorem B1493351 : Blo 1492066 1493351 := bstep (se 1 (by rfl) ⟨1120013, by rfl⟩ : syracuseStep 1493351 = 2240027) B2240027
theorem B2238911 : Blo 1492066 2238911 := bstep (se 1 (by rfl) ⟨1679183, by rfl⟩ : syracuseStep 2238911 = 3358367) B3358367
theorem B206826043 : Blo 1492066 206826043 := bstep (se 1 (by rfl) ⟨155119532, by rfl⟩ : syracuseStep 206826043 = 310239065) B310239065
theorem B2239295 : Blo 1492066 2239295 := bstep (se 1 (by rfl) ⟨1679471, by rfl⟩ : syracuseStep 2239295 = 3358943) B3358943
theorem B4254535 : Blo 1492066 4254535 := bstep (se 1 (by rfl) ⟨3190901, by rfl⟩ : syracuseStep 4254535 = 6381803) B6381803
theorem B2240447 : Blo 1492066 2240447 := bstep (se 1 (by rfl) ⟨1680335, by rfl⟩ : syracuseStep 2240447 = 3360671) B3360671
theorem B2240747 : Blo 1492066 2240747 := bstep (se 1 (by rfl) ⟨1680560, by rfl⟩ : syracuseStep 2240747 = 3361121) B3361121
theorem B2519599 : Blo 1492066 2519599 := bstep (se 1 (by rfl) ⟨1889699, by rfl⟩ : syracuseStep 2519599 = 3779399) B3779399
theorem B8500049 : Blo 1492066 8500049 := bstep (se 2 (by rfl) ⟨3187518, by rfl⟩ : syracuseStep 8500049 = 6375037) B6375037
theorem B5665895 : Blo 1492066 5665895 := bstep (se 1 (by rfl) ⟨4249421, by rfl⟩ : syracuseStep 5665895 = 8498843) B8498843
theorem B19133927 : Blo 1492066 19133927 := bstep (se 1 (by rfl) ⟨14350445, by rfl⟩ : syracuseStep 19133927 = 28700891) B28700891
theorem B54499691 : Blo 1492066 54499691 := bstep (se 1 (by rfl) ⟨40874768, by rfl⟩ : syracuseStep 54499691 = 81749537) B81749537
theorem B34470355 : Blo 1492066 34470355 := bstep (se 1 (by rfl) ⟨25852766, by rfl⟩ : syracuseStep 34470355 = 51705533) B51705533
theorem B19134953 : Blo 1492066 19134953 := bstep (se 2 (by rfl) ⟨7175607, by rfl⟩ : syracuseStep 19134953 = 14351215) B14351215
theorem B3357287 : Blo 1492066 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B3359465 : Blo 1492066 3359465 := bstep (se 2 (by rfl) ⟨1259799, by rfl⟩ : syracuseStep 3359465 = 2519599) B2519599
theorem B3777263 : Blo 1492066 3777263 := bstep (se 1 (by rfl) ⟨2832947, by rfl⟩ : syracuseStep 3777263 = 5665895) B5665895
theorem B275768057 : Blo 1492066 275768057 := bstep (se 2 (by rfl) ⟨103413021, by rfl⟩ : syracuseStep 275768057 = 206826043) B206826043
theorem B12755951 : Blo 1492066 12755951 := bstep (se 1 (by rfl) ⟨9566963, by rfl⟩ : syracuseStep 12755951 = 19133927) B19133927
theorem B36333127 : Blo 1492066 36333127 := bstep (se 1 (by rfl) ⟨27249845, by rfl⟩ : syracuseStep 36333127 = 54499691) B54499691
theorem B1492607 : Blo 1492066 1492607 := bstep (se 1 (by rfl) ⟨1119455, by rfl⟩ : syracuseStep 1492607 = 2238911) B2238911
theorem B12756635 : Blo 1492066 12756635 := bstep (se 1 (by rfl) ⟨9567476, by rfl⟩ : syracuseStep 12756635 = 19134953) B19134953
theorem B2238191 : Blo 1492066 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B49088273 : Blo 1492066 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B1492863 : Blo 1492066 1492863 := bstep (se 1 (by rfl) ⟨1119647, by rfl⟩ : syracuseStep 1492863 = 2239295) B2239295
theorem B1493631 : Blo 1492066 1493631 := bstep (se 1 (by rfl) ⟨1120223, by rfl⟩ : syracuseStep 1493631 = 2240447) B2240447
theorem B1493831 : Blo 1492066 1493831 := bstep (se 1 (by rfl) ⟨1120373, by rfl⟩ : syracuseStep 1493831 = 2240747) B2240747
theorem B45960473 : Blo 1492066 45960473 := bstep (se 2 (by rfl) ⟨17235177, by rfl⟩ : syracuseStep 45960473 = 34470355) B34470355
theorem B5672713 : Blo 1492066 5672713 := bstep (se 2 (by rfl) ⟨2127267, by rfl⟩ : syracuseStep 5672713 = 4254535) B4254535
theorem B3780827 : Blo 1492066 3780827 := bstep (se 1 (by rfl) ⟨2835620, by rfl⟩ : syracuseStep 3780827 = 5671241) B5671241
theorem B6379343 : Blo 1492066 6379343 := bstep (se 1 (by rfl) ⟨4784507, by rfl⟩ : syracuseStep 6379343 = 9569015) B9569015
theorem B5666699 : Blo 1492066 5666699 := bstep (se 1 (by rfl) ⟨4250024, by rfl⟩ : syracuseStep 5666699 = 8500049) B8500049
theorem B523608245 : Blo 1492066 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B183845371 : Blo 1492066 183845371 := bstep (se 1 (by rfl) ⟨137884028, by rfl⟩ : syracuseStep 183845371 = 275768057) B275768057
theorem B8503967 : Blo 1492066 8503967 := bstep (se 1 (by rfl) ⟨6377975, by rfl⟩ : syracuseStep 8503967 = 12755951) B12755951
theorem B8504423 : Blo 1492066 8504423 := bstep (se 1 (by rfl) ⟨6378317, by rfl⟩ : syracuseStep 8504423 = 12756635) B12756635
theorem B1492127 : Blo 1492066 1492127 := bstep (se 1 (by rfl) ⟨1119095, by rfl⟩ : syracuseStep 1492127 = 2238191) B2238191
theorem B4252895 : Blo 1492066 4252895 := bstep (se 1 (by rfl) ⟨3189671, by rfl⟩ : syracuseStep 4252895 = 6379343) B6379343
theorem B3777799 : Blo 1492066 3777799 := bstep (se 1 (by rfl) ⟨2833349, by rfl⟩ : syracuseStep 3777799 = 5666699) B5666699
theorem B30640315 : Blo 1492066 30640315 := bstep (se 1 (by rfl) ⟨22980236, by rfl⟩ : syracuseStep 30640315 = 45960473) B45960473
theorem B7563617 : Blo 1492066 7563617 := bstep (se 2 (by rfl) ⟨2836356, by rfl⟩ : syracuseStep 7563617 = 5672713) B5672713
theorem B2239643 : Blo 1492066 2239643 := bstep (se 1 (by rfl) ⟨1679732, by rfl⟩ : syracuseStep 2239643 = 3359465) B3359465
theorem B2518175 : Blo 1492066 2518175 := bstep (se 1 (by rfl) ⟨1888631, by rfl⟩ : syracuseStep 2518175 = 3777263) B3777263
theorem B48444169 : Blo 1492066 48444169 := bstep (se 2 (by rfl) ⟨18166563, by rfl⟩ : syracuseStep 48444169 = 36333127) B36333127
theorem B2520551 : Blo 1492066 2520551 := bstep (se 1 (by rfl) ⟨1890413, by rfl⟩ : syracuseStep 2520551 = 3780827) B3780827
theorem B40853753 : Blo 1492066 40853753 := bstep (se 2 (by rfl) ⟨15320157, by rfl⟩ : syracuseStep 40853753 = 30640315) B30640315
theorem B5669311 : Blo 1492066 5669311 := bstep (se 1 (by rfl) ⟨4251983, by rfl⟩ : syracuseStep 5669311 = 8503967) B8503967
theorem B5669615 : Blo 1492066 5669615 := bstep (se 1 (by rfl) ⟨4252211, by rfl⟩ : syracuseStep 5669615 = 8504423) B8504423
theorem B2835263 : Blo 1492066 2835263 := bstep (se 1 (by rfl) ⟨2126447, by rfl⟩ : syracuseStep 2835263 = 4252895) B4252895
theorem B1680367 : Blo 1492066 1680367 := bstep (se 1 (by rfl) ⟨1260275, by rfl⟩ : syracuseStep 1680367 = 2520551) B2520551
theorem B1493095 : Blo 1492066 1493095 := bstep (se 1 (by rfl) ⟨1119821, by rfl⟩ : syracuseStep 1493095 = 2239643) B2239643
theorem B349072163 : Blo 1492066 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B5042411 : Blo 1492066 5042411 := bstep (se 1 (by rfl) ⟨3781808, by rfl⟩ : syracuseStep 5042411 = 7563617) B7563617
theorem B245127161 : Blo 1492066 245127161 := bstep (se 2 (by rfl) ⟨91922685, by rfl⟩ : syracuseStep 245127161 = 183845371) B183845371
theorem B64592225 : Blo 1492066 64592225 := bstep (se 2 (by rfl) ⟨24222084, by rfl⟩ : syracuseStep 64592225 = 48444169) B48444169
theorem B5037065 : Blo 1492066 5037065 := bstep (se 2 (by rfl) ⟨1888899, by rfl⟩ : syracuseStep 5037065 = 3777799) B3777799
theorem B1678783 : Blo 1492066 1678783 := bstep (se 1 (by rfl) ⟨1259087, by rfl⟩ : syracuseStep 1678783 = 2518175) B2518175
theorem B2238377 : Blo 1492066 2238377 := bstep (se 2 (by rfl) ⟨839391, by rfl⟩ : syracuseStep 2238377 = 1678783) B1678783
theorem B3361607 : Blo 1492066 3361607 := bstep (se 1 (by rfl) ⟨2521205, by rfl⟩ : syracuseStep 3361607 = 5042411) B5042411
theorem B3779743 : Blo 1492066 3779743 := bstep (se 1 (by rfl) ⟨2834807, by rfl⟩ : syracuseStep 3779743 = 5669615) B5669615
theorem B2240489 : Blo 1492066 2240489 := bstep (se 2 (by rfl) ⟨840183, by rfl⟩ : syracuseStep 2240489 = 1680367) B1680367
theorem B163418107 : Blo 1492066 163418107 := bstep (se 1 (by rfl) ⟨122563580, by rfl⟩ : syracuseStep 163418107 = 245127161) B245127161
theorem B43061483 : Blo 1492066 43061483 := bstep (se 1 (by rfl) ⟨32296112, by rfl⟩ : syracuseStep 43061483 = 64592225) B64592225
theorem B232714775 : Blo 1492066 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B27235835 : Blo 1492066 27235835 := bstep (se 1 (by rfl) ⟨20426876, by rfl⟩ : syracuseStep 27235835 = 40853753) B40853753
theorem B7559081 : Blo 1492066 7559081 := bstep (se 2 (by rfl) ⟨2834655, by rfl⟩ : syracuseStep 7559081 = 5669311) B5669311
theorem B3358043 : Blo 1492066 3358043 := bstep (se 1 (by rfl) ⟨2518532, by rfl⟩ : syracuseStep 3358043 = 5037065) B5037065
theorem B7560701 : Blo 1492066 7560701 := bstep (se 3 (by rfl) ⟨1417631, by rfl⟩ : syracuseStep 7560701 = 2835263) B2835263
theorem B1492251 : Blo 1492066 1492251 := bstep (se 1 (by rfl) ⟨1119188, by rfl⟩ : syracuseStep 1492251 = 2238377) B2238377
theorem B5039387 : Blo 1492066 5039387 := bstep (se 1 (by rfl) ⟨3779540, by rfl⟩ : syracuseStep 5039387 = 7559081) B7559081
theorem B5039657 : Blo 1492066 5039657 := bstep (se 2 (by rfl) ⟨1889871, by rfl⟩ : syracuseStep 5039657 = 3779743) B3779743
theorem B2238695 : Blo 1492066 2238695 := bstep (se 1 (by rfl) ⟨1679021, by rfl⟩ : syracuseStep 2238695 = 3358043) B3358043
theorem B5040467 : Blo 1492066 5040467 := bstep (se 1 (by rfl) ⟨3780350, by rfl⟩ : syracuseStep 5040467 = 7560701) B7560701
theorem B1493659 : Blo 1492066 1493659 := bstep (se 1 (by rfl) ⟨1120244, by rfl⟩ : syracuseStep 1493659 = 2240489) B2240489
theorem B28707655 : Blo 1492066 28707655 := bstep (se 1 (by rfl) ⟨21530741, by rfl⟩ : syracuseStep 28707655 = 43061483) B43061483
theorem B155143183 : Blo 1492066 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B18157223 : Blo 1492066 18157223 := bstep (se 1 (by rfl) ⟨13617917, by rfl⟩ : syracuseStep 18157223 = 27235835) B27235835
theorem B2241071 : Blo 1492066 2241071 := bstep (se 1 (by rfl) ⟨1680803, by rfl⟩ : syracuseStep 2241071 = 3361607) B3361607
theorem B217890809 : Blo 1492066 217890809 := bstep (se 2 (by rfl) ⟨81709053, by rfl⟩ : syracuseStep 217890809 = 163418107) B163418107
theorem B3359591 : Blo 1492066 3359591 := bstep (se 1 (by rfl) ⟨2519693, by rfl⟩ : syracuseStep 3359591 = 5039387) B5039387
theorem B3359771 : Blo 1492066 3359771 := bstep (se 1 (by rfl) ⟨2519828, by rfl⟩ : syracuseStep 3359771 = 5039657) B5039657
theorem B206857577 : Blo 1492066 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B1492463 : Blo 1492066 1492463 := bstep (se 1 (by rfl) ⟨1119347, by rfl⟩ : syracuseStep 1492463 = 2238695) B2238695
theorem B3360311 : Blo 1492066 3360311 := bstep (se 1 (by rfl) ⟨2520233, by rfl⟩ : syracuseStep 3360311 = 5040467) B5040467
theorem B1494047 : Blo 1492066 1494047 := bstep (se 1 (by rfl) ⟨1120535, by rfl⟩ : syracuseStep 1494047 = 2241071) B2241071
theorem B38276873 : Blo 1492066 38276873 := bstep (se 2 (by rfl) ⟨14353827, by rfl⟩ : syracuseStep 38276873 = 28707655) B28707655
theorem B12104815 : Blo 1492066 12104815 := bstep (se 1 (by rfl) ⟨9078611, by rfl⟩ : syracuseStep 12104815 = 18157223) B18157223
theorem B145260539 : Blo 1492066 145260539 := bstep (se 1 (by rfl) ⟨108945404, by rfl⟩ : syracuseStep 145260539 = 217890809) B217890809
theorem B137905051 : Blo 1492066 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B16139753 : Blo 1492066 16139753 := bstep (se 2 (by rfl) ⟨6052407, by rfl⟩ : syracuseStep 16139753 = 12104815) B12104815
theorem B96840359 : Blo 1492066 96840359 := bstep (se 1 (by rfl) ⟨72630269, by rfl⟩ : syracuseStep 96840359 = 145260539) B145260539
theorem B2239727 : Blo 1492066 2239727 := bstep (se 1 (by rfl) ⟨1679795, by rfl⟩ : syracuseStep 2239727 = 3359591) B3359591
theorem B2239847 : Blo 1492066 2239847 := bstep (se 1 (by rfl) ⟨1679885, by rfl⟩ : syracuseStep 2239847 = 3359771) B3359771
theorem B2240207 : Blo 1492066 2240207 := bstep (se 1 (by rfl) ⟨1680155, by rfl⟩ : syracuseStep 2240207 = 3360311) B3360311
theorem B25517915 : Blo 1492066 25517915 := bstep (se 1 (by rfl) ⟨19138436, by rfl⟩ : syracuseStep 25517915 = 38276873) B38276873
theorem B1493151 : Blo 1492066 1493151 := bstep (se 1 (by rfl) ⟨1119863, by rfl⟩ : syracuseStep 1493151 = 2239727) B2239727
theorem B1493231 : Blo 1492066 1493231 := bstep (se 1 (by rfl) ⟨1119923, by rfl⟩ : syracuseStep 1493231 = 2239847) B2239847
theorem B1493471 : Blo 1492066 1493471 := bstep (se 1 (by rfl) ⟨1120103, by rfl⟩ : syracuseStep 1493471 = 2240207) B2240207
theorem B10759835 : Blo 1492066 10759835 := bstep (se 1 (by rfl) ⟨8069876, by rfl⟩ : syracuseStep 10759835 = 16139753) B16139753
theorem B183873401 : Blo 1492066 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B17011943 : Blo 1492066 17011943 := bstep (se 1 (by rfl) ⟨12758957, by rfl⟩ : syracuseStep 17011943 = 25517915) B25517915
theorem B64560239 : Blo 1492066 64560239 := bstep (se 1 (by rfl) ⟨48420179, by rfl⟩ : syracuseStep 64560239 = 96840359) B96840359
theorem B11341295 : Blo 1492066 11341295 := bstep (se 1 (by rfl) ⟨8505971, by rfl⟩ : syracuseStep 11341295 = 17011943) B17011943
theorem B28692893 : Blo 1492066 28692893 := bstep (se 3 (by rfl) ⟨5379917, by rfl⟩ : syracuseStep 28692893 = 10759835) B10759835
theorem B122582267 : Blo 1492066 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B43040159 : Blo 1492066 43040159 := bstep (se 1 (by rfl) ⟨32280119, by rfl⟩ : syracuseStep 43040159 = 64560239) B64560239
theorem B19128595 : Blo 1492066 19128595 := bstep (se 1 (by rfl) ⟨14346446, by rfl⟩ : syracuseStep 19128595 = 28692893) B28692893
theorem B28693439 : Blo 1492066 28693439 := bstep (se 1 (by rfl) ⟨21520079, by rfl⟩ : syracuseStep 28693439 = 43040159) B43040159
theorem B81721511 : Blo 1492066 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B7560863 : Blo 1492066 7560863 := bstep (se 1 (by rfl) ⟨5670647, by rfl⟩ : syracuseStep 7560863 = 11341295) B11341295
theorem B19128959 : Blo 1492066 19128959 := bstep (se 1 (by rfl) ⟨14346719, by rfl⟩ : syracuseStep 19128959 = 28693439) B28693439
theorem B5040575 : Blo 1492066 5040575 := bstep (se 1 (by rfl) ⟨3780431, by rfl⟩ : syracuseStep 5040575 = 7560863) B7560863
theorem B25504793 : Blo 1492066 25504793 := bstep (se 2 (by rfl) ⟨9564297, by rfl⟩ : syracuseStep 25504793 = 19128595) B19128595
theorem B54481007 : Blo 1492066 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B3360383 : Blo 1492066 3360383 := bstep (se 1 (by rfl) ⟨2520287, by rfl⟩ : syracuseStep 3360383 = 5040575) B5040575
theorem B17003195 : Blo 1492066 17003195 := bstep (se 1 (by rfl) ⟨12752396, by rfl⟩ : syracuseStep 17003195 = 25504793) B25504793
theorem B36320671 : Blo 1492066 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B12752639 : Blo 1492066 12752639 := bstep (se 1 (by rfl) ⟨9564479, by rfl⟩ : syracuseStep 12752639 = 19128959) B19128959
theorem B2240255 : Blo 1492066 2240255 := bstep (se 1 (by rfl) ⟨1680191, by rfl⟩ : syracuseStep 2240255 = 3360383) B3360383
theorem B48427561 : Blo 1492066 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B11335463 : Blo 1492066 11335463 := bstep (se 1 (by rfl) ⟨8501597, by rfl⟩ : syracuseStep 11335463 = 17003195) B17003195
theorem B8501759 : Blo 1492066 8501759 := bstep (se 1 (by rfl) ⟨6376319, by rfl⟩ : syracuseStep 8501759 = 12752639) B12752639
theorem B64570081 : Blo 1492066 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B1493503 : Blo 1492066 1493503 := bstep (se 1 (by rfl) ⟨1120127, by rfl⟩ : syracuseStep 1493503 = 2240255) B2240255
theorem B7556975 : Blo 1492066 7556975 := bstep (se 1 (by rfl) ⟨5667731, by rfl⟩ : syracuseStep 7556975 = 11335463) B11335463
theorem B5667839 : Blo 1492066 5667839 := bstep (se 1 (by rfl) ⟨4250879, by rfl⟩ : syracuseStep 5667839 = 8501759) B8501759
theorem B3778559 : Blo 1492066 3778559 := bstep (se 1 (by rfl) ⟨2833919, by rfl⟩ : syracuseStep 3778559 = 5667839) B5667839
theorem B86093441 : Blo 1492066 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B5037983 : Blo 1492066 5037983 := bstep (se 1 (by rfl) ⟨3778487, by rfl⟩ : syracuseStep 5037983 = 7556975) B7556975
theorem B57395627 : Blo 1492066 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B2519039 : Blo 1492066 2519039 := bstep (se 1 (by rfl) ⟨1889279, by rfl⟩ : syracuseStep 2519039 = 3778559) B3778559
theorem B3358655 : Blo 1492066 3358655 := bstep (se 1 (by rfl) ⟨2518991, by rfl⟩ : syracuseStep 3358655 = 5037983) B5037983
theorem B2239103 : Blo 1492066 2239103 := bstep (se 1 (by rfl) ⟨1679327, by rfl⟩ : syracuseStep 2239103 = 3358655) B3358655
theorem B38263751 : Blo 1492066 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B1679359 : Blo 1492066 1679359 := bstep (se 1 (by rfl) ⟨1259519, by rfl⟩ : syracuseStep 1679359 = 2519039) B2519039
theorem B1492735 : Blo 1492066 1492735 := bstep (se 1 (by rfl) ⟨1119551, by rfl⟩ : syracuseStep 1492735 = 2239103) B2239103
theorem B2239145 : Blo 1492066 2239145 := bstep (se 2 (by rfl) ⟨839679, by rfl⟩ : syracuseStep 2239145 = 1679359) B1679359
theorem B25509167 : Blo 1492066 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B1492763 : Blo 1492066 1492763 := bstep (se 1 (by rfl) ⟨1119572, by rfl⟩ : syracuseStep 1492763 = 2239145) B2239145
theorem B17006111 : Blo 1492066 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B11337407 : Blo 1492066 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B7558271 : Blo 1492066 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B5038847 : Blo 1492066 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B3359231 : Blo 1492066 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B2239487 : Blo 1492066 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B1492991 : Blo 1492066 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487

theorem C0 (j : ℕ) (h1 : 373016 ≤ j) (h2 : j ≤ 373515) : Blo 1492066 (4 * j + 3) := by
  interval_cases j
  · exact B1492067
  · exact B1492071
  · exact B1492075
  · exact B1492079
  · exact B1492083
  · exact B1492087
  · exact B1492091
  · exact B1492095
  · exact B1492099
  · exact B1492103
  · exact B1492107
  · exact B1492111
  · exact B1492115
  · exact B1492119
  · exact B1492123
  · exact B1492127
  · exact B1492131
  · exact B1492135
  · exact B1492139
  · exact B1492143
  · exact B1492147
  · exact B1492151
  · exact B1492155
  · exact B1492159
  · exact B1492163
  · exact B1492167
  · exact B1492171
  · exact B1492175
  · exact B1492179
  · exact B1492183
  · exact B1492187
  · exact B1492191
  · exact B1492195
  · exact B1492199
  · exact B1492203
  · exact B1492207
  · exact B1492211
  · exact B1492215
  · exact B1492219
  · exact B1492223
  · exact B1492227
  · exact B1492231
  · exact B1492235
  · exact B1492239
  · exact B1492243
  · exact B1492247
  · exact B1492251
  · exact B1492255
  · exact B1492259
  · exact B1492263
  · exact B1492267
  · exact B1492271
  · exact B1492275
  · exact B1492279
  · exact B1492283
  · exact B1492287
  · exact B1492291
  · exact B1492295
  · exact B1492299
  · exact B1492303
  · exact B1492307
  · exact B1492311
  · exact B1492315
  · exact B1492319
  · exact B1492323
  · exact B1492327
  · exact B1492331
  · exact B1492335
  · exact B1492339
  · exact B1492343
  · exact B1492347
  · exact B1492351
  · exact B1492355
  · exact B1492359
  · exact B1492363
  · exact B1492367
  · exact B1492371
  · exact B1492375
  · exact B1492379
  · exact B1492383
  · exact B1492387
  · exact B1492391
  · exact B1492395
  · exact B1492399
  · exact B1492403
  · exact B1492407
  · exact B1492411
  · exact B1492415
  · exact B1492419
  · exact B1492423
  · exact B1492427
  · exact B1492431
  · exact B1492435
  · exact B1492439
  · exact B1492443
  · exact B1492447
  · exact B1492451
  · exact B1492455
  · exact B1492459
  · exact B1492463
  · exact B1492467
  · exact B1492471
  · exact B1492475
  · exact B1492479
  · exact B1492483
  · exact B1492487
  · exact B1492491
  · exact B1492495
  · exact B1492499
  · exact B1492503
  · exact B1492507
  · exact B1492511
  · exact B1492515
  · exact B1492519
  · exact B1492523
  · exact B1492527
  · exact B1492531
  · exact B1492535
  · exact B1492539
  · exact B1492543
  · exact B1492547
  · exact B1492551
  · exact B1492555
  · exact B1492559
  · exact B1492563
  · exact B1492567
  · exact B1492571
  · exact B1492575
  · exact B1492579
  · exact B1492583
  · exact B1492587
  · exact B1492591
  · exact B1492595
  · exact B1492599
  · exact B1492603
  · exact B1492607
  · exact B1492611
  · exact B1492615
  · exact B1492619
  · exact B1492623
  · exact B1492627
  · exact B1492631
  · exact B1492635
  · exact B1492639
  · exact B1492643
  · exact B1492647
  · exact B1492651
  · exact B1492655
  · exact B1492659
  · exact B1492663
  · exact B1492667
  · exact B1492671
  · exact B1492675
  · exact B1492679
  · exact B1492683
  · exact B1492687
  · exact B1492691
  · exact B1492695
  · exact B1492699
  · exact B1492703
  · exact B1492707
  · exact B1492711
  · exact B1492715
  · exact B1492719
  · exact B1492723
  · exact B1492727
  · exact B1492731
  · exact B1492735
  · exact B1492739
  · exact B1492743
  · exact B1492747
  · exact B1492751
  · exact B1492755
  · exact B1492759
  · exact B1492763
  · exact B1492767
  · exact B1492771
  · exact B1492775
  · exact B1492779
  · exact B1492783
  · exact B1492787
  · exact B1492791
  · exact B1492795
  · exact B1492799
  · exact B1492803
  · exact B1492807
  · exact B1492811
  · exact B1492815
  · exact B1492819
  · exact B1492823
  · exact B1492827
  · exact B1492831
  · exact B1492835
  · exact B1492839
  · exact B1492843
  · exact B1492847
  · exact B1492851
  · exact B1492855
  · exact B1492859
  · exact B1492863
  · exact B1492867
  · exact B1492871
  · exact B1492875
  · exact B1492879
  · exact B1492883
  · exact B1492887
  · exact B1492891
  · exact B1492895
  · exact B1492899
  · exact B1492903
  · exact B1492907
  · exact B1492911
  · exact B1492915
  · exact B1492919
  · exact B1492923
  · exact B1492927
  · exact B1492931
  · exact B1492935
  · exact B1492939
  · exact B1492943
  · exact B1492947
  · exact B1492951
  · exact B1492955
  · exact B1492959
  · exact B1492963
  · exact B1492967
  · exact B1492971
  · exact B1492975
  · exact B1492979
  · exact B1492983
  · exact B1492987
  · exact B1492991
  · exact B1492995
  · exact B1492999
  · exact B1493003
  · exact B1493007
  · exact B1493011
  · exact B1493015
  · exact B1493019
  · exact B1493023
  · exact B1493027
  · exact B1493031
  · exact B1493035
  · exact B1493039
  · exact B1493043
  · exact B1493047
  · exact B1493051
  · exact B1493055
  · exact B1493059
  · exact B1493063
  · exact B1493067
  · exact B1493071
  · exact B1493075
  · exact B1493079
  · exact B1493083
  · exact B1493087
  · exact B1493091
  · exact B1493095
  · exact B1493099
  · exact B1493103
  · exact B1493107
  · exact B1493111
  · exact B1493115
  · exact B1493119
  · exact B1493123
  · exact B1493127
  · exact B1493131
  · exact B1493135
  · exact B1493139
  · exact B1493143
  · exact B1493147
  · exact B1493151
  · exact B1493155
  · exact B1493159
  · exact B1493163
  · exact B1493167
  · exact B1493171
  · exact B1493175
  · exact B1493179
  · exact B1493183
  · exact B1493187
  · exact B1493191
  · exact B1493195
  · exact B1493199
  · exact B1493203
  · exact B1493207
  · exact B1493211
  · exact B1493215
  · exact B1493219
  · exact B1493223
  · exact B1493227
  · exact B1493231
  · exact B1493235
  · exact B1493239
  · exact B1493243
  · exact B1493247
  · exact B1493251
  · exact B1493255
  · exact B1493259
  · exact B1493263
  · exact B1493267
  · exact B1493271
  · exact B1493275
  · exact B1493279
  · exact B1493283
  · exact B1493287
  · exact B1493291
  · exact B1493295
  · exact B1493299
  · exact B1493303
  · exact B1493307
  · exact B1493311
  · exact B1493315
  · exact B1493319
  · exact B1493323
  · exact B1493327
  · exact B1493331
  · exact B1493335
  · exact B1493339
  · exact B1493343
  · exact B1493347
  · exact B1493351
  · exact B1493355
  · exact B1493359
  · exact B1493363
  · exact B1493367
  · exact B1493371
  · exact B1493375
  · exact B1493379
  · exact B1493383
  · exact B1493387
  · exact B1493391
  · exact B1493395
  · exact B1493399
  · exact B1493403
  · exact B1493407
  · exact B1493411
  · exact B1493415
  · exact B1493419
  · exact B1493423
  · exact B1493427
  · exact B1493431
  · exact B1493435
  · exact B1493439
  · exact B1493443
  · exact B1493447
  · exact B1493451
  · exact B1493455
  · exact B1493459
  · exact B1493463
  · exact B1493467
  · exact B1493471
  · exact B1493475
  · exact B1493479
  · exact B1493483
  · exact B1493487
  · exact B1493491
  · exact B1493495
  · exact B1493499
  · exact B1493503
  · exact B1493507
  · exact B1493511
  · exact B1493515
  · exact B1493519
  · exact B1493523
  · exact B1493527
  · exact B1493531
  · exact B1493535
  · exact B1493539
  · exact B1493543
  · exact B1493547
  · exact B1493551
  · exact B1493555
  · exact B1493559
  · exact B1493563
  · exact B1493567
  · exact B1493571
  · exact B1493575
  · exact B1493579
  · exact B1493583
  · exact B1493587
  · exact B1493591
  · exact B1493595
  · exact B1493599
  · exact B1493603
  · exact B1493607
  · exact B1493611
  · exact B1493615
  · exact B1493619
  · exact B1493623
  · exact B1493627
  · exact B1493631
  · exact B1493635
  · exact B1493639
  · exact B1493643
  · exact B1493647
  · exact B1493651
  · exact B1493655
  · exact B1493659
  · exact B1493663
  · exact B1493667
  · exact B1493671
  · exact B1493675
  · exact B1493679
  · exact B1493683
  · exact B1493687
  · exact B1493691
  · exact B1493695
  · exact B1493699
  · exact B1493703
  · exact B1493707
  · exact B1493711
  · exact B1493715
  · exact B1493719
  · exact B1493723
  · exact B1493727
  · exact B1493731
  · exact B1493735
  · exact B1493739
  · exact B1493743
  · exact B1493747
  · exact B1493751
  · exact B1493755
  · exact B1493759
  · exact B1493763
  · exact B1493767
  · exact B1493771
  · exact B1493775
  · exact B1493779
  · exact B1493783
  · exact B1493787
  · exact B1493791
  · exact B1493795
  · exact B1493799
  · exact B1493803
  · exact B1493807
  · exact B1493811
  · exact B1493815
  · exact B1493819
  · exact B1493823
  · exact B1493827
  · exact B1493831
  · exact B1493835
  · exact B1493839
  · exact B1493843
  · exact B1493847
  · exact B1493851
  · exact B1493855
  · exact B1493859
  · exact B1493863
  · exact B1493867
  · exact B1493871
  · exact B1493875
  · exact B1493879
  · exact B1493883
  · exact B1493887
  · exact B1493891
  · exact B1493895
  · exact B1493899
  · exact B1493903
  · exact B1493907
  · exact B1493911
  · exact B1493915
  · exact B1493919
  · exact B1493923
  · exact B1493927
  · exact B1493931
  · exact B1493935
  · exact B1493939
  · exact B1493943
  · exact B1493947
  · exact B1493951
  · exact B1493955
  · exact B1493959
  · exact B1493963
  · exact B1493967
  · exact B1493971
  · exact B1493975
  · exact B1493979
  · exact B1493983
  · exact B1493987
  · exact B1493991
  · exact B1493995
  · exact B1493999
  · exact B1494003
  · exact B1494007
  · exact B1494011
  · exact B1494015
  · exact B1494019
  · exact B1494023
  · exact B1494027
  · exact B1494031
  · exact B1494035
  · exact B1494039
  · exact B1494043
  · exact B1494047
  · exact B1494051
  · exact B1494055
  · exact B1494059
  · exact B1494063

theorem solution (m : ℕ) (hlo : 1492066 ≤ m) (hhi : m ≤ 1494066) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 373016 ≤ j := by omega
    have hj2 : j ≤ 373515 := by omega
    have hb : Blo 1492066 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
