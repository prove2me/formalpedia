-- Prove2me | solution 1 for syracuse_descends_range_1735068_1736568
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:32:50.629548+00:00
-- url     : https://prove2.me/submissions/7843e035-a03c-4bed-abe3-f65efcd301e6

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


theorem B5857541 : Blo 1735068 5857541 := bbase (se 4 (by rfl) ⟨549144, by rfl⟩ : syracuseStep 5857541 = 1098289) (by norm_num)
theorem B2113813 : Blo 1735068 2113813 := bbase (se 6 (by rfl) ⟨49542, by rfl⟩ : syracuseStep 2113813 = 99085) (by norm_num)
theorem B2196001 : Blo 1735068 2196001 := bbase (se 2 (by rfl) ⟨823500, by rfl⟩ : syracuseStep 2196001 = 1647001) (by norm_num)
theorem B7414325 : Blo 1735068 7414325 := bbase (se 5 (by rfl) ⟨347546, by rfl⟩ : syracuseStep 7414325 = 695093) (by norm_num)
theorem B6955637 : Blo 1735068 6955637 := bbase (se 5 (by rfl) ⟨326045, by rfl⟩ : syracuseStep 6955637 = 652091) (by norm_num)
theorem B2171525 : Blo 1735068 2171525 := bbase (se 4 (by rfl) ⟨203580, by rfl⟩ : syracuseStep 2171525 = 407161) (by norm_num)
theorem B4170413 : Blo 1735068 4170413 := bbase (se 3 (by rfl) ⟨781952, by rfl⟩ : syracuseStep 4170413 = 1563905) (by norm_num)
theorem B5857973 : Blo 1735068 5857973 := bbase (se 5 (by rfl) ⟨274592, by rfl⟩ : syracuseStep 5857973 = 549185) (by norm_num)
theorem B2196173 : Blo 1735068 2196173 := bbase (se 3 (by rfl) ⟨411782, by rfl⟩ : syracuseStep 2196173 = 823565) (by norm_num)
theorem B3293941 : Blo 1735068 3293941 := bbase (se 5 (by rfl) ⟨154403, by rfl⟩ : syracuseStep 3293941 = 308807) (by norm_num)
theorem B2196229 : Blo 1735068 2196229 := bbase (se 4 (by rfl) ⟨205896, by rfl⟩ : syracuseStep 2196229 = 411793) (by norm_num)
theorem B5563205 : Blo 1735068 5563205 := bbase (se 4 (by rfl) ⟨521550, by rfl⟩ : syracuseStep 5563205 = 1043101) (by norm_num)
theorem B2196325 : Blo 1735068 2196325 := bbase (se 4 (by rfl) ⟨205905, by rfl⟩ : syracuseStep 2196325 = 411811) (by norm_num)
theorem B3294101 : Blo 1735068 3294101 := bbase (se 6 (by rfl) ⟨77205, by rfl⟩ : syracuseStep 3294101 = 154411) (by norm_num)
theorem B4391941 : Blo 1735068 4391941 := bbase (se 4 (by rfl) ⟨411744, by rfl⟩ : syracuseStep 4391941 = 823489) (by norm_num)
theorem B2196497 : Blo 1735068 2196497 := bbase (se 2 (by rfl) ⟨823686, by rfl⟩ : syracuseStep 2196497 = 1647373) (by norm_num)
theorem B3294245 : Blo 1735068 3294245 := bbase (se 4 (by rfl) ⟨308835, by rfl⟩ : syracuseStep 3294245 = 617671) (by norm_num)
theorem B2196553 : Blo 1735068 2196553 := bbase (se 2 (by rfl) ⟨823707, by rfl⟩ : syracuseStep 2196553 = 1647415) (by norm_num)
theorem B3171421 : Blo 1735068 3171421 := bbase (se 3 (by rfl) ⟨594641, by rfl⟩ : syracuseStep 3171421 = 1189283) (by norm_num)
theorem B5858405 : Blo 1735068 5858405 := bbase (se 4 (by rfl) ⟨549225, by rfl⟩ : syracuseStep 5858405 = 1098451) (by norm_num)
theorem B4285541 : Blo 1735068 4285541 := bbase (se 4 (by rfl) ⟨401769, by rfl⟩ : syracuseStep 4285541 = 803539) (by norm_num)
theorem B4392053 : Blo 1735068 4392053 := bbase (se 5 (by rfl) ⟨205877, by rfl⟩ : syracuseStep 4392053 = 411755) (by norm_num)
theorem B2196649 : Blo 1735068 2196649 := bbase (se 2 (by rfl) ⟨823743, by rfl⟩ : syracuseStep 2196649 = 1647487) (by norm_num)
theorem B8791253 : Blo 1735068 8791253 := bbase (se 7 (by rfl) ⟨103022, by rfl⟩ : syracuseStep 8791253 = 206045) (by norm_num)
theorem B4228325 : Blo 1735068 4228325 := bbase (se 4 (by rfl) ⟨396405, by rfl⟩ : syracuseStep 4228325 = 792811) (by norm_num)
theorem B4392245 : Blo 1735068 4392245 := bbase (se 5 (by rfl) ⟨205886, by rfl⟩ : syracuseStep 4392245 = 411773) (by norm_num)
theorem B3294533 : Blo 1735068 3294533 := bbase (se 4 (by rfl) ⟨308862, by rfl⟩ : syracuseStep 3294533 = 617725) (by norm_num)
theorem B2196821 : Blo 1735068 2196821 := bbase (se 12 (by rfl) ⟨804, by rfl⟩ : syracuseStep 2196821 = 1609) (by norm_num)
theorem B2196877 : Blo 1735068 2196877 := bbase (se 3 (by rfl) ⟨411914, by rfl⟩ : syracuseStep 2196877 = 823829) (by norm_num)
theorem B4941253 : Blo 1735068 4941253 := bbase (se 4 (by rfl) ⟨463242, by rfl⟩ : syracuseStep 4941253 = 926485) (by norm_num)
theorem B1852885 : Blo 1735068 1852885 := bbase (se 7 (by rfl) ⟨21713, by rfl⟩ : syracuseStep 1852885 = 43427) (by norm_num)
theorem B3294685 : Blo 1735068 3294685 := bbase (se 3 (by rfl) ⟨617753, by rfl⟩ : syracuseStep 3294685 = 1235507) (by norm_num)
theorem B2196973 : Blo 1735068 2196973 := bbase (se 3 (by rfl) ⟨411932, by rfl⟩ : syracuseStep 2196973 = 823865) (by norm_num)
theorem B5858837 : Blo 1735068 5858837 := bbase (se 6 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 5858837 = 274633) (by norm_num)
theorem B7415333 : Blo 1735068 7415333 := bbase (se 4 (by rfl) ⟨695187, by rfl⟩ : syracuseStep 7415333 = 1390375) (by norm_num)
theorem B4392589 : Blo 1735068 4392589 := bbase (se 3 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 4392589 = 1647221) (by norm_num)
theorem B2197145 : Blo 1735068 2197145 := bbase (se 2 (by rfl) ⟨823929, by rfl⟩ : syracuseStep 2197145 = 1647859) (by norm_num)
theorem B2197201 : Blo 1735068 2197201 := bbase (se 2 (by rfl) ⟨823950, by rfl⟩ : syracuseStep 2197201 = 1647901) (by norm_num)
theorem B7038677 : Blo 1735068 7038677 := bbase (se 7 (by rfl) ⟨82484, by rfl⟩ : syracuseStep 7038677 = 164969) (by norm_num)
theorem B4392701 : Blo 1735068 4392701 := bbase (se 3 (by rfl) ⟨823631, by rfl⟩ : syracuseStep 4392701 = 1647263) (by norm_num)
theorem B3294989 : Blo 1735068 3294989 := bbase (se 3 (by rfl) ⟨617810, by rfl⟩ : syracuseStep 3294989 = 1235621) (by norm_num)
theorem B2197297 : Blo 1735068 2197297 := bbase (se 2 (by rfl) ⟨823986, by rfl⟩ : syracuseStep 2197297 = 1647973) (by norm_num)
theorem B1853329 : Blo 1735068 1853329 := bbase (se 2 (by rfl) ⟨694998, by rfl⟩ : syracuseStep 1853329 = 1389997) (by norm_num)
theorem B3008429 : Blo 1735068 3008429 := bbase (se 3 (by rfl) ⟨564080, by rfl⟩ : syracuseStep 3008429 = 1128161) (by norm_num)
theorem B4392893 : Blo 1735068 4392893 := bbase (se 3 (by rfl) ⟨823667, by rfl⟩ : syracuseStep 4392893 = 1647335) (by norm_num)
theorem B5859269 : Blo 1735068 5859269 := bbase (se 4 (by rfl) ⟨549306, by rfl⟩ : syracuseStep 5859269 = 1098613) (by norm_num)
theorem B1853389 : Blo 1735068 1853389 := bbase (se 3 (by rfl) ⟨347510, by rfl⟩ : syracuseStep 1853389 = 695021) (by norm_num)
theorem B2197469 : Blo 1735068 2197469 := bbase (se 3 (by rfl) ⟨412025, by rfl⟩ : syracuseStep 2197469 = 824051) (by norm_num)
theorem B2197525 : Blo 1735068 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B2197621 : Blo 1735068 2197621 := bbase (se 5 (by rfl) ⟨103013, by rfl⟩ : syracuseStep 2197621 = 206027) (by norm_num)
theorem B1951969 : Blo 1735068 1951969 := bbase (se 2 (by rfl) ⟨731988, by rfl⟩ : syracuseStep 1951969 = 1463977) (by norm_num)
theorem B1952005 : Blo 1735068 1952005 := bbase (se 4 (by rfl) ⟨183000, by rfl⟩ : syracuseStep 1952005 = 366001) (by norm_num)
theorem B1853705 : Blo 1735068 1853705 := bbase (se 2 (by rfl) ⟨695139, by rfl⟩ : syracuseStep 1853705 = 1390279) (by norm_num)
theorem B4393237 : Blo 1735068 4393237 := bbase (se 6 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 4393237 = 205933) (by norm_num)
theorem B2197793 : Blo 1735068 2197793 := bbase (se 2 (by rfl) ⟨824172, by rfl⟩ : syracuseStep 2197793 = 1648345) (by norm_num)
theorem B1952041 : Blo 1735068 1952041 := bbase (se 2 (by rfl) ⟨732015, by rfl⟩ : syracuseStep 1952041 = 1464031) (by norm_num)
theorem B1952077 : Blo 1735068 1952077 := bbase (se 3 (by rfl) ⟨366014, by rfl⟩ : syracuseStep 1952077 = 732029) (by norm_num)
theorem B2640205 : Blo 1735068 2640205 := bbase (se 3 (by rfl) ⟨495038, by rfl⟩ : syracuseStep 2640205 = 990077) (by norm_num)
theorem B1952113 : Blo 1735068 1952113 := bbase (se 2 (by rfl) ⟨732042, by rfl⟩ : syracuseStep 1952113 = 1464085) (by norm_num)
theorem B5859701 : Blo 1735068 5859701 := bbase (se 5 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 5859701 = 549347) (by norm_num)
theorem B4393349 : Blo 1735068 4393349 := bbase (se 4 (by rfl) ⟨411876, by rfl⟩ : syracuseStep 4393349 = 823753) (by norm_num)
theorem B1952149 : Blo 1735068 1952149 := bbase (se 6 (by rfl) ⟨45753, by rfl⟩ : syracuseStep 1952149 = 91507) (by norm_num)
theorem B1952185 : Blo 1735068 1952185 := bbase (se 2 (by rfl) ⟨732069, by rfl⟩ : syracuseStep 1952185 = 1464139) (by norm_num)
theorem B1952221 : Blo 1735068 1952221 := bbase (se 3 (by rfl) ⟨366041, by rfl⟩ : syracuseStep 1952221 = 732083) (by norm_num)
theorem B2968045 : Blo 1735068 2968045 := bbase (se 3 (by rfl) ⟨556508, by rfl⟩ : syracuseStep 2968045 = 1113017) (by norm_num)
theorem B3959293 : Blo 1735068 3959293 := bbase (se 3 (by rfl) ⟨742367, by rfl⟩ : syracuseStep 3959293 = 1484735) (by norm_num)
theorem B3295741 : Blo 1735068 3295741 := bbase (se 3 (by rfl) ⟨617951, by rfl⟩ : syracuseStep 3295741 = 1235903) (by norm_num)
theorem B1952257 : Blo 1735068 1952257 := bbase (se 2 (by rfl) ⟨732096, by rfl⟩ : syracuseStep 1952257 = 1464193) (by norm_num)
theorem B1952293 : Blo 1735068 1952293 := bbase (se 4 (by rfl) ⟨183027, by rfl⟩ : syracuseStep 1952293 = 366055) (by norm_num)
theorem B4393541 : Blo 1735068 4393541 := bbase (se 4 (by rfl) ⟨411894, by rfl⟩ : syracuseStep 4393541 = 823789) (by norm_num)
theorem B1952329 : Blo 1735068 1952329 := bbase (se 2 (by rfl) ⟨732123, by rfl⟩ : syracuseStep 1952329 = 1464247) (by norm_num)
theorem B1952365 : Blo 1735068 1952365 := bbase (se 3 (by rfl) ⟨366068, by rfl⟩ : syracuseStep 1952365 = 732137) (by norm_num)
theorem B3295885 : Blo 1735068 3295885 := bbase (se 3 (by rfl) ⟨617978, by rfl⟩ : syracuseStep 3295885 = 1235957) (by norm_num)
theorem B1952401 : Blo 1735068 1952401 := bbase (se 2 (by rfl) ⟨732150, by rfl⟩ : syracuseStep 1952401 = 1464301) (by norm_num)
theorem B5638805 : Blo 1735068 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B1952437 : Blo 1735068 1952437 := bbase (se 5 (by rfl) ⟨91520, by rfl⟩ : syracuseStep 1952437 = 183041) (by norm_num)
theorem B1854149 : Blo 1735068 1854149 := bbase (se 4 (by rfl) ⟨173826, by rfl⟩ : syracuseStep 1854149 = 347653) (by norm_num)
theorem B1952473 : Blo 1735068 1952473 := bbase (se 2 (by rfl) ⟨732177, by rfl⟩ : syracuseStep 1952473 = 1464355) (by norm_num)
theorem B4401917 : Blo 1735068 4401917 := bbase (se 3 (by rfl) ⟨825359, by rfl⟩ : syracuseStep 4401917 = 1650719) (by norm_num)
theorem B1952509 : Blo 1735068 1952509 := bbase (se 3 (by rfl) ⟨366095, by rfl⟩ : syracuseStep 1952509 = 732191) (by norm_num)
theorem B1854209 : Blo 1735068 1854209 := bbase (se 2 (by rfl) ⟨695328, by rfl⟩ : syracuseStep 1854209 = 1390657) (by norm_num)
theorem B1952545 : Blo 1735068 1952545 := bbase (se 2 (by rfl) ⟨732204, by rfl⟩ : syracuseStep 1952545 = 1464409) (by norm_num)
theorem B5860133 : Blo 1735068 5860133 := bbase (se 4 (by rfl) ⟨549387, by rfl⟩ : syracuseStep 5860133 = 1098775) (by norm_num)
theorem B3296045 : Blo 1735068 3296045 := bbase (se 3 (by rfl) ⟨618008, by rfl⟩ : syracuseStep 3296045 = 1236017) (by norm_num)
theorem B1878841 : Blo 1735068 1878841 := bbase (se 2 (by rfl) ⟨704565, by rfl⟩ : syracuseStep 1878841 = 1409131) (by norm_num)
theorem B1952581 : Blo 1735068 1952581 := bbase (se 4 (by rfl) ⟨183054, by rfl⟩ : syracuseStep 1952581 = 366109) (by norm_num)
theorem B1952617 : Blo 1735068 1952617 := bbase (se 2 (by rfl) ⟨732231, by rfl⟩ : syracuseStep 1952617 = 1464463) (by norm_num)
theorem B9882485 : Blo 1735068 9882485 := bbase (se 5 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 9882485 = 926483) (by norm_num)
theorem B1854337 : Blo 1735068 1854337 := bbase (se 2 (by rfl) ⟨695376, by rfl⟩ : syracuseStep 1854337 = 1390753) (by norm_num)
theorem B8784773 : Blo 1735068 8784773 := bbase (se 4 (by rfl) ⟨823572, by rfl⟩ : syracuseStep 8784773 = 1647145) (by norm_num)
theorem B1952653 : Blo 1735068 1952653 := bbase (se 3 (by rfl) ⟨366122, by rfl⟩ : syracuseStep 1952653 = 732245) (by norm_num)
theorem B13732757 : Blo 1735068 13732757 := bbase (se 6 (by rfl) ⟨321861, by rfl⟩ : syracuseStep 13732757 = 643723) (by norm_num)
theorem B4393885 : Blo 1735068 4393885 := bbase (se 3 (by rfl) ⟨823853, by rfl⟩ : syracuseStep 4393885 = 1647707) (by norm_num)
theorem B4942757 : Blo 1735068 4942757 := bbase (se 4 (by rfl) ⟨463383, by rfl⟩ : syracuseStep 4942757 = 926767) (by norm_num)
theorem B1878953 : Blo 1735068 1878953 := bbase (se 2 (by rfl) ⟨704607, by rfl⟩ : syracuseStep 1878953 = 1409215) (by norm_num)
theorem B1952689 : Blo 1735068 1952689 := bbase (se 2 (by rfl) ⟨732258, by rfl⟩ : syracuseStep 1952689 = 1464517) (by norm_num)
theorem B3296189 : Blo 1735068 3296189 := bbase (se 3 (by rfl) ⟨618035, by rfl⟩ : syracuseStep 3296189 = 1236071) (by norm_num)
theorem B6679493 : Blo 1735068 6679493 := bbase (se 4 (by rfl) ⟨626202, by rfl⟩ : syracuseStep 6679493 = 1252405) (by norm_num)
theorem B1952725 : Blo 1735068 1952725 := bbase (se 7 (by rfl) ⟨22883, by rfl⟩ : syracuseStep 1952725 = 45767) (by norm_num)
theorem B3705821 : Blo 1735068 3705821 := bbase (se 3 (by rfl) ⟨694841, by rfl⟩ : syracuseStep 3705821 = 1389683) (by norm_num)
theorem B1952761 : Blo 1735068 1952761 := bbase (se 2 (by rfl) ⟨732285, by rfl⟩ : syracuseStep 1952761 = 1464571) (by norm_num)
theorem B2780173 : Blo 1735068 2780173 := bbase (se 3 (by rfl) ⟨521282, by rfl⟩ : syracuseStep 2780173 = 1042565) (by norm_num)
theorem B4393997 : Blo 1735068 4393997 := bbase (se 3 (by rfl) ⟨823874, by rfl⟩ : syracuseStep 4393997 = 1647749) (by norm_num)
theorem B1952797 : Blo 1735068 1952797 := bbase (se 3 (by rfl) ⟨366149, by rfl⟩ : syracuseStep 1952797 = 732299) (by norm_num)
theorem B1952833 : Blo 1735068 1952833 := bbase (se 2 (by rfl) ⟨732312, by rfl⟩ : syracuseStep 1952833 = 1464625) (by norm_num)
theorem B1952869 : Blo 1735068 1952869 := bbase (se 4 (by rfl) ⟨183081, by rfl⟩ : syracuseStep 1952869 = 366163) (by norm_num)
theorem B1952905 : Blo 1735068 1952905 := bbase (se 2 (by rfl) ⟨732339, by rfl⟩ : syracuseStep 1952905 = 1464679) (by norm_num)
theorem B1952941 : Blo 1735068 1952941 := bbase (se 3 (by rfl) ⟨366176, by rfl⟩ : syracuseStep 1952941 = 732353) (by norm_num)
theorem B4394189 : Blo 1735068 4394189 := bbase (se 3 (by rfl) ⟨823910, by rfl⟩ : syracuseStep 4394189 = 1647821) (by norm_num)
theorem B1952977 : Blo 1735068 1952977 := bbase (se 2 (by rfl) ⟨732366, by rfl⟩ : syracuseStep 1952977 = 1464733) (by norm_num)
theorem B3706069 : Blo 1735068 3706069 := bbase (se 7 (by rfl) ⟨43430, by rfl⟩ : syracuseStep 3706069 = 86861) (by norm_num)
theorem B5860565 : Blo 1735068 5860565 := bbase (se 7 (by rfl) ⟨68678, by rfl⟩ : syracuseStep 5860565 = 137357) (by norm_num)
theorem B3296477 : Blo 1735068 3296477 := bbase (se 3 (by rfl) ⟨618089, by rfl⟩ : syracuseStep 3296477 = 1236179) (by norm_num)
theorem B1953013 : Blo 1735068 1953013 := bbase (se 5 (by rfl) ⟨91547, by rfl⟩ : syracuseStep 1953013 = 183095) (by norm_num)
theorem B7417109 : Blo 1735068 7417109 := bbase (se 6 (by rfl) ⟨173838, by rfl⟩ : syracuseStep 7417109 = 347677) (by norm_num)
theorem B1953049 : Blo 1735068 1953049 := bbase (se 2 (by rfl) ⟨732393, by rfl⟩ : syracuseStep 1953049 = 1464787) (by norm_num)
theorem B2346301 : Blo 1735068 2346301 := bbase (se 3 (by rfl) ⟨439931, by rfl⟩ : syracuseStep 2346301 = 879863) (by norm_num)
theorem B1953085 : Blo 1735068 1953085 := bbase (se 3 (by rfl) ⟨366203, by rfl⟩ : syracuseStep 1953085 = 732407) (by norm_num)
theorem B6589781 : Blo 1735068 6589781 := bbase (se 11 (by rfl) ⟨4826, by rfl⟩ : syracuseStep 6589781 = 9653) (by norm_num)
theorem B1953121 : Blo 1735068 1953121 := bbase (se 2 (by rfl) ⟨732420, by rfl⟩ : syracuseStep 1953121 = 1464841) (by norm_num)
theorem B2927981 : Blo 1735068 2927981 := bbase (se 3 (by rfl) ⟨548996, by rfl⟩ : syracuseStep 2927981 = 1097993) (by norm_num)
theorem B3296629 : Blo 1735068 3296629 := bbase (se 5 (by rfl) ⟨154529, by rfl⟩ : syracuseStep 3296629 = 309059) (by norm_num)
theorem B1953157 : Blo 1735068 1953157 := bbase (se 4 (by rfl) ⟨183108, by rfl⟩ : syracuseStep 1953157 = 366217) (by norm_num)
theorem B1953193 : Blo 1735068 1953193 := bbase (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) (by norm_num)
theorem B1953229 : Blo 1735068 1953229 := bbase (se 3 (by rfl) ⟨366230, by rfl⟩ : syracuseStep 1953229 = 732461) (by norm_num)
theorem B2928109 : Blo 1735068 2928109 := bbase (se 3 (by rfl) ⟨549020, by rfl⟩ : syracuseStep 2928109 = 1098041) (by norm_num)
theorem B1953265 : Blo 1735068 1953265 := bbase (se 2 (by rfl) ⟨732474, by rfl⟩ : syracuseStep 1953265 = 1464949) (by norm_num)
theorem B1953301 : Blo 1735068 1953301 := bbase (se 6 (by rfl) ⟨45780, by rfl⟩ : syracuseStep 1953301 = 91561) (by norm_num)
theorem B4394533 : Blo 1735068 4394533 := bbase (se 4 (by rfl) ⟨411987, by rfl⟩ : syracuseStep 4394533 = 823975) (by norm_num)
theorem B1953337 : Blo 1735068 1953337 := bbase (se 2 (by rfl) ⟨732501, by rfl⟩ : syracuseStep 1953337 = 1465003) (by norm_num)
theorem B2928197 : Blo 1735068 2928197 := bbase (se 4 (by rfl) ⟨274518, by rfl⟩ : syracuseStep 2928197 = 549037) (by norm_num)
theorem B1879633 : Blo 1735068 1879633 := bbase (se 2 (by rfl) ⟨704862, by rfl⟩ : syracuseStep 1879633 = 1409725) (by norm_num)
theorem B1953373 : Blo 1735068 1953373 := bbase (se 3 (by rfl) ⟨366257, by rfl⟩ : syracuseStep 1953373 = 732515) (by norm_num)
theorem B6590069 : Blo 1735068 6590069 := bbase (se 5 (by rfl) ⟨308909, by rfl⟩ : syracuseStep 6590069 = 617819) (by norm_num)
theorem B1953409 : Blo 1735068 1953409 := bbase (se 2 (by rfl) ⟨732528, by rfl⟩ : syracuseStep 1953409 = 1465057) (by norm_num)
theorem B4394645 : Blo 1735068 4394645 := bbase (se 6 (by rfl) ⟨102999, by rfl⟩ : syracuseStep 4394645 = 205999) (by norm_num)
theorem B1953445 : Blo 1735068 1953445 := bbase (se 4 (by rfl) ⟨183135, by rfl⟩ : syracuseStep 1953445 = 366271) (by norm_num)
theorem B13184693 : Blo 1735068 13184693 := bbase (se 5 (by rfl) ⟨618032, by rfl⟩ : syracuseStep 13184693 = 1236065) (by norm_num)
theorem B4452029 : Blo 1735068 4452029 := bbase (se 3 (by rfl) ⟨834755, by rfl⟩ : syracuseStep 4452029 = 1669511) (by norm_num)
theorem B2928325 : Blo 1735068 2928325 := bbase (se 4 (by rfl) ⟨274530, by rfl⟩ : syracuseStep 2928325 = 549061) (by norm_num)
theorem B1953481 : Blo 1735068 1953481 := bbase (se 2 (by rfl) ⟨732555, by rfl⟩ : syracuseStep 1953481 = 1465111) (by norm_num)
theorem B3706573 : Blo 1735068 3706573 := bbase (se 3 (by rfl) ⟨694982, by rfl⟩ : syracuseStep 3706573 = 1389965) (by norm_num)
theorem B2780885 : Blo 1735068 2780885 := bbase (se 7 (by rfl) ⟨32588, by rfl⟩ : syracuseStep 2780885 = 65177) (by norm_num)
theorem B8343269 : Blo 1735068 8343269 := bbase (se 4 (by rfl) ⟨782181, by rfl⟩ : syracuseStep 8343269 = 1564363) (by norm_num)
theorem B1953517 : Blo 1735068 1953517 := bbase (se 3 (by rfl) ⟨366284, by rfl⟩ : syracuseStep 1953517 = 732569) (by norm_num)
theorem B1953553 : Blo 1735068 1953553 := bbase (se 2 (by rfl) ⟨732582, by rfl⟩ : syracuseStep 1953553 = 1465165) (by norm_num)
theorem B2928413 : Blo 1735068 2928413 := bbase (se 3 (by rfl) ⟨549077, by rfl⟩ : syracuseStep 2928413 = 1098155) (by norm_num)
theorem B1953589 : Blo 1735068 1953589 := bbase (se 5 (by rfl) ⟨91574, by rfl⟩ : syracuseStep 1953589 = 183149) (by norm_num)
theorem B4394837 : Blo 1735068 4394837 := bbase (se 9 (by rfl) ⟨12875, by rfl⟩ : syracuseStep 4394837 = 25751) (by norm_num)
theorem B1953625 : Blo 1735068 1953625 := bbase (se 2 (by rfl) ⟨732609, by rfl⟩ : syracuseStep 1953625 = 1465219) (by norm_num)
theorem B3518333 : Blo 1735068 3518333 := bbase (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) (by norm_num)
theorem B2928541 : Blo 1735068 2928541 := bbase (se 3 (by rfl) ⟨549101, by rfl⟩ : syracuseStep 2928541 = 1098203) (by norm_num)
theorem B6254581 : Blo 1735068 6254581 := bbase (se 5 (by rfl) ⟨293183, by rfl⟩ : syracuseStep 6254581 = 586367) (by norm_num)
theorem B2928629 : Blo 1735068 2928629 := bbase (se 5 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 2928629 = 274559) (by norm_num)
theorem B13176917 : Blo 1735068 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B2928757 : Blo 1735068 2928757 := bbase (se 5 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 2928757 = 274571) (by norm_num)
theorem B8786069 : Blo 1735068 8786069 := bbase (se 6 (by rfl) ⟨205923, by rfl⟩ : syracuseStep 8786069 = 411847) (by norm_num)
theorem B4395181 : Blo 1735068 4395181 := bbase (se 3 (by rfl) ⟨824096, by rfl⟩ : syracuseStep 4395181 = 1648193) (by norm_num)
theorem B2928845 : Blo 1735068 2928845 := bbase (se 3 (by rfl) ⟨549158, by rfl⟩ : syracuseStep 2928845 = 1098317) (by norm_num)
theorem B2085149 : Blo 1735068 2085149 := bbase (se 3 (by rfl) ⟨390965, by rfl⟩ : syracuseStep 2085149 = 781931) (by norm_num)
theorem B4395293 : Blo 1735068 4395293 := bbase (se 3 (by rfl) ⟨824117, by rfl⟩ : syracuseStep 4395293 = 1648235) (by norm_num)
theorem B2928973 : Blo 1735068 2928973 := bbase (se 3 (by rfl) ⟨549182, by rfl⟩ : syracuseStep 2928973 = 1098365) (by norm_num)
theorem B2781557 : Blo 1735068 2781557 := bbase (se 5 (by rfl) ⟨130385, by rfl⟩ : syracuseStep 2781557 = 260771) (by norm_num)
theorem B3567997 : Blo 1735068 3567997 := bbase (se 3 (by rfl) ⟨668999, by rfl⟩ : syracuseStep 3567997 = 1337999) (by norm_num)
theorem B2929061 : Blo 1735068 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B11121077 : Blo 1735068 11121077 := bbase (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) (by norm_num)
theorem B4944341 : Blo 1735068 4944341 := bbase (se 7 (by rfl) ⟨57941, by rfl⟩ : syracuseStep 4944341 = 115883) (by norm_num)
theorem B3903965 : Blo 1735068 3903965 := bbase (se 3 (by rfl) ⟨731993, by rfl⟩ : syracuseStep 3903965 = 1463987) (by norm_num)
theorem B4395485 : Blo 1735068 4395485 := bbase (se 3 (by rfl) ⟨824153, by rfl⟩ : syracuseStep 4395485 = 1648307) (by norm_num)
theorem B3518981 : Blo 1735068 3518981 := bbase (se 4 (by rfl) ⟨329904, by rfl⟩ : syracuseStep 3518981 = 659809) (by norm_num)
theorem B2929189 : Blo 1735068 2929189 := bbase (se 4 (by rfl) ⟨274611, by rfl⟩ : syracuseStep 2929189 = 549223) (by norm_num)
theorem B3904037 : Blo 1735068 3904037 := bbase (se 4 (by rfl) ⟨366003, by rfl⟩ : syracuseStep 3904037 = 732007) (by norm_num)
theorem B3707461 : Blo 1735068 3707461 := bbase (se 4 (by rfl) ⟨347574, by rfl⟩ : syracuseStep 3707461 = 695149) (by norm_num)
theorem B3904109 : Blo 1735068 3904109 := bbase (se 3 (by rfl) ⟨732020, by rfl⟩ : syracuseStep 3904109 = 1464041) (by norm_num)
theorem B2929277 : Blo 1735068 2929277 := bbase (se 3 (by rfl) ⟨549239, by rfl⟩ : syracuseStep 2929277 = 1098479) (by norm_num)
theorem B2257573 : Blo 1735068 2257573 := bbase (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) (by norm_num)
theorem B3904181 : Blo 1735068 3904181 := bbase (se 5 (by rfl) ⟨183008, by rfl⟩ : syracuseStep 3904181 = 366017) (by norm_num)
theorem B3756773 : Blo 1735068 3756773 := bbase (se 4 (by rfl) ⟨352197, by rfl⟩ : syracuseStep 3756773 = 704395) (by norm_num)
theorem B3904253 : Blo 1735068 3904253 := bbase (se 3 (by rfl) ⟨732047, by rfl⟩ : syracuseStep 3904253 = 1464095) (by norm_num)
theorem B2929405 : Blo 1735068 2929405 := bbase (se 3 (by rfl) ⟨549263, by rfl⟩ : syracuseStep 2929405 = 1098527) (by norm_num)
theorem B6591253 : Blo 1735068 6591253 := bbase (se 6 (by rfl) ⟨154482, by rfl⟩ : syracuseStep 6591253 = 308965) (by norm_num)
theorem B3904325 : Blo 1735068 3904325 := bbase (se 4 (by rfl) ⟨366030, by rfl⟩ : syracuseStep 3904325 = 732061) (by norm_num)
theorem B2929493 : Blo 1735068 2929493 := bbase (se 9 (by rfl) ⟨8582, by rfl⟩ : syracuseStep 2929493 = 17165) (by norm_num)
theorem B2085745 : Blo 1735068 2085745 := bbase (se 2 (by rfl) ⟨782154, by rfl⟩ : syracuseStep 2085745 = 1564309) (by norm_num)
theorem B3904397 : Blo 1735068 3904397 := bbase (se 3 (by rfl) ⟨732074, by rfl⟩ : syracuseStep 3904397 = 1464149) (by norm_num)
theorem B1930133 : Blo 1735068 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B2085841 : Blo 1735068 2085841 := bbase (se 2 (by rfl) ⟨782190, by rfl⟩ : syracuseStep 2085841 = 1564381) (by norm_num)
theorem B3904469 : Blo 1735068 3904469 := bbase (se 7 (by rfl) ⟨45755, by rfl⟩ : syracuseStep 3904469 = 91511) (by norm_num)
theorem B2929621 : Blo 1735068 2929621 := bbase (se 7 (by rfl) ⟨34331, by rfl⟩ : syracuseStep 2929621 = 68663) (by norm_num)
theorem B4453381 : Blo 1735068 4453381 := bbase (se 4 (by rfl) ⟨417504, by rfl⟩ : syracuseStep 4453381 = 835009) (by norm_num)
theorem B9884693 : Blo 1735068 9884693 := bbase (se 6 (by rfl) ⟨231672, by rfl⟩ : syracuseStep 9884693 = 463345) (by norm_num)
theorem B3904541 : Blo 1735068 3904541 := bbase (se 3 (by rfl) ⟨732101, by rfl⟩ : syracuseStep 3904541 = 1464203) (by norm_num)
theorem B2929709 : Blo 1735068 2929709 := bbase (se 3 (by rfl) ⟨549320, by rfl⟩ : syracuseStep 2929709 = 1098641) (by norm_num)
theorem B3707957 : Blo 1735068 3707957 := bbase (se 5 (by rfl) ⟨173810, by rfl⟩ : syracuseStep 3707957 = 347621) (by norm_num)
theorem B6591557 : Blo 1735068 6591557 := bbase (se 4 (by rfl) ⟨617958, by rfl⟩ : syracuseStep 6591557 = 1235917) (by norm_num)
theorem B3904613 : Blo 1735068 3904613 := bbase (se 4 (by rfl) ⟨366057, by rfl⟩ : syracuseStep 3904613 = 732115) (by norm_num)
theorem B4945013 : Blo 1735068 4945013 := bbase (se 5 (by rfl) ⟨231797, by rfl⟩ : syracuseStep 4945013 = 463595) (by norm_num)
theorem B2675837 : Blo 1735068 2675837 := bbase (se 3 (by rfl) ⟨501719, by rfl⟩ : syracuseStep 2675837 = 1003439) (by norm_num)
theorem B2471077 : Blo 1735068 2471077 := bbase (se 4 (by rfl) ⟨231663, by rfl⟩ : syracuseStep 2471077 = 463327) (by norm_num)
theorem B3904685 : Blo 1735068 3904685 := bbase (se 3 (by rfl) ⟨732128, by rfl⟩ : syracuseStep 3904685 = 1464257) (by norm_num)
theorem B2929837 : Blo 1735068 2929837 := bbase (se 3 (by rfl) ⟨549344, by rfl⟩ : syracuseStep 2929837 = 1098689) (by norm_num)
theorem B3904757 : Blo 1735068 3904757 := bbase (se 5 (by rfl) ⟨183035, by rfl⟩ : syracuseStep 3904757 = 366071) (by norm_num)
theorem B2929925 : Blo 1735068 2929925 := bbase (se 4 (by rfl) ⟨274680, by rfl⟩ : syracuseStep 2929925 = 549361) (by norm_num)
theorem B16676117 : Blo 1735068 16676117 := bbase (se 6 (by rfl) ⟨390846, by rfl⟩ : syracuseStep 16676117 = 781693) (by norm_num)
theorem B3904829 : Blo 1735068 3904829 := bbase (se 3 (by rfl) ⟨732155, by rfl⟩ : syracuseStep 3904829 = 1464311) (by norm_num)
theorem B5715317 : Blo 1735068 5715317 := bbase (se 5 (by rfl) ⟨267905, by rfl⟩ : syracuseStep 5715317 = 535811) (by norm_num)
theorem B3904901 : Blo 1735068 3904901 := bbase (se 4 (by rfl) ⟨366084, by rfl⟩ : syracuseStep 3904901 = 732169) (by norm_num)
theorem B2930053 : Blo 1735068 2930053 := bbase (se 4 (by rfl) ⟨274692, by rfl⟩ : syracuseStep 2930053 = 549385) (by norm_num)
theorem B14824853 : Blo 1735068 14824853 := bbase (se 6 (by rfl) ⟨347457, by rfl⟩ : syracuseStep 14824853 = 694915) (by norm_num)
theorem B8787365 : Blo 1735068 8787365 := bbase (se 4 (by rfl) ⟨823815, by rfl⟩ : syracuseStep 8787365 = 1647631) (by norm_num)
theorem B3904973 : Blo 1735068 3904973 := bbase (se 3 (by rfl) ⟨732182, by rfl⟩ : syracuseStep 3904973 = 1464365) (by norm_num)
theorem B2930141 : Blo 1735068 2930141 := bbase (se 3 (by rfl) ⟨549401, by rfl⟩ : syracuseStep 2930141 = 1098803) (by norm_num)
theorem B2471413 : Blo 1735068 2471413 := bbase (se 5 (by rfl) ⟨115847, by rfl⟩ : syracuseStep 2471413 = 231695) (by norm_num)
theorem B3905045 : Blo 1735068 3905045 := bbase (se 6 (by rfl) ⟨91524, by rfl⟩ : syracuseStep 3905045 = 183049) (by norm_num)
theorem B3905117 : Blo 1735068 3905117 := bbase (se 3 (by rfl) ⟨732209, by rfl⟩ : syracuseStep 3905117 = 1464419) (by norm_num)
theorem B2930269 : Blo 1735068 2930269 := bbase (se 3 (by rfl) ⟨549425, by rfl⟩ : syracuseStep 2930269 = 1098851) (by norm_num)
theorem B2602613 : Blo 1735068 2602613 := bbase (se 5 (by rfl) ⟨121997, by rfl⟩ : syracuseStep 2602613 = 243995) (by norm_num)
theorem B7411333 : Blo 1735068 7411333 := bbase (se 4 (by rfl) ⟨694812, by rfl⟩ : syracuseStep 7411333 = 1389625) (by norm_num)
theorem B3126917 : Blo 1735068 3126917 := bbase (se 4 (by rfl) ⟨293148, by rfl⟩ : syracuseStep 3126917 = 586297) (by norm_num)
theorem B2602637 : Blo 1735068 2602637 := bbase (se 3 (by rfl) ⟨487994, by rfl⟩ : syracuseStep 2602637 = 975989) (by norm_num)
theorem B2602661 : Blo 1735068 2602661 := bbase (se 4 (by rfl) ⟨243999, by rfl⟩ : syracuseStep 2602661 = 487999) (by norm_num)
theorem B3905189 : Blo 1735068 3905189 := bbase (se 4 (by rfl) ⟨366111, by rfl⟩ : syracuseStep 3905189 = 732223) (by norm_num)
theorem B4691621 : Blo 1735068 4691621 := bbase (se 4 (by rfl) ⟨439839, by rfl⟩ : syracuseStep 4691621 = 879679) (by norm_num)
theorem B2930357 : Blo 1735068 2930357 := bbase (se 5 (by rfl) ⟨137360, by rfl⟩ : syracuseStep 2930357 = 274721) (by norm_num)
theorem B2602685 : Blo 1735068 2602685 := bbase (se 3 (by rfl) ⟨488003, by rfl⟩ : syracuseStep 2602685 = 976007) (by norm_num)
theorem B2471629 : Blo 1735068 2471629 := bbase (se 3 (by rfl) ⟨463430, by rfl⟩ : syracuseStep 2471629 = 926861) (by norm_num)
theorem B2602709 : Blo 1735068 2602709 := bbase (se 7 (by rfl) ⟨30500, by rfl⟩ : syracuseStep 2602709 = 61001) (by norm_num)
theorem B21108437 : Blo 1735068 21108437 := bbase (se 7 (by rfl) ⟨247364, by rfl⟩ : syracuseStep 21108437 = 494729) (by norm_num)
theorem B2602733 : Blo 1735068 2602733 := bbase (se 3 (by rfl) ⟨488012, by rfl⟩ : syracuseStep 2602733 = 976025) (by norm_num)
theorem B3905261 : Blo 1735068 3905261 := bbase (se 3 (by rfl) ⟨732236, by rfl⟩ : syracuseStep 3905261 = 1464473) (by norm_num)
theorem B2602757 : Blo 1735068 2602757 := bbase (se 4 (by rfl) ⟨244008, by rfl⟩ : syracuseStep 2602757 = 488017) (by norm_num)
theorem B4888325 : Blo 1735068 4888325 := bbase (se 4 (by rfl) ⟨458280, by rfl⟩ : syracuseStep 4888325 = 916561) (by norm_num)
theorem B2602781 : Blo 1735068 2602781 := bbase (se 3 (by rfl) ⟨488021, by rfl⟩ : syracuseStep 2602781 = 976043) (by norm_num)
theorem B2602805 : Blo 1735068 2602805 := bbase (se 5 (by rfl) ⟨122006, by rfl⟩ : syracuseStep 2602805 = 244013) (by norm_num)
theorem B3905333 : Blo 1735068 3905333 := bbase (se 5 (by rfl) ⟨183062, by rfl⟩ : syracuseStep 3905333 = 366125) (by norm_num)
theorem B1783625 : Blo 1735068 1783625 := bbase (se 2 (by rfl) ⟨668859, by rfl⟩ : syracuseStep 1783625 = 1337719) (by norm_num)
theorem B2602829 : Blo 1735068 2602829 := bbase (se 3 (by rfl) ⟨488030, by rfl⟩ : syracuseStep 2602829 = 976061) (by norm_num)
theorem B15841109 : Blo 1735068 15841109 := bbase (se 9 (by rfl) ⟨46409, by rfl⟩ : syracuseStep 15841109 = 92819) (by norm_num)
theorem B3127133 : Blo 1735068 3127133 := bbase (se 3 (by rfl) ⟨586337, by rfl⟩ : syracuseStep 3127133 = 1172675) (by norm_num)
theorem B2602853 : Blo 1735068 2602853 := bbase (se 4 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 2602853 = 488035) (by norm_num)
theorem B2602877 : Blo 1735068 2602877 := bbase (se 3 (by rfl) ⟨488039, by rfl⟩ : syracuseStep 2602877 = 976079) (by norm_num)
theorem B3905405 : Blo 1735068 3905405 := bbase (se 3 (by rfl) ⟨732263, by rfl⟩ : syracuseStep 3905405 = 1464527) (by norm_num)
theorem B3757957 : Blo 1735068 3757957 := bbase (se 4 (by rfl) ⟨352308, by rfl⟩ : syracuseStep 3757957 = 704617) (by norm_num)
theorem B2602901 : Blo 1735068 2602901 := bbase (se 6 (by rfl) ⟨61005, by rfl⟩ : syracuseStep 2602901 = 122011) (by norm_num)
theorem B3127205 : Blo 1735068 3127205 := bbase (se 4 (by rfl) ⟨293175, by rfl⟩ : syracuseStep 3127205 = 586351) (by norm_num)
theorem B2602925 : Blo 1735068 2602925 := bbase (se 3 (by rfl) ⟨488048, by rfl⟩ : syracuseStep 2602925 = 976097) (by norm_num)
theorem B3708845 : Blo 1735068 3708845 := bbase (se 3 (by rfl) ⟨695408, by rfl⟩ : syracuseStep 3708845 = 1390817) (by norm_num)
theorem B2602949 : Blo 1735068 2602949 := bbase (se 4 (by rfl) ⟨244026, by rfl⟩ : syracuseStep 2602949 = 488053) (by norm_num)
theorem B3905477 : Blo 1735068 3905477 := bbase (se 4 (by rfl) ⟨366138, by rfl⟩ : syracuseStep 3905477 = 732277) (by norm_num)
theorem B2602973 : Blo 1735068 2602973 := bbase (se 3 (by rfl) ⟨488057, by rfl⟩ : syracuseStep 2602973 = 976115) (by norm_num)
theorem B3340253 : Blo 1735068 3340253 := bbase (se 3 (by rfl) ⟨626297, by rfl⟩ : syracuseStep 3340253 = 1252595) (by norm_num)
theorem B2602997 : Blo 1735068 2602997 := bbase (se 5 (by rfl) ⟨122015, by rfl⟩ : syracuseStep 2602997 = 244031) (by norm_num)
theorem B3127285 : Blo 1735068 3127285 := bbase (se 5 (by rfl) ⟨146591, by rfl⟩ : syracuseStep 3127285 = 293183) (by norm_num)
theorem B2603021 : Blo 1735068 2603021 := bbase (se 3 (by rfl) ⟨488066, by rfl⟩ : syracuseStep 2603021 = 976133) (by norm_num)
theorem B3905549 : Blo 1735068 3905549 := bbase (se 3 (by rfl) ⟨732290, by rfl⟩ : syracuseStep 3905549 = 1464581) (by norm_num)
theorem B2603045 : Blo 1735068 2603045 := bbase (se 4 (by rfl) ⟨244035, by rfl⟩ : syracuseStep 2603045 = 488071) (by norm_num)
theorem B3127349 : Blo 1735068 3127349 := bbase (se 5 (by rfl) ⟨146594, by rfl⟩ : syracuseStep 3127349 = 293189) (by norm_num)
theorem B2603069 : Blo 1735068 2603069 := bbase (se 3 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 2603069 = 976151) (by norm_num)
theorem B2472005 : Blo 1735068 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B2603093 : Blo 1735068 2603093 := bbase (se 8 (by rfl) ⟨15252, by rfl⟩ : syracuseStep 2603093 = 30505) (by norm_num)
theorem B3905621 : Blo 1735068 3905621 := bbase (se 8 (by rfl) ⟨22884, by rfl⟩ : syracuseStep 3905621 = 45769) (by norm_num)
theorem B2603117 : Blo 1735068 2603117 := bbase (se 3 (by rfl) ⟨488084, by rfl⟩ : syracuseStep 2603117 = 976169) (by norm_num)
theorem B2603141 : Blo 1735068 2603141 := bbase (se 4 (by rfl) ⟨244044, by rfl⟩ : syracuseStep 2603141 = 488089) (by norm_num)
theorem B2603165 : Blo 1735068 2603165 := bbase (se 3 (by rfl) ⟨488093, by rfl⟩ : syracuseStep 2603165 = 976187) (by norm_num)
theorem B3905693 : Blo 1735068 3905693 := bbase (se 3 (by rfl) ⟨732317, by rfl⟩ : syracuseStep 3905693 = 1464635) (by norm_num)
theorem B2603189 : Blo 1735068 2603189 := bbase (se 5 (by rfl) ⟨122024, by rfl⟩ : syracuseStep 2603189 = 244049) (by norm_num)
theorem B2603213 : Blo 1735068 2603213 := bbase (se 3 (by rfl) ⟨488102, by rfl⟩ : syracuseStep 2603213 = 976205) (by norm_num)
theorem B2603237 : Blo 1735068 2603237 := bbase (se 4 (by rfl) ⟨244053, by rfl⟩ : syracuseStep 2603237 = 488107) (by norm_num)
theorem B3905765 : Blo 1735068 3905765 := bbase (se 4 (by rfl) ⟨366165, by rfl⟩ : syracuseStep 3905765 = 732331) (by norm_num)
theorem B2603261 : Blo 1735068 2603261 := bbase (se 3 (by rfl) ⟨488111, by rfl⟩ : syracuseStep 2603261 = 976223) (by norm_num)
theorem B2603285 : Blo 1735068 2603285 := bbase (se 6 (by rfl) ⟨61014, by rfl⟩ : syracuseStep 2603285 = 122029) (by norm_num)
theorem B2603309 : Blo 1735068 2603309 := bbase (se 3 (by rfl) ⟨488120, by rfl⟩ : syracuseStep 2603309 = 976241) (by norm_num)
theorem B3905837 : Blo 1735068 3905837 := bbase (se 3 (by rfl) ⟨732344, by rfl⟩ : syracuseStep 3905837 = 1464689) (by norm_num)
theorem B4692277 : Blo 1735068 4692277 := bbase (se 5 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 4692277 = 439901) (by norm_num)
theorem B2603333 : Blo 1735068 2603333 := bbase (se 4 (by rfl) ⟨244062, by rfl⟩ : syracuseStep 2603333 = 488125) (by norm_num)
theorem B3127637 : Blo 1735068 3127637 := bbase (se 10 (by rfl) ⟨4581, by rfl⟩ : syracuseStep 3127637 = 9163) (by norm_num)
theorem B2603357 : Blo 1735068 2603357 := bbase (se 3 (by rfl) ⟨488129, by rfl⟩ : syracuseStep 2603357 = 976259) (by norm_num)
theorem B2603381 : Blo 1735068 2603381 := bbase (se 5 (by rfl) ⟨122033, by rfl⟩ : syracuseStep 2603381 = 244067) (by norm_num)
theorem B3905909 : Blo 1735068 3905909 := bbase (se 5 (by rfl) ⟨183089, by rfl⟩ : syracuseStep 3905909 = 366179) (by norm_num)
theorem B2603405 : Blo 1735068 2603405 := bbase (se 3 (by rfl) ⟨488138, by rfl⟩ : syracuseStep 2603405 = 976277) (by norm_num)
theorem B1759649 : Blo 1735068 1759649 := bbase (se 2 (by rfl) ⟨659868, by rfl⟩ : syracuseStep 1759649 = 1319737) (by norm_num)
theorem B2603429 : Blo 1735068 2603429 := bbase (se 4 (by rfl) ⟨244071, by rfl⟩ : syracuseStep 2603429 = 488143) (by norm_num)
theorem B2603453 : Blo 1735068 2603453 := bbase (se 3 (by rfl) ⟨488147, by rfl⟩ : syracuseStep 2603453 = 976295) (by norm_num)
theorem B3905981 : Blo 1735068 3905981 := bbase (se 3 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 3905981 = 1464743) (by norm_num)
theorem B2603477 : Blo 1735068 2603477 := bbase (se 7 (by rfl) ⟨30509, by rfl⟩ : syracuseStep 2603477 = 61019) (by norm_num)
theorem B2603501 : Blo 1735068 2603501 := bbase (se 3 (by rfl) ⟨488156, by rfl⟩ : syracuseStep 2603501 = 976313) (by norm_num)
theorem B2603525 : Blo 1735068 2603525 := bbase (se 4 (by rfl) ⟨244080, by rfl⟩ : syracuseStep 2603525 = 488161) (by norm_num)
theorem B3906053 : Blo 1735068 3906053 := bbase (se 4 (by rfl) ⟨366192, by rfl⟩ : syracuseStep 3906053 = 732385) (by norm_num)
theorem B2603549 : Blo 1735068 2603549 := bbase (se 3 (by rfl) ⟨488165, by rfl⟩ : syracuseStep 2603549 = 976331) (by norm_num)
theorem B2603573 : Blo 1735068 2603573 := bbase (se 5 (by rfl) ⟨122042, by rfl⟩ : syracuseStep 2603573 = 244085) (by norm_num)
theorem B2603597 : Blo 1735068 2603597 := bbase (se 3 (by rfl) ⟨488174, by rfl⟩ : syracuseStep 2603597 = 976349) (by norm_num)
theorem B3906125 : Blo 1735068 3906125 := bbase (se 3 (by rfl) ⟨732398, by rfl⟩ : syracuseStep 3906125 = 1464797) (by norm_num)
theorem B2603621 : Blo 1735068 2603621 := bbase (se 4 (by rfl) ⟨244089, by rfl⟩ : syracuseStep 2603621 = 488179) (by norm_num)
theorem B5560949 : Blo 1735068 5560949 := bbase (se 5 (by rfl) ⟨260669, by rfl⟩ : syracuseStep 5560949 = 521339) (by norm_num)
theorem B2603645 : Blo 1735068 2603645 := bbase (se 3 (by rfl) ⟨488183, by rfl⟩ : syracuseStep 2603645 = 976367) (by norm_num)
theorem B2603669 : Blo 1735068 2603669 := bbase (se 6 (by rfl) ⟨61023, by rfl⟩ : syracuseStep 2603669 = 122047) (by norm_num)
theorem B3906197 : Blo 1735068 3906197 := bbase (se 6 (by rfl) ⟨91551, by rfl⟩ : syracuseStep 3906197 = 183103) (by norm_num)
theorem B2603693 : Blo 1735068 2603693 := bbase (se 3 (by rfl) ⟨488192, by rfl⟩ : syracuseStep 2603693 = 976385) (by norm_num)
theorem B8788661 : Blo 1735068 8788661 := bbase (se 5 (by rfl) ⟨411968, by rfl⟩ : syracuseStep 8788661 = 823937) (by norm_num)
theorem B2603717 : Blo 1735068 2603717 := bbase (se 4 (by rfl) ⟨244098, by rfl⟩ : syracuseStep 2603717 = 488197) (by norm_num)
theorem B2603741 : Blo 1735068 2603741 := bbase (se 3 (by rfl) ⟨488201, by rfl⟩ : syracuseStep 2603741 = 976403) (by norm_num)
theorem B3906269 : Blo 1735068 3906269 := bbase (se 3 (by rfl) ⟨732425, by rfl⟩ : syracuseStep 3906269 = 1464851) (by norm_num)
theorem B2603765 : Blo 1735068 2603765 := bbase (se 5 (by rfl) ⟨122051, by rfl⟩ : syracuseStep 2603765 = 244103) (by norm_num)
theorem B2603789 : Blo 1735068 2603789 := bbase (se 3 (by rfl) ⟨488210, by rfl⟩ : syracuseStep 2603789 = 976421) (by norm_num)
theorem B2603813 : Blo 1735068 2603813 := bbase (se 4 (by rfl) ⟨244107, by rfl⟩ : syracuseStep 2603813 = 488215) (by norm_num)
theorem B3906341 : Blo 1735068 3906341 := bbase (se 4 (by rfl) ⟨366219, by rfl⟩ : syracuseStep 3906341 = 732439) (by norm_num)
theorem B6683429 : Blo 1735068 6683429 := bbase (se 4 (by rfl) ⟨626571, by rfl⟩ : syracuseStep 6683429 = 1253143) (by norm_num)
theorem B2603837 : Blo 1735068 2603837 := bbase (se 3 (by rfl) ⟨488219, by rfl⟩ : syracuseStep 2603837 = 976439) (by norm_num)
theorem B2603861 : Blo 1735068 2603861 := bbase (se 9 (by rfl) ⟨7628, by rfl⟩ : syracuseStep 2603861 = 15257) (by norm_num)
theorem B2603885 : Blo 1735068 2603885 := bbase (se 3 (by rfl) ⟨488228, by rfl⟩ : syracuseStep 2603885 = 976457) (by norm_num)
theorem B3906413 : Blo 1735068 3906413 := bbase (se 3 (by rfl) ⟨732452, by rfl⟩ : syracuseStep 3906413 = 1464905) (by norm_num)
theorem B2603909 : Blo 1735068 2603909 := bbase (se 4 (by rfl) ⟨244116, by rfl⟩ : syracuseStep 2603909 = 488233) (by norm_num)
theorem B2603933 : Blo 1735068 2603933 := bbase (se 3 (by rfl) ⟨488237, by rfl⟩ : syracuseStep 2603933 = 976475) (by norm_num)
theorem B2603957 : Blo 1735068 2603957 := bbase (se 5 (by rfl) ⟨122060, by rfl⟩ : syracuseStep 2603957 = 244121) (by norm_num)
theorem B3906485 : Blo 1735068 3906485 := bbase (se 5 (by rfl) ⟨183116, by rfl⟩ : syracuseStep 3906485 = 366233) (by norm_num)
theorem B2603981 : Blo 1735068 2603981 := bbase (se 3 (by rfl) ⟨488246, by rfl⟩ : syracuseStep 2603981 = 976493) (by norm_num)
theorem B2604005 : Blo 1735068 2604005 := bbase (se 4 (by rfl) ⟨244125, by rfl⟩ : syracuseStep 2604005 = 488251) (by norm_num)
theorem B5856245 : Blo 1735068 5856245 := bbase (se 5 (by rfl) ⟨274511, by rfl⟩ : syracuseStep 5856245 = 549023) (by norm_num)
theorem B2604029 : Blo 1735068 2604029 := bbase (se 3 (by rfl) ⟨488255, by rfl⟩ : syracuseStep 2604029 = 976511) (by norm_num)
theorem B3906557 : Blo 1735068 3906557 := bbase (se 3 (by rfl) ⟨732479, by rfl⟩ : syracuseStep 3906557 = 1464959) (by norm_num)
theorem B2604053 : Blo 1735068 2604053 := bbase (se 6 (by rfl) ⟨61032, by rfl⟩ : syracuseStep 2604053 = 122065) (by norm_num)
theorem B2227225 : Blo 1735068 2227225 := bbase (se 2 (by rfl) ⟨835209, by rfl⟩ : syracuseStep 2227225 = 1670419) (by norm_num)
theorem B2604077 : Blo 1735068 2604077 := bbase (se 3 (by rfl) ⟨488264, by rfl⟩ : syracuseStep 2604077 = 976529) (by norm_num)
theorem B2604101 : Blo 1735068 2604101 := bbase (se 4 (by rfl) ⟨244134, by rfl⟩ : syracuseStep 2604101 = 488269) (by norm_num)
theorem B3906629 : Blo 1735068 3906629 := bbase (se 4 (by rfl) ⟨366246, by rfl⟩ : syracuseStep 3906629 = 732493) (by norm_num)
theorem B2604125 : Blo 1735068 2604125 := bbase (se 3 (by rfl) ⟨488273, by rfl⟩ : syracuseStep 2604125 = 976547) (by norm_num)
theorem B2604149 : Blo 1735068 2604149 := bbase (se 5 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 2604149 = 244139) (by norm_num)
theorem B2604173 : Blo 1735068 2604173 := bbase (se 3 (by rfl) ⟨488282, by rfl⟩ : syracuseStep 2604173 = 976565) (by norm_num)
theorem B3906701 : Blo 1735068 3906701 := bbase (se 3 (by rfl) ⟨732506, by rfl⟩ : syracuseStep 3906701 = 1465013) (by norm_num)
theorem B2604197 : Blo 1735068 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B2604221 : Blo 1735068 2604221 := bbase (se 3 (by rfl) ⟨488291, by rfl⟩ : syracuseStep 2604221 = 976583) (by norm_num)
theorem B2604245 : Blo 1735068 2604245 := bbase (se 7 (by rfl) ⟨30518, by rfl⟩ : syracuseStep 2604245 = 61037) (by norm_num)
theorem B3906773 : Blo 1735068 3906773 := bbase (se 7 (by rfl) ⟨45782, by rfl⟩ : syracuseStep 3906773 = 91565) (by norm_num)
theorem B2604269 : Blo 1735068 2604269 := bbase (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) (by norm_num)
theorem B2604293 : Blo 1735068 2604293 := bbase (se 4 (by rfl) ⟨244152, by rfl⟩ : syracuseStep 2604293 = 488305) (by norm_num)
theorem B2604317 : Blo 1735068 2604317 := bbase (se 3 (by rfl) ⟨488309, by rfl⟩ : syracuseStep 2604317 = 976619) (by norm_num)
theorem B3906845 : Blo 1735068 3906845 := bbase (se 3 (by rfl) ⟨732533, by rfl⟩ : syracuseStep 3906845 = 1465067) (by norm_num)
theorem B2604341 : Blo 1735068 2604341 := bbase (se 5 (by rfl) ⟨122078, by rfl⟩ : syracuseStep 2604341 = 244157) (by norm_num)
theorem B2604365 : Blo 1735068 2604365 := bbase (se 3 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 2604365 = 976637) (by norm_num)
theorem B2604389 : Blo 1735068 2604389 := bbase (se 4 (by rfl) ⟨244161, by rfl⟩ : syracuseStep 2604389 = 488323) (by norm_num)
theorem B3906917 : Blo 1735068 3906917 := bbase (se 4 (by rfl) ⟨366273, by rfl⟩ : syracuseStep 3906917 = 732547) (by norm_num)
theorem B2604413 : Blo 1735068 2604413 := bbase (se 3 (by rfl) ⟨488327, by rfl⟩ : syracuseStep 2604413 = 976655) (by norm_num)
theorem B2604437 : Blo 1735068 2604437 := bbase (se 6 (by rfl) ⟨61041, by rfl⟩ : syracuseStep 2604437 = 122083) (by norm_num)
theorem B5856677 : Blo 1735068 5856677 := bbase (se 4 (by rfl) ⟨549063, by rfl⟩ : syracuseStep 5856677 = 1098127) (by norm_num)
theorem B2604461 : Blo 1735068 2604461 := bbase (se 3 (by rfl) ⟨488336, by rfl⟩ : syracuseStep 2604461 = 976673) (by norm_num)
theorem B3906989 : Blo 1735068 3906989 := bbase (se 3 (by rfl) ⟨732560, by rfl⟩ : syracuseStep 3906989 = 1465121) (by norm_num)
theorem B2604485 : Blo 1735068 2604485 := bbase (se 4 (by rfl) ⟨244170, by rfl⟩ : syracuseStep 2604485 = 488341) (by norm_num)
theorem B4693445 : Blo 1735068 4693445 := bbase (se 4 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 4693445 = 880021) (by norm_num)
theorem B2604509 : Blo 1735068 2604509 := bbase (se 3 (by rfl) ⟨488345, by rfl⟩ : syracuseStep 2604509 = 976691) (by norm_num)
theorem B2604533 : Blo 1735068 2604533 := bbase (se 5 (by rfl) ⟨122087, by rfl⟩ : syracuseStep 2604533 = 244175) (by norm_num)
theorem B3907061 : Blo 1735068 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B2604557 : Blo 1735068 2604557 := bbase (se 3 (by rfl) ⟨488354, by rfl⟩ : syracuseStep 2604557 = 976709) (by norm_num)
theorem B2604581 : Blo 1735068 2604581 := bbase (se 4 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 2604581 = 488359) (by norm_num)
theorem B2604605 : Blo 1735068 2604605 := bbase (se 3 (by rfl) ⟨488363, by rfl⟩ : syracuseStep 2604605 = 976727) (by norm_num)
theorem B3907133 : Blo 1735068 3907133 := bbase (se 3 (by rfl) ⟨732587, by rfl⟩ : syracuseStep 3907133 = 1465175) (by norm_num)
theorem B2604629 : Blo 1735068 2604629 := bbase (se 8 (by rfl) ⟨15261, by rfl⟩ : syracuseStep 2604629 = 30523) (by norm_num)
theorem B2604653 : Blo 1735068 2604653 := bbase (se 3 (by rfl) ⟨488372, by rfl⟩ : syracuseStep 2604653 = 976745) (by norm_num)
theorem B3128957 : Blo 1735068 3128957 := bbase (se 3 (by rfl) ⟨586679, by rfl⟩ : syracuseStep 3128957 = 1173359) (by norm_num)
theorem B2604677 : Blo 1735068 2604677 := bbase (se 4 (by rfl) ⟨244188, by rfl⟩ : syracuseStep 2604677 = 488377) (by norm_num)
theorem B3907205 : Blo 1735068 3907205 := bbase (se 4 (by rfl) ⟨366300, by rfl⟩ : syracuseStep 3907205 = 732601) (by norm_num)
theorem B4169357 : Blo 1735068 4169357 := bbase (se 3 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 4169357 = 1563509) (by norm_num)
theorem B2604701 : Blo 1735068 2604701 := bbase (se 3 (by rfl) ⟨488381, by rfl⟩ : syracuseStep 2604701 = 976763) (by norm_num)
theorem B5562037 : Blo 1735068 5562037 := bbase (se 5 (by rfl) ⟨260720, by rfl⟩ : syracuseStep 5562037 = 521441) (by norm_num)
theorem B2604725 : Blo 1735068 2604725 := bbase (se 5 (by rfl) ⟨122096, by rfl⟩ : syracuseStep 2604725 = 244193) (by norm_num)
theorem B4169413 : Blo 1735068 4169413 := bbase (se 4 (by rfl) ⟨390882, by rfl⟩ : syracuseStep 4169413 = 781765) (by norm_num)
theorem B2604749 : Blo 1735068 2604749 := bbase (se 3 (by rfl) ⟨488390, by rfl⟩ : syracuseStep 2604749 = 976781) (by norm_num)
theorem B3907277 : Blo 1735068 3907277 := bbase (se 3 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 3907277 = 1465229) (by norm_num)
theorem B2604773 : Blo 1735068 2604773 := bbase (se 4 (by rfl) ⟨244197, by rfl⟩ : syracuseStep 2604773 = 488395) (by norm_num)
theorem B2604797 : Blo 1735068 2604797 := bbase (se 3 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 2604797 = 976799) (by norm_num)
theorem B2604821 : Blo 1735068 2604821 := bbase (se 6 (by rfl) ⟨61050, by rfl⟩ : syracuseStep 2604821 = 122101) (by norm_num)
theorem B2604845 : Blo 1735068 2604845 := bbase (se 3 (by rfl) ⟨488408, by rfl⟩ : syracuseStep 2604845 = 976817) (by norm_num)
theorem B13360949 : Blo 1735068 13360949 := bbase (se 5 (by rfl) ⟨626294, by rfl⟩ : syracuseStep 13360949 = 1252589) (by norm_num)
theorem B5857109 : Blo 1735068 5857109 := bbase (se 9 (by rfl) ⟨17159, by rfl⟩ : syracuseStep 5857109 = 34319) (by norm_num)
theorem B8339365 : Blo 1735068 8339365 := bbase (se 4 (by rfl) ⟨781815, by rfl⟩ : syracuseStep 8339365 = 1563631) (by norm_num)
theorem B8789957 : Blo 1735068 8789957 := bbase (se 4 (by rfl) ⟨824058, by rfl⟩ : syracuseStep 8789957 = 1648117) (by norm_num)
theorem B5857325 : Blo 1735068 5857325 := bstep (se 3 (by rfl) ⟨1098248, by rfl⟩ : syracuseStep 5857325 = 2196497) B2196497
theorem B5857379 : Blo 1735068 5857379 := bstep (se 1 (by rfl) ⟨4393034, by rfl⟩ : syracuseStep 5857379 = 8786069) B8786069
theorem B8339597 : Blo 1735068 8339597 := bstep (se 3 (by rfl) ⟨1563674, by rfl⟩ : syracuseStep 8339597 = 3127349) B3127349
theorem B7414051 : Blo 1735068 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B5857649 : Blo 1735068 5857649 := bstep (se 2 (by rfl) ⟨2196618, by rfl⟩ : syracuseStep 5857649 = 4393237) B4393237
theorem B2818417 : Blo 1735068 2818417 := bstep (se 2 (by rfl) ⟨1056906, by rfl⟩ : syracuseStep 2818417 = 2113813) B2113813
theorem B8790605 : Blo 1735068 8790605 := bstep (se 3 (by rfl) ⟨1648238, by rfl⟩ : syracuseStep 8790605 = 3296477) B3296477
theorem B2196067 : Blo 1735068 2196067 := bstep (se 1 (by rfl) ⟨1647050, by rfl⟩ : syracuseStep 2196067 = 3294101) B3294101
theorem B2196163 : Blo 1735068 2196163 := bstep (se 1 (by rfl) ⟨1647122, by rfl⟩ : syracuseStep 2196163 = 3294245) B3294245
theorem B2818883 : Blo 1735068 2818883 := bstep (se 1 (by rfl) ⟨2114162, by rfl⟩ : syracuseStep 2818883 = 4228325) B4228325
theorem B11117411 : Blo 1735068 11117411 := bstep (se 1 (by rfl) ⟨8338058, by rfl⟩ : syracuseStep 11117411 = 16676117) B16676117
theorem B5858189 : Blo 1735068 5858189 := bstep (se 3 (by rfl) ⟨1098410, by rfl⟩ : syracuseStep 5858189 = 2196821) B2196821
theorem B5858243 : Blo 1735068 5858243 := bstep (se 1 (by rfl) ⟨4393682, by rfl⟩ : syracuseStep 5858243 = 8787365) B8787365
theorem B4391921 : Blo 1735068 4391921 := bstep (se 2 (by rfl) ⟨1646970, by rfl⟩ : syracuseStep 4391921 = 3293941) B3293941
theorem B2196659 : Blo 1735068 2196659 := bstep (se 1 (by rfl) ⟨1647494, by rfl⟩ : syracuseStep 2196659 = 3294989) B3294989
theorem B5858513 : Blo 1735068 5858513 := bstep (se 2 (by rfl) ⟨2196942, by rfl⟩ : syracuseStep 5858513 = 4393885) B4393885
theorem B10560739 : Blo 1735068 10560739 := bstep (se 1 (by rfl) ⟨7920554, by rfl⟩ : syracuseStep 10560739 = 15841109) B15841109
theorem B4228561 : Blo 1735068 4228561 := bstep (se 2 (by rfl) ⟨1585710, by rfl⟩ : syracuseStep 4228561 = 3171421) B3171421
theorem B3294769 : Blo 1735068 3294769 := bstep (se 2 (by rfl) ⟨1235538, by rfl⟩ : syracuseStep 3294769 = 2471077) B2471077
theorem B4941425 : Blo 1735068 4941425 := bstep (se 2 (by rfl) ⟨1853034, by rfl⟩ : syracuseStep 4941425 = 3706069) B3706069
theorem B10020485 : Blo 1735068 10020485 := bstep (se 4 (by rfl) ⟨939420, by rfl⟩ : syracuseStep 10020485 = 1878841) B1878841
theorem B18548365 : Blo 1735068 18548365 := bstep (se 3 (by rfl) ⟨3477818, by rfl⟩ : syracuseStep 18548365 = 6955637) B6955637
theorem B5859053 : Blo 1735068 5859053 := bstep (se 3 (by rfl) ⟨1098572, by rfl⟩ : syracuseStep 5859053 = 2197145) B2197145
theorem B5859107 : Blo 1735068 5859107 := bstep (se 1 (by rfl) ⟨4394330, by rfl⟩ : syracuseStep 5859107 = 8788661) B8788661
theorem B2934611 : Blo 1735068 2934611 := bstep (se 1 (by rfl) ⟨2200958, by rfl⟩ : syracuseStep 2934611 = 4401917) B4401917
theorem B2197363 : Blo 1735068 2197363 := bstep (se 1 (by rfl) ⟨1648022, by rfl⟩ : syracuseStep 2197363 = 3296045) B3296045
theorem B18769805 : Blo 1735068 18769805 := bstep (se 3 (by rfl) ⟨3519338, by rfl⟩ : syracuseStep 18769805 = 7038677) B7038677
theorem B6588323 : Blo 1735068 6588323 := bstep (se 1 (by rfl) ⟨4941242, by rfl⟩ : syracuseStep 6588323 = 9882485) B9882485
theorem B6588337 : Blo 1735068 6588337 := bstep (se 2 (by rfl) ⟨2470626, by rfl⟩ : syracuseStep 6588337 = 4941253) B4941253
theorem B3295171 : Blo 1735068 3295171 := bstep (se 1 (by rfl) ⟨2471378, by rfl⟩ : syracuseStep 3295171 = 4942757) B4942757
theorem B4392913 : Blo 1735068 4392913 := bstep (se 2 (by rfl) ⟨1647342, by rfl⟩ : syracuseStep 4392913 = 3294685) B3294685
theorem B2197459 : Blo 1735068 2197459 := bstep (se 1 (by rfl) ⟨1648094, by rfl⟩ : syracuseStep 2197459 = 3296189) B3296189
theorem B3295217 : Blo 1735068 3295217 := bstep (se 2 (by rfl) ⟨1235706, by rfl⟩ : syracuseStep 3295217 = 2471413) B2471413
theorem B5859377 : Blo 1735068 5859377 := bstep (se 2 (by rfl) ⟨2197266, by rfl⟩ : syracuseStep 5859377 = 4394533) B4394533
theorem B9881777 : Blo 1735068 9881777 := bstep (se 2 (by rfl) ⟨3705666, by rfl⟩ : syracuseStep 9881777 = 7411333) B7411333
theorem B4393187 : Blo 1735068 4393187 := bstep (se 1 (by rfl) ⟨3294890, by rfl⟩ : syracuseStep 4393187 = 6589781) B6589781
theorem B7416049 : Blo 1735068 7416049 := bstep (se 2 (by rfl) ⟨2781018, by rfl⟩ : syracuseStep 7416049 = 5562037) B5562037
theorem B1951987 : Blo 1735068 1951987 := bstep (se 1 (by rfl) ⟨1463990, by rfl⟩ : syracuseStep 1951987 = 2927981) B2927981
theorem B4942097 : Blo 1735068 4942097 := bstep (se 2 (by rfl) ⟨1853286, by rfl⟩ : syracuseStep 4942097 = 3706573) B3706573
theorem B3295505 : Blo 1735068 3295505 := bstep (se 2 (by rfl) ⟨1235814, by rfl⟩ : syracuseStep 3295505 = 2471629) B2471629
theorem B1952131 : Blo 1735068 1952131 := bstep (se 1 (by rfl) ⟨1464098, by rfl⟩ : syracuseStep 1952131 = 2928197) B2928197
theorem B5147021 : Blo 1735068 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B4393379 : Blo 1735068 4393379 := bstep (se 1 (by rfl) ⟨3295034, by rfl⟩ : syracuseStep 4393379 = 6590069) B6590069
theorem B2779571 : Blo 1735068 2779571 := bstep (se 1 (by rfl) ⟨2084678, by rfl⟩ : syracuseStep 2779571 = 4169357) B4169357
theorem B2968019 : Blo 1735068 2968019 := bstep (se 1 (by rfl) ⟨2226014, by rfl⟩ : syracuseStep 2968019 = 4452029) B4452029
theorem B1853923 : Blo 1735068 1853923 := bstep (se 1 (by rfl) ⟨1390442, by rfl⟩ : syracuseStep 1853923 = 2780885) B2780885
theorem B1952275 : Blo 1735068 1952275 := bstep (se 1 (by rfl) ⟨1464206, by rfl⟩ : syracuseStep 1952275 = 2928413) B2928413
theorem B8907299 : Blo 1735068 8907299 := bstep (se 1 (by rfl) ⟨6680474, by rfl⟩ : syracuseStep 8907299 = 13360949) B13360949
theorem B11119153 : Blo 1735068 11119153 := bstep (se 2 (by rfl) ⟨4169682, by rfl⟩ : syracuseStep 11119153 = 8339365) B8339365
theorem B15829573 : Blo 1735068 15829573 := bstep (se 4 (by rfl) ⟨1484022, by rfl⟩ : syracuseStep 15829573 = 2968045) B2968045
theorem B5859917 : Blo 1735068 5859917 := bstep (se 3 (by rfl) ⟨1098734, by rfl⟩ : syracuseStep 5859917 = 2197469) B2197469
theorem B2345555 : Blo 1735068 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B5859971 : Blo 1735068 5859971 := bstep (se 1 (by rfl) ⟨4394978, by rfl⟩ : syracuseStep 5859971 = 8789957) B8789957
theorem B1952419 : Blo 1735068 1952419 := bstep (se 1 (by rfl) ⟨1464314, by rfl⟩ : syracuseStep 1952419 = 2928629) B2928629
theorem B23751365 : Blo 1735068 23751365 := bstep (se 4 (by rfl) ⟨2226690, by rfl⟩ : syracuseStep 23751365 = 4453381) B4453381
theorem B8784611 : Blo 1735068 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B80169749 : Blo 1735068 80169749 := bstep (se 6 (by rfl) ⟨1878978, by rfl⟩ : syracuseStep 80169749 = 3757957) B3757957
theorem B1952563 : Blo 1735068 1952563 := bstep (se 1 (by rfl) ⟨1464422, by rfl⟩ : syracuseStep 1952563 = 2928845) B2928845
theorem B5860241 : Blo 1735068 5860241 := bstep (se 2 (by rfl) ⟨2197590, by rfl⟩ : syracuseStep 5860241 = 4395181) B4395181
theorem B1854371 : Blo 1735068 1854371 := bstep (se 1 (by rfl) ⟨1390778, by rfl⟩ : syracuseStep 1854371 = 2781557) B2781557
theorem B1952707 : Blo 1735068 1952707 := bstep (se 1 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 1952707 = 2929061) B2929061
theorem B3296227 : Blo 1735068 3296227 := bstep (se 1 (by rfl) ⟨2472170, by rfl⟩ : syracuseStep 3296227 = 4944341) B4944341
theorem B2345987 : Blo 1735068 2345987 := bstep (se 1 (by rfl) ⟨1759490, by rfl⟩ : syracuseStep 2345987 = 3518981) B3518981
theorem B4942883 : Blo 1735068 4942883 := bstep (se 1 (by rfl) ⟨3707162, by rfl⟩ : syracuseStep 4942883 = 7414325) B7414325
theorem B1952851 : Blo 1735068 1952851 := bstep (se 1 (by rfl) ⟨1464638, by rfl⟩ : syracuseStep 1952851 = 2929277) B2929277
theorem B1952995 : Blo 1735068 1952995 := bstep (se 1 (by rfl) ⟨1464746, by rfl⟩ : syracuseStep 1952995 = 2929493) B2929493
theorem B5279057 : Blo 1735068 5279057 := bstep (se 2 (by rfl) ⟨1979646, by rfl⟩ : syracuseStep 5279057 = 3959293) B3959293
theorem B4394321 : Blo 1735068 4394321 := bstep (se 2 (by rfl) ⟨1647870, by rfl⟩ : syracuseStep 4394321 = 3295741) B3295741
theorem B6589795 : Blo 1735068 6589795 := bstep (se 1 (by rfl) ⟨4942346, by rfl⟩ : syracuseStep 6589795 = 9884693) B9884693
theorem B4943213 : Blo 1735068 4943213 := bstep (se 3 (by rfl) ⟨926852, by rfl⟩ : syracuseStep 4943213 = 1853705) B1853705
theorem B1953139 : Blo 1735068 1953139 := bstep (se 1 (by rfl) ⟨1464854, by rfl⟩ : syracuseStep 1953139 = 2929709) B2929709
theorem B2928001 : Blo 1735068 2928001 := bstep (se 2 (by rfl) ⟨1098000, by rfl⟩ : syracuseStep 2928001 = 2196001) B2196001
theorem B4394371 : Blo 1735068 4394371 := bstep (se 1 (by rfl) ⟨3295778, by rfl⟩ : syracuseStep 4394371 = 6591557) B6591557
theorem B2928035 : Blo 1735068 2928035 := bstep (se 1 (by rfl) ⟨2196026, by rfl⟩ : syracuseStep 2928035 = 4392053) B4392053
theorem B3296675 : Blo 1735068 3296675 := bstep (se 1 (by rfl) ⟨2472506, by rfl⟩ : syracuseStep 3296675 = 4945013) B4945013
theorem B5860781 : Blo 1735068 5860781 := bstep (se 3 (by rfl) ⟨1098896, by rfl⟩ : syracuseStep 5860781 = 2197793) B2197793
theorem B4943281 : Blo 1735068 4943281 := bstep (se 2 (by rfl) ⟨1853730, by rfl⟩ : syracuseStep 4943281 = 3707461) B3707461
theorem B5860835 : Blo 1735068 5860835 := bstep (se 1 (by rfl) ⟨4395626, by rfl⟩ : syracuseStep 5860835 = 8791253) B8791253
theorem B1953283 : Blo 1735068 1953283 := bstep (se 1 (by rfl) ⟨1464962, by rfl⟩ : syracuseStep 1953283 = 2929925) B2929925
theorem B8785421 : Blo 1735068 8785421 := bstep (se 3 (by rfl) ⟨1647266, by rfl⟩ : syracuseStep 8785421 = 3294533) B3294533
theorem B4394513 : Blo 1735068 4394513 := bstep (se 2 (by rfl) ⟨1647942, by rfl⟩ : syracuseStep 4394513 = 3295885) B3295885
theorem B2928163 : Blo 1735068 2928163 := bstep (se 1 (by rfl) ⟨2196122, by rfl⟩ : syracuseStep 2928163 = 4392245) B4392245
theorem B3010097 : Blo 1735068 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B9883235 : Blo 1735068 9883235 := bstep (se 1 (by rfl) ⟨7412426, by rfl⟩ : syracuseStep 9883235 = 14824853) B14824853
theorem B15240845 : Blo 1735068 15240845 := bstep (se 3 (by rfl) ⟨2857658, by rfl⟩ : syracuseStep 15240845 = 5715317) B5715317
theorem B1953427 : Blo 1735068 1953427 := bstep (se 1 (by rfl) ⟨1465070, by rfl⟩ : syracuseStep 1953427 = 2930141) B2930141
theorem B2928305 : Blo 1735068 2928305 := bstep (se 2 (by rfl) ⟨1098114, by rfl⟩ : syracuseStep 2928305 = 2196229) B2196229
theorem B4943555 : Blo 1735068 4943555 := bstep (se 1 (by rfl) ⟨3707666, by rfl⟩ : syracuseStep 4943555 = 7415333) B7415333
theorem B22236869 : Blo 1735068 22236869 := bstep (se 4 (by rfl) ⟨2084706, by rfl⟩ : syracuseStep 22236869 = 4169413) B4169413
theorem B2084611 : Blo 1735068 2084611 := bstep (se 1 (by rfl) ⟨1563458, by rfl⟩ : syracuseStep 2084611 = 3126917) B3126917
theorem B1953571 : Blo 1735068 1953571 := bstep (se 1 (by rfl) ⟨1465178, by rfl⟩ : syracuseStep 1953571 = 2930357) B2930357
theorem B2928433 : Blo 1735068 2928433 := bstep (se 2 (by rfl) ⟨1098162, by rfl⟩ : syracuseStep 2928433 = 2196325) B2196325
theorem B2780993 : Blo 1735068 2780993 := bstep (se 2 (by rfl) ⟨1042872, by rfl⟩ : syracuseStep 2780993 = 2085745) B2085745
theorem B2928467 : Blo 1735068 2928467 := bstep (se 1 (by rfl) ⟨2196350, by rfl⟩ : syracuseStep 2928467 = 4392701) B4392701
theorem B2928595 : Blo 1735068 2928595 := bstep (se 1 (by rfl) ⟨2196446, by rfl⟩ : syracuseStep 2928595 = 4392893) B4392893
theorem B3706897 : Blo 1735068 3706897 := bstep (se 2 (by rfl) ⟨1390086, by rfl⟩ : syracuseStep 3706897 = 2780173) B2780173
theorem B2969633 : Blo 1735068 2969633 := bstep (se 2 (by rfl) ⟨1113612, by rfl⟩ : syracuseStep 2969633 = 2227225) B2227225
theorem B2928737 : Blo 1735068 2928737 := bstep (se 2 (by rfl) ⟨1098276, by rfl⟩ : syracuseStep 2928737 = 2196553) B2196553
theorem B2928865 : Blo 1735068 2928865 := bstep (se 2 (by rfl) ⟨1098324, by rfl⟩ : syracuseStep 2928865 = 2196649) B2196649
theorem B2085091 : Blo 1735068 2085091 := bstep (se 1 (by rfl) ⟨1563818, by rfl⟩ : syracuseStep 2085091 = 3127637) B3127637
theorem B2928899 : Blo 1735068 2928899 := bstep (se 1 (by rfl) ⟨2196674, by rfl⟩ : syracuseStep 2928899 = 4393349) B4393349
theorem B2929027 : Blo 1735068 2929027 := bstep (se 1 (by rfl) ⟨2196770, by rfl⟩ : syracuseStep 2929027 = 4393541) B4393541
theorem B3707299 : Blo 1735068 3707299 := bstep (se 1 (by rfl) ⟨2780474, by rfl⟩ : syracuseStep 3707299 = 5560949) B5560949
theorem B11121101 : Blo 1735068 11121101 := bstep (se 3 (by rfl) ⟨2085206, by rfl⟩ : syracuseStep 11121101 = 4170413) B4170413
theorem B4395505 : Blo 1735068 4395505 := bstep (se 2 (by rfl) ⟨1648314, by rfl⟩ : syracuseStep 4395505 = 3296629) B3296629
theorem B4944397 : Blo 1735068 4944397 := bstep (se 3 (by rfl) ⟨927074, by rfl⟩ : syracuseStep 4944397 = 1854149) B1854149
theorem B2929169 : Blo 1735068 2929169 := bstep (se 2 (by rfl) ⟨1098438, by rfl⟩ : syracuseStep 2929169 = 2196877) B2196877
theorem B9155171 : Blo 1735068 9155171 := bstep (se 1 (by rfl) ⟨6866378, by rfl⟩ : syracuseStep 9155171 = 13732757) B13732757
theorem B2470513 : Blo 1735068 2470513 := bstep (se 2 (by rfl) ⟨926442, by rfl⟩ : syracuseStep 2470513 = 1852885) B1852885
theorem B4452995 : Blo 1735068 4452995 := bstep (se 1 (by rfl) ⟨3339746, by rfl⟩ : syracuseStep 4452995 = 6679493) B6679493
theorem B3904145 : Blo 1735068 3904145 := bstep (se 2 (by rfl) ⟨1464054, by rfl⟩ : syracuseStep 3904145 = 2928109) B2928109
theorem B2929297 : Blo 1735068 2929297 := bstep (se 2 (by rfl) ⟨1098486, by rfl⟩ : syracuseStep 2929297 = 2196973) B2196973
theorem B2470547 : Blo 1735068 2470547 := bstep (se 1 (by rfl) ⟨1852910, by rfl⟩ : syracuseStep 2470547 = 3705821) B3705821
theorem B3904163 : Blo 1735068 3904163 := bstep (se 1 (by rfl) ⟨2928122, by rfl⟩ : syracuseStep 3904163 = 5856245) B5856245
theorem B4944557 : Blo 1735068 4944557 := bstep (se 3 (by rfl) ⟨927104, by rfl⟩ : syracuseStep 4944557 = 1854209) B1854209
theorem B2929331 : Blo 1735068 2929331 := bstep (se 1 (by rfl) ⟨2196998, by rfl⟩ : syracuseStep 2929331 = 4393997) B4393997
theorem B17822477 : Blo 1735068 17822477 := bstep (se 3 (by rfl) ⟨3341714, by rfl⟩ : syracuseStep 17822477 = 6683429) B6683429
theorem B2929459 : Blo 1735068 2929459 := bstep (se 1 (by rfl) ⟨2197094, by rfl⟩ : syracuseStep 2929459 = 4394189) B4394189
theorem B4944739 : Blo 1735068 4944739 := bstep (se 1 (by rfl) ⟨3708554, by rfl⟩ : syracuseStep 4944739 = 7417109) B7417109
theorem B4756333 : Blo 1735068 4756333 := bstep (se 3 (by rfl) ⟨891812, by rfl⟩ : syracuseStep 4756333 = 1783625) B1783625
theorem B3904433 : Blo 1735068 3904433 := bstep (se 2 (by rfl) ⟨1464162, by rfl⟩ : syracuseStep 3904433 = 2928325) B2928325
theorem B2929601 : Blo 1735068 2929601 := bstep (se 2 (by rfl) ⟨1098600, by rfl⟩ : syracuseStep 2929601 = 2197201) B2197201
theorem B3904451 : Blo 1735068 3904451 := bstep (se 1 (by rfl) ⟨2928338, by rfl⟩ : syracuseStep 3904451 = 5856677) B5856677
theorem B2929729 : Blo 1735068 2929729 := bstep (se 2 (by rfl) ⟨1098648, by rfl⟩ : syracuseStep 2929729 = 2197297) B2197297
theorem B2085971 : Blo 1735068 2085971 := bstep (se 1 (by rfl) ⟨1564478, by rfl⟩ : syracuseStep 2085971 = 3128957) B3128957
theorem B2929763 : Blo 1735068 2929763 := bstep (se 1 (by rfl) ⟨2197322, by rfl⟩ : syracuseStep 2929763 = 4394645) B4394645
theorem B5010541 : Blo 1735068 5010541 := bstep (se 3 (by rfl) ⟨939476, by rfl⟩ : syracuseStep 5010541 = 1878953) B1878953
theorem B2471105 : Blo 1735068 2471105 := bstep (se 2 (by rfl) ⟨926664, by rfl⟩ : syracuseStep 2471105 = 1853329) B1853329
theorem B3904721 : Blo 1735068 3904721 := bstep (se 2 (by rfl) ⟨1464270, by rfl⟩ : syracuseStep 3904721 = 2928541) B2928541
theorem B3904739 : Blo 1735068 3904739 := bstep (se 1 (by rfl) ⟨2928554, by rfl⟩ : syracuseStep 3904739 = 5857109) B5857109
theorem B2929891 : Blo 1735068 2929891 := bstep (se 1 (by rfl) ⟨2197418, by rfl⟩ : syracuseStep 2929891 = 4394837) B4394837
theorem B2471185 : Blo 1735068 2471185 := bstep (se 2 (by rfl) ⟨926694, by rfl⟩ : syracuseStep 2471185 = 1853389) B1853389
theorem B2930033 : Blo 1735068 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B3905009 : Blo 1735068 3905009 := bstep (se 2 (by rfl) ⟨1464378, by rfl⟩ : syracuseStep 3905009 = 2928757) B2928757
theorem B2930161 : Blo 1735068 2930161 := bstep (se 2 (by rfl) ⟨1098810, by rfl⟩ : syracuseStep 2930161 = 2197621) B2197621
theorem B3905027 : Blo 1735068 3905027 := bstep (se 1 (by rfl) ⟨2928770, by rfl⟩ : syracuseStep 3905027 = 5857541) B5857541
theorem B6592013 : Blo 1735068 6592013 := bstep (se 3 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 6592013 = 2472005) B2472005
theorem B2930195 : Blo 1735068 2930195 := bstep (se 1 (by rfl) ⟨2197646, by rfl⟩ : syracuseStep 2930195 = 4395293) B4395293
theorem B2602625 : Blo 1735068 2602625 := bstep (se 2 (by rfl) ⟨975984, by rfl⟩ : syracuseStep 2602625 = 1951969) B1951969
theorem B2602643 : Blo 1735068 2602643 := bstep (se 1 (by rfl) ⟨1951982, by rfl⟩ : syracuseStep 2602643 = 3903965) B3903965
theorem B2930323 : Blo 1735068 2930323 := bstep (se 1 (by rfl) ⟨2197742, by rfl⟩ : syracuseStep 2930323 = 4395485) B4395485
theorem B2602673 : Blo 1735068 2602673 := bstep (se 2 (by rfl) ⟨976002, by rfl⟩ : syracuseStep 2602673 = 1952005) B1952005
theorem B2602691 : Blo 1735068 2602691 := bstep (se 1 (by rfl) ⟨1952018, by rfl⟩ : syracuseStep 2602691 = 3904037) B3904037
theorem B2602721 : Blo 1735068 2602721 := bstep (se 2 (by rfl) ⟨976020, by rfl⟩ : syracuseStep 2602721 = 1952041) B1952041
theorem B6256369 : Blo 1735068 6256369 := bstep (se 2 (by rfl) ⟨2346138, by rfl⟩ : syracuseStep 6256369 = 4692277) B4692277
theorem B2602739 : Blo 1735068 2602739 := bstep (se 1 (by rfl) ⟨1952054, by rfl⟩ : syracuseStep 2602739 = 3904109) B3904109
theorem B2602769 : Blo 1735068 2602769 := bstep (se 2 (by rfl) ⟨976038, by rfl⟩ : syracuseStep 2602769 = 1952077) B1952077
theorem B3905297 : Blo 1735068 3905297 := bstep (se 2 (by rfl) ⟨1464486, by rfl⟩ : syracuseStep 3905297 = 2928973) B2928973
theorem B3520273 : Blo 1735068 3520273 := bstep (se 2 (by rfl) ⟨1320102, by rfl⟩ : syracuseStep 3520273 = 2640205) B2640205
theorem B2602787 : Blo 1735068 2602787 := bstep (se 1 (by rfl) ⟨1952090, by rfl⟩ : syracuseStep 2602787 = 3904181) B3904181
theorem B3905315 : Blo 1735068 3905315 := bstep (se 1 (by rfl) ⟨2928986, by rfl⟩ : syracuseStep 3905315 = 5857973) B5857973
theorem B2602817 : Blo 1735068 2602817 := bstep (se 2 (by rfl) ⟨976056, by rfl⟩ : syracuseStep 2602817 = 1952113) B1952113
theorem B2504515 : Blo 1735068 2504515 := bstep (se 1 (by rfl) ⟨1878386, by rfl⟩ : syracuseStep 2504515 = 3756773) B3756773
theorem B4757329 : Blo 1735068 4757329 := bstep (se 2 (by rfl) ⟨1783998, by rfl⟩ : syracuseStep 4757329 = 3567997) B3567997
theorem B2602835 : Blo 1735068 2602835 := bstep (se 1 (by rfl) ⟨1952126, by rfl⟩ : syracuseStep 2602835 = 3904253) B3904253
theorem B2602865 : Blo 1735068 2602865 := bstep (se 2 (by rfl) ⟨976074, by rfl⟩ : syracuseStep 2602865 = 1952149) B1952149
theorem B2602883 : Blo 1735068 2602883 := bstep (se 1 (by rfl) ⟨1952162, by rfl⟩ : syracuseStep 2602883 = 3904325) B3904325
theorem B3708803 : Blo 1735068 3708803 := bstep (se 1 (by rfl) ⟨2781602, by rfl⟩ : syracuseStep 3708803 = 5563205) B5563205
theorem B2602913 : Blo 1735068 2602913 := bstep (se 2 (by rfl) ⟨976092, by rfl⟩ : syracuseStep 2602913 = 1952185) B1952185
theorem B2602931 : Blo 1735068 2602931 := bstep (se 1 (by rfl) ⟨1952198, by rfl⟩ : syracuseStep 2602931 = 3904397) B3904397
theorem B2602961 : Blo 1735068 2602961 := bstep (se 2 (by rfl) ⟨976110, by rfl⟩ : syracuseStep 2602961 = 1952221) B1952221
theorem B2602979 : Blo 1735068 2602979 := bstep (se 1 (by rfl) ⟨1952234, by rfl⟩ : syracuseStep 2602979 = 3904469) B3904469
theorem B2603009 : Blo 1735068 2603009 := bstep (se 2 (by rfl) ⟨976128, by rfl⟩ : syracuseStep 2603009 = 1952257) B1952257
theorem B2603027 : Blo 1735068 2603027 := bstep (se 1 (by rfl) ⟨1952270, by rfl⟩ : syracuseStep 2603027 = 3904541) B3904541
theorem B2471971 : Blo 1735068 2471971 := bstep (se 1 (by rfl) ⟨1853978, by rfl⟩ : syracuseStep 2471971 = 3707957) B3707957
theorem B2603057 : Blo 1735068 2603057 := bstep (se 2 (by rfl) ⟨976146, by rfl⟩ : syracuseStep 2603057 = 1952293) B1952293
theorem B3905585 : Blo 1735068 3905585 := bstep (se 2 (by rfl) ⟨1464594, by rfl⟩ : syracuseStep 3905585 = 2929189) B2929189
theorem B2603075 : Blo 1735068 2603075 := bstep (se 1 (by rfl) ⟨1952306, by rfl⟩ : syracuseStep 2603075 = 3904613) B3904613
theorem B3905603 : Blo 1735068 3905603 := bstep (se 1 (by rfl) ⟨2929202, by rfl⟩ : syracuseStep 3905603 = 5858405) B5858405
theorem B2857027 : Blo 1735068 2857027 := bstep (se 1 (by rfl) ⟨2142770, by rfl⟩ : syracuseStep 2857027 = 4285541) B4285541
theorem B5560397 : Blo 1735068 5560397 := bstep (se 3 (by rfl) ⟨1042574, by rfl⟩ : syracuseStep 5560397 = 2085149) B2085149
theorem B1783891 : Blo 1735068 1783891 := bstep (se 1 (by rfl) ⟨1337918, by rfl⟩ : syracuseStep 1783891 = 2675837) B2675837
theorem B2603105 : Blo 1735068 2603105 := bstep (se 2 (by rfl) ⟨976164, by rfl⟩ : syracuseStep 2603105 = 1952329) B1952329
theorem B2603123 : Blo 1735068 2603123 := bstep (se 1 (by rfl) ⟨1952342, by rfl⟩ : syracuseStep 2603123 = 3904685) B3904685
theorem B2603153 : Blo 1735068 2603153 := bstep (se 2 (by rfl) ⟨976182, by rfl⟩ : syracuseStep 2603153 = 1952365) B1952365
theorem B2603171 : Blo 1735068 2603171 := bstep (se 1 (by rfl) ⟨1952378, by rfl⟩ : syracuseStep 2603171 = 3904757) B3904757
theorem B2603201 : Blo 1735068 2603201 := bstep (se 2 (by rfl) ⟨976200, by rfl⟩ : syracuseStep 2603201 = 1952401) B1952401
theorem B2603219 : Blo 1735068 2603219 := bstep (se 1 (by rfl) ⟨1952414, by rfl⟩ : syracuseStep 2603219 = 3904829) B3904829
theorem B2603249 : Blo 1735068 2603249 := bstep (se 2 (by rfl) ⟨976218, by rfl⟩ : syracuseStep 2603249 = 1952437) B1952437
theorem B2603267 : Blo 1735068 2603267 := bstep (se 1 (by rfl) ⟨1952450, by rfl⟩ : syracuseStep 2603267 = 3904901) B3904901
theorem B2603297 : Blo 1735068 2603297 := bstep (se 2 (by rfl) ⟨976236, by rfl⟩ : syracuseStep 2603297 = 1952473) B1952473
theorem B2603315 : Blo 1735068 2603315 := bstep (se 1 (by rfl) ⟨1952486, by rfl⟩ : syracuseStep 2603315 = 3904973) B3904973
theorem B2603345 : Blo 1735068 2603345 := bstep (se 2 (by rfl) ⟨976254, by rfl⟩ : syracuseStep 2603345 = 1952509) B1952509
theorem B3905873 : Blo 1735068 3905873 := bstep (se 2 (by rfl) ⟨1464702, by rfl⟩ : syracuseStep 3905873 = 2929405) B2929405
theorem B2603363 : Blo 1735068 2603363 := bstep (se 1 (by rfl) ⟨1952522, by rfl⟩ : syracuseStep 2603363 = 3905045) B3905045
theorem B3905891 : Blo 1735068 3905891 := bstep (se 1 (by rfl) ⟨2929418, by rfl⟩ : syracuseStep 3905891 = 5858837) B5858837
theorem B8788337 : Blo 1735068 8788337 := bstep (se 2 (by rfl) ⟨3295626, by rfl⟩ : syracuseStep 8788337 = 6591253) B6591253
theorem B2603393 : Blo 1735068 2603393 := bstep (se 2 (by rfl) ⟨976272, by rfl⟩ : syracuseStep 2603393 = 1952545) B1952545
theorem B2603411 : Blo 1735068 2603411 := bstep (se 1 (by rfl) ⟨1952558, by rfl⟩ : syracuseStep 2603411 = 3905117) B3905117
theorem B1735075 : Blo 1735068 1735075 := bstep (se 1 (by rfl) ⟨1301306, by rfl⟩ : syracuseStep 1735075 = 2602613) B2602613
theorem B4692397 : Blo 1735068 4692397 := bstep (se 3 (by rfl) ⟨879824, by rfl⟩ : syracuseStep 4692397 = 1759649) B1759649
theorem B2603441 : Blo 1735068 2603441 := bstep (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) B1952581
theorem B1735091 : Blo 1735068 1735091 := bstep (se 1 (by rfl) ⟨1301318, by rfl⟩ : syracuseStep 1735091 = 2602637) B2602637
theorem B1735107 : Blo 1735068 1735107 := bstep (se 1 (by rfl) ⟨1301330, by rfl⟩ : syracuseStep 1735107 = 2602661) B2602661
theorem B2603459 : Blo 1735068 2603459 := bstep (se 1 (by rfl) ⟨1952594, by rfl⟩ : syracuseStep 2603459 = 3905189) B3905189
theorem B3127747 : Blo 1735068 3127747 := bstep (se 1 (by rfl) ⟨2345810, by rfl⟩ : syracuseStep 3127747 = 4691621) B4691621
theorem B1735123 : Blo 1735068 1735123 := bstep (se 1 (by rfl) ⟨1301342, by rfl⟩ : syracuseStep 1735123 = 2602685) B2602685
theorem B2603489 : Blo 1735068 2603489 := bstep (se 2 (by rfl) ⟨976308, by rfl⟩ : syracuseStep 2603489 = 1952617) B1952617
theorem B1735139 : Blo 1735068 1735139 := bstep (se 1 (by rfl) ⟨1301354, by rfl⟩ : syracuseStep 1735139 = 2602709) B2602709
theorem B14072291 : Blo 1735068 14072291 := bstep (se 1 (by rfl) ⟨10554218, by rfl⟩ : syracuseStep 14072291 = 21108437) B21108437
theorem B1735155 : Blo 1735068 1735155 := bstep (se 1 (by rfl) ⟨1301366, by rfl⟩ : syracuseStep 1735155 = 2602733) B2602733
theorem B2603507 : Blo 1735068 2603507 := bstep (se 1 (by rfl) ⟨1952630, by rfl⟩ : syracuseStep 2603507 = 3905261) B3905261
theorem B2472449 : Blo 1735068 2472449 := bstep (se 2 (by rfl) ⟨927168, by rfl⟩ : syracuseStep 2472449 = 1854337) B1854337
theorem B1735171 : Blo 1735068 1735171 := bstep (se 1 (by rfl) ⟨1301378, by rfl⟩ : syracuseStep 1735171 = 2602757) B2602757
theorem B3258883 : Blo 1735068 3258883 := bstep (se 1 (by rfl) ⟨2444162, by rfl⟩ : syracuseStep 3258883 = 4888325) B4888325
theorem B2603537 : Blo 1735068 2603537 := bstep (se 2 (by rfl) ⟨976326, by rfl⟩ : syracuseStep 2603537 = 1952653) B1952653
theorem B1735187 : Blo 1735068 1735187 := bstep (se 1 (by rfl) ⟨1301390, by rfl⟩ : syracuseStep 1735187 = 2602781) B2602781
theorem B1735203 : Blo 1735068 1735203 := bstep (se 1 (by rfl) ⟨1301402, by rfl⟩ : syracuseStep 1735203 = 2602805) B2602805
theorem B2603555 : Blo 1735068 2603555 := bstep (se 1 (by rfl) ⟨1952666, by rfl⟩ : syracuseStep 2603555 = 3905333) B3905333
theorem B1735219 : Blo 1735068 1735219 := bstep (se 1 (by rfl) ⟨1301414, by rfl⟩ : syracuseStep 1735219 = 2602829) B2602829
theorem B2603585 : Blo 1735068 2603585 := bstep (se 2 (by rfl) ⟨976344, by rfl⟩ : syracuseStep 2603585 = 1952689) B1952689
theorem B1735235 : Blo 1735068 1735235 := bstep (se 1 (by rfl) ⟨1301426, by rfl⟩ : syracuseStep 1735235 = 2602853) B2602853
theorem B1735251 : Blo 1735068 1735251 := bstep (se 1 (by rfl) ⟨1301438, by rfl⟩ : syracuseStep 1735251 = 2602877) B2602877
theorem B2603603 : Blo 1735068 2603603 := bstep (se 1 (by rfl) ⟨1952702, by rfl⟩ : syracuseStep 2603603 = 3905405) B3905405
theorem B1735267 : Blo 1735068 1735267 := bstep (se 1 (by rfl) ⟨1301450, by rfl⟩ : syracuseStep 1735267 = 2602901) B2602901
theorem B2603633 : Blo 1735068 2603633 := bstep (se 2 (by rfl) ⟨976362, by rfl⟩ : syracuseStep 2603633 = 1952725) B1952725
theorem B3906161 : Blo 1735068 3906161 := bstep (se 2 (by rfl) ⟨1464810, by rfl⟩ : syracuseStep 3906161 = 2929621) B2929621
theorem B2005619 : Blo 1735068 2005619 := bstep (se 1 (by rfl) ⟨1504214, by rfl⟩ : syracuseStep 2005619 = 3008429) B3008429
theorem B1735283 : Blo 1735068 1735283 := bstep (se 1 (by rfl) ⟨1301462, by rfl⟩ : syracuseStep 1735283 = 2602925) B2602925
theorem B2472563 : Blo 1735068 2472563 := bstep (se 1 (by rfl) ⟨1854422, by rfl⟩ : syracuseStep 2472563 = 3708845) B3708845
theorem B1735299 : Blo 1735068 1735299 := bstep (se 1 (by rfl) ⟨1301474, by rfl⟩ : syracuseStep 1735299 = 2602949) B2602949
theorem B2603651 : Blo 1735068 2603651 := bstep (se 1 (by rfl) ⟨1952738, by rfl⟩ : syracuseStep 2603651 = 3905477) B3905477
theorem B3906179 : Blo 1735068 3906179 := bstep (se 1 (by rfl) ⟨2929634, by rfl⟩ : syracuseStep 3906179 = 5859269) B5859269
theorem B1735315 : Blo 1735068 1735315 := bstep (se 1 (by rfl) ⟨1301486, by rfl⟩ : syracuseStep 1735315 = 2602973) B2602973
theorem B2226835 : Blo 1735068 2226835 := bstep (se 1 (by rfl) ⟨1670126, by rfl⟩ : syracuseStep 2226835 = 3340253) B3340253
theorem B2603681 : Blo 1735068 2603681 := bstep (se 2 (by rfl) ⟨976380, by rfl⟩ : syracuseStep 2603681 = 1952761) B1952761
theorem B1735331 : Blo 1735068 1735331 := bstep (se 1 (by rfl) ⟨1301498, by rfl⟩ : syracuseStep 1735331 = 2602997) B2602997
theorem B5855921 : Blo 1735068 5855921 := bstep (se 2 (by rfl) ⟨2195970, by rfl⟩ : syracuseStep 5855921 = 4391941) B4391941
theorem B1735347 : Blo 1735068 1735347 := bstep (se 1 (by rfl) ⟨1301510, by rfl⟩ : syracuseStep 1735347 = 2603021) B2603021
theorem B2603699 : Blo 1735068 2603699 := bstep (se 1 (by rfl) ⟨1952774, by rfl⟩ : syracuseStep 2603699 = 3905549) B3905549
theorem B1735363 : Blo 1735068 1735363 := bstep (se 1 (by rfl) ⟨1301522, by rfl⟩ : syracuseStep 1735363 = 2603045) B2603045
theorem B2603729 : Blo 1735068 2603729 := bstep (se 2 (by rfl) ⟨976398, by rfl⟩ : syracuseStep 2603729 = 1952797) B1952797
theorem B1735379 : Blo 1735068 1735379 := bstep (se 1 (by rfl) ⟨1301534, by rfl⟩ : syracuseStep 1735379 = 2603069) B2603069
theorem B1735395 : Blo 1735068 1735395 := bstep (se 1 (by rfl) ⟨1301546, by rfl⟩ : syracuseStep 1735395 = 2603093) B2603093
theorem B2603747 : Blo 1735068 2603747 := bstep (se 1 (by rfl) ⟨1952810, by rfl⟩ : syracuseStep 2603747 = 3905621) B3905621
theorem B1735411 : Blo 1735068 1735411 := bstep (se 1 (by rfl) ⟨1301558, by rfl⟩ : syracuseStep 1735411 = 2603117) B2603117
theorem B2603777 : Blo 1735068 2603777 := bstep (se 2 (by rfl) ⟨976416, by rfl⟩ : syracuseStep 2603777 = 1952833) B1952833
theorem B1735427 : Blo 1735068 1735427 := bstep (se 1 (by rfl) ⟨1301570, by rfl⟩ : syracuseStep 1735427 = 2603141) B2603141
theorem B1735443 : Blo 1735068 1735443 := bstep (se 1 (by rfl) ⟨1301582, by rfl⟩ : syracuseStep 1735443 = 2603165) B2603165
theorem B2603795 : Blo 1735068 2603795 := bstep (se 1 (by rfl) ⟨1952846, by rfl⟩ : syracuseStep 2603795 = 3905693) B3905693
theorem B1735459 : Blo 1735068 1735459 := bstep (se 1 (by rfl) ⟨1301594, by rfl⟩ : syracuseStep 1735459 = 2603189) B2603189
theorem B2603825 : Blo 1735068 2603825 := bstep (se 2 (by rfl) ⟨976434, by rfl⟩ : syracuseStep 2603825 = 1952869) B1952869
theorem B1735475 : Blo 1735068 1735475 := bstep (se 1 (by rfl) ⟨1301606, by rfl⟩ : syracuseStep 1735475 = 2603213) B2603213
theorem B1735491 : Blo 1735068 1735491 := bstep (se 1 (by rfl) ⟨1301618, by rfl⟩ : syracuseStep 1735491 = 2603237) B2603237
theorem B2603843 : Blo 1735068 2603843 := bstep (se 1 (by rfl) ⟨1952882, by rfl⟩ : syracuseStep 2603843 = 3905765) B3905765
theorem B1735507 : Blo 1735068 1735507 := bstep (se 1 (by rfl) ⟨1301630, by rfl⟩ : syracuseStep 1735507 = 2603261) B2603261
theorem B2603873 : Blo 1735068 2603873 := bstep (se 2 (by rfl) ⟨976452, by rfl⟩ : syracuseStep 2603873 = 1952905) B1952905
theorem B1735523 : Blo 1735068 1735523 := bstep (se 1 (by rfl) ⟨1301642, by rfl⟩ : syracuseStep 1735523 = 2603285) B2603285
theorem B1735539 : Blo 1735068 1735539 := bstep (se 1 (by rfl) ⟨1301654, by rfl⟩ : syracuseStep 1735539 = 2603309) B2603309
theorem B2603891 : Blo 1735068 2603891 := bstep (se 1 (by rfl) ⟨1952918, by rfl⟩ : syracuseStep 2603891 = 3905837) B3905837
theorem B1735555 : Blo 1735068 1735555 := bstep (se 1 (by rfl) ⟨1301666, by rfl⟩ : syracuseStep 1735555 = 2603333) B2603333
theorem B2603921 : Blo 1735068 2603921 := bstep (se 2 (by rfl) ⟨976470, by rfl⟩ : syracuseStep 2603921 = 1952941) B1952941
theorem B3906449 : Blo 1735068 3906449 := bstep (se 2 (by rfl) ⟨1464918, by rfl⟩ : syracuseStep 3906449 = 2929837) B2929837
theorem B1735571 : Blo 1735068 1735571 := bstep (se 1 (by rfl) ⟨1301678, by rfl⟩ : syracuseStep 1735571 = 2603357) B2603357
theorem B1735587 : Blo 1735068 1735587 := bstep (se 1 (by rfl) ⟨1301690, by rfl⟩ : syracuseStep 1735587 = 2603381) B2603381
theorem B2603939 : Blo 1735068 2603939 := bstep (se 1 (by rfl) ⟨1952954, by rfl⟩ : syracuseStep 2603939 = 3905909) B3905909
theorem B3906467 : Blo 1735068 3906467 := bstep (se 1 (by rfl) ⟨2929850, by rfl⟩ : syracuseStep 3906467 = 5859701) B5859701
theorem B1735603 : Blo 1735068 1735603 := bstep (se 1 (by rfl) ⟨1301702, by rfl⟩ : syracuseStep 1735603 = 2603405) B2603405
theorem B2603969 : Blo 1735068 2603969 := bstep (se 2 (by rfl) ⟨976488, by rfl⟩ : syracuseStep 2603969 = 1952977) B1952977
theorem B1735619 : Blo 1735068 1735619 := bstep (se 1 (by rfl) ⟨1301714, by rfl⟩ : syracuseStep 1735619 = 2603429) B2603429
theorem B1735635 : Blo 1735068 1735635 := bstep (se 1 (by rfl) ⟨1301726, by rfl⟩ : syracuseStep 1735635 = 2603453) B2603453
theorem B2603987 : Blo 1735068 2603987 := bstep (se 1 (by rfl) ⟨1952990, by rfl⟩ : syracuseStep 2603987 = 3905981) B3905981
theorem B1735651 : Blo 1735068 1735651 := bstep (se 1 (by rfl) ⟨1301738, by rfl⟩ : syracuseStep 1735651 = 2603477) B2603477
theorem B2604017 : Blo 1735068 2604017 := bstep (se 2 (by rfl) ⟨976506, by rfl⟩ : syracuseStep 2604017 = 1953013) B1953013
theorem B1735667 : Blo 1735068 1735667 := bstep (se 1 (by rfl) ⟨1301750, by rfl⟩ : syracuseStep 1735667 = 2603501) B2603501
theorem B1735683 : Blo 1735068 1735683 := bstep (se 1 (by rfl) ⟨1301762, by rfl⟩ : syracuseStep 1735683 = 2603525) B2603525
theorem B2604035 : Blo 1735068 2604035 := bstep (se 1 (by rfl) ⟨1953026, by rfl⟩ : syracuseStep 2604035 = 3906053) B3906053
theorem B5790733 : Blo 1735068 5790733 := bstep (se 3 (by rfl) ⟨1085762, by rfl⟩ : syracuseStep 5790733 = 2171525) B2171525
theorem B1735699 : Blo 1735068 1735699 := bstep (se 1 (by rfl) ⟨1301774, by rfl⟩ : syracuseStep 1735699 = 2603549) B2603549
theorem B2604065 : Blo 1735068 2604065 := bstep (se 2 (by rfl) ⟨976524, by rfl⟩ : syracuseStep 2604065 = 1953049) B1953049
theorem B1735715 : Blo 1735068 1735715 := bstep (se 1 (by rfl) ⟨1301786, by rfl⟩ : syracuseStep 1735715 = 2603573) B2603573
theorem B1735731 : Blo 1735068 1735731 := bstep (se 1 (by rfl) ⟨1301798, by rfl⟩ : syracuseStep 1735731 = 2603597) B2603597
theorem B2604083 : Blo 1735068 2604083 := bstep (se 1 (by rfl) ⟨1953062, by rfl⟩ : syracuseStep 2604083 = 3906125) B3906125
theorem B1735747 : Blo 1735068 1735747 := bstep (se 1 (by rfl) ⟨1301810, by rfl⟩ : syracuseStep 1735747 = 2603621) B2603621
theorem B3128401 : Blo 1735068 3128401 := bstep (se 2 (by rfl) ⟨1173150, by rfl⟩ : syracuseStep 3128401 = 2346301) B2346301
theorem B2604113 : Blo 1735068 2604113 := bstep (se 2 (by rfl) ⟨976542, by rfl⟩ : syracuseStep 2604113 = 1953085) B1953085
theorem B1735763 : Blo 1735068 1735763 := bstep (se 1 (by rfl) ⟨1301822, by rfl⟩ : syracuseStep 1735763 = 2603645) B2603645
theorem B1735779 : Blo 1735068 1735779 := bstep (se 1 (by rfl) ⟨1301834, by rfl⟩ : syracuseStep 1735779 = 2603669) B2603669
theorem B2604131 : Blo 1735068 2604131 := bstep (se 1 (by rfl) ⟨1953098, by rfl⟩ : syracuseStep 2604131 = 3906197) B3906197
theorem B3759203 : Blo 1735068 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B1735795 : Blo 1735068 1735795 := bstep (se 1 (by rfl) ⟨1301846, by rfl⟩ : syracuseStep 1735795 = 2603693) B2603693
theorem B2604161 : Blo 1735068 2604161 := bstep (se 2 (by rfl) ⟨976560, by rfl⟩ : syracuseStep 2604161 = 1953121) B1953121
theorem B1735811 : Blo 1735068 1735811 := bstep (se 1 (by rfl) ⟨1301858, by rfl⟩ : syracuseStep 1735811 = 2603717) B2603717
theorem B1735827 : Blo 1735068 1735827 := bstep (se 1 (by rfl) ⟨1301870, by rfl⟩ : syracuseStep 1735827 = 2603741) B2603741
theorem B2604179 : Blo 1735068 2604179 := bstep (se 1 (by rfl) ⟨1953134, by rfl⟩ : syracuseStep 2604179 = 3906269) B3906269
theorem B1735843 : Blo 1735068 1735843 := bstep (se 1 (by rfl) ⟨1301882, by rfl⟩ : syracuseStep 1735843 = 2603765) B2603765
theorem B2604209 : Blo 1735068 2604209 := bstep (se 2 (by rfl) ⟨976578, by rfl⟩ : syracuseStep 2604209 = 1953157) B1953157
theorem B3906737 : Blo 1735068 3906737 := bstep (se 2 (by rfl) ⟨1465026, by rfl⟩ : syracuseStep 3906737 = 2930053) B2930053
theorem B1735859 : Blo 1735068 1735859 := bstep (se 1 (by rfl) ⟨1301894, by rfl⟩ : syracuseStep 1735859 = 2603789) B2603789
theorem B1735875 : Blo 1735068 1735875 := bstep (se 1 (by rfl) ⟨1301906, by rfl⟩ : syracuseStep 1735875 = 2603813) B2603813
theorem B2604227 : Blo 1735068 2604227 := bstep (se 1 (by rfl) ⟨1953170, by rfl⟩ : syracuseStep 2604227 = 3906341) B3906341
theorem B3906755 : Blo 1735068 3906755 := bstep (se 1 (by rfl) ⟨2930066, by rfl⟩ : syracuseStep 3906755 = 5860133) B5860133
theorem B5856461 : Blo 1735068 5856461 := bstep (se 3 (by rfl) ⟨1098086, by rfl⟩ : syracuseStep 5856461 = 2196173) B2196173
theorem B1735891 : Blo 1735068 1735891 := bstep (se 1 (by rfl) ⟨1301918, by rfl⟩ : syracuseStep 1735891 = 2603837) B2603837
theorem B2604257 : Blo 1735068 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B1735907 : Blo 1735068 1735907 := bstep (se 1 (by rfl) ⟨1301930, by rfl⟩ : syracuseStep 1735907 = 2603861) B2603861
theorem B1735923 : Blo 1735068 1735923 := bstep (se 1 (by rfl) ⟨1301942, by rfl⟩ : syracuseStep 1735923 = 2603885) B2603885
theorem B2604275 : Blo 1735068 2604275 := bstep (se 1 (by rfl) ⟨1953206, by rfl⟩ : syracuseStep 2604275 = 3906413) B3906413
theorem B5856515 : Blo 1735068 5856515 := bstep (se 1 (by rfl) ⟨4392386, by rfl⟩ : syracuseStep 5856515 = 8784773) B8784773
theorem B1735939 : Blo 1735068 1735939 := bstep (se 1 (by rfl) ⟨1301954, by rfl⟩ : syracuseStep 1735939 = 2603909) B2603909
theorem B2604305 : Blo 1735068 2604305 := bstep (se 2 (by rfl) ⟨976614, by rfl⟩ : syracuseStep 2604305 = 1953229) B1953229
theorem B1735955 : Blo 1735068 1735955 := bstep (se 1 (by rfl) ⟨1301966, by rfl⟩ : syracuseStep 1735955 = 2603933) B2603933
theorem B1735971 : Blo 1735068 1735971 := bstep (se 1 (by rfl) ⟨1301978, by rfl⟩ : syracuseStep 1735971 = 2603957) B2603957
theorem B2604323 : Blo 1735068 2604323 := bstep (se 1 (by rfl) ⟨1953242, by rfl⟩ : syracuseStep 2604323 = 3906485) B3906485
theorem B1735987 : Blo 1735068 1735987 := bstep (se 1 (by rfl) ⟨1301990, by rfl⟩ : syracuseStep 1735987 = 2603981) B2603981
theorem B2604353 : Blo 1735068 2604353 := bstep (se 2 (by rfl) ⟨976632, by rfl⟩ : syracuseStep 2604353 = 1953265) B1953265
theorem B1736003 : Blo 1735068 1736003 := bstep (se 1 (by rfl) ⟨1302002, by rfl⟩ : syracuseStep 1736003 = 2604005) B2604005
theorem B1736019 : Blo 1735068 1736019 := bstep (se 1 (by rfl) ⟨1302014, by rfl⟩ : syracuseStep 1736019 = 2604029) B2604029
theorem B2604371 : Blo 1735068 2604371 := bstep (se 1 (by rfl) ⟨1953278, by rfl⟩ : syracuseStep 2604371 = 3906557) B3906557
theorem B1736035 : Blo 1735068 1736035 := bstep (se 1 (by rfl) ⟨1302026, by rfl⟩ : syracuseStep 1736035 = 2604053) B2604053
theorem B2604401 : Blo 1735068 2604401 := bstep (se 2 (by rfl) ⟨976650, by rfl⟩ : syracuseStep 2604401 = 1953301) B1953301
theorem B1736051 : Blo 1735068 1736051 := bstep (se 1 (by rfl) ⟨1302038, by rfl⟩ : syracuseStep 1736051 = 2604077) B2604077
theorem B1736067 : Blo 1735068 1736067 := bstep (se 1 (by rfl) ⟨1302050, by rfl⟩ : syracuseStep 1736067 = 2604101) B2604101
theorem B2604419 : Blo 1735068 2604419 := bstep (se 1 (by rfl) ⟨1953314, by rfl⟩ : syracuseStep 2604419 = 3906629) B3906629
theorem B1736083 : Blo 1735068 1736083 := bstep (se 1 (by rfl) ⟨1302062, by rfl⟩ : syracuseStep 1736083 = 2604125) B2604125
theorem B2604449 : Blo 1735068 2604449 := bstep (se 2 (by rfl) ⟨976668, by rfl⟩ : syracuseStep 2604449 = 1953337) B1953337
theorem B1736099 : Blo 1735068 1736099 := bstep (se 1 (by rfl) ⟨1302074, by rfl⟩ : syracuseStep 1736099 = 2604149) B2604149
theorem B1736115 : Blo 1735068 1736115 := bstep (se 1 (by rfl) ⟨1302086, by rfl⟩ : syracuseStep 1736115 = 2604173) B2604173
theorem B2604467 : Blo 1735068 2604467 := bstep (se 1 (by rfl) ⟨1953350, by rfl⟩ : syracuseStep 2604467 = 3906701) B3906701
theorem B1736131 : Blo 1735068 1736131 := bstep (se 1 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 1736131 = 2604197) B2604197
theorem B2506177 : Blo 1735068 2506177 := bstep (se 2 (by rfl) ⟨939816, by rfl⟩ : syracuseStep 2506177 = 1879633) B1879633
theorem B2604497 : Blo 1735068 2604497 := bstep (se 2 (by rfl) ⟨976686, by rfl⟩ : syracuseStep 2604497 = 1953373) B1953373
theorem B3907025 : Blo 1735068 3907025 := bstep (se 2 (by rfl) ⟨1465134, by rfl⟩ : syracuseStep 3907025 = 2930269) B2930269
theorem B1736147 : Blo 1735068 1736147 := bstep (se 1 (by rfl) ⟨1302110, by rfl⟩ : syracuseStep 1736147 = 2604221) B2604221
theorem B1736163 : Blo 1735068 1736163 := bstep (se 1 (by rfl) ⟨1302122, by rfl⟩ : syracuseStep 1736163 = 2604245) B2604245
theorem B2604515 : Blo 1735068 2604515 := bstep (se 1 (by rfl) ⟨1953386, by rfl⟩ : syracuseStep 2604515 = 3906773) B3906773
theorem B3907043 : Blo 1735068 3907043 := bstep (se 1 (by rfl) ⟨2930282, by rfl⟩ : syracuseStep 3907043 = 5860565) B5860565
theorem B1736179 : Blo 1735068 1736179 := bstep (se 1 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 1736179 = 2604269) B2604269
theorem B2604545 : Blo 1735068 2604545 := bstep (se 2 (by rfl) ⟨976704, by rfl⟩ : syracuseStep 2604545 = 1953409) B1953409
theorem B1736195 : Blo 1735068 1736195 := bstep (se 1 (by rfl) ⟨1302146, by rfl⟩ : syracuseStep 1736195 = 2604293) B2604293
theorem B5856785 : Blo 1735068 5856785 := bstep (se 2 (by rfl) ⟨2196294, by rfl⟩ : syracuseStep 5856785 = 4392589) B4392589
theorem B1736211 : Blo 1735068 1736211 := bstep (se 1 (by rfl) ⟨1302158, by rfl⟩ : syracuseStep 1736211 = 2604317) B2604317
theorem B2604563 : Blo 1735068 2604563 := bstep (se 1 (by rfl) ⟨1953422, by rfl⟩ : syracuseStep 2604563 = 3906845) B3906845
theorem B1736227 : Blo 1735068 1736227 := bstep (se 1 (by rfl) ⟨1302170, by rfl⟩ : syracuseStep 1736227 = 2604341) B2604341
theorem B2604593 : Blo 1735068 2604593 := bstep (se 2 (by rfl) ⟨976722, by rfl⟩ : syracuseStep 2604593 = 1953445) B1953445
theorem B1736243 : Blo 1735068 1736243 := bstep (se 1 (by rfl) ⟨1302182, by rfl⟩ : syracuseStep 1736243 = 2604365) B2604365
theorem B1736259 : Blo 1735068 1736259 := bstep (se 1 (by rfl) ⟨1302194, by rfl⟩ : syracuseStep 1736259 = 2604389) B2604389
theorem B2604611 : Blo 1735068 2604611 := bstep (se 1 (by rfl) ⟨1953458, by rfl⟩ : syracuseStep 2604611 = 3906917) B3906917
theorem B8339021 : Blo 1735068 8339021 := bstep (se 3 (by rfl) ⟨1563566, by rfl⟩ : syracuseStep 8339021 = 3127133) B3127133
theorem B1736275 : Blo 1735068 1736275 := bstep (se 1 (by rfl) ⟨1302206, by rfl⟩ : syracuseStep 1736275 = 2604413) B2604413
theorem B2604641 : Blo 1735068 2604641 := bstep (se 2 (by rfl) ⟨976740, by rfl⟩ : syracuseStep 2604641 = 1953481) B1953481
theorem B1736291 : Blo 1735068 1736291 := bstep (se 1 (by rfl) ⟨1302218, by rfl⟩ : syracuseStep 1736291 = 2604437) B2604437
theorem B1736307 : Blo 1735068 1736307 := bstep (se 1 (by rfl) ⟨1302230, by rfl⟩ : syracuseStep 1736307 = 2604461) B2604461
theorem B2604659 : Blo 1735068 2604659 := bstep (se 1 (by rfl) ⟨1953494, by rfl⟩ : syracuseStep 2604659 = 3906989) B3906989
theorem B1736323 : Blo 1735068 1736323 := bstep (se 1 (by rfl) ⟨1302242, by rfl⟩ : syracuseStep 1736323 = 2604485) B2604485
theorem B3128963 : Blo 1735068 3128963 := bstep (se 1 (by rfl) ⟨2346722, by rfl⟩ : syracuseStep 3128963 = 4693445) B4693445
theorem B2604689 : Blo 1735068 2604689 := bstep (se 2 (by rfl) ⟨976758, by rfl⟩ : syracuseStep 2604689 = 1953517) B1953517
theorem B1736339 : Blo 1735068 1736339 := bstep (se 1 (by rfl) ⟨1302254, by rfl⟩ : syracuseStep 1736339 = 2604509) B2604509
theorem B1736355 : Blo 1735068 1736355 := bstep (se 1 (by rfl) ⟨1302266, by rfl⟩ : syracuseStep 1736355 = 2604533) B2604533
theorem B2604707 : Blo 1735068 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B1736371 : Blo 1735068 1736371 := bstep (se 1 (by rfl) ⟨1302278, by rfl⟩ : syracuseStep 1736371 = 2604557) B2604557
theorem B2604737 : Blo 1735068 2604737 := bstep (se 2 (by rfl) ⟨976776, by rfl⟩ : syracuseStep 2604737 = 1953553) B1953553
theorem B1736387 : Blo 1735068 1736387 := bstep (se 1 (by rfl) ⟨1302290, by rfl⟩ : syracuseStep 1736387 = 2604581) B2604581
theorem B1736403 : Blo 1735068 1736403 := bstep (se 1 (by rfl) ⟨1302302, by rfl⟩ : syracuseStep 1736403 = 2604605) B2604605
theorem B2604755 : Blo 1735068 2604755 := bstep (se 1 (by rfl) ⟨1953566, by rfl⟩ : syracuseStep 2604755 = 3907133) B3907133
theorem B1736419 : Blo 1735068 1736419 := bstep (se 1 (by rfl) ⟨1302314, by rfl⟩ : syracuseStep 1736419 = 2604629) B2604629
theorem B2604785 : Blo 1735068 2604785 := bstep (se 2 (by rfl) ⟨976794, by rfl⟩ : syracuseStep 2604785 = 1953589) B1953589
theorem B1736435 : Blo 1735068 1736435 := bstep (se 1 (by rfl) ⟨1302326, by rfl⟩ : syracuseStep 1736435 = 2604653) B2604653
theorem B1736451 : Blo 1735068 1736451 := bstep (se 1 (by rfl) ⟨1302338, by rfl⟩ : syracuseStep 1736451 = 2604677) B2604677
theorem B2604803 : Blo 1735068 2604803 := bstep (se 1 (by rfl) ⟨1953602, by rfl⟩ : syracuseStep 2604803 = 3907205) B3907205
theorem B11124485 : Blo 1735068 11124485 := bstep (se 4 (by rfl) ⟨1042920, by rfl⟩ : syracuseStep 11124485 = 2085841) B2085841
theorem B8339213 : Blo 1735068 8339213 := bstep (se 3 (by rfl) ⟨1563602, by rfl⟩ : syracuseStep 8339213 = 3127205) B3127205
theorem B1736467 : Blo 1735068 1736467 := bstep (se 1 (by rfl) ⟨1302350, by rfl⟩ : syracuseStep 1736467 = 2604701) B2604701
theorem B2604833 : Blo 1735068 2604833 := bstep (se 2 (by rfl) ⟨976812, by rfl⟩ : syracuseStep 2604833 = 1953625) B1953625
theorem B8789795 : Blo 1735068 8789795 := bstep (se 1 (by rfl) ⟨6592346, by rfl⟩ : syracuseStep 8789795 = 13184693) B13184693
theorem B1736483 : Blo 1735068 1736483 := bstep (se 1 (by rfl) ⟨1302362, by rfl⟩ : syracuseStep 1736483 = 2604725) B2604725
theorem B1736499 : Blo 1735068 1736499 := bstep (se 1 (by rfl) ⟨1302374, by rfl⟩ : syracuseStep 1736499 = 2604749) B2604749
theorem B2604851 : Blo 1735068 2604851 := bstep (se 1 (by rfl) ⟨1953638, by rfl⟩ : syracuseStep 2604851 = 3907277) B3907277
theorem B5562179 : Blo 1735068 5562179 := bstep (se 1 (by rfl) ⟨4171634, by rfl⟩ : syracuseStep 5562179 = 8343269) B8343269
theorem B1736515 : Blo 1735068 1736515 := bstep (se 1 (by rfl) ⟨1302386, by rfl⟩ : syracuseStep 1736515 = 2604773) B2604773
theorem B1736531 : Blo 1735068 1736531 := bstep (se 1 (by rfl) ⟨1302398, by rfl⟩ : syracuseStep 1736531 = 2604797) B2604797
theorem B1736547 : Blo 1735068 1736547 := bstep (se 1 (by rfl) ⟨1302410, by rfl⟩ : syracuseStep 1736547 = 2604821) B2604821
theorem B1736563 : Blo 1735068 1736563 := bstep (se 1 (by rfl) ⟨1302422, by rfl⟩ : syracuseStep 1736563 = 2604845) B2604845
theorem B4169713 : Blo 1735068 4169713 := bstep (se 2 (by rfl) ⟨1563642, by rfl⟩ : syracuseStep 4169713 = 3127285) B3127285
theorem B8339441 : Blo 1735068 8339441 := bstep (se 2 (by rfl) ⟨3127290, by rfl⟩ : syracuseStep 8339441 = 6254581) B6254581
theorem B30883909 : Blo 1735068 30883909 := bstep (se 4 (by rfl) ⟨2895366, by rfl⟩ : syracuseStep 30883909 = 5790733) B5790733
theorem B3809369 : Blo 1735068 3809369 := bstep (se 2 (by rfl) ⟨1428513, by rfl⟩ : syracuseStep 3809369 = 2857027) B2857027
theorem B5562589 : Blo 1735068 5562589 := bstep (se 3 (by rfl) ⟨1042985, by rfl⟩ : syracuseStep 5562589 = 2085971) B2085971
theorem B7414067 : Blo 1735068 7414067 := bstep (se 1 (by rfl) ⟨5560550, by rfl⟩ : syracuseStep 7414067 = 11121101) B11121101
theorem B9888065 : Blo 1735068 9888065 := bstep (se 2 (by rfl) ⟨3708024, by rfl⟩ : syracuseStep 9888065 = 7416049) B7416049
theorem B5857757 : Blo 1735068 5857757 := bstep (se 3 (by rfl) ⟨1098329, by rfl⟩ : syracuseStep 5857757 = 2196659) B2196659
theorem B26722885 : Blo 1735068 26722885 := bstep (se 4 (by rfl) ⟨2505270, by rfl⟩ : syracuseStep 26722885 = 5010541) B5010541
theorem B4170329 : Blo 1735068 4170329 := bstep (se 2 (by rfl) ⟨1563873, by rfl⟩ : syracuseStep 4170329 = 3127747) B3127747
theorem B3294017 : Blo 1735068 3294017 := bstep (se 2 (by rfl) ⟨1235256, by rfl⟩ : syracuseStep 3294017 = 2470513) B2470513
theorem B3294283 : Blo 1735068 3294283 := bstep (se 1 (by rfl) ⟨2470712, by rfl⟩ : syracuseStep 3294283 = 4941425) B4941425
theorem B6341777 : Blo 1735068 6341777 := bstep (se 2 (by rfl) ⟨2378166, by rfl⟩ : syracuseStep 6341777 = 4756333) B4756333
theorem B33367301 : Blo 1735068 33367301 := bstep (se 4 (by rfl) ⟨3128184, by rfl⟩ : syracuseStep 33367301 = 6256369) B6256369
theorem B4392215 : Blo 1735068 4392215 := bstep (se 1 (by rfl) ⟨3294161, by rfl⟩ : syracuseStep 4392215 = 6588323) B6588323
theorem B2196811 : Blo 1735068 2196811 := bstep (se 1 (by rfl) ⟨1647608, by rfl⟩ : syracuseStep 2196811 = 3295217) B3295217
theorem B6587851 : Blo 1735068 6587851 := bstep (se 1 (by rfl) ⟨4940888, by rfl⟩ : syracuseStep 6587851 = 9881777) B9881777
theorem B3294731 : Blo 1735068 3294731 := bstep (se 1 (by rfl) ⟨2471048, by rfl⟩ : syracuseStep 3294731 = 4942097) B4942097
theorem B5858891 : Blo 1735068 5858891 := bstep (se 1 (by rfl) ⟨4394168, by rfl⟩ : syracuseStep 5858891 = 8788337) B8788337
theorem B24413789 : Blo 1735068 24413789 := bstep (se 3 (by rfl) ⟨4577585, by rfl⟩ : syracuseStep 24413789 = 9155171) B9155171
theorem B1853047 : Blo 1735068 1853047 := bstep (se 1 (by rfl) ⟨1389785, by rfl⟩ : syracuseStep 1853047 = 2779571) B2779571
theorem B9381527 : Blo 1735068 9381527 := bstep (se 1 (by rfl) ⟨7036145, by rfl⟩ : syracuseStep 9381527 = 14072291) B14072291
theorem B3294913 : Blo 1735068 3294913 := bstep (se 2 (by rfl) ⟨1235592, by rfl⟩ : syracuseStep 3294913 = 2471185) B2471185
theorem B6588125 : Blo 1735068 6588125 := bstep (se 3 (by rfl) ⟨1235273, by rfl⟩ : syracuseStep 6588125 = 2470547) B2470547
theorem B5859161 : Blo 1735068 5859161 := bstep (se 2 (by rfl) ⟨2197185, by rfl⟩ : syracuseStep 5859161 = 4394371) B4394371
theorem B53446499 : Blo 1735068 53446499 := bstep (se 1 (by rfl) ⟨40084874, by rfl⟩ : syracuseStep 53446499 = 80169749) B80169749
theorem B5638081 : Blo 1735068 5638081 := bstep (se 2 (by rfl) ⟨2114280, by rfl⟩ : syracuseStep 5638081 = 4228561) B4228561
theorem B3295255 : Blo 1735068 3295255 := bstep (se 1 (by rfl) ⟨2471441, by rfl⟩ : syracuseStep 3295255 = 4942883) B4942883
theorem B4393025 : Blo 1735068 4393025 := bstep (se 2 (by rfl) ⟨1647384, by rfl⟩ : syracuseStep 4393025 = 3294769) B3294769
theorem B7415981 : Blo 1735068 7415981 := bstep (se 3 (by rfl) ⟨1390496, by rfl⟩ : syracuseStep 7415981 = 2780993) B2780993
theorem B3295475 : Blo 1735068 3295475 := bstep (se 1 (by rfl) ⟨2471606, by rfl⟩ : syracuseStep 3295475 = 4943213) B4943213
theorem B1952023 : Blo 1735068 1952023 := bstep (se 1 (by rfl) ⟨1464017, by rfl⟩ : syracuseStep 1952023 = 2928035) B2928035
theorem B2197783 : Blo 1735068 2197783 := bstep (se 1 (by rfl) ⟨1648337, by rfl⟩ : syracuseStep 2197783 = 3296675) B3296675
theorem B2779481 : Blo 1735068 2779481 := bstep (se 2 (by rfl) ⟨1042305, by rfl⟩ : syracuseStep 2779481 = 2084611) B2084611
theorem B6588823 : Blo 1735068 6588823 := bstep (se 1 (by rfl) ⟨4941617, by rfl⟩ : syracuseStep 6588823 = 9883235) B9883235
theorem B10160563 : Blo 1735068 10160563 := bstep (se 1 (by rfl) ⟨7620422, by rfl⟩ : syracuseStep 10160563 = 15240845) B15240845
theorem B6343105 : Blo 1735068 6343105 := bstep (se 2 (by rfl) ⟨2378664, by rfl⟩ : syracuseStep 6343105 = 4757329) B4757329
theorem B1952203 : Blo 1735068 1952203 := bstep (se 1 (by rfl) ⟨1464152, by rfl⟩ : syracuseStep 1952203 = 2928305) B2928305
theorem B3295703 : Blo 1735068 3295703 := bstep (se 1 (by rfl) ⟨2471777, by rfl⟩ : syracuseStep 3295703 = 4943555) B4943555
theorem B7416323 : Blo 1735068 7416323 := bstep (se 1 (by rfl) ⟨5562242, by rfl⟩ : syracuseStep 7416323 = 11124485) B11124485
theorem B5859863 : Blo 1735068 5859863 := bstep (se 1 (by rfl) ⟨4394897, by rfl⟩ : syracuseStep 5859863 = 8789795) B8789795
theorem B1952311 : Blo 1735068 1952311 := bstep (se 1 (by rfl) ⟨1464233, by rfl⟩ : syracuseStep 1952311 = 2928467) B2928467
theorem B8784449 : Blo 1735068 8784449 := bstep (se 2 (by rfl) ⟨3294168, by rfl⟩ : syracuseStep 8784449 = 6588337) B6588337
theorem B4393561 : Blo 1735068 4393561 := bstep (se 2 (by rfl) ⟨1647585, by rfl⟩ : syracuseStep 4393561 = 3295171) B3295171
theorem B4942529 : Blo 1735068 4942529 := bstep (se 2 (by rfl) ⟨1853448, by rfl⟩ : syracuseStep 4942529 = 3706897) B3706897
theorem B3295961 : Blo 1735068 3295961 := bstep (se 2 (by rfl) ⟨1235985, by rfl⟩ : syracuseStep 3295961 = 2471971) B2471971
theorem B1952491 : Blo 1735068 1952491 := bstep (se 1 (by rfl) ⟨1464368, by rfl⟩ : syracuseStep 1952491 = 2928737) B2928737
theorem B2378521 : Blo 1735068 2378521 := bstep (se 2 (by rfl) ⟨891945, by rfl⟩ : syracuseStep 2378521 = 1783891) B1783891
theorem B1952599 : Blo 1735068 1952599 := bstep (se 1 (by rfl) ⟨1464449, by rfl⟩ : syracuseStep 1952599 = 2928899) B2928899
theorem B1952779 : Blo 1735068 1952779 := bstep (se 1 (by rfl) ⟨1464584, by rfl⟩ : syracuseStep 1952779 = 2929169) B2929169
theorem B5860403 : Blo 1735068 5860403 := bstep (se 1 (by rfl) ⟨4395302, by rfl⟩ : syracuseStep 5860403 = 8790605) B8790605
theorem B2968663 : Blo 1735068 2968663 := bstep (se 1 (by rfl) ⟨2226497, by rfl⟩ : syracuseStep 2968663 = 4452995) B4452995
theorem B3296371 : Blo 1735068 3296371 := bstep (se 1 (by rfl) ⟨2472278, by rfl⟩ : syracuseStep 3296371 = 4944557) B4944557
theorem B1952887 : Blo 1735068 1952887 := bstep (se 1 (by rfl) ⟨1464665, by rfl⟩ : syracuseStep 1952887 = 2929331) B2929331
theorem B6589613 : Blo 1735068 6589613 := bstep (se 3 (by rfl) ⟨1235552, by rfl⟩ : syracuseStep 6589613 = 2471105) B2471105
theorem B11881651 : Blo 1735068 11881651 := bstep (se 1 (by rfl) ⟨8911238, by rfl⟩ : syracuseStep 11881651 = 17822477) B17822477
theorem B4943065 : Blo 1735068 4943065 := bstep (se 2 (by rfl) ⟨1853649, by rfl⟩ : syracuseStep 4943065 = 3707299) B3707299
theorem B1953067 : Blo 1735068 1953067 := bstep (se 1 (by rfl) ⟨1464800, by rfl⟩ : syracuseStep 1953067 = 2929601) B2929601
theorem B5860673 : Blo 1735068 5860673 := bstep (se 2 (by rfl) ⟨2197752, by rfl⟩ : syracuseStep 5860673 = 4395505) B4395505
theorem B2927947 : Blo 1735068 2927947 := bstep (se 1 (by rfl) ⟨2195960, by rfl⟩ : syracuseStep 2927947 = 4391921) B4391921
theorem B4345177 : Blo 1735068 4345177 := bstep (se 2 (by rfl) ⟨1629441, by rfl⟩ : syracuseStep 4345177 = 3258883) B3258883
theorem B1953175 : Blo 1735068 1953175 := bstep (se 1 (by rfl) ⟨1464881, by rfl⟩ : syracuseStep 1953175 = 2929763) B2929763
theorem B21106097 : Blo 1735068 21106097 := bstep (se 2 (by rfl) ⟨7914786, by rfl⟩ : syracuseStep 21106097 = 15829573) B15829573
theorem B2928089 : Blo 1735068 2928089 := bstep (se 2 (by rfl) ⟨1098033, by rfl⟩ : syracuseStep 2928089 = 2196067) B2196067
theorem B1953355 : Blo 1735068 1953355 := bstep (se 1 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 1953355 = 2930033) B2930033
theorem B2928217 : Blo 1735068 2928217 := bstep (se 2 (by rfl) ⟨1098081, by rfl⟩ : syracuseStep 2928217 = 2196163) B2196163
theorem B4394675 : Blo 1735068 4394675 := bstep (se 1 (by rfl) ⟨3296006, by rfl⟩ : syracuseStep 4394675 = 6592013) B6592013
theorem B1953463 : Blo 1735068 1953463 := bstep (se 1 (by rfl) ⟨1465097, by rfl⟩ : syracuseStep 1953463 = 2930195) B2930195
theorem B6680323 : Blo 1735068 6680323 := bstep (se 1 (by rfl) ⟨5010242, by rfl⟩ : syracuseStep 6680323 = 10020485) B10020485
theorem B11120485 : Blo 1735068 11120485 := bstep (se 4 (by rfl) ⟨1042545, by rfl⟩ : syracuseStep 11120485 = 2085091) B2085091
theorem B12513203 : Blo 1735068 12513203 := bstep (se 1 (by rfl) ⟨9384902, by rfl⟩ : syracuseStep 12513203 = 18769805) B18769805
theorem B4394969 : Blo 1735068 4394969 := bstep (se 2 (by rfl) ⟨1648113, by rfl⟩ : syracuseStep 4394969 = 3296227) B3296227
theorem B3706931 : Blo 1735068 3706931 := bstep (se 1 (by rfl) ⟨2780198, by rfl⟩ : syracuseStep 3706931 = 5560397) B5560397
theorem B2928791 : Blo 1735068 2928791 := bstep (se 1 (by rfl) ⟨2196593, by rfl⟩ : syracuseStep 2928791 = 4393187) B4393187
theorem B6254813 : Blo 1735068 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B2928919 : Blo 1735068 2928919 := bstep (se 1 (by rfl) ⟨2196689, by rfl⟩ : syracuseStep 2928919 = 4393379) B4393379
theorem B1978679 : Blo 1735068 1978679 := bstep (se 1 (by rfl) ⟨1484009, by rfl⟩ : syracuseStep 1978679 = 2968019) B2968019
theorem B8343901 : Blo 1735068 8343901 := bstep (se 3 (by rfl) ⟨1564481, by rfl⟩ : syracuseStep 8343901 = 3128963) B3128963
theorem B3903947 : Blo 1735068 3903947 := bstep (se 1 (by rfl) ⟨2927960, by rfl⟩ : syracuseStep 3903947 = 5855921) B5855921
theorem B8786393 : Blo 1735068 8786393 := bstep (se 2 (by rfl) ⟨3294897, by rfl⟩ : syracuseStep 8786393 = 6589795) B6589795
theorem B3904001 : Blo 1735068 3904001 := bstep (se 2 (by rfl) ⟨1464000, by rfl⟩ : syracuseStep 3904001 = 2928001) B2928001
theorem B63336973 : Blo 1735068 63336973 := bstep (se 3 (by rfl) ⟨11875682, by rfl⟩ : syracuseStep 63336973 = 23751365) B23751365
theorem B6591041 : Blo 1735068 6591041 := bstep (se 2 (by rfl) ⟨2471640, by rfl⟩ : syracuseStep 6591041 = 4943281) B4943281
theorem B3904217 : Blo 1735068 3904217 := bstep (se 2 (by rfl) ⟨1464081, by rfl⟩ : syracuseStep 3904217 = 2928163) B2928163
theorem B3904307 : Blo 1735068 3904307 := bstep (se 1 (by rfl) ⟨2928230, by rfl⟩ : syracuseStep 3904307 = 5856461) B5856461
theorem B3904343 : Blo 1735068 3904343 := bstep (se 1 (by rfl) ⟨2928257, by rfl⟩ : syracuseStep 3904343 = 5856515) B5856515
theorem B7517021 : Blo 1735068 7517021 := bstep (se 3 (by rfl) ⟨1409441, by rfl⟩ : syracuseStep 7517021 = 2818883) B2818883
theorem B3519371 : Blo 1735068 3519371 := bstep (se 1 (by rfl) ⟨2639528, by rfl⟩ : syracuseStep 3519371 = 5279057) B5279057
theorem B2929547 : Blo 1735068 2929547 := bstep (se 1 (by rfl) ⟨2197160, by rfl⟩ : syracuseStep 2929547 = 4394321) B4394321
theorem B3904523 : Blo 1735068 3904523 := bstep (se 1 (by rfl) ⟨2928392, by rfl⟩ : syracuseStep 3904523 = 5856785) B5856785
theorem B2929675 : Blo 1735068 2929675 := bstep (se 1 (by rfl) ⟨2197256, by rfl⟩ : syracuseStep 2929675 = 4394513) B4394513
theorem B5559347 : Blo 1735068 5559347 := bstep (se 1 (by rfl) ⟨4169510, by rfl⟩ : syracuseStep 5559347 = 8339021) B8339021
theorem B3904577 : Blo 1735068 3904577 := bstep (se 2 (by rfl) ⟨1464216, by rfl⟩ : syracuseStep 3904577 = 2928433) B2928433
theorem B3339353 : Blo 1735068 3339353 := bstep (se 2 (by rfl) ⟨1252257, by rfl⟩ : syracuseStep 3339353 = 2504515) B2504515
theorem B4944989 : Blo 1735068 4944989 := bstep (se 3 (by rfl) ⟨927185, by rfl⟩ : syracuseStep 4944989 = 1854371) B1854371
theorem B14824579 : Blo 1735068 14824579 := bstep (se 1 (by rfl) ⟨11118434, by rfl⟩ : syracuseStep 14824579 = 22236869) B22236869
theorem B2929817 : Blo 1735068 2929817 := bstep (se 2 (by rfl) ⟨1098681, by rfl⟩ : syracuseStep 2929817 = 2197363) B2197363
theorem B5559475 : Blo 1735068 5559475 := bstep (se 1 (by rfl) ⟨4169606, by rfl⟩ : syracuseStep 5559475 = 8339213) B8339213
theorem B3708119 : Blo 1735068 3708119 := bstep (se 1 (by rfl) ⟨2781089, by rfl⟩ : syracuseStep 3708119 = 5562179) B5562179
theorem B3904793 : Blo 1735068 3904793 := bstep (se 2 (by rfl) ⟨1464297, by rfl⟩ : syracuseStep 3904793 = 2928595) B2928595
theorem B2929945 : Blo 1735068 2929945 := bstep (se 2 (by rfl) ⟨1098729, by rfl⟩ : syracuseStep 2929945 = 2197459) B2197459
theorem B22238509 : Blo 1735068 22238509 := bstep (se 3 (by rfl) ⟨4169720, by rfl⟩ : syracuseStep 22238509 = 8339441) B8339441
theorem B5559617 : Blo 1735068 5559617 := bstep (se 2 (by rfl) ⟨2084856, by rfl⟩ : syracuseStep 5559617 = 4169713) B4169713
theorem B6255965 : Blo 1735068 6255965 := bstep (se 3 (by rfl) ⟨1172993, by rfl⟩ : syracuseStep 6255965 = 2345987) B2345987
theorem B3904883 : Blo 1735068 3904883 := bstep (se 1 (by rfl) ⟨2928662, by rfl⟩ : syracuseStep 3904883 = 5857325) B5857325
theorem B3904919 : Blo 1735068 3904919 := bstep (se 1 (by rfl) ⟨2928689, by rfl⟩ : syracuseStep 3904919 = 5857379) B5857379
theorem B7919021 : Blo 1735068 7919021 := bstep (se 3 (by rfl) ⟨1484816, by rfl⟩ : syracuseStep 7919021 = 2969633) B2969633
theorem B5559731 : Blo 1735068 5559731 := bstep (se 1 (by rfl) ⟨4169798, by rfl⟩ : syracuseStep 5559731 = 8339597) B8339597
theorem B3905099 : Blo 1735068 3905099 := bstep (se 1 (by rfl) ⟨2928824, by rfl⟩ : syracuseStep 3905099 = 5857649) B5857649
theorem B10024541 : Blo 1735068 10024541 := bstep (se 3 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 10024541 = 3759203) B3759203
theorem B3905153 : Blo 1735068 3905153 := bstep (se 2 (by rfl) ⟨1464432, by rfl⟩ : syracuseStep 3905153 = 2928865) B2928865
theorem B2602649 : Blo 1735068 2602649 := bstep (se 2 (by rfl) ⟨975993, by rfl⟩ : syracuseStep 2602649 = 1951987) B1951987
theorem B9885401 : Blo 1735068 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B16684805 : Blo 1735068 16684805 := bstep (se 4 (by rfl) ⟨1564200, by rfl⟩ : syracuseStep 16684805 = 3128401) B3128401
theorem B2602763 : Blo 1735068 2602763 := bstep (se 1 (by rfl) ⟨1952072, by rfl⟩ : syracuseStep 2602763 = 3904145) B3904145
theorem B2602775 : Blo 1735068 2602775 := bstep (se 1 (by rfl) ⟨1952081, by rfl⟩ : syracuseStep 2602775 = 3904163) B3904163
theorem B3757889 : Blo 1735068 3757889 := bstep (se 2 (by rfl) ⟨1409208, by rfl⟩ : syracuseStep 3757889 = 2818417) B2818417
theorem B2602841 : Blo 1735068 2602841 := bstep (se 2 (by rfl) ⟨976065, by rfl⟩ : syracuseStep 2602841 = 1952131) B1952131
theorem B3905369 : Blo 1735068 3905369 := bstep (se 2 (by rfl) ⟨1464513, by rfl⟩ : syracuseStep 3905369 = 2929027) B2929027
theorem B6256529 : Blo 1735068 6256529 := bstep (se 2 (by rfl) ⟨2346198, by rfl⟩ : syracuseStep 6256529 = 4692397) B4692397
theorem B7411607 : Blo 1735068 7411607 := bstep (se 1 (by rfl) ⟨5558705, by rfl⟩ : syracuseStep 7411607 = 11117411) B11117411
theorem B3905459 : Blo 1735068 3905459 := bstep (se 1 (by rfl) ⟨2929094, by rfl⟩ : syracuseStep 3905459 = 5858189) B5858189
theorem B2602955 : Blo 1735068 2602955 := bstep (se 1 (by rfl) ⟨1952216, by rfl⟩ : syracuseStep 2602955 = 3904433) B3904433
theorem B2602967 : Blo 1735068 2602967 := bstep (se 1 (by rfl) ⟨1952225, by rfl⟩ : syracuseStep 2602967 = 3904451) B3904451
theorem B3905495 : Blo 1735068 3905495 := bstep (se 1 (by rfl) ⟨2929121, by rfl⟩ : syracuseStep 3905495 = 5858243) B5858243
theorem B2471897 : Blo 1735068 2471897 := bstep (se 2 (by rfl) ⟨926961, by rfl⟩ : syracuseStep 2471897 = 1853923) B1853923
theorem B6592529 : Blo 1735068 6592529 := bstep (se 2 (by rfl) ⟨2472198, by rfl⟩ : syracuseStep 6592529 = 4944397) B4944397
theorem B2603033 : Blo 1735068 2603033 := bstep (se 2 (by rfl) ⟨976137, by rfl⟩ : syracuseStep 2603033 = 1952275) B1952275
theorem B8788013 : Blo 1735068 8788013 := bstep (se 3 (by rfl) ⟨1647752, by rfl⟩ : syracuseStep 8788013 = 3295505) B3295505
theorem B14825537 : Blo 1735068 14825537 := bstep (se 2 (by rfl) ⟨5559576, by rfl⟩ : syracuseStep 14825537 = 11119153) B11119153
theorem B11876453 : Blo 1735068 11876453 := bstep (se 4 (by rfl) ⟨1113417, by rfl⟩ : syracuseStep 11876453 = 2226835) B2226835
theorem B2603147 : Blo 1735068 2603147 := bstep (se 1 (by rfl) ⟨1952360, by rfl⟩ : syracuseStep 2603147 = 3904721) B3904721
theorem B3905675 : Blo 1735068 3905675 := bstep (se 1 (by rfl) ⟨2929256, by rfl⟩ : syracuseStep 3905675 = 5858513) B5858513
theorem B2603159 : Blo 1735068 2603159 := bstep (se 1 (by rfl) ⟨1952369, by rfl⟩ : syracuseStep 2603159 = 3904739) B3904739
theorem B3905729 : Blo 1735068 3905729 := bstep (se 2 (by rfl) ⟨1464648, by rfl⟩ : syracuseStep 3905729 = 2929297) B2929297
theorem B2603225 : Blo 1735068 2603225 := bstep (se 2 (by rfl) ⟨976209, by rfl⟩ : syracuseStep 2603225 = 1952419) B1952419
theorem B2603339 : Blo 1735068 2603339 := bstep (se 1 (by rfl) ⟨1952504, by rfl⟩ : syracuseStep 2603339 = 3905009) B3905009
theorem B2603351 : Blo 1735068 2603351 := bstep (se 1 (by rfl) ⟨1952513, by rfl⟩ : syracuseStep 2603351 = 3905027) B3905027
theorem B2603417 : Blo 1735068 2603417 := bstep (se 2 (by rfl) ⟨976281, by rfl⟩ : syracuseStep 2603417 = 1952563) B1952563
theorem B3905945 : Blo 1735068 3905945 := bstep (se 2 (by rfl) ⟨1464729, by rfl⟩ : syracuseStep 3905945 = 2929459) B2929459
theorem B1735083 : Blo 1735068 1735083 := bstep (se 1 (by rfl) ⟨1301312, by rfl⟩ : syracuseStep 1735083 = 2602625) B2602625
theorem B1735095 : Blo 1735068 1735095 := bstep (se 1 (by rfl) ⟨1301321, by rfl⟩ : syracuseStep 1735095 = 2602643) B2602643
theorem B1735115 : Blo 1735068 1735115 := bstep (se 1 (by rfl) ⟨1301336, by rfl⟩ : syracuseStep 1735115 = 2602673) B2602673
theorem B1735127 : Blo 1735068 1735127 := bstep (se 1 (by rfl) ⟨1301345, by rfl⟩ : syracuseStep 1735127 = 2602691) B2602691
theorem B6592985 : Blo 1735068 6592985 := bstep (se 2 (by rfl) ⟨2472369, by rfl⟩ : syracuseStep 6592985 = 4944739) B4944739
theorem B1735147 : Blo 1735068 1735147 := bstep (se 1 (by rfl) ⟨1301360, by rfl⟩ : syracuseStep 1735147 = 2602721) B2602721
theorem B3906035 : Blo 1735068 3906035 := bstep (se 1 (by rfl) ⟨2929526, by rfl⟩ : syracuseStep 3906035 = 5859053) B5859053
theorem B1735159 : Blo 1735068 1735159 := bstep (se 1 (by rfl) ⟨1301369, by rfl⟩ : syracuseStep 1735159 = 2602739) B2602739
theorem B1735179 : Blo 1735068 1735179 := bstep (se 1 (by rfl) ⟨1301384, by rfl⟩ : syracuseStep 1735179 = 2602769) B2602769
theorem B2603531 : Blo 1735068 2603531 := bstep (se 1 (by rfl) ⟨1952648, by rfl⟩ : syracuseStep 2603531 = 3905297) B3905297
theorem B1735191 : Blo 1735068 1735191 := bstep (se 1 (by rfl) ⟨1301393, by rfl⟩ : syracuseStep 1735191 = 2602787) B2602787
theorem B2603543 : Blo 1735068 2603543 := bstep (se 1 (by rfl) ⟨1952657, by rfl⟩ : syracuseStep 2603543 = 3905315) B3905315
theorem B3906071 : Blo 1735068 3906071 := bstep (se 1 (by rfl) ⟨2929553, by rfl⟩ : syracuseStep 3906071 = 5859107) B5859107
theorem B1735211 : Blo 1735068 1735211 := bstep (se 1 (by rfl) ⟨1301408, by rfl⟩ : syracuseStep 1735211 = 2602817) B2602817
theorem B1735223 : Blo 1735068 1735223 := bstep (se 1 (by rfl) ⟨1301417, by rfl⟩ : syracuseStep 1735223 = 2602835) B2602835
theorem B1956407 : Blo 1735068 1956407 := bstep (se 1 (by rfl) ⟨1467305, by rfl⟩ : syracuseStep 1956407 = 2934611) B2934611
theorem B1735243 : Blo 1735068 1735243 := bstep (se 1 (by rfl) ⟨1301432, by rfl⟩ : syracuseStep 1735243 = 2602865) B2602865
theorem B1735255 : Blo 1735068 1735255 := bstep (se 1 (by rfl) ⟨1301441, by rfl⟩ : syracuseStep 1735255 = 2602883) B2602883
theorem B2472535 : Blo 1735068 2472535 := bstep (se 1 (by rfl) ⟨1854401, by rfl⟩ : syracuseStep 2472535 = 3708803) B3708803
theorem B2603609 : Blo 1735068 2603609 := bstep (se 2 (by rfl) ⟨976353, by rfl⟩ : syracuseStep 2603609 = 1952707) B1952707
theorem B1735275 : Blo 1735068 1735275 := bstep (se 1 (by rfl) ⟨1301456, by rfl⟩ : syracuseStep 1735275 = 2602913) B2602913
theorem B1735287 : Blo 1735068 1735287 := bstep (se 1 (by rfl) ⟨1301465, by rfl⟩ : syracuseStep 1735287 = 2602931) B2602931
theorem B1735307 : Blo 1735068 1735307 := bstep (se 1 (by rfl) ⟨1301480, by rfl⟩ : syracuseStep 1735307 = 2602961) B2602961
theorem B1735319 : Blo 1735068 1735319 := bstep (se 1 (by rfl) ⟨1301489, by rfl⟩ : syracuseStep 1735319 = 2602979) B2602979
theorem B1735339 : Blo 1735068 1735339 := bstep (se 1 (by rfl) ⟨1301504, by rfl⟩ : syracuseStep 1735339 = 2603009) B2603009
theorem B6593197 : Blo 1735068 6593197 := bstep (se 3 (by rfl) ⟨1236224, by rfl⟩ : syracuseStep 6593197 = 2472449) B2472449
theorem B1735351 : Blo 1735068 1735351 := bstep (se 1 (by rfl) ⟨1301513, by rfl⟩ : syracuseStep 1735351 = 2603027) B2603027
theorem B1735371 : Blo 1735068 1735371 := bstep (se 1 (by rfl) ⟨1301528, by rfl⟩ : syracuseStep 1735371 = 2603057) B2603057
theorem B2603723 : Blo 1735068 2603723 := bstep (se 1 (by rfl) ⟨1952792, by rfl⟩ : syracuseStep 2603723 = 3905585) B3905585
theorem B3906251 : Blo 1735068 3906251 := bstep (se 1 (by rfl) ⟨2929688, by rfl⟩ : syracuseStep 3906251 = 5859377) B5859377
theorem B1735383 : Blo 1735068 1735383 := bstep (se 1 (by rfl) ⟨1301537, by rfl⟩ : syracuseStep 1735383 = 2603075) B2603075
theorem B2603735 : Blo 1735068 2603735 := bstep (se 1 (by rfl) ⟨1952801, by rfl⟩ : syracuseStep 2603735 = 3905603) B3905603
theorem B1735403 : Blo 1735068 1735403 := bstep (se 1 (by rfl) ⟨1301552, by rfl⟩ : syracuseStep 1735403 = 2603105) B2603105
theorem B1735415 : Blo 1735068 1735415 := bstep (se 1 (by rfl) ⟨1301561, by rfl⟩ : syracuseStep 1735415 = 2603123) B2603123
theorem B3906305 : Blo 1735068 3906305 := bstep (se 2 (by rfl) ⟨1464864, by rfl⟩ : syracuseStep 3906305 = 2929729) B2929729
theorem B1735435 : Blo 1735068 1735435 := bstep (se 1 (by rfl) ⟨1301576, by rfl⟩ : syracuseStep 1735435 = 2603153) B2603153
theorem B1735447 : Blo 1735068 1735447 := bstep (se 1 (by rfl) ⟨1301585, by rfl⟩ : syracuseStep 1735447 = 2603171) B2603171
theorem B2603801 : Blo 1735068 2603801 := bstep (se 2 (by rfl) ⟨976425, by rfl⟩ : syracuseStep 2603801 = 1952851) B1952851
theorem B1735467 : Blo 1735068 1735467 := bstep (se 1 (by rfl) ⟨1301600, by rfl⟩ : syracuseStep 1735467 = 2603201) B2603201
theorem B1735479 : Blo 1735068 1735479 := bstep (se 1 (by rfl) ⟨1301609, by rfl⟩ : syracuseStep 1735479 = 2603219) B2603219
theorem B1735499 : Blo 1735068 1735499 := bstep (se 1 (by rfl) ⟨1301624, by rfl⟩ : syracuseStep 1735499 = 2603249) B2603249
theorem B1735511 : Blo 1735068 1735511 := bstep (se 1 (by rfl) ⟨1301633, by rfl⟩ : syracuseStep 1735511 = 2603267) B2603267
theorem B1735531 : Blo 1735068 1735531 := bstep (se 1 (by rfl) ⟨1301648, by rfl⟩ : syracuseStep 1735531 = 2603297) B2603297
theorem B1735543 : Blo 1735068 1735543 := bstep (se 1 (by rfl) ⟨1301657, by rfl⟩ : syracuseStep 1735543 = 2603315) B2603315
theorem B1735563 : Blo 1735068 1735563 := bstep (se 1 (by rfl) ⟨1301672, by rfl⟩ : syracuseStep 1735563 = 2603345) B2603345
theorem B2603915 : Blo 1735068 2603915 := bstep (se 1 (by rfl) ⟨1952936, by rfl⟩ : syracuseStep 2603915 = 3905873) B3905873
theorem B1735575 : Blo 1735068 1735575 := bstep (se 1 (by rfl) ⟨1301681, by rfl⟩ : syracuseStep 1735575 = 2603363) B2603363
theorem B2603927 : Blo 1735068 2603927 := bstep (se 1 (by rfl) ⟨1952945, by rfl⟩ : syracuseStep 2603927 = 3905891) B3905891
theorem B1735595 : Blo 1735068 1735595 := bstep (se 1 (by rfl) ⟨1301696, by rfl⟩ : syracuseStep 1735595 = 2603393) B2603393
theorem B3431347 : Blo 1735068 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B1735607 : Blo 1735068 1735607 := bstep (se 1 (by rfl) ⟨1301705, by rfl⟩ : syracuseStep 1735607 = 2603411) B2603411
theorem B1735627 : Blo 1735068 1735627 := bstep (se 1 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 1735627 = 2603441) B2603441
theorem B1735639 : Blo 1735068 1735639 := bstep (se 1 (by rfl) ⟨1301729, by rfl⟩ : syracuseStep 1735639 = 2603459) B2603459
theorem B2603993 : Blo 1735068 2603993 := bstep (se 2 (by rfl) ⟨976497, by rfl⟩ : syracuseStep 2603993 = 1952995) B1952995
theorem B3906521 : Blo 1735068 3906521 := bstep (se 2 (by rfl) ⟨1464945, by rfl⟩ : syracuseStep 3906521 = 2929891) B2929891
theorem B14080985 : Blo 1735068 14080985 := bstep (se 2 (by rfl) ⟨5280369, by rfl⟩ : syracuseStep 14080985 = 10560739) B10560739
theorem B5348317 : Blo 1735068 5348317 := bstep (se 3 (by rfl) ⟨1002809, by rfl⟩ : syracuseStep 5348317 = 2005619) B2005619
theorem B6593501 : Blo 1735068 6593501 := bstep (se 3 (by rfl) ⟨1236281, by rfl⟩ : syracuseStep 6593501 = 2472563) B2472563
theorem B1735659 : Blo 1735068 1735659 := bstep (se 1 (by rfl) ⟨1301744, by rfl⟩ : syracuseStep 1735659 = 2603489) B2603489
theorem B1735671 : Blo 1735068 1735671 := bstep (se 1 (by rfl) ⟨1301753, by rfl⟩ : syracuseStep 1735671 = 2603507) B2603507
theorem B1735691 : Blo 1735068 1735691 := bstep (se 1 (by rfl) ⟨1301768, by rfl⟩ : syracuseStep 1735691 = 2603537) B2603537
theorem B1735703 : Blo 1735068 1735703 := bstep (se 1 (by rfl) ⟨1301777, by rfl⟩ : syracuseStep 1735703 = 2603555) B2603555
theorem B5938199 : Blo 1735068 5938199 := bstep (se 1 (by rfl) ⟨4453649, by rfl⟩ : syracuseStep 5938199 = 8907299) B8907299
theorem B1735723 : Blo 1735068 1735723 := bstep (se 1 (by rfl) ⟨1301792, by rfl⟩ : syracuseStep 1735723 = 2603585) B2603585
theorem B3906611 : Blo 1735068 3906611 := bstep (se 1 (by rfl) ⟨2929958, by rfl⟩ : syracuseStep 3906611 = 5859917) B5859917
theorem B1735735 : Blo 1735068 1735735 := bstep (se 1 (by rfl) ⟨1301801, by rfl⟩ : syracuseStep 1735735 = 2603603) B2603603
theorem B1735755 : Blo 1735068 1735755 := bstep (se 1 (by rfl) ⟨1301816, by rfl⟩ : syracuseStep 1735755 = 2603633) B2603633
theorem B2604107 : Blo 1735068 2604107 := bstep (se 1 (by rfl) ⟨1953080, by rfl⟩ : syracuseStep 2604107 = 3906161) B3906161
theorem B1735767 : Blo 1735068 1735767 := bstep (se 1 (by rfl) ⟨1301825, by rfl⟩ : syracuseStep 1735767 = 2603651) B2603651
theorem B2604119 : Blo 1735068 2604119 := bstep (se 1 (by rfl) ⟨1953089, by rfl⟩ : syracuseStep 2604119 = 3906179) B3906179
theorem B3906647 : Blo 1735068 3906647 := bstep (se 1 (by rfl) ⟨2929985, by rfl⟩ : syracuseStep 3906647 = 5859971) B5859971
theorem B1735787 : Blo 1735068 1735787 := bstep (se 1 (by rfl) ⟨1301840, by rfl⟩ : syracuseStep 1735787 = 2603681) B2603681
theorem B1735799 : Blo 1735068 1735799 := bstep (se 1 (by rfl) ⟨1301849, by rfl⟩ : syracuseStep 1735799 = 2603699) B2603699
theorem B1735819 : Blo 1735068 1735819 := bstep (se 1 (by rfl) ⟨1301864, by rfl⟩ : syracuseStep 1735819 = 2603729) B2603729
theorem B5856407 : Blo 1735068 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B1735831 : Blo 1735068 1735831 := bstep (se 1 (by rfl) ⟨1301873, by rfl⟩ : syracuseStep 1735831 = 2603747) B2603747
theorem B2604185 : Blo 1735068 2604185 := bstep (se 2 (by rfl) ⟨976569, by rfl⟩ : syracuseStep 2604185 = 1953139) B1953139
theorem B1735851 : Blo 1735068 1735851 := bstep (se 1 (by rfl) ⟨1301888, by rfl⟩ : syracuseStep 1735851 = 2603777) B2603777
theorem B1735863 : Blo 1735068 1735863 := bstep (se 1 (by rfl) ⟨1301897, by rfl⟩ : syracuseStep 1735863 = 2603795) B2603795
theorem B1735883 : Blo 1735068 1735883 := bstep (se 1 (by rfl) ⟨1301912, by rfl⟩ : syracuseStep 1735883 = 2603825) B2603825
theorem B1735895 : Blo 1735068 1735895 := bstep (se 1 (by rfl) ⟨1301921, by rfl⟩ : syracuseStep 1735895 = 2603843) B2603843
theorem B1735915 : Blo 1735068 1735915 := bstep (se 1 (by rfl) ⟨1301936, by rfl⟩ : syracuseStep 1735915 = 2603873) B2603873
theorem B1735927 : Blo 1735068 1735927 := bstep (se 1 (by rfl) ⟨1301945, by rfl⟩ : syracuseStep 1735927 = 2603891) B2603891
theorem B3341569 : Blo 1735068 3341569 := bstep (se 2 (by rfl) ⟨1253088, by rfl⟩ : syracuseStep 3341569 = 2506177) B2506177
theorem B1735947 : Blo 1735068 1735947 := bstep (se 1 (by rfl) ⟨1301960, by rfl⟩ : syracuseStep 1735947 = 2603921) B2603921
theorem B2604299 : Blo 1735068 2604299 := bstep (se 1 (by rfl) ⟨1953224, by rfl⟩ : syracuseStep 2604299 = 3906449) B3906449
theorem B3906827 : Blo 1735068 3906827 := bstep (se 1 (by rfl) ⟨2930120, by rfl⟩ : syracuseStep 3906827 = 5860241) B5860241
theorem B1735959 : Blo 1735068 1735959 := bstep (se 1 (by rfl) ⟨1301969, by rfl⟩ : syracuseStep 1735959 = 2603939) B2603939
theorem B2604311 : Blo 1735068 2604311 := bstep (se 1 (by rfl) ⟨1953233, by rfl⟩ : syracuseStep 2604311 = 3906467) B3906467
theorem B1735979 : Blo 1735068 1735979 := bstep (se 1 (by rfl) ⟨1301984, by rfl⟩ : syracuseStep 1735979 = 2603969) B2603969
theorem B1735991 : Blo 1735068 1735991 := bstep (se 1 (by rfl) ⟨1301993, by rfl⟩ : syracuseStep 1735991 = 2603987) B2603987
theorem B3906881 : Blo 1735068 3906881 := bstep (se 2 (by rfl) ⟨1465080, by rfl⟩ : syracuseStep 3906881 = 2930161) B2930161
theorem B1736011 : Blo 1735068 1736011 := bstep (se 1 (by rfl) ⟨1302008, by rfl⟩ : syracuseStep 1736011 = 2604017) B2604017
theorem B1736023 : Blo 1735068 1736023 := bstep (se 1 (by rfl) ⟨1302017, by rfl⟩ : syracuseStep 1736023 = 2604035) B2604035
theorem B2604377 : Blo 1735068 2604377 := bstep (se 2 (by rfl) ⟨976641, by rfl⟩ : syracuseStep 2604377 = 1953283) B1953283
theorem B1736043 : Blo 1735068 1736043 := bstep (se 1 (by rfl) ⟨1302032, by rfl⟩ : syracuseStep 1736043 = 2604065) B2604065
theorem B1736055 : Blo 1735068 1736055 := bstep (se 1 (by rfl) ⟨1302041, by rfl⟩ : syracuseStep 1736055 = 2604083) B2604083
theorem B1736075 : Blo 1735068 1736075 := bstep (se 1 (by rfl) ⟨1302056, by rfl⟩ : syracuseStep 1736075 = 2604113) B2604113
theorem B1736087 : Blo 1735068 1736087 := bstep (se 1 (by rfl) ⟨1302065, by rfl⟩ : syracuseStep 1736087 = 2604131) B2604131
theorem B1736107 : Blo 1735068 1736107 := bstep (se 1 (by rfl) ⟨1302080, by rfl⟩ : syracuseStep 1736107 = 2604161) B2604161
theorem B1736119 : Blo 1735068 1736119 := bstep (se 1 (by rfl) ⟨1302089, by rfl⟩ : syracuseStep 1736119 = 2604179) B2604179
theorem B1736139 : Blo 1735068 1736139 := bstep (se 1 (by rfl) ⟨1302104, by rfl⟩ : syracuseStep 1736139 = 2604209) B2604209
theorem B2604491 : Blo 1735068 2604491 := bstep (se 1 (by rfl) ⟨1953368, by rfl⟩ : syracuseStep 2604491 = 3906737) B3906737
theorem B1736151 : Blo 1735068 1736151 := bstep (se 1 (by rfl) ⟨1302113, by rfl⟩ : syracuseStep 1736151 = 2604227) B2604227
theorem B2604503 : Blo 1735068 2604503 := bstep (se 1 (by rfl) ⟨1953377, by rfl⟩ : syracuseStep 2604503 = 3906755) B3906755
theorem B1736171 : Blo 1735068 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B1736183 : Blo 1735068 1736183 := bstep (se 1 (by rfl) ⟨1302137, by rfl⟩ : syracuseStep 1736183 = 2604275) B2604275
theorem B1736203 : Blo 1735068 1736203 := bstep (se 1 (by rfl) ⟨1302152, by rfl⟩ : syracuseStep 1736203 = 2604305) B2604305
theorem B24731153 : Blo 1735068 24731153 := bstep (se 2 (by rfl) ⟨9274182, by rfl⟩ : syracuseStep 24731153 = 18548365) B18548365
theorem B1736215 : Blo 1735068 1736215 := bstep (se 1 (by rfl) ⟨1302161, by rfl⟩ : syracuseStep 1736215 = 2604323) B2604323
theorem B2604569 : Blo 1735068 2604569 := bstep (se 2 (by rfl) ⟨976713, by rfl⟩ : syracuseStep 2604569 = 1953427) B1953427
theorem B3907097 : Blo 1735068 3907097 := bstep (se 2 (by rfl) ⟨1465161, by rfl⟩ : syracuseStep 3907097 = 2930323) B2930323
theorem B1736235 : Blo 1735068 1736235 := bstep (se 1 (by rfl) ⟨1302176, by rfl⟩ : syracuseStep 1736235 = 2604353) B2604353
theorem B1736247 : Blo 1735068 1736247 := bstep (se 1 (by rfl) ⟨1302185, by rfl⟩ : syracuseStep 1736247 = 2604371) B2604371
theorem B1736267 : Blo 1735068 1736267 := bstep (se 1 (by rfl) ⟨1302200, by rfl⟩ : syracuseStep 1736267 = 2604401) B2604401
theorem B1736279 : Blo 1735068 1736279 := bstep (se 1 (by rfl) ⟨1302209, by rfl⟩ : syracuseStep 1736279 = 2604419) B2604419
theorem B1736299 : Blo 1735068 1736299 := bstep (se 1 (by rfl) ⟨1302224, by rfl⟩ : syracuseStep 1736299 = 2604449) B2604449
theorem B3907187 : Blo 1735068 3907187 := bstep (se 1 (by rfl) ⟨2930390, by rfl⟩ : syracuseStep 3907187 = 5860781) B5860781
theorem B1736311 : Blo 1735068 1736311 := bstep (se 1 (by rfl) ⟨1302233, by rfl⟩ : syracuseStep 1736311 = 2604467) B2604467
theorem B1736331 : Blo 1735068 1736331 := bstep (se 1 (by rfl) ⟨1302248, by rfl⟩ : syracuseStep 1736331 = 2604497) B2604497
theorem B2604683 : Blo 1735068 2604683 := bstep (se 1 (by rfl) ⟨1953512, by rfl⟩ : syracuseStep 2604683 = 3907025) B3907025
theorem B1736343 : Blo 1735068 1736343 := bstep (se 1 (by rfl) ⟨1302257, by rfl⟩ : syracuseStep 1736343 = 2604515) B2604515
theorem B2604695 : Blo 1735068 2604695 := bstep (se 1 (by rfl) ⟨1953521, by rfl⟩ : syracuseStep 2604695 = 3907043) B3907043
theorem B3907223 : Blo 1735068 3907223 := bstep (se 1 (by rfl) ⟨2930417, by rfl⟩ : syracuseStep 3907223 = 5860835) B5860835
theorem B1736363 : Blo 1735068 1736363 := bstep (se 1 (by rfl) ⟨1302272, by rfl⟩ : syracuseStep 1736363 = 2604545) B2604545
theorem B5856947 : Blo 1735068 5856947 := bstep (se 1 (by rfl) ⟨4392710, by rfl⟩ : syracuseStep 5856947 = 8785421) B8785421
theorem B1736375 : Blo 1735068 1736375 := bstep (se 1 (by rfl) ⟨1302281, by rfl⟩ : syracuseStep 1736375 = 2604563) B2604563
theorem B4693697 : Blo 1735068 4693697 := bstep (se 2 (by rfl) ⟨1760136, by rfl⟩ : syracuseStep 4693697 = 3520273) B3520273
theorem B2006731 : Blo 1735068 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B1736395 : Blo 1735068 1736395 := bstep (se 1 (by rfl) ⟨1302296, by rfl⟩ : syracuseStep 1736395 = 2604593) B2604593
theorem B1736407 : Blo 1735068 1736407 := bstep (se 1 (by rfl) ⟨1302305, by rfl⟩ : syracuseStep 1736407 = 2604611) B2604611
theorem B2604761 : Blo 1735068 2604761 := bstep (se 2 (by rfl) ⟨976785, by rfl⟩ : syracuseStep 2604761 = 1953571) B1953571
theorem B1736427 : Blo 1735068 1736427 := bstep (se 1 (by rfl) ⟨1302320, by rfl⟩ : syracuseStep 1736427 = 2604641) B2604641
theorem B1736439 : Blo 1735068 1736439 := bstep (se 1 (by rfl) ⟨1302329, by rfl⟩ : syracuseStep 1736439 = 2604659) B2604659
theorem B1736459 : Blo 1735068 1736459 := bstep (se 1 (by rfl) ⟨1302344, by rfl⟩ : syracuseStep 1736459 = 2604689) B2604689
theorem B1736471 : Blo 1735068 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B1736491 : Blo 1735068 1736491 := bstep (se 1 (by rfl) ⟨1302368, by rfl⟩ : syracuseStep 1736491 = 2604737) B2604737
theorem B1736503 : Blo 1735068 1736503 := bstep (se 1 (by rfl) ⟨1302377, by rfl⟩ : syracuseStep 1736503 = 2604755) B2604755
theorem B1736523 : Blo 1735068 1736523 := bstep (se 1 (by rfl) ⟨1302392, by rfl⟩ : syracuseStep 1736523 = 2604785) B2604785
theorem B1736535 : Blo 1735068 1736535 := bstep (se 1 (by rfl) ⟨1302401, by rfl⟩ : syracuseStep 1736535 = 2604803) B2604803
theorem B1736555 : Blo 1735068 1736555 := bstep (se 1 (by rfl) ⟨1302416, by rfl⟩ : syracuseStep 1736555 = 2604833) B2604833
theorem B1736567 : Blo 1735068 1736567 := bstep (se 1 (by rfl) ⟨1302425, by rfl⟩ : syracuseStep 1736567 = 2604851) B2604851
theorem B5857217 : Blo 1735068 5857217 := bstep (se 2 (by rfl) ⟨2196456, by rfl⟩ : syracuseStep 5857217 = 4392913) B4392913
theorem B2539579 : Blo 1735068 2539579 := bstep (se 1 (by rfl) ⟨1904684, by rfl⟩ : syracuseStep 2539579 = 3809369) B3809369
theorem B4169875 : Blo 1735068 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B8904941 : Blo 1735068 8904941 := bstep (se 3 (by rfl) ⟨1669676, by rfl⟩ : syracuseStep 8904941 = 3339353) B3339353
theorem B5857595 : Blo 1735068 5857595 := bstep (se 1 (by rfl) ⟨4393196, by rfl⟩ : syracuseStep 5857595 = 8786393) B8786393
theorem B11125201 : Blo 1735068 11125201 := bstep (se 2 (by rfl) ⟨4171950, by rfl⟩ : syracuseStep 11125201 = 8343901) B8343901
theorem B2196011 : Blo 1735068 2196011 := bstep (se 1 (by rfl) ⟨1647008, by rfl⟩ : syracuseStep 2196011 = 3294017) B3294017
theorem B9888317 : Blo 1735068 9888317 := bstep (se 3 (by rfl) ⟨1854059, by rfl⟩ : syracuseStep 9888317 = 3708119) B3708119
theorem B4227851 : Blo 1735068 4227851 := bstep (se 1 (by rfl) ⟨3170888, by rfl⟩ : syracuseStep 4227851 = 6341777) B6341777
theorem B5858081 : Blo 1735068 5858081 := bstep (se 2 (by rfl) ⟨2196780, by rfl⟩ : syracuseStep 5858081 = 4393561) B4393561
theorem B5276477 : Blo 1735068 5276477 := bstep (se 3 (by rfl) ⟨989339, by rfl⟩ : syracuseStep 5276477 = 1978679) B1978679
theorem B8790929 : Blo 1735068 8790929 := bstep (se 2 (by rfl) ⟨3296598, by rfl⟩ : syracuseStep 8790929 = 6593197) B6593197
theorem B2196487 : Blo 1735068 2196487 := bstep (se 1 (by rfl) ⟨1647365, by rfl⟩ : syracuseStep 2196487 = 3294731) B3294731
theorem B3171361 : Blo 1735068 3171361 := bstep (se 2 (by rfl) ⟨1189260, by rfl⟩ : syracuseStep 3171361 = 2378521) B2378521
theorem B4392083 : Blo 1735068 4392083 := bstep (se 1 (by rfl) ⟨3294062, by rfl⟩ : syracuseStep 4392083 = 6588125) B6588125
theorem B4171019 : Blo 1735068 4171019 := bstep (se 1 (by rfl) ⟨3128264, by rfl⟩ : syracuseStep 4171019 = 6256529) B6256529
theorem B4941071 : Blo 1735068 4941071 := bstep (se 1 (by rfl) ⟨3705803, by rfl⟩ : syracuseStep 4941071 = 7411607) B7411607
theorem B5858675 : Blo 1735068 5858675 := bstep (se 1 (by rfl) ⟨4394006, by rfl⟩ : syracuseStep 5858675 = 8788013) B8788013
theorem B4392377 : Blo 1735068 4392377 := bstep (se 2 (by rfl) ⟨1647141, by rfl⟩ : syracuseStep 4392377 = 3294283) B3294283
theorem B3958217 : Blo 1735068 3958217 := bstep (se 2 (by rfl) ⟨1484331, by rfl⟩ : syracuseStep 3958217 = 2968663) B2968663
theorem B2196983 : Blo 1735068 2196983 := bstep (se 1 (by rfl) ⟨1647737, by rfl⟩ : syracuseStep 2196983 = 3295475) B3295475
theorem B65103437 : Blo 1735068 65103437 := bstep (se 3 (by rfl) ⟨12206894, by rfl⟩ : syracuseStep 65103437 = 24413789) B24413789
theorem B2197135 : Blo 1735068 2197135 := bstep (se 1 (by rfl) ⟨1647851, by rfl⟩ : syracuseStep 2197135 = 3295703) B3295703
theorem B5793569 : Blo 1735068 5793569 := bstep (se 2 (by rfl) ⟨2172588, by rfl⟩ : syracuseStep 5793569 = 4345177) B4345177
theorem B3295019 : Blo 1735068 3295019 := bstep (se 1 (by rfl) ⟨2471264, by rfl⟩ : syracuseStep 3295019 = 4942529) B4942529
theorem B2197307 : Blo 1735068 2197307 := bstep (se 1 (by rfl) ⟨1647980, by rfl⟩ : syracuseStep 2197307 = 3295961) B3295961
theorem B8783801 : Blo 1735068 8783801 := bstep (se 2 (by rfl) ⟨3293925, by rfl⟩ : syracuseStep 8783801 = 6587851) B6587851
theorem B3958799 : Blo 1735068 3958799 := bstep (se 1 (by rfl) ⟨2969099, by rfl⟩ : syracuseStep 3958799 = 5938199) B5938199
theorem B4393075 : Blo 1735068 4393075 := bstep (se 1 (by rfl) ⟨3294806, by rfl⟩ : syracuseStep 4393075 = 6589613) B6589613
theorem B4393217 : Blo 1735068 4393217 := bstep (se 2 (by rfl) ⟨1647456, by rfl⟩ : syracuseStep 4393217 = 3294913) B3294913
theorem B1952059 : Blo 1735068 1952059 := bstep (se 1 (by rfl) ⟨1464044, by rfl⟩ : syracuseStep 1952059 = 2928089) B2928089
theorem B8907097 : Blo 1735068 8907097 := bstep (se 2 (by rfl) ⟨3340161, by rfl⟩ : syracuseStep 8907097 = 6680323) B6680323
theorem B8342135 : Blo 1735068 8342135 := bstep (se 1 (by rfl) ⟨6256601, by rfl⟩ : syracuseStep 8342135 = 12513203) B12513203
theorem B4393673 : Blo 1735068 4393673 := bstep (se 2 (by rfl) ⟨1647627, by rfl⟩ : syracuseStep 4393673 = 3295255) B3295255
theorem B1952527 : Blo 1735068 1952527 := bstep (se 1 (by rfl) ⟨1464395, by rfl⟩ : syracuseStep 1952527 = 2928791) B2928791
theorem B4942711 : Blo 1735068 4942711 := bstep (se 1 (by rfl) ⟨3707033, by rfl⟩ : syracuseStep 4942711 = 7414067) B7414067
theorem B7416785 : Blo 1735068 7416785 := bstep (se 2 (by rfl) ⟨2781294, by rfl⟩ : syracuseStep 7416785 = 5562589) B5562589
theorem B4394027 : Blo 1735068 4394027 := bstep (se 1 (by rfl) ⟨3295520, by rfl⟩ : syracuseStep 4394027 = 6591041) B6591041
theorem B2780219 : Blo 1735068 2780219 := bstep (se 1 (by rfl) ⟨2085164, by rfl⟩ : syracuseStep 2780219 = 4170329) B4170329
theorem B8785097 : Blo 1735068 8785097 := bstep (se 2 (by rfl) ⟨3294411, by rfl⟩ : syracuseStep 8785097 = 6588823) B6588823
theorem B8457473 : Blo 1735068 8457473 := bstep (se 2 (by rfl) ⟨3171552, by rfl⟩ : syracuseStep 8457473 = 6343105) B6343105
theorem B2346247 : Blo 1735068 2346247 := bstep (se 1 (by rfl) ⟨1759685, by rfl⟩ : syracuseStep 2346247 = 3519371) B3519371
theorem B1953031 : Blo 1735068 1953031 := bstep (se 1 (by rfl) ⟨1464773, by rfl⟩ : syracuseStep 1953031 = 2929547) B2929547
theorem B9882917 : Blo 1735068 9882917 := bstep (se 4 (by rfl) ⟨926523, by rfl⟩ : syracuseStep 9882917 = 1853047) B1853047
theorem B3706231 : Blo 1735068 3706231 := bstep (se 1 (by rfl) ⟨2779673, by rfl⟩ : syracuseStep 3706231 = 5559347) B5559347
theorem B35630513 : Blo 1735068 35630513 := bstep (se 2 (by rfl) ⟨13361442, by rfl⟩ : syracuseStep 35630513 = 26722885) B26722885
theorem B1953211 : Blo 1735068 1953211 := bstep (se 1 (by rfl) ⟨1464908, by rfl⟩ : syracuseStep 1953211 = 2929817) B2929817
theorem B3296713 : Blo 1735068 3296713 := bstep (se 2 (by rfl) ⟨1236267, by rfl⟩ : syracuseStep 3296713 = 2472535) B2472535
theorem B22244867 : Blo 1735068 22244867 := bstep (se 1 (by rfl) ⟨16683650, by rfl⟩ : syracuseStep 22244867 = 33367301) B33367301
theorem B2928143 : Blo 1735068 2928143 := bstep (se 1 (by rfl) ⟨2196107, by rfl⟩ : syracuseStep 2928143 = 4392215) B4392215
theorem B3706411 : Blo 1735068 3706411 := bstep (se 1 (by rfl) ⟨2779808, by rfl⟩ : syracuseStep 3706411 = 5559617) B5559617
theorem B16682573 : Blo 1735068 16682573 := bstep (se 3 (by rfl) ⟨3127982, by rfl⟩ : syracuseStep 16682573 = 6255965) B6255965
theorem B5279347 : Blo 1735068 5279347 := bstep (se 1 (by rfl) ⟨3959510, by rfl⟩ : syracuseStep 5279347 = 7919021) B7919021
theorem B3706487 : Blo 1735068 3706487 := bstep (se 1 (by rfl) ⟨2779865, by rfl⟩ : syracuseStep 3706487 = 5559731) B5559731
theorem B6254351 : Blo 1735068 6254351 := bstep (se 1 (by rfl) ⟨4690763, by rfl⟩ : syracuseStep 6254351 = 9381527) B9381527
theorem B6590267 : Blo 1735068 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B35630999 : Blo 1735068 35630999 := bstep (se 1 (by rfl) ⟨26723249, by rfl⟩ : syracuseStep 35630999 = 53446499) B53446499
theorem B7131089 : Blo 1735068 7131089 := bstep (se 2 (by rfl) ⟨2674158, by rfl⟩ : syracuseStep 7131089 = 5348317) B5348317
theorem B4395019 : Blo 1735068 4395019 := bstep (se 1 (by rfl) ⟨3296264, by rfl⟩ : syracuseStep 4395019 = 6592529) B6592529
theorem B9883691 : Blo 1735068 9883691 := bstep (se 1 (by rfl) ⟨7412768, by rfl⟩ : syracuseStep 9883691 = 14825537) B14825537
theorem B2928683 : Blo 1735068 2928683 := bstep (se 1 (by rfl) ⟨2196512, by rfl⟩ : syracuseStep 2928683 = 4393025) B4393025
theorem B7917635 : Blo 1735068 7917635 := bstep (se 1 (by rfl) ⟨5938226, by rfl⟩ : syracuseStep 7917635 = 11876453) B11876453
theorem B4943987 : Blo 1735068 4943987 := bstep (se 1 (by rfl) ⟨3707990, by rfl⟩ : syracuseStep 4943987 = 7415981) B7415981
theorem B4395161 : Blo 1735068 4395161 := bstep (se 2 (by rfl) ⟨1648185, by rfl⟩ : syracuseStep 4395161 = 3296371) B3296371
theorem B6590753 : Blo 1735068 6590753 := bstep (se 2 (by rfl) ⟨2471532, by rfl⟩ : syracuseStep 6590753 = 4943065) B4943065
theorem B4395323 : Blo 1735068 4395323 := bstep (se 1 (by rfl) ⟨3296492, by rfl⟩ : syracuseStep 4395323 = 6592985) B6592985
theorem B4944215 : Blo 1735068 4944215 := bstep (se 1 (by rfl) ⟨3708161, by rfl⟩ : syracuseStep 4944215 = 7416323) B7416323
theorem B29651345 : Blo 1735068 29651345 := bstep (se 2 (by rfl) ⟨11119254, by rfl⟩ : syracuseStep 29651345 = 22238509) B22238509
theorem B3903929 : Blo 1735068 3903929 := bstep (se 2 (by rfl) ⟨1463973, by rfl⟩ : syracuseStep 3903929 = 2927947) B2927947
theorem B2929081 : Blo 1735068 2929081 := bstep (se 2 (by rfl) ⟨1098405, by rfl⟩ : syracuseStep 2929081 = 2196811) B2196811
theorem B4395667 : Blo 1735068 4395667 := bstep (se 1 (by rfl) ⟨3296750, by rfl⟩ : syracuseStep 4395667 = 6593501) B6593501
theorem B3904271 : Blo 1735068 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B3904289 : Blo 1735068 3904289 := bstep (se 2 (by rfl) ⟨1464108, by rfl⟩ : syracuseStep 3904289 = 2928217) B2928217
theorem B2675641 : Blo 1735068 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B14070731 : Blo 1735068 14070731 := bstep (se 1 (by rfl) ⟨10553048, by rfl⟩ : syracuseStep 14070731 = 21106097) B21106097
theorem B16487435 : Blo 1735068 16487435 := bstep (se 1 (by rfl) ⟨12365576, by rfl⟩ : syracuseStep 16487435 = 24731153) B24731153
theorem B3904631 : Blo 1735068 3904631 := bstep (se 1 (by rfl) ⟨2928473, by rfl⟩ : syracuseStep 3904631 = 5856947) B5856947
theorem B2929783 : Blo 1735068 2929783 := bstep (se 1 (by rfl) ⟨2197337, by rfl⟩ : syracuseStep 2929783 = 4394675) B4394675
theorem B6591725 : Blo 1735068 6591725 := bstep (se 3 (by rfl) ⟨1235948, by rfl⟩ : syracuseStep 6591725 = 2471897) B2471897
theorem B7517441 : Blo 1735068 7517441 := bstep (se 2 (by rfl) ⟨2819040, by rfl⟩ : syracuseStep 7517441 = 5638081) B5638081
theorem B3904811 : Blo 1735068 3904811 := bstep (se 1 (by rfl) ⟨2928608, by rfl⟩ : syracuseStep 3904811 = 5857217) B5857217
theorem B2929979 : Blo 1735068 2929979 := bstep (se 1 (by rfl) ⟨2197484, by rfl⟩ : syracuseStep 2929979 = 4394969) B4394969
theorem B41178545 : Blo 1735068 41178545 := bstep (se 2 (by rfl) ⟨15441954, by rfl⟩ : syracuseStep 41178545 = 30883909) B30883909
theorem B9885149 : Blo 1735068 9885149 := bstep (se 3 (by rfl) ⟨1853465, by rfl⟩ : syracuseStep 9885149 = 3706931) B3706931
theorem B6592043 : Blo 1735068 6592043 := bstep (se 1 (by rfl) ⟨4944032, by rfl⟩ : syracuseStep 6592043 = 9888065) B9888065
theorem B13186637 : Blo 1735068 13186637 := bstep (se 3 (by rfl) ⟨2472494, by rfl⟩ : syracuseStep 13186637 = 4944989) B4944989
theorem B2602631 : Blo 1735068 2602631 := bstep (se 1 (by rfl) ⟨1951973, by rfl⟩ : syracuseStep 2602631 = 3903947) B3903947
theorem B3905171 : Blo 1735068 3905171 := bstep (se 1 (by rfl) ⟨2928878, by rfl⟩ : syracuseStep 3905171 = 5857757) B5857757
theorem B2602667 : Blo 1735068 2602667 := bstep (se 1 (by rfl) ⟨1952000, by rfl⟩ : syracuseStep 2602667 = 3904001) B3904001
theorem B2602697 : Blo 1735068 2602697 := bstep (se 2 (by rfl) ⟨976011, by rfl⟩ : syracuseStep 2602697 = 1952023) B1952023
theorem B3905225 : Blo 1735068 3905225 := bstep (se 2 (by rfl) ⟨1464459, by rfl⟩ : syracuseStep 3905225 = 2928919) B2928919
theorem B2930377 : Blo 1735068 2930377 := bstep (se 2 (by rfl) ⟨1098891, by rfl⟩ : syracuseStep 2930377 = 2197783) B2197783
theorem B2602811 : Blo 1735068 2602811 := bstep (se 1 (by rfl) ⟨1952108, by rfl⟩ : syracuseStep 2602811 = 3904217) B3904217
theorem B2602871 : Blo 1735068 2602871 := bstep (se 1 (by rfl) ⟨1952153, by rfl⟩ : syracuseStep 2602871 = 3904307) B3904307
theorem B2602895 : Blo 1735068 2602895 := bstep (se 1 (by rfl) ⟨1952171, by rfl⟩ : syracuseStep 2602895 = 3904343) B3904343
theorem B13547417 : Blo 1735068 13547417 := bstep (se 2 (by rfl) ⟨5080281, by rfl⟩ : syracuseStep 13547417 = 10160563) B10160563
theorem B2602937 : Blo 1735068 2602937 := bstep (se 2 (by rfl) ⟨976101, by rfl⟩ : syracuseStep 2602937 = 1952203) B1952203
theorem B2603015 : Blo 1735068 2603015 := bstep (se 1 (by rfl) ⟨1952261, by rfl⟩ : syracuseStep 2603015 = 3904523) B3904523
theorem B84449297 : Blo 1735068 84449297 := bstep (se 2 (by rfl) ⟨31668486, by rfl⟩ : syracuseStep 84449297 = 63336973) B63336973
theorem B2603051 : Blo 1735068 2603051 := bstep (se 1 (by rfl) ⟨1952288, by rfl⟩ : syracuseStep 2603051 = 3904577) B3904577
theorem B2603081 : Blo 1735068 2603081 := bstep (se 2 (by rfl) ⟨976155, by rfl⟩ : syracuseStep 2603081 = 1952311) B1952311
theorem B2603195 : Blo 1735068 2603195 := bstep (se 1 (by rfl) ⟨1952396, by rfl⟩ : syracuseStep 2603195 = 3904793) B3904793
theorem B7411949 : Blo 1735068 7411949 := bstep (se 3 (by rfl) ⟨1389740, by rfl⟩ : syracuseStep 7411949 = 2779481) B2779481
theorem B2603255 : Blo 1735068 2603255 := bstep (se 1 (by rfl) ⟨1952441, by rfl⟩ : syracuseStep 2603255 = 3904883) B3904883
theorem B2603279 : Blo 1735068 2603279 := bstep (se 1 (by rfl) ⟨1952459, by rfl⟩ : syracuseStep 2603279 = 3904919) B3904919
theorem B106928437 : Blo 1735068 106928437 := bstep (se 5 (by rfl) ⟨5012270, by rfl⟩ : syracuseStep 106928437 = 10024541) B10024541
theorem B2603321 : Blo 1735068 2603321 := bstep (se 2 (by rfl) ⟨976245, by rfl⟩ : syracuseStep 2603321 = 1952491) B1952491
theorem B2603399 : Blo 1735068 2603399 := bstep (se 1 (by rfl) ⟨1952549, by rfl⟩ : syracuseStep 2603399 = 3905099) B3905099
theorem B3905927 : Blo 1735068 3905927 := bstep (se 1 (by rfl) ⟨2929445, by rfl⟩ : syracuseStep 3905927 = 5858891) B5858891
theorem B73202069 : Blo 1735068 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B2603435 : Blo 1735068 2603435 := bstep (se 1 (by rfl) ⟨1952576, by rfl⟩ : syracuseStep 2603435 = 3905153) B3905153
theorem B1735099 : Blo 1735068 1735099 := bstep (se 1 (by rfl) ⟨1301324, by rfl⟩ : syracuseStep 1735099 = 2602649) B2602649
theorem B2603465 : Blo 1735068 2603465 := bstep (se 2 (by rfl) ⟨976299, by rfl⟩ : syracuseStep 2603465 = 1952599) B1952599
theorem B11123203 : Blo 1735068 11123203 := bstep (se 1 (by rfl) ⟨8342402, by rfl⟩ : syracuseStep 11123203 = 16684805) B16684805
theorem B1735175 : Blo 1735068 1735175 := bstep (se 1 (by rfl) ⟨1301381, by rfl⟩ : syracuseStep 1735175 = 2602763) B2602763
theorem B1735183 : Blo 1735068 1735183 := bstep (se 1 (by rfl) ⟨1301387, by rfl⟩ : syracuseStep 1735183 = 2602775) B2602775
theorem B2505259 : Blo 1735068 2505259 := bstep (se 1 (by rfl) ⟨1878944, by rfl⟩ : syracuseStep 2505259 = 3757889) B3757889
theorem B1735227 : Blo 1735068 1735227 := bstep (se 1 (by rfl) ⟨1301420, by rfl⟩ : syracuseStep 1735227 = 2602841) B2602841
theorem B2603579 : Blo 1735068 2603579 := bstep (se 1 (by rfl) ⟨1952684, by rfl⟩ : syracuseStep 2603579 = 3905369) B3905369
theorem B3906107 : Blo 1735068 3906107 := bstep (se 1 (by rfl) ⟨2929580, by rfl⟩ : syracuseStep 3906107 = 5859161) B5859161
theorem B2603639 : Blo 1735068 2603639 := bstep (se 1 (by rfl) ⟨1952729, by rfl⟩ : syracuseStep 2603639 = 3905459) B3905459
theorem B1735303 : Blo 1735068 1735303 := bstep (se 1 (by rfl) ⟨1301477, by rfl⟩ : syracuseStep 1735303 = 2602955) B2602955
theorem B1735311 : Blo 1735068 1735311 := bstep (se 1 (by rfl) ⟨1301483, by rfl⟩ : syracuseStep 1735311 = 2602967) B2602967
theorem B2603663 : Blo 1735068 2603663 := bstep (se 1 (by rfl) ⟨1952747, by rfl⟩ : syracuseStep 2603663 = 3905495) B3905495
theorem B2603705 : Blo 1735068 2603705 := bstep (se 2 (by rfl) ⟨976389, by rfl⟩ : syracuseStep 2603705 = 1952779) B1952779
theorem B3906233 : Blo 1735068 3906233 := bstep (se 2 (by rfl) ⟨1464837, by rfl⟩ : syracuseStep 3906233 = 2929675) B2929675
theorem B1735355 : Blo 1735068 1735355 := bstep (se 1 (by rfl) ⟨1301516, by rfl⟩ : syracuseStep 1735355 = 2603033) B2603033
theorem B1735431 : Blo 1735068 1735431 := bstep (se 1 (by rfl) ⟨1301573, by rfl⟩ : syracuseStep 1735431 = 2603147) B2603147
theorem B2603783 : Blo 1735068 2603783 := bstep (se 1 (by rfl) ⟨1952837, by rfl⟩ : syracuseStep 2603783 = 3905675) B3905675
theorem B1735439 : Blo 1735068 1735439 := bstep (se 1 (by rfl) ⟨1301579, by rfl⟩ : syracuseStep 1735439 = 2603159) B2603159
theorem B2603819 : Blo 1735068 2603819 := bstep (se 1 (by rfl) ⟨1952864, by rfl⟩ : syracuseStep 2603819 = 3905729) B3905729
theorem B1735483 : Blo 1735068 1735483 := bstep (se 1 (by rfl) ⟨1301612, by rfl⟩ : syracuseStep 1735483 = 2603225) B2603225
theorem B5217085 : Blo 1735068 5217085 := bstep (se 3 (by rfl) ⟨978203, by rfl⟩ : syracuseStep 5217085 = 1956407) B1956407
theorem B2603849 : Blo 1735068 2603849 := bstep (se 2 (by rfl) ⟨976443, by rfl⟩ : syracuseStep 2603849 = 1952887) B1952887
theorem B19766105 : Blo 1735068 19766105 := bstep (se 2 (by rfl) ⟨7412289, by rfl⟩ : syracuseStep 19766105 = 14824579) B14824579
theorem B1735559 : Blo 1735068 1735559 := bstep (se 1 (by rfl) ⟨1301669, by rfl⟩ : syracuseStep 1735559 = 2603339) B2603339
theorem B1735567 : Blo 1735068 1735567 := bstep (se 1 (by rfl) ⟨1301675, by rfl⟩ : syracuseStep 1735567 = 2603351) B2603351
theorem B7412633 : Blo 1735068 7412633 := bstep (se 2 (by rfl) ⟨2779737, by rfl⟩ : syracuseStep 7412633 = 5559475) B5559475
theorem B15842201 : Blo 1735068 15842201 := bstep (se 2 (by rfl) ⟨5940825, by rfl⟩ : syracuseStep 15842201 = 11881651) B11881651
theorem B1735611 : Blo 1735068 1735611 := bstep (se 1 (by rfl) ⟨1301708, by rfl⟩ : syracuseStep 1735611 = 2603417) B2603417
theorem B2603963 : Blo 1735068 2603963 := bstep (se 1 (by rfl) ⟨1952972, by rfl⟩ : syracuseStep 2603963 = 3905945) B3905945
theorem B2604023 : Blo 1735068 2604023 := bstep (se 1 (by rfl) ⟨1953017, by rfl⟩ : syracuseStep 2604023 = 3906035) B3906035
theorem B4455425 : Blo 1735068 4455425 := bstep (se 2 (by rfl) ⟨1670784, by rfl⟩ : syracuseStep 4455425 = 3341569) B3341569
theorem B1735687 : Blo 1735068 1735687 := bstep (se 1 (by rfl) ⟨1301765, by rfl⟩ : syracuseStep 1735687 = 2603531) B2603531
theorem B1735695 : Blo 1735068 1735695 := bstep (se 1 (by rfl) ⟨1301771, by rfl⟩ : syracuseStep 1735695 = 2603543) B2603543
theorem B2604047 : Blo 1735068 2604047 := bstep (se 1 (by rfl) ⟨1953035, by rfl⟩ : syracuseStep 2604047 = 3906071) B3906071
theorem B3906575 : Blo 1735068 3906575 := bstep (se 1 (by rfl) ⟨2929931, by rfl⟩ : syracuseStep 3906575 = 5859863) B5859863
theorem B3906593 : Blo 1735068 3906593 := bstep (se 2 (by rfl) ⟨1464972, by rfl⟩ : syracuseStep 3906593 = 2929945) B2929945
theorem B5856299 : Blo 1735068 5856299 := bstep (se 1 (by rfl) ⟨4392224, by rfl⟩ : syracuseStep 5856299 = 8784449) B8784449
theorem B2604089 : Blo 1735068 2604089 := bstep (se 2 (by rfl) ⟨976533, by rfl⟩ : syracuseStep 2604089 = 1953067) B1953067
theorem B1735739 : Blo 1735068 1735739 := bstep (se 1 (by rfl) ⟨1301804, by rfl⟩ : syracuseStep 1735739 = 2603609) B2603609
theorem B1735815 : Blo 1735068 1735815 := bstep (se 1 (by rfl) ⟨1301861, by rfl⟩ : syracuseStep 1735815 = 2603723) B2603723
theorem B2604167 : Blo 1735068 2604167 := bstep (se 1 (by rfl) ⟨1953125, by rfl⟩ : syracuseStep 2604167 = 3906251) B3906251
theorem B1735823 : Blo 1735068 1735823 := bstep (se 1 (by rfl) ⟨1301867, by rfl⟩ : syracuseStep 1735823 = 2603735) B2603735
theorem B2604203 : Blo 1735068 2604203 := bstep (se 1 (by rfl) ⟨1953152, by rfl⟩ : syracuseStep 2604203 = 3906305) B3906305
theorem B1735867 : Blo 1735068 1735867 := bstep (se 1 (by rfl) ⟨1301900, by rfl⟩ : syracuseStep 1735867 = 2603801) B2603801
theorem B2604233 : Blo 1735068 2604233 := bstep (se 2 (by rfl) ⟨976587, by rfl⟩ : syracuseStep 2604233 = 1953175) B1953175
theorem B1735943 : Blo 1735068 1735943 := bstep (se 1 (by rfl) ⟨1301957, by rfl⟩ : syracuseStep 1735943 = 2603915) B2603915
theorem B1735951 : Blo 1735068 1735951 := bstep (se 1 (by rfl) ⟨1301963, by rfl⟩ : syracuseStep 1735951 = 2603927) B2603927
theorem B1735995 : Blo 1735068 1735995 := bstep (se 1 (by rfl) ⟨1301996, by rfl⟩ : syracuseStep 1735995 = 2603993) B2603993
theorem B2604347 : Blo 1735068 2604347 := bstep (se 1 (by rfl) ⟨1953260, by rfl⟩ : syracuseStep 2604347 = 3906521) B3906521
theorem B9387323 : Blo 1735068 9387323 := bstep (se 1 (by rfl) ⟨7040492, by rfl⟩ : syracuseStep 9387323 = 14080985) B14080985
theorem B2604407 : Blo 1735068 2604407 := bstep (se 1 (by rfl) ⟨1953305, by rfl⟩ : syracuseStep 2604407 = 3906611) B3906611
theorem B3906935 : Blo 1735068 3906935 := bstep (se 1 (by rfl) ⟨2930201, by rfl⟩ : syracuseStep 3906935 = 5860403) B5860403
theorem B1736071 : Blo 1735068 1736071 := bstep (se 1 (by rfl) ⟨1302053, by rfl⟩ : syracuseStep 1736071 = 2604107) B2604107
theorem B1736079 : Blo 1735068 1736079 := bstep (se 1 (by rfl) ⟨1302059, by rfl⟩ : syracuseStep 1736079 = 2604119) B2604119
theorem B2604431 : Blo 1735068 2604431 := bstep (se 1 (by rfl) ⟨1953323, by rfl⟩ : syracuseStep 2604431 = 3906647) B3906647
theorem B2604473 : Blo 1735068 2604473 := bstep (se 2 (by rfl) ⟨976677, by rfl⟩ : syracuseStep 2604473 = 1953355) B1953355
theorem B1736123 : Blo 1735068 1736123 := bstep (se 1 (by rfl) ⟨1302092, by rfl⟩ : syracuseStep 1736123 = 2604185) B2604185
theorem B1736199 : Blo 1735068 1736199 := bstep (se 1 (by rfl) ⟨1302149, by rfl⟩ : syracuseStep 1736199 = 2604299) B2604299
theorem B2604551 : Blo 1735068 2604551 := bstep (se 1 (by rfl) ⟨1953413, by rfl⟩ : syracuseStep 2604551 = 3906827) B3906827
theorem B1736207 : Blo 1735068 1736207 := bstep (se 1 (by rfl) ⟨1302155, by rfl⟩ : syracuseStep 1736207 = 2604311) B2604311
theorem B2604587 : Blo 1735068 2604587 := bstep (se 1 (by rfl) ⟨1953440, by rfl⟩ : syracuseStep 2604587 = 3906881) B3906881
theorem B3907115 : Blo 1735068 3907115 := bstep (se 1 (by rfl) ⟨2930336, by rfl⟩ : syracuseStep 3907115 = 5860673) B5860673
theorem B1736251 : Blo 1735068 1736251 := bstep (se 1 (by rfl) ⟨1302188, by rfl⟩ : syracuseStep 1736251 = 2604377) B2604377
theorem B2604617 : Blo 1735068 2604617 := bstep (se 2 (by rfl) ⟨976731, by rfl⟩ : syracuseStep 2604617 = 1953463) B1953463
theorem B20045389 : Blo 1735068 20045389 := bstep (se 3 (by rfl) ⟨3758510, by rfl⟩ : syracuseStep 20045389 = 7517021) B7517021
theorem B1736327 : Blo 1735068 1736327 := bstep (se 1 (by rfl) ⟨1302245, by rfl⟩ : syracuseStep 1736327 = 2604491) B2604491
theorem B1736335 : Blo 1735068 1736335 := bstep (se 1 (by rfl) ⟨1302251, by rfl⟩ : syracuseStep 1736335 = 2604503) B2604503
theorem B1736379 : Blo 1735068 1736379 := bstep (se 1 (by rfl) ⟨1302284, by rfl⟩ : syracuseStep 1736379 = 2604569) B2604569
theorem B2604731 : Blo 1735068 2604731 := bstep (se 1 (by rfl) ⟨1953548, by rfl⟩ : syracuseStep 2604731 = 3907097) B3907097
theorem B2604791 : Blo 1735068 2604791 := bstep (se 1 (by rfl) ⟨1953593, by rfl⟩ : syracuseStep 2604791 = 3907187) B3907187
theorem B1736455 : Blo 1735068 1736455 := bstep (se 1 (by rfl) ⟨1302341, by rfl⟩ : syracuseStep 1736455 = 2604683) B2604683
theorem B1736463 : Blo 1735068 1736463 := bstep (se 1 (by rfl) ⟨1302347, by rfl⟩ : syracuseStep 1736463 = 2604695) B2604695
theorem B2604815 : Blo 1735068 2604815 := bstep (se 1 (by rfl) ⟨1953611, by rfl⟩ : syracuseStep 2604815 = 3907223) B3907223
theorem B3129131 : Blo 1735068 3129131 := bstep (se 1 (by rfl) ⟨2346848, by rfl⟩ : syracuseStep 3129131 = 4693697) B4693697
theorem B14827313 : Blo 1735068 14827313 := bstep (se 2 (by rfl) ⟨5560242, by rfl⟩ : syracuseStep 14827313 = 11120485) B11120485
theorem B1736507 : Blo 1735068 1736507 := bstep (se 1 (by rfl) ⟨1302380, by rfl⟩ : syracuseStep 1736507 = 2604761) B2604761
theorem B5857433 : Blo 1735068 5857433 := bstep (se 2 (by rfl) ⟨2196537, by rfl⟩ : syracuseStep 5857433 = 4393075) B4393075
theorem B19767563 : Blo 1735068 19767563 := bstep (se 1 (by rfl) ⟨14825672, by rfl⟩ : syracuseStep 19767563 = 29651345) B29651345
theorem B2818567 : Blo 1735068 2818567 := bstep (se 1 (by rfl) ⟨2113925, by rfl⟩ : syracuseStep 2818567 = 4227851) B4227851
theorem B28156517 : Blo 1735068 28156517 := bstep (se 4 (by rfl) ⟨2639673, by rfl⟩ : syracuseStep 28156517 = 5279347) B5279347
theorem B22553261 : Blo 1735068 22553261 := bstep (se 3 (by rfl) ⟨4228736, by rfl⟩ : syracuseStep 22553261 = 8457473) B8457473
theorem B3294047 : Blo 1735068 3294047 := bstep (se 1 (by rfl) ⟨2470535, by rfl⟩ : syracuseStep 3294047 = 4941071) B4941071
theorem B27452363 : Blo 1735068 27452363 := bstep (se 1 (by rfl) ⟨20589272, by rfl⟩ : syracuseStep 27452363 = 41178545) B41178545
theorem B2638811 : Blo 1735068 2638811 := bstep (se 1 (by rfl) ⟨1979108, by rfl⟩ : syracuseStep 2638811 = 3958217) B3958217
theorem B43402291 : Blo 1735068 43402291 := bstep (se 1 (by rfl) ⟨32551718, by rfl⟩ : syracuseStep 43402291 = 65103437) B65103437
theorem B8791091 : Blo 1735068 8791091 := bstep (se 1 (by rfl) ⟨6593318, by rfl⟩ : syracuseStep 8791091 = 13186637) B13186637
theorem B6956113 : Blo 1735068 6956113 := bstep (se 2 (by rfl) ⟨2608542, by rfl⟩ : syracuseStep 6956113 = 5217085) B5217085
theorem B5858621 : Blo 1735068 5858621 := bstep (se 3 (by rfl) ⟨1098491, by rfl⟩ : syracuseStep 5858621 = 2196983) B2196983
theorem B4228481 : Blo 1735068 4228481 := bstep (se 2 (by rfl) ⟨1585680, by rfl⟩ : syracuseStep 4228481 = 3171361) B3171361
theorem B4941299 : Blo 1735068 4941299 := bstep (se 1 (by rfl) ⟨3705974, by rfl⟩ : syracuseStep 4941299 = 7411949) B7411949
theorem B48801379 : Blo 1735068 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B4941641 : Blo 1735068 4941641 := bstep (se 2 (by rfl) ⟨1853115, by rfl⟩ : syracuseStep 4941641 = 3706231) B3706231
theorem B4941755 : Blo 1735068 4941755 := bstep (se 1 (by rfl) ⟨3706316, by rfl⟩ : syracuseStep 4941755 = 7412633) B7412633
theorem B1853479 : Blo 1735068 1853479 := bstep (se 1 (by rfl) ⟨1390109, by rfl⟩ : syracuseStep 1853479 = 2780219) B2780219
theorem B4941881 : Blo 1735068 4941881 := bstep (se 2 (by rfl) ⟨1853205, by rfl⟩ : syracuseStep 4941881 = 3706411) B3706411
theorem B5859485 : Blo 1735068 5859485 := bstep (se 3 (by rfl) ⟨1098653, by rfl⟩ : syracuseStep 5859485 = 2197307) B2197307
theorem B6588611 : Blo 1735068 6588611 := bstep (se 1 (by rfl) ⟨4941458, by rfl⟩ : syracuseStep 6588611 = 9882917) B9882917
theorem B14829911 : Blo 1735068 14829911 := bstep (se 1 (by rfl) ⟨11122433, by rfl⟩ : syracuseStep 14829911 = 22244867) B22244867
theorem B1952095 : Blo 1735068 1952095 := bstep (se 1 (by rfl) ⟨1464071, by rfl⟩ : syracuseStep 1952095 = 2928143) B2928143
theorem B37521949 : Blo 1735068 37521949 := bstep (se 3 (by rfl) ⟨7035365, by rfl⟩ : syracuseStep 37521949 = 14070731) B14070731
theorem B4393511 : Blo 1735068 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B19016237 : Blo 1735068 19016237 := bstep (se 3 (by rfl) ⟨3565544, by rfl⟩ : syracuseStep 19016237 = 7131089) B7131089
theorem B11881133 : Blo 1735068 11881133 := bstep (se 3 (by rfl) ⟨2227712, by rfl⟩ : syracuseStep 11881133 = 4455425) B4455425
theorem B5860025 : Blo 1735068 5860025 := bstep (se 2 (by rfl) ⟨2197509, by rfl⟩ : syracuseStep 5860025 = 4395019) B4395019
theorem B6589127 : Blo 1735068 6589127 := bstep (se 1 (by rfl) ⟨4941845, by rfl⟩ : syracuseStep 6589127 = 9883691) B9883691
theorem B1952455 : Blo 1735068 1952455 := bstep (se 1 (by rfl) ⟨1464341, by rfl⟩ : syracuseStep 1952455 = 2928683) B2928683
theorem B3295991 : Blo 1735068 3295991 := bstep (se 1 (by rfl) ⟨2471993, by rfl⟩ : syracuseStep 3295991 = 4943987) B4943987
theorem B3386105 : Blo 1735068 3386105 := bstep (se 2 (by rfl) ⟨1269789, by rfl⟩ : syracuseStep 3386105 = 2539579) B2539579
theorem B21113693 : Blo 1735068 21113693 := bstep (se 3 (by rfl) ⟨3958817, by rfl⟩ : syracuseStep 21113693 = 7917635) B7917635
theorem B4393835 : Blo 1735068 4393835 := bstep (se 1 (by rfl) ⟨3295376, by rfl⟩ : syracuseStep 4393835 = 6590753) B6590753
theorem B3296143 : Blo 1735068 3296143 := bstep (se 1 (by rfl) ⟨2472107, by rfl⟩ : syracuseStep 3296143 = 4944215) B4944215
theorem B3517651 : Blo 1735068 3517651 := bstep (se 1 (by rfl) ⟨2638238, by rfl⟩ : syracuseStep 3517651 = 5276477) B5276477
theorem B5860619 : Blo 1735068 5860619 := bstep (se 1 (by rfl) ⟨4395464, by rfl⟩ : syracuseStep 5860619 = 8790929) B8790929
theorem B14830937 : Blo 1735068 14830937 := bstep (se 2 (by rfl) ⟨5561601, by rfl⟩ : syracuseStep 14830937 = 11123203) B11123203
theorem B2928055 : Blo 1735068 2928055 := bstep (se 1 (by rfl) ⟨2196041, by rfl⟩ : syracuseStep 2928055 = 4392083) B4392083
theorem B4394483 : Blo 1735068 4394483 := bstep (se 1 (by rfl) ⟨3295862, by rfl⟩ : syracuseStep 4394483 = 6591725) B6591725
theorem B5860889 : Blo 1735068 5860889 := bstep (se 2 (by rfl) ⟨2197833, by rfl⟩ : syracuseStep 5860889 = 4395667) B4395667
theorem B1953319 : Blo 1735068 1953319 := bstep (se 1 (by rfl) ⟨1464989, by rfl⟩ : syracuseStep 1953319 = 2929979) B2929979
theorem B2928251 : Blo 1735068 2928251 := bstep (se 1 (by rfl) ⟨2196188, by rfl⟩ : syracuseStep 2928251 = 4392377) B4392377
theorem B6590099 : Blo 1735068 6590099 := bstep (se 1 (by rfl) ⟨4942574, by rfl⟩ : syracuseStep 6590099 = 9885149) B9885149
theorem B4394695 : Blo 1735068 4394695 := bstep (se 1 (by rfl) ⟨3296021, by rfl⟩ : syracuseStep 4394695 = 6592043) B6592043
theorem B6590281 : Blo 1735068 6590281 := bstep (se 2 (by rfl) ⟨2471355, by rfl⟩ : syracuseStep 6590281 = 4942711) B4942711
theorem B3862379 : Blo 1735068 3862379 := bstep (se 1 (by rfl) ⟨2896784, by rfl⟩ : syracuseStep 3862379 = 5793569) B5793569
theorem B3567521 : Blo 1735068 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B2928649 : Blo 1735068 2928649 := bstep (se 2 (by rfl) ⟨1098243, by rfl⟩ : syracuseStep 2928649 = 2196487) B2196487
theorem B56299531 : Blo 1735068 56299531 := bstep (se 1 (by rfl) ⟨42224648, by rfl⟩ : syracuseStep 56299531 = 84449297) B84449297
theorem B2928811 : Blo 1735068 2928811 := bstep (se 1 (by rfl) ⟨2196608, by rfl⟩ : syracuseStep 2928811 = 4393217) B4393217
theorem B2929115 : Blo 1735068 2929115 := bstep (se 1 (by rfl) ⟨2196836, by rfl⟩ : syracuseStep 2929115 = 4393673) B4393673
theorem B13177403 : Blo 1735068 13177403 := bstep (se 1 (by rfl) ⟨9883052, by rfl⟩ : syracuseStep 13177403 = 19766105) B19766105
theorem B4395617 : Blo 1735068 4395617 := bstep (se 2 (by rfl) ⟨1648356, by rfl⟩ : syracuseStep 4395617 = 3296713) B3296713
theorem B4944523 : Blo 1735068 4944523 := bstep (se 1 (by rfl) ⟨3708392, by rfl⟩ : syracuseStep 4944523 = 7416785) B7416785
theorem B3904199 : Blo 1735068 3904199 := bstep (se 1 (by rfl) ⟨2928149, by rfl⟩ : syracuseStep 3904199 = 5856299) B5856299
theorem B2929351 : Blo 1735068 2929351 := bstep (se 1 (by rfl) ⟨2197013, by rfl⟩ : syracuseStep 2929351 = 4394027) B4394027
theorem B26727185 : Blo 1735068 26727185 := bstep (se 2 (by rfl) ⟨10022694, by rfl⟩ : syracuseStep 26727185 = 20045389) B20045389
theorem B8786717 : Blo 1735068 8786717 := bstep (se 3 (by rfl) ⟨1647509, by rfl⟩ : syracuseStep 8786717 = 3295019) B3295019
theorem B2929513 : Blo 1735068 2929513 := bstep (se 2 (by rfl) ⟨1098567, by rfl⟩ : syracuseStep 2929513 = 2197135) B2197135
theorem B23753675 : Blo 1735068 23753675 := bstep (se 1 (by rfl) ⟨17815256, by rfl⟩ : syracuseStep 23753675 = 35630513) B35630513
theorem B11121715 : Blo 1735068 11121715 := bstep (se 1 (by rfl) ⟨8341286, by rfl⟩ : syracuseStep 11121715 = 16682573) B16682573
theorem B2470991 : Blo 1735068 2470991 := bstep (se 1 (by rfl) ⟨1853243, by rfl⟩ : syracuseStep 2470991 = 3706487) B3706487
theorem B2086087 : Blo 1735068 2086087 := bstep (se 1 (by rfl) ⟨1564565, by rfl⟩ : syracuseStep 2086087 = 3129131) B3129131
theorem B9884875 : Blo 1735068 9884875 := bstep (se 1 (by rfl) ⟨7413656, by rfl⟩ : syracuseStep 9884875 = 14827313) B14827313
theorem B23753999 : Blo 1735068 23753999 := bstep (se 1 (by rfl) ⟨17815499, by rfl⟩ : syracuseStep 23753999 = 35630999) B35630999
theorem B2930107 : Blo 1735068 2930107 := bstep (se 1 (by rfl) ⟨2197580, by rfl⟩ : syracuseStep 2930107 = 4395161) B4395161
theorem B5936627 : Blo 1735068 5936627 := bstep (se 1 (by rfl) ⟨4452470, by rfl⟩ : syracuseStep 5936627 = 8904941) B8904941
theorem B42227189 : Blo 1735068 42227189 := bstep (se 5 (by rfl) ⟨1979399, by rfl⟩ : syracuseStep 42227189 = 3958799) B3958799
theorem B5559833 : Blo 1735068 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B3905063 : Blo 1735068 3905063 := bstep (se 1 (by rfl) ⟨2928797, by rfl⟩ : syracuseStep 3905063 = 5857595) B5857595
theorem B2930215 : Blo 1735068 2930215 := bstep (se 1 (by rfl) ⟨2197661, by rfl⟩ : syracuseStep 2930215 = 4395323) B4395323
theorem B2602619 : Blo 1735068 2602619 := bstep (se 1 (by rfl) ⟨1951964, by rfl⟩ : syracuseStep 2602619 = 3903929) B3903929
theorem B6592211 : Blo 1735068 6592211 := bstep (se 1 (by rfl) ⟨4944158, by rfl⟩ : syracuseStep 6592211 = 9888317) B9888317
theorem B142571249 : Blo 1735068 142571249 := bstep (se 2 (by rfl) ⟨53464218, by rfl⟩ : syracuseStep 142571249 = 106928437) B106928437
theorem B2602745 : Blo 1735068 2602745 := bstep (se 2 (by rfl) ⟨976029, by rfl⟩ : syracuseStep 2602745 = 1952059) B1952059
theorem B11876129 : Blo 1735068 11876129 := bstep (se 2 (by rfl) ⟨4453548, by rfl⟩ : syracuseStep 11876129 = 8907097) B8907097
theorem B2602847 : Blo 1735068 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B2602859 : Blo 1735068 2602859 := bstep (se 1 (by rfl) ⟨1952144, by rfl⟩ : syracuseStep 2602859 = 3904289) B3904289
theorem B3905387 : Blo 1735068 3905387 := bstep (se 1 (by rfl) ⟨2929040, by rfl⟩ : syracuseStep 3905387 = 5858081) B5858081
theorem B3905441 : Blo 1735068 3905441 := bstep (se 2 (by rfl) ⟨1464540, by rfl⟩ : syracuseStep 3905441 = 2929081) B2929081
theorem B14833601 : Blo 1735068 14833601 := bstep (se 2 (by rfl) ⟨5562600, by rfl⟩ : syracuseStep 14833601 = 11125201) B11125201
theorem B10991623 : Blo 1735068 10991623 := bstep (se 1 (by rfl) ⟨8243717, by rfl⟩ : syracuseStep 10991623 = 16487435) B16487435
theorem B11122717 : Blo 1735068 11122717 := bstep (se 3 (by rfl) ⟨2085509, by rfl⟩ : syracuseStep 11122717 = 4171019) B4171019
theorem B3340345 : Blo 1735068 3340345 := bstep (se 2 (by rfl) ⟨1252629, by rfl⟩ : syracuseStep 3340345 = 2505259) B2505259
theorem B2603087 : Blo 1735068 2603087 := bstep (se 1 (by rfl) ⟨1952315, by rfl⟩ : syracuseStep 2603087 = 3904631) B3904631
theorem B5011627 : Blo 1735068 5011627 := bstep (se 1 (by rfl) ⟨3758720, by rfl⟩ : syracuseStep 5011627 = 7517441) B7517441
theorem B2603207 : Blo 1735068 2603207 := bstep (se 1 (by rfl) ⟨1952405, by rfl⟩ : syracuseStep 2603207 = 3904811) B3904811
theorem B3905783 : Blo 1735068 3905783 := bstep (se 1 (by rfl) ⟨2929337, by rfl⟩ : syracuseStep 3905783 = 5858675) B5858675
theorem B2603369 : Blo 1735068 2603369 := bstep (se 2 (by rfl) ⟨976263, by rfl⟩ : syracuseStep 2603369 = 1952527) B1952527
theorem B1735087 : Blo 1735068 1735087 := bstep (se 1 (by rfl) ⟨1301315, by rfl⟩ : syracuseStep 1735087 = 2602631) B2602631
theorem B2603447 : Blo 1735068 2603447 := bstep (se 1 (by rfl) ⟨1952585, by rfl⟩ : syracuseStep 2603447 = 3905171) B3905171
theorem B1735111 : Blo 1735068 1735111 := bstep (se 1 (by rfl) ⟨1301333, by rfl⟩ : syracuseStep 1735111 = 2602667) B2602667
theorem B1735131 : Blo 1735068 1735131 := bstep (se 1 (by rfl) ⟨1301348, by rfl⟩ : syracuseStep 1735131 = 2602697) B2602697
theorem B2603483 : Blo 1735068 2603483 := bstep (se 1 (by rfl) ⟨1952612, by rfl⟩ : syracuseStep 2603483 = 3905225) B3905225
theorem B1735207 : Blo 1735068 1735207 := bstep (se 1 (by rfl) ⟨1301405, by rfl⟩ : syracuseStep 1735207 = 2602811) B2602811
theorem B1735247 : Blo 1735068 1735247 := bstep (se 1 (by rfl) ⟨1301435, by rfl⟩ : syracuseStep 1735247 = 2602871) B2602871
theorem B1735263 : Blo 1735068 1735263 := bstep (se 1 (by rfl) ⟨1301447, by rfl⟩ : syracuseStep 1735263 = 2602895) B2602895
theorem B5855867 : Blo 1735068 5855867 := bstep (se 1 (by rfl) ⟨4391900, by rfl⟩ : syracuseStep 5855867 = 8783801) B8783801
theorem B1735291 : Blo 1735068 1735291 := bstep (se 1 (by rfl) ⟨1301468, by rfl⟩ : syracuseStep 1735291 = 2602937) B2602937
theorem B1735343 : Blo 1735068 1735343 := bstep (se 1 (by rfl) ⟨1301507, by rfl⟩ : syracuseStep 1735343 = 2603015) B2603015
theorem B1735367 : Blo 1735068 1735367 := bstep (se 1 (by rfl) ⟨1301525, by rfl⟩ : syracuseStep 1735367 = 2603051) B2603051
theorem B1735387 : Blo 1735068 1735387 := bstep (se 1 (by rfl) ⟨1301540, by rfl⟩ : syracuseStep 1735387 = 2603081) B2603081
theorem B5856029 : Blo 1735068 5856029 := bstep (se 3 (by rfl) ⟨1098005, by rfl⟩ : syracuseStep 5856029 = 2196011) B2196011
theorem B1735463 : Blo 1735068 1735463 := bstep (se 1 (by rfl) ⟨1301597, by rfl⟩ : syracuseStep 1735463 = 2603195) B2603195
theorem B3906377 : Blo 1735068 3906377 := bstep (se 2 (by rfl) ⟨1464891, by rfl⟩ : syracuseStep 3906377 = 2929783) B2929783
theorem B1735503 : Blo 1735068 1735503 := bstep (se 1 (by rfl) ⟨1301627, by rfl⟩ : syracuseStep 1735503 = 2603255) B2603255
theorem B1735519 : Blo 1735068 1735519 := bstep (se 1 (by rfl) ⟨1301639, by rfl⟩ : syracuseStep 1735519 = 2603279) B2603279
theorem B1735547 : Blo 1735068 1735547 := bstep (se 1 (by rfl) ⟨1301660, by rfl⟩ : syracuseStep 1735547 = 2603321) B2603321
theorem B1735599 : Blo 1735068 1735599 := bstep (se 1 (by rfl) ⟨1301699, by rfl⟩ : syracuseStep 1735599 = 2603399) B2603399
theorem B2603951 : Blo 1735068 2603951 := bstep (se 1 (by rfl) ⟨1952963, by rfl⟩ : syracuseStep 2603951 = 3905927) B3905927
theorem B1735623 : Blo 1735068 1735623 := bstep (se 1 (by rfl) ⟨1301717, by rfl⟩ : syracuseStep 1735623 = 2603435) B2603435
theorem B1735643 : Blo 1735068 1735643 := bstep (se 1 (by rfl) ⟨1301732, by rfl⟩ : syracuseStep 1735643 = 2603465) B2603465
theorem B3128329 : Blo 1735068 3128329 := bstep (se 2 (by rfl) ⟨1173123, by rfl⟩ : syracuseStep 3128329 = 2346247) B2346247
theorem B2604041 : Blo 1735068 2604041 := bstep (se 2 (by rfl) ⟨976515, by rfl⟩ : syracuseStep 2604041 = 1953031) B1953031
theorem B1735719 : Blo 1735068 1735719 := bstep (se 1 (by rfl) ⟨1301789, by rfl⟩ : syracuseStep 1735719 = 2603579) B2603579
theorem B2604071 : Blo 1735068 2604071 := bstep (se 1 (by rfl) ⟨1953053, by rfl⟩ : syracuseStep 2604071 = 3906107) B3906107
theorem B1735759 : Blo 1735068 1735759 := bstep (se 1 (by rfl) ⟨1301819, by rfl⟩ : syracuseStep 1735759 = 2603639) B2603639
theorem B5561423 : Blo 1735068 5561423 := bstep (se 1 (by rfl) ⟨4171067, by rfl⟩ : syracuseStep 5561423 = 8342135) B8342135
theorem B1735775 : Blo 1735068 1735775 := bstep (se 1 (by rfl) ⟨1301831, by rfl⟩ : syracuseStep 1735775 = 2603663) B2603663
theorem B1735803 : Blo 1735068 1735803 := bstep (se 1 (by rfl) ⟨1301852, by rfl⟩ : syracuseStep 1735803 = 2603705) B2603705
theorem B2604155 : Blo 1735068 2604155 := bstep (se 1 (by rfl) ⟨1953116, by rfl⟩ : syracuseStep 2604155 = 3906233) B3906233
theorem B1735855 : Blo 1735068 1735855 := bstep (se 1 (by rfl) ⟨1301891, by rfl⟩ : syracuseStep 1735855 = 2603783) B2603783
theorem B1735879 : Blo 1735068 1735879 := bstep (se 1 (by rfl) ⟨1301909, by rfl⟩ : syracuseStep 1735879 = 2603819) B2603819
theorem B1735899 : Blo 1735068 1735899 := bstep (se 1 (by rfl) ⟨1301924, by rfl⟩ : syracuseStep 1735899 = 2603849) B2603849
theorem B2604281 : Blo 1735068 2604281 := bstep (se 2 (by rfl) ⟨976605, by rfl⟩ : syracuseStep 2604281 = 1953211) B1953211
theorem B1735975 : Blo 1735068 1735975 := bstep (se 1 (by rfl) ⟨1301981, by rfl⟩ : syracuseStep 1735975 = 2603963) B2603963
theorem B1736015 : Blo 1735068 1736015 := bstep (se 1 (by rfl) ⟨1302011, by rfl⟩ : syracuseStep 1736015 = 2604023) B2604023
theorem B1736031 : Blo 1735068 1736031 := bstep (se 1 (by rfl) ⟨1302023, by rfl⟩ : syracuseStep 1736031 = 2604047) B2604047
theorem B2604383 : Blo 1735068 2604383 := bstep (se 1 (by rfl) ⟨1953287, by rfl⟩ : syracuseStep 2604383 = 3906575) B3906575
theorem B2604395 : Blo 1735068 2604395 := bstep (se 1 (by rfl) ⟨1953296, by rfl⟩ : syracuseStep 2604395 = 3906593) B3906593
theorem B1736059 : Blo 1735068 1736059 := bstep (se 1 (by rfl) ⟨1302044, by rfl⟩ : syracuseStep 1736059 = 2604089) B2604089
theorem B1736111 : Blo 1735068 1736111 := bstep (se 1 (by rfl) ⟨1302083, by rfl⟩ : syracuseStep 1736111 = 2604167) B2604167
theorem B1736135 : Blo 1735068 1736135 := bstep (se 1 (by rfl) ⟨1302101, by rfl⟩ : syracuseStep 1736135 = 2604203) B2604203
theorem B5856731 : Blo 1735068 5856731 := bstep (se 1 (by rfl) ⟨4392548, by rfl⟩ : syracuseStep 5856731 = 8785097) B8785097
theorem B1736155 : Blo 1735068 1736155 := bstep (se 1 (by rfl) ⟨1302116, by rfl⟩ : syracuseStep 1736155 = 2604233) B2604233
theorem B1736231 : Blo 1735068 1736231 := bstep (se 1 (by rfl) ⟨1302173, by rfl⟩ : syracuseStep 1736231 = 2604347) B2604347
theorem B6258215 : Blo 1735068 6258215 := bstep (se 1 (by rfl) ⟨4693661, by rfl⟩ : syracuseStep 6258215 = 9387323) B9387323
theorem B1736271 : Blo 1735068 1736271 := bstep (se 1 (by rfl) ⟨1302203, by rfl⟩ : syracuseStep 1736271 = 2604407) B2604407
theorem B2604623 : Blo 1735068 2604623 := bstep (se 1 (by rfl) ⟨1953467, by rfl⟩ : syracuseStep 2604623 = 3906935) B3906935
theorem B1736287 : Blo 1735068 1736287 := bstep (se 1 (by rfl) ⟨1302215, by rfl⟩ : syracuseStep 1736287 = 2604431) B2604431
theorem B3907169 : Blo 1735068 3907169 := bstep (se 2 (by rfl) ⟨1465188, by rfl⟩ : syracuseStep 3907169 = 2930377) B2930377
theorem B1736315 : Blo 1735068 1736315 := bstep (se 1 (by rfl) ⟨1302236, by rfl⟩ : syracuseStep 1736315 = 2604473) B2604473
theorem B1736367 : Blo 1735068 1736367 := bstep (se 1 (by rfl) ⟨1302275, by rfl⟩ : syracuseStep 1736367 = 2604551) B2604551
theorem B1736391 : Blo 1735068 1736391 := bstep (se 1 (by rfl) ⟨1302293, by rfl⟩ : syracuseStep 1736391 = 2604587) B2604587
theorem B2604743 : Blo 1735068 2604743 := bstep (se 1 (by rfl) ⟨1953557, by rfl⟩ : syracuseStep 2604743 = 3907115) B3907115
theorem B1736411 : Blo 1735068 1736411 := bstep (se 1 (by rfl) ⟨1302308, by rfl⟩ : syracuseStep 1736411 = 2604617) B2604617
theorem B36126445 : Blo 1735068 36126445 := bstep (se 3 (by rfl) ⟨6773708, by rfl⟩ : syracuseStep 36126445 = 13547417) B13547417
theorem B42245869 : Blo 1735068 42245869 := bstep (se 3 (by rfl) ⟨7921100, by rfl⟩ : syracuseStep 42245869 = 15842201) B15842201
theorem B1736487 : Blo 1735068 1736487 := bstep (se 1 (by rfl) ⟨1302365, by rfl⟩ : syracuseStep 1736487 = 2604731) B2604731
theorem B1736527 : Blo 1735068 1736527 := bstep (se 1 (by rfl) ⟨1302395, by rfl⟩ : syracuseStep 1736527 = 2604791) B2604791
theorem B4169567 : Blo 1735068 4169567 := bstep (se 1 (by rfl) ⟨3127175, by rfl⟩ : syracuseStep 4169567 = 6254351) B6254351
theorem B1736543 : Blo 1735068 1736543 := bstep (se 1 (by rfl) ⟨1302407, by rfl⟩ : syracuseStep 1736543 = 2604815) B2604815
theorem B14655497 : Blo 1735068 14655497 := bstep (se 2 (by rfl) ⟨5495811, by rfl⟩ : syracuseStep 14655497 = 10991623) B10991623
theorem B5857811 : Blo 1735068 5857811 := bstep (se 1 (by rfl) ⟨4393358, by rfl⟩ : syracuseStep 5857811 = 8786717) B8786717
theorem B15835783 : Blo 1735068 15835783 := bstep (se 1 (by rfl) ⟨11876837, by rfl⟩ : syracuseStep 15835783 = 23753675) B23753675
theorem B50029265 : Blo 1735068 50029265 := bstep (se 2 (by rfl) ⟨18760974, by rfl⟩ : syracuseStep 50029265 = 37521949) B37521949
theorem B15835999 : Blo 1735068 15835999 := bstep (se 1 (by rfl) ⟨11876999, by rfl⟩ : syracuseStep 15835999 = 23753999) B23753999
theorem B3294199 : Blo 1735068 3294199 := bstep (se 1 (by rfl) ⟨2470649, by rfl⟩ : syracuseStep 3294199 = 4941299) B4941299
theorem B3957751 : Blo 1735068 3957751 := bstep (se 1 (by rfl) ⟨2968313, by rfl⟩ : syracuseStep 3957751 = 5936627) B5936627
theorem B18760805 : Blo 1735068 18760805 := bstep (se 4 (by rfl) ⟨1758825, by rfl⟩ : syracuseStep 18760805 = 3517651) B3517651
theorem B3294427 : Blo 1735068 3294427 := bstep (se 1 (by rfl) ⟨2470820, by rfl⟩ : syracuseStep 3294427 = 4941641) B4941641
theorem B3294503 : Blo 1735068 3294503 := bstep (se 1 (by rfl) ⟨2470877, by rfl⟩ : syracuseStep 3294503 = 4941755) B4941755
theorem B9889067 : Blo 1735068 9889067 := bstep (se 1 (by rfl) ⟨7416800, by rfl⟩ : syracuseStep 9889067 = 14833601) B14833601
theorem B4171105 : Blo 1735068 4171105 := bstep (se 2 (by rfl) ⟨1564164, by rfl⟩ : syracuseStep 4171105 = 3128329) B3128329
theorem B3294587 : Blo 1735068 3294587 := bstep (se 1 (by rfl) ⟨2470940, by rfl⟩ : syracuseStep 3294587 = 4941881) B4941881
theorem B14828953 : Blo 1735068 14828953 := bstep (se 2 (by rfl) ⟨5560857, by rfl⟩ : syracuseStep 14828953 = 11121715) B11121715
theorem B9274817 : Blo 1735068 9274817 := bstep (se 2 (by rfl) ⟨3478056, by rfl⟩ : syracuseStep 9274817 = 6956113) B6956113
theorem B4392407 : Blo 1735068 4392407 := bstep (se 1 (by rfl) ⟨3294305, by rfl⟩ : syracuseStep 4392407 = 6588611) B6588611
theorem B4392751 : Blo 1735068 4392751 := bstep (se 1 (by rfl) ⟨3294563, by rfl⟩ : syracuseStep 4392751 = 6589127) B6589127
theorem B14075795 : Blo 1735068 14075795 := bstep (se 1 (by rfl) ⟨10556846, by rfl⟩ : syracuseStep 14075795 = 21113693) B21113693
theorem B71272493 : Blo 1735068 71272493 := bstep (se 3 (by rfl) ⟨13363592, by rfl⟩ : syracuseStep 71272493 = 26727185) B26727185
theorem B8784125 : Blo 1735068 8784125 := bstep (se 3 (by rfl) ⟨1647023, by rfl⟩ : syracuseStep 8784125 = 3294047) B3294047
theorem B11118845 : Blo 1735068 11118845 := bstep (se 3 (by rfl) ⟨2084783, by rfl⟩ : syracuseStep 11118845 = 4169567) B4169567
theorem B5859593 : Blo 1735068 5859593 := bstep (se 2 (by rfl) ⟨2197347, by rfl⟩ : syracuseStep 5859593 = 4394695) B4394695
theorem B4172143 : Blo 1735068 4172143 := bstep (se 1 (by rfl) ⟨3129107, by rfl⟩ : syracuseStep 4172143 = 6258215) B6258215
theorem B1952167 : Blo 1735068 1952167 := bstep (se 1 (by rfl) ⟨1464125, by rfl⟩ : syracuseStep 1952167 = 2928251) B2928251
theorem B9513389 : Blo 1735068 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B4393399 : Blo 1735068 4393399 := bstep (se 1 (by rfl) ⟨3295049, by rfl⟩ : syracuseStep 4393399 = 6590099) B6590099
theorem B73206301 : Blo 1735068 73206301 := bstep (se 3 (by rfl) ⟨13726181, by rfl⟩ : syracuseStep 73206301 = 27452363) B27452363
theorem B2574919 : Blo 1735068 2574919 := bstep (se 1 (by rfl) ⟨1931189, by rfl⟩ : syracuseStep 2574919 = 3862379) B3862379
theorem B75066041 : Blo 1735068 75066041 := bstep (se 2 (by rfl) ⟨28149765, by rfl⟩ : syracuseStep 75066041 = 56299531) B56299531
theorem B14830289 : Blo 1735068 14830289 := bstep (se 2 (by rfl) ⟨5561358, by rfl⟩ : syracuseStep 14830289 = 11122717) B11122717
theorem B6589309 : Blo 1735068 6589309 := bstep (se 3 (by rfl) ⟨1235495, by rfl⟩ : syracuseStep 6589309 = 2470991) B2470991
theorem B1952743 : Blo 1735068 1952743 := bstep (se 1 (by rfl) ⟨1464557, by rfl⟩ : syracuseStep 1952743 = 2929115) B2929115
theorem B8784935 : Blo 1735068 8784935 := bstep (se 1 (by rfl) ⟨6588701, by rfl⟩ : syracuseStep 8784935 = 13177403) B13177403
theorem B18771011 : Blo 1735068 18771011 := bstep (se 1 (by rfl) ⟨14078258, by rfl⟩ : syracuseStep 18771011 = 28156517) B28156517
theorem B15035507 : Blo 1735068 15035507 := bstep (se 1 (by rfl) ⟨11276630, by rfl⟩ : syracuseStep 15035507 = 22553261) B22553261
theorem B5860727 : Blo 1735068 5860727 := bstep (se 1 (by rfl) ⟨4395545, by rfl⟩ : syracuseStep 5860727 = 8791091) B8791091
theorem B28151459 : Blo 1735068 28151459 := bstep (se 1 (by rfl) ⟨21113594, by rfl⟩ : syracuseStep 28151459 = 42227189) B42227189
theorem B11275949 : Blo 1735068 11275949 := bstep (se 3 (by rfl) ⟨2114240, by rfl⟩ : syracuseStep 11275949 = 4228481) B4228481
theorem B3706555 : Blo 1735068 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B4394807 : Blo 1735068 4394807 := bstep (se 1 (by rfl) ⟨3296105, by rfl⟩ : syracuseStep 4394807 = 6592211) B6592211
theorem B95047499 : Blo 1735068 95047499 := bstep (se 1 (by rfl) ⟨71285624, by rfl⟩ : syracuseStep 95047499 = 142571249) B142571249
theorem B4394857 : Blo 1735068 4394857 := bstep (se 2 (by rfl) ⟨1648071, by rfl⟩ : syracuseStep 4394857 = 3296143) B3296143
theorem B7917419 : Blo 1735068 7917419 := bstep (se 1 (by rfl) ⟨5938064, by rfl⟩ : syracuseStep 7917419 = 11876129) B11876129
theorem B2781449 : Blo 1735068 2781449 := bstep (se 2 (by rfl) ⟨1043043, by rfl⟩ : syracuseStep 2781449 = 2086087) B2086087
theorem B2929007 : Blo 1735068 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B12677491 : Blo 1735068 12677491 := bstep (se 1 (by rfl) ⟨9508118, by rfl⟩ : syracuseStep 12677491 = 19016237) B19016237
theorem B3903911 : Blo 1735068 3903911 := bstep (se 1 (by rfl) ⟨2927933, by rfl⟩ : syracuseStep 3903911 = 5855867) B5855867
theorem B2257403 : Blo 1735068 2257403 := bstep (se 1 (by rfl) ⟨1693052, by rfl⟩ : syracuseStep 2257403 = 3386105) B3386105
theorem B3904019 : Blo 1735068 3904019 := bstep (se 1 (by rfl) ⟨2928014, by rfl⟩ : syracuseStep 3904019 = 5856029) B5856029
theorem B2929223 : Blo 1735068 2929223 := bstep (se 1 (by rfl) ⟨2196917, by rfl⟩ : syracuseStep 2929223 = 4393835) B4393835
theorem B3904073 : Blo 1735068 3904073 := bstep (se 2 (by rfl) ⟨1464027, by rfl⟩ : syracuseStep 3904073 = 2928055) B2928055
theorem B3707615 : Blo 1735068 3707615 := bstep (se 1 (by rfl) ⟨2780711, by rfl⟩ : syracuseStep 3707615 = 5561423) B5561423
theorem B3904487 : Blo 1735068 3904487 := bstep (se 1 (by rfl) ⟨2928365, by rfl⟩ : syracuseStep 3904487 = 5856731) B5856731
theorem B2929655 : Blo 1735068 2929655 := bstep (se 1 (by rfl) ⟨2197241, by rfl⟩ : syracuseStep 2929655 = 4394483) B4394483
theorem B8787041 : Blo 1735068 8787041 := bstep (se 2 (by rfl) ⟨3295140, by rfl⟩ : syracuseStep 8787041 = 6590281) B6590281
theorem B3904865 : Blo 1735068 3904865 := bstep (se 2 (by rfl) ⟨1464324, by rfl⟩ : syracuseStep 3904865 = 2928649) B2928649
theorem B2471305 : Blo 1735068 2471305 := bstep (se 2 (by rfl) ⟨926739, by rfl⟩ : syracuseStep 2471305 = 1853479) B1853479
theorem B4453793 : Blo 1735068 4453793 := bstep (se 2 (by rfl) ⟨1670172, by rfl⟩ : syracuseStep 4453793 = 3340345) B3340345
theorem B3904955 : Blo 1735068 3904955 := bstep (se 1 (by rfl) ⟨2928716, by rfl⟩ : syracuseStep 3904955 = 5857433) B5857433
theorem B13178375 : Blo 1735068 13178375 := bstep (se 1 (by rfl) ⟨9883781, by rfl⟩ : syracuseStep 13178375 = 19767563) B19767563
theorem B3905081 : Blo 1735068 3905081 := bstep (se 2 (by rfl) ⟨1464405, by rfl⟩ : syracuseStep 3905081 = 2928811) B2928811
theorem B6682169 : Blo 1735068 6682169 := bstep (se 2 (by rfl) ⟨2505813, by rfl⟩ : syracuseStep 6682169 = 5011627) B5011627
theorem B231478885 : Blo 1735068 231478885 := bstep (se 4 (by rfl) ⟨21701145, by rfl⟩ : syracuseStep 231478885 = 43402291) B43402291
theorem B2930411 : Blo 1735068 2930411 := bstep (se 1 (by rfl) ⟨2197808, by rfl⟩ : syracuseStep 2930411 = 4395617) B4395617
theorem B2602793 : Blo 1735068 2602793 := bstep (se 2 (by rfl) ⟨976047, by rfl⟩ : syracuseStep 2602793 = 1952095) B1952095
theorem B2602799 : Blo 1735068 2602799 := bstep (se 1 (by rfl) ⟨1952099, by rfl⟩ : syracuseStep 2602799 = 3904199) B3904199
theorem B1759207 : Blo 1735068 1759207 := bstep (se 1 (by rfl) ⟨1319405, by rfl⟩ : syracuseStep 1759207 = 2638811) B2638811
theorem B3758089 : Blo 1735068 3758089 := bstep (se 2 (by rfl) ⟨1409283, by rfl⟩ : syracuseStep 3758089 = 2818567) B2818567
theorem B6592697 : Blo 1735068 6592697 := bstep (se 2 (by rfl) ⟨2472261, by rfl⟩ : syracuseStep 6592697 = 4944523) B4944523
theorem B3905747 : Blo 1735068 3905747 := bstep (se 1 (by rfl) ⟨2929310, by rfl⟩ : syracuseStep 3905747 = 5858621) B5858621
theorem B2603273 : Blo 1735068 2603273 := bstep (se 2 (by rfl) ⟨976227, by rfl⟩ : syracuseStep 2603273 = 1952455) B1952455
theorem B3905801 : Blo 1735068 3905801 := bstep (se 2 (by rfl) ⟨1464675, by rfl⟩ : syracuseStep 3905801 = 2929351) B2929351
theorem B2603375 : Blo 1735068 2603375 := bstep (se 1 (by rfl) ⟨1952531, by rfl⟩ : syracuseStep 2603375 = 3905063) B3905063
theorem B1735079 : Blo 1735068 1735079 := bstep (se 1 (by rfl) ⟨1301309, by rfl⟩ : syracuseStep 1735079 = 2602619) B2602619
theorem B3906017 : Blo 1735068 3906017 := bstep (se 2 (by rfl) ⟨1464756, by rfl⟩ : syracuseStep 3906017 = 2929513) B2929513
theorem B1735163 : Blo 1735068 1735163 := bstep (se 1 (by rfl) ⟨1301372, by rfl⟩ : syracuseStep 1735163 = 2602745) B2602745
theorem B1735231 : Blo 1735068 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B1735239 : Blo 1735068 1735239 := bstep (se 1 (by rfl) ⟨1301429, by rfl⟩ : syracuseStep 1735239 = 2602859) B2602859
theorem B2603591 : Blo 1735068 2603591 := bstep (se 1 (by rfl) ⟨1952693, by rfl⟩ : syracuseStep 2603591 = 3905387) B3905387
theorem B2603627 : Blo 1735068 2603627 := bstep (se 1 (by rfl) ⟨1952720, by rfl⟩ : syracuseStep 2603627 = 3905441) B3905441
theorem B1735391 : Blo 1735068 1735391 := bstep (se 1 (by rfl) ⟨1301543, by rfl⟩ : syracuseStep 1735391 = 2603087) B2603087
theorem B3906323 : Blo 1735068 3906323 := bstep (se 1 (by rfl) ⟨2929742, by rfl⟩ : syracuseStep 3906323 = 5859485) B5859485
theorem B1735471 : Blo 1735068 1735471 := bstep (se 1 (by rfl) ⟨1301603, by rfl⟩ : syracuseStep 1735471 = 2603207) B2603207
theorem B2603855 : Blo 1735068 2603855 := bstep (se 1 (by rfl) ⟨1952891, by rfl⟩ : syracuseStep 2603855 = 3905783) B3905783
theorem B9886607 : Blo 1735068 9886607 := bstep (se 1 (by rfl) ⟨7414955, by rfl⟩ : syracuseStep 9886607 = 14829911) B14829911
theorem B1735579 : Blo 1735068 1735579 := bstep (se 1 (by rfl) ⟨1301684, by rfl⟩ : syracuseStep 1735579 = 2603369) B2603369
theorem B13179833 : Blo 1735068 13179833 := bstep (se 2 (by rfl) ⟨4942437, by rfl⟩ : syracuseStep 13179833 = 9884875) B9884875
theorem B1735631 : Blo 1735068 1735631 := bstep (se 1 (by rfl) ⟨1301723, by rfl⟩ : syracuseStep 1735631 = 2603447) B2603447
theorem B1735655 : Blo 1735068 1735655 := bstep (se 1 (by rfl) ⟨1301741, by rfl⟩ : syracuseStep 1735655 = 2603483) B2603483
theorem B7920755 : Blo 1735068 7920755 := bstep (se 1 (by rfl) ⟨5940566, by rfl⟩ : syracuseStep 7920755 = 11881133) B11881133
theorem B3906683 : Blo 1735068 3906683 := bstep (se 1 (by rfl) ⟨2930012, by rfl⟩ : syracuseStep 3906683 = 5860025) B5860025
theorem B2604251 : Blo 1735068 2604251 := bstep (se 1 (by rfl) ⟨1953188, by rfl⟩ : syracuseStep 2604251 = 3906377) B3906377
theorem B3906809 : Blo 1735068 3906809 := bstep (se 2 (by rfl) ⟨1465053, by rfl⟩ : syracuseStep 3906809 = 2930107) B2930107
theorem B1735967 : Blo 1735068 1735967 := bstep (se 1 (by rfl) ⟨1301975, by rfl⟩ : syracuseStep 1735967 = 2603951) B2603951
theorem B8789309 : Blo 1735068 8789309 := bstep (se 3 (by rfl) ⟨1647995, by rfl⟩ : syracuseStep 8789309 = 3295991) B3295991
theorem B1736027 : Blo 1735068 1736027 := bstep (se 1 (by rfl) ⟨1302020, by rfl⟩ : syracuseStep 1736027 = 2604041) B2604041
theorem B1736047 : Blo 1735068 1736047 := bstep (se 1 (by rfl) ⟨1302035, by rfl⟩ : syracuseStep 1736047 = 2604071) B2604071
theorem B2604425 : Blo 1735068 2604425 := bstep (se 2 (by rfl) ⟨976659, by rfl⟩ : syracuseStep 2604425 = 1953319) B1953319
theorem B3906953 : Blo 1735068 3906953 := bstep (se 2 (by rfl) ⟨1465107, by rfl⟩ : syracuseStep 3906953 = 2930215) B2930215
theorem B1736103 : Blo 1735068 1736103 := bstep (se 1 (by rfl) ⟨1302077, by rfl⟩ : syracuseStep 1736103 = 2604155) B2604155
theorem B65068505 : Blo 1735068 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B1736187 : Blo 1735068 1736187 := bstep (se 1 (by rfl) ⟨1302140, by rfl⟩ : syracuseStep 1736187 = 2604281) B2604281
theorem B3907079 : Blo 1735068 3907079 := bstep (se 1 (by rfl) ⟨2930309, by rfl⟩ : syracuseStep 3907079 = 5860619) B5860619
theorem B9887291 : Blo 1735068 9887291 := bstep (se 1 (by rfl) ⟨7415468, by rfl⟩ : syracuseStep 9887291 = 14830937) B14830937
theorem B1736255 : Blo 1735068 1736255 := bstep (se 1 (by rfl) ⟨1302191, by rfl⟩ : syracuseStep 1736255 = 2604383) B2604383
theorem B1736263 : Blo 1735068 1736263 := bstep (se 1 (by rfl) ⟨1302197, by rfl⟩ : syracuseStep 1736263 = 2604395) B2604395
theorem B48168593 : Blo 1735068 48168593 := bstep (se 2 (by rfl) ⟨18063222, by rfl⟩ : syracuseStep 48168593 = 36126445) B36126445
theorem B56327825 : Blo 1735068 56327825 := bstep (se 2 (by rfl) ⟨21122934, by rfl⟩ : syracuseStep 56327825 = 42245869) B42245869
theorem B3907259 : Blo 1735068 3907259 := bstep (se 1 (by rfl) ⟨2930444, by rfl⟩ : syracuseStep 3907259 = 5860889) B5860889
theorem B1736415 : Blo 1735068 1736415 := bstep (se 1 (by rfl) ⟨1302311, by rfl⟩ : syracuseStep 1736415 = 2604623) B2604623
theorem B2604779 : Blo 1735068 2604779 := bstep (se 1 (by rfl) ⟨1953584, by rfl⟩ : syracuseStep 2604779 = 3907169) B3907169
theorem B1736495 : Blo 1735068 1736495 := bstep (se 1 (by rfl) ⟨1302371, by rfl⟩ : syracuseStep 1736495 = 2604743) B2604743
theorem B5562857 : Blo 1735068 5562857 := bstep (se 2 (by rfl) ⟨2086071, by rfl⟩ : syracuseStep 5562857 = 4172143) B4172143
theorem B5857865 : Blo 1735068 5857865 := bstep (se 2 (by rfl) ⟨2196699, by rfl⟩ : syracuseStep 5857865 = 4393399) B4393399
theorem B97608401 : Blo 1735068 97608401 := bstep (se 2 (by rfl) ⟨36603150, by rfl⟩ : syracuseStep 97608401 = 73206301) B73206301
theorem B5858027 : Blo 1735068 5858027 := bstep (se 1 (by rfl) ⟨4393520, by rfl⟩ : syracuseStep 5858027 = 8787041) B8787041
theorem B2196335 : Blo 1735068 2196335 := bstep (se 1 (by rfl) ⟨1647251, by rfl⟩ : syracuseStep 2196335 = 3294503) B3294503
theorem B2196391 : Blo 1735068 2196391 := bstep (se 1 (by rfl) ⟨1647293, by rfl⟩ : syracuseStep 2196391 = 3294587) B3294587
theorem B24732845 : Blo 1735068 24732845 := bstep (se 3 (by rfl) ⟨4637408, by rfl⟩ : syracuseStep 24732845 = 9274817) B9274817
theorem B4392265 : Blo 1735068 4392265 := bstep (se 2 (by rfl) ⟨1647099, by rfl⟩ : syracuseStep 4392265 = 3294199) B3294199
theorem B5277001 : Blo 1735068 5277001 := bstep (se 2 (by rfl) ⟨1978875, by rfl⟩ : syracuseStep 5277001 = 3957751) B3957751
theorem B47514995 : Blo 1735068 47514995 := bstep (se 1 (by rfl) ⟨35636246, by rfl⟩ : syracuseStep 47514995 = 71272493) B71272493
theorem B6342259 : Blo 1735068 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B4392569 : Blo 1735068 4392569 := bstep (se 2 (by rfl) ⟨1647213, by rfl⟩ : syracuseStep 4392569 = 3294427) B3294427
theorem B3295073 : Blo 1735068 3295073 := bstep (se 2 (by rfl) ⟨1235652, by rfl⟩ : syracuseStep 3295073 = 2471305) B2471305
theorem B5859539 : Blo 1735068 5859539 := bstep (se 1 (by rfl) ⟨4394654, by rfl⟩ : syracuseStep 5859539 = 8789309) B8789309
theorem B4942073 : Blo 1735068 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B43379003 : Blo 1735068 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B5859809 : Blo 1735068 5859809 := bstep (se 2 (by rfl) ⟨2197428, by rfl⟩ : syracuseStep 5859809 = 4394857) B4394857
theorem B5278279 : Blo 1735068 5278279 := bstep (se 1 (by rfl) ⟨3958709, by rfl⟩ : syracuseStep 5278279 = 7917419) B7917419
theorem B24078965 : Blo 1735068 24078965 := bstep (se 5 (by rfl) ⟨1128701, by rfl⟩ : syracuseStep 24078965 = 2257403) B2257403
theorem B2345609 : Blo 1735068 2345609 := bstep (se 2 (by rfl) ⟨879603, by rfl⟩ : syracuseStep 2345609 = 1759207) B1759207
theorem B1854299 : Blo 1735068 1854299 := bstep (se 1 (by rfl) ⟨1390724, by rfl⟩ : syracuseStep 1854299 = 2781449) B2781449
theorem B1952671 : Blo 1735068 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B13732901 : Blo 1735068 13732901 := bstep (se 4 (by rfl) ⟨1287459, by rfl⟩ : syracuseStep 13732901 = 2574919) B2574919
theorem B1952815 : Blo 1735068 1952815 := bstep (se 1 (by rfl) ⟨1464611, by rfl⟩ : syracuseStep 1952815 = 2929223) B2929223
theorem B33352843 : Blo 1735068 33352843 := bstep (se 1 (by rfl) ⟨25014632, by rfl⟩ : syracuseStep 33352843 = 50029265) B50029265
theorem B1953103 : Blo 1735068 1953103 := bstep (se 1 (by rfl) ⟨1464827, by rfl⟩ : syracuseStep 1953103 = 2929655) B2929655
theorem B21114377 : Blo 1735068 21114377 := bstep (se 2 (by rfl) ⟨7917891, by rfl⟩ : syracuseStep 21114377 = 15835783) B15835783
theorem B2969195 : Blo 1735068 2969195 := bstep (se 1 (by rfl) ⟨2226896, by rfl⟩ : syracuseStep 2969195 = 4453793) B4453793
theorem B2928271 : Blo 1735068 2928271 := bstep (se 1 (by rfl) ⟨2196203, by rfl⟩ : syracuseStep 2928271 = 4392407) B4392407
theorem B8785583 : Blo 1735068 8785583 := bstep (se 1 (by rfl) ⟨6589187, by rfl⟩ : syracuseStep 8785583 = 13178375) B13178375
theorem B21114665 : Blo 1735068 21114665 := bstep (se 2 (by rfl) ⟨7917999, by rfl⟩ : syracuseStep 21114665 = 15835999) B15835999
theorem B1953607 : Blo 1735068 1953607 := bstep (se 1 (by rfl) ⟨1465205, by rfl⟩ : syracuseStep 1953607 = 2930411) B2930411
theorem B8785745 : Blo 1735068 8785745 := bstep (se 2 (by rfl) ⟨3294654, by rfl⟩ : syracuseStep 8785745 = 6589309) B6589309
theorem B9383863 : Blo 1735068 9383863 := bstep (se 1 (by rfl) ⟨7037897, by rfl⟩ : syracuseStep 9383863 = 14075795) B14075795
theorem B4395131 : Blo 1735068 4395131 := bstep (se 1 (by rfl) ⟨3296348, by rfl⟩ : syracuseStep 4395131 = 6592697) B6592697
theorem B19771937 : Blo 1735068 19771937 := bstep (se 2 (by rfl) ⟨7414476, by rfl⟩ : syracuseStep 19771937 = 14828953) B14828953
theorem B6591071 : Blo 1735068 6591071 := bstep (se 1 (by rfl) ⟨4943303, by rfl⟩ : syracuseStep 6591071 = 9886607) B9886607
theorem B67613285 : Blo 1735068 67613285 := bstep (se 4 (by rfl) ⟨6338745, by rfl⟩ : syracuseStep 67613285 = 12677491) B12677491
theorem B8786555 : Blo 1735068 8786555 := bstep (se 1 (by rfl) ⟨6589916, by rfl⟩ : syracuseStep 8786555 = 13179833) B13179833
theorem B12514007 : Blo 1735068 12514007 := bstep (se 1 (by rfl) ⟨9385505, by rfl⟩ : syracuseStep 12514007 = 18771011) B18771011
theorem B10023671 : Blo 1735068 10023671 := bstep (se 1 (by rfl) ⟨7517753, by rfl⟩ : syracuseStep 10023671 = 15035507) B15035507
theorem B5280503 : Blo 1735068 5280503 := bstep (se 1 (by rfl) ⟨3960377, by rfl⟩ : syracuseStep 5280503 = 7920755) B7920755
theorem B308638513 : Blo 1735068 308638513 := bstep (se 2 (by rfl) ⟨115739442, by rfl⟩ : syracuseStep 308638513 = 231478885) B231478885
theorem B6591527 : Blo 1735068 6591527 := bstep (se 1 (by rfl) ⟨4943645, by rfl⟩ : syracuseStep 6591527 = 9887291) B9887291
theorem B7517299 : Blo 1735068 7517299 := bstep (se 1 (by rfl) ⟨5637974, by rfl⟩ : syracuseStep 7517299 = 11275949) B11275949
theorem B2929871 : Blo 1735068 2929871 := bstep (se 1 (by rfl) ⟨2197403, by rfl⟩ : syracuseStep 2929871 = 4394807) B4394807
theorem B5010785 : Blo 1735068 5010785 := bstep (se 2 (by rfl) ⟨1879044, by rfl⟩ : syracuseStep 5010785 = 3758089) B3758089
theorem B39081325 : Blo 1735068 39081325 := bstep (se 3 (by rfl) ⟨7327748, by rfl⟩ : syracuseStep 39081325 = 14655497) B14655497
theorem B2602607 : Blo 1735068 2602607 := bstep (se 1 (by rfl) ⟨1951955, by rfl⟩ : syracuseStep 2602607 = 3903911) B3903911
theorem B2602679 : Blo 1735068 2602679 := bstep (se 1 (by rfl) ⟨1952009, by rfl⟩ : syracuseStep 2602679 = 3904019) B3904019
theorem B3905207 : Blo 1735068 3905207 := bstep (se 1 (by rfl) ⟨2928905, by rfl⟩ : syracuseStep 3905207 = 5857811) B5857811
theorem B2602715 : Blo 1735068 2602715 := bstep (se 1 (by rfl) ⟨1952036, by rfl⟩ : syracuseStep 2602715 = 3904073) B3904073
theorem B2471743 : Blo 1735068 2471743 := bstep (se 1 (by rfl) ⟨1853807, by rfl⟩ : syracuseStep 2471743 = 3707615) B3707615
theorem B2602889 : Blo 1735068 2602889 := bstep (se 2 (by rfl) ⟨976083, by rfl⟩ : syracuseStep 2602889 = 1952167) B1952167
theorem B2602991 : Blo 1735068 2602991 := bstep (se 1 (by rfl) ⟨1952243, by rfl⟩ : syracuseStep 2602991 = 3904487) B3904487
theorem B12507203 : Blo 1735068 12507203 := bstep (se 1 (by rfl) ⟨9380402, by rfl⟩ : syracuseStep 12507203 = 18760805) B18760805
theorem B6592711 : Blo 1735068 6592711 := bstep (se 1 (by rfl) ⟨4944533, by rfl⟩ : syracuseStep 6592711 = 9889067) B9889067
theorem B2603243 : Blo 1735068 2603243 := bstep (se 1 (by rfl) ⟨1952432, by rfl⟩ : syracuseStep 2603243 = 3904865) B3904865
theorem B2603303 : Blo 1735068 2603303 := bstep (se 1 (by rfl) ⟨1952477, by rfl⟩ : syracuseStep 2603303 = 3904955) B3904955
theorem B2603387 : Blo 1735068 2603387 := bstep (se 1 (by rfl) ⟨1952540, by rfl⟩ : syracuseStep 2603387 = 3905081) B3905081
theorem B4454779 : Blo 1735068 4454779 := bstep (se 1 (by rfl) ⟨3341084, by rfl⟩ : syracuseStep 4454779 = 6682169) B6682169
theorem B1735195 : Blo 1735068 1735195 := bstep (se 1 (by rfl) ⟨1301396, by rfl⟩ : syracuseStep 1735195 = 2602793) B2602793
theorem B1735199 : Blo 1735068 1735199 := bstep (se 1 (by rfl) ⟨1301399, by rfl⟩ : syracuseStep 1735199 = 2602799) B2602799
theorem B2603657 : Blo 1735068 2603657 := bstep (se 2 (by rfl) ⟨976371, by rfl⟩ : syracuseStep 2603657 = 1952743) B1952743
theorem B2603831 : Blo 1735068 2603831 := bstep (se 1 (by rfl) ⟨1952873, by rfl⟩ : syracuseStep 2603831 = 3905747) B3905747
theorem B5856083 : Blo 1735068 5856083 := bstep (se 1 (by rfl) ⟨4392062, by rfl⟩ : syracuseStep 5856083 = 8784125) B8784125
theorem B7412563 : Blo 1735068 7412563 := bstep (se 1 (by rfl) ⟨5559422, by rfl⟩ : syracuseStep 7412563 = 11118845) B11118845
theorem B1735515 : Blo 1735068 1735515 := bstep (se 1 (by rfl) ⟨1301636, by rfl⟩ : syracuseStep 1735515 = 2603273) B2603273
theorem B2603867 : Blo 1735068 2603867 := bstep (se 1 (by rfl) ⟨1952900, by rfl⟩ : syracuseStep 2603867 = 3905801) B3905801
theorem B3906395 : Blo 1735068 3906395 := bstep (se 1 (by rfl) ⟨2929796, by rfl⟩ : syracuseStep 3906395 = 5859593) B5859593
theorem B1735583 : Blo 1735068 1735583 := bstep (se 1 (by rfl) ⟨1301687, by rfl⟩ : syracuseStep 1735583 = 2603375) B2603375
theorem B2604011 : Blo 1735068 2604011 := bstep (se 1 (by rfl) ⟨1953008, by rfl⟩ : syracuseStep 2604011 = 3906017) B3906017
theorem B1735727 : Blo 1735068 1735727 := bstep (se 1 (by rfl) ⟨1301795, by rfl⟩ : syracuseStep 1735727 = 2603591) B2603591
theorem B1735751 : Blo 1735068 1735751 := bstep (se 1 (by rfl) ⟨1301813, by rfl⟩ : syracuseStep 1735751 = 2603627) B2603627
theorem B50044027 : Blo 1735068 50044027 := bstep (se 1 (by rfl) ⟨37533020, by rfl⟩ : syracuseStep 50044027 = 75066041) B75066041
theorem B5561473 : Blo 1735068 5561473 := bstep (se 2 (by rfl) ⟨2085552, by rfl⟩ : syracuseStep 5561473 = 4171105) B4171105
theorem B9886859 : Blo 1735068 9886859 := bstep (se 1 (by rfl) ⟨7415144, by rfl⟩ : syracuseStep 9886859 = 14830289) B14830289
theorem B2604215 : Blo 1735068 2604215 := bstep (se 1 (by rfl) ⟨1953161, by rfl⟩ : syracuseStep 2604215 = 3906323) B3906323
theorem B1735903 : Blo 1735068 1735903 := bstep (se 1 (by rfl) ⟨1301927, by rfl⟩ : syracuseStep 1735903 = 2603855) B2603855
theorem B5856623 : Blo 1735068 5856623 := bstep (se 1 (by rfl) ⟨4392467, by rfl⟩ : syracuseStep 5856623 = 8784935) B8784935
theorem B2604455 : Blo 1735068 2604455 := bstep (se 1 (by rfl) ⟨1953341, by rfl⟩ : syracuseStep 2604455 = 3906683) B3906683
theorem B1736167 : Blo 1735068 1736167 := bstep (se 1 (by rfl) ⟨1302125, by rfl⟩ : syracuseStep 1736167 = 2604251) B2604251
theorem B2604539 : Blo 1735068 2604539 := bstep (se 1 (by rfl) ⟨1953404, by rfl⟩ : syracuseStep 2604539 = 3906809) B3906809
theorem B3907151 : Blo 1735068 3907151 := bstep (se 1 (by rfl) ⟨2930363, by rfl⟩ : syracuseStep 3907151 = 5860727) B5860727
theorem B1736283 : Blo 1735068 1736283 := bstep (se 1 (by rfl) ⟨1302212, by rfl⟩ : syracuseStep 1736283 = 2604425) B2604425
theorem B2604635 : Blo 1735068 2604635 := bstep (se 1 (by rfl) ⟨1953476, by rfl⟩ : syracuseStep 2604635 = 3906953) B3906953
theorem B2604719 : Blo 1735068 2604719 := bstep (se 1 (by rfl) ⟨1953539, by rfl⟩ : syracuseStep 2604719 = 3907079) B3907079
theorem B5857001 : Blo 1735068 5857001 := bstep (se 2 (by rfl) ⟨2196375, by rfl⟩ : syracuseStep 5857001 = 4392751) B4392751
theorem B32112395 : Blo 1735068 32112395 := bstep (se 1 (by rfl) ⟨24084296, by rfl⟩ : syracuseStep 32112395 = 48168593) B48168593
theorem B37551883 : Blo 1735068 37551883 := bstep (se 1 (by rfl) ⟨28163912, by rfl⟩ : syracuseStep 37551883 = 56327825) B56327825
theorem B18767639 : Blo 1735068 18767639 := bstep (se 1 (by rfl) ⟨14075729, by rfl⟩ : syracuseStep 18767639 = 28151459) B28151459
theorem B2604839 : Blo 1735068 2604839 := bstep (se 1 (by rfl) ⟨1953629, by rfl⟩ : syracuseStep 2604839 = 3907259) B3907259
theorem B1736519 : Blo 1735068 1736519 := bstep (se 1 (by rfl) ⟨1302389, by rfl⟩ : syracuseStep 1736519 = 2604779) B2604779
theorem B63364999 : Blo 1735068 63364999 := bstep (se 1 (by rfl) ⟨47523749, by rfl⟩ : syracuseStep 63364999 = 95047499) B95047499
theorem B8790281 : Blo 1735068 8790281 := bstep (se 2 (by rfl) ⟨3296355, by rfl⟩ : syracuseStep 8790281 = 6592711) B6592711
theorem B13181291 : Blo 1735068 13181291 := bstep (se 1 (by rfl) ⟨9885968, by rfl⟩ : syracuseStep 13181291 = 19771937) B19771937
theorem B5857703 : Blo 1735068 5857703 := bstep (se 1 (by rfl) ⟨4393277, by rfl⟩ : syracuseStep 5857703 = 8786555) B8786555
theorem B5939705 : Blo 1735068 5939705 := bstep (se 2 (by rfl) ⟨2227389, by rfl⟩ : syracuseStep 5939705 = 4454779) B4454779
theorem B7037705 : Blo 1735068 7037705 := bstep (se 2 (by rfl) ⟨2639139, by rfl⟩ : syracuseStep 7037705 = 5278279) B5278279
theorem B411518017 : Blo 1735068 411518017 := bstep (se 2 (by rfl) ⟨154319256, by rfl⟩ : syracuseStep 411518017 = 308638513) B308638513
theorem B2196715 : Blo 1735068 2196715 := bstep (se 1 (by rfl) ⟨1647536, by rfl⟩ : syracuseStep 2196715 = 3295073) B3295073
theorem B66725369 : Blo 1735068 66725369 := bstep (se 2 (by rfl) ⟨25022013, by rfl⟩ : syracuseStep 66725369 = 50044027) B50044027
theorem B7415297 : Blo 1735068 7415297 := bstep (se 2 (by rfl) ⟨2780736, by rfl⟩ : syracuseStep 7415297 = 5561473) B5561473
theorem B64210573 : Blo 1735068 64210573 := bstep (se 3 (by rfl) ⟨12039482, by rfl⟩ : syracuseStep 64210573 = 24078965) B24078965
theorem B8456345 : Blo 1735068 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B14076251 : Blo 1735068 14076251 := bstep (se 1 (by rfl) ⟨10557188, by rfl⟩ : syracuseStep 14076251 = 21114377) B21114377
theorem B3295657 : Blo 1735068 3295657 := bstep (se 2 (by rfl) ⟨1235871, by rfl⟩ : syracuseStep 3295657 = 2471743) B2471743
theorem B21408263 : Blo 1735068 21408263 := bstep (se 1 (by rfl) ⟨16056197, by rfl⟩ : syracuseStep 21408263 = 32112395) B32112395
theorem B84486665 : Blo 1735068 84486665 := bstep (se 2 (by rfl) ⟨31682499, by rfl⟩ : syracuseStep 84486665 = 63364999) B63364999
theorem B12511759 : Blo 1735068 12511759 := bstep (se 1 (by rfl) ⟨9383819, by rfl⟩ : syracuseStep 12511759 = 18767639) B18767639
theorem B14076443 : Blo 1735068 14076443 := bstep (se 1 (by rfl) ⟨10557332, by rfl⟩ : syracuseStep 14076443 = 21114665) B21114665
theorem B12511817 : Blo 1735068 12511817 := bstep (se 2 (by rfl) ⟨4691931, by rfl⟩ : syracuseStep 12511817 = 9383863) B9383863
theorem B4394047 : Blo 1735068 4394047 := bstep (se 1 (by rfl) ⟨3295535, by rfl⟩ : syracuseStep 4394047 = 6591071) B6591071
theorem B45075523 : Blo 1735068 45075523 := bstep (se 1 (by rfl) ⟨33806642, by rfl⟩ : syracuseStep 45075523 = 67613285) B67613285
theorem B65072267 : Blo 1735068 65072267 := bstep (se 1 (by rfl) ⟨48804200, by rfl⟩ : syracuseStep 65072267 = 97608401) B97608401
theorem B8342671 : Blo 1735068 8342671 := bstep (se 1 (by rfl) ⟨6257003, by rfl⟩ : syracuseStep 8342671 = 12514007) B12514007
theorem B4394351 : Blo 1735068 4394351 := bstep (se 1 (by rfl) ⟨3295763, by rfl⟩ : syracuseStep 4394351 = 6591527) B6591527
theorem B1953247 : Blo 1735068 1953247 := bstep (se 1 (by rfl) ⟨1464935, by rfl⟩ : syracuseStep 1953247 = 2929871) B2929871
theorem B2928379 : Blo 1735068 2928379 := bstep (se 1 (by rfl) ⟨2196284, by rfl⟩ : syracuseStep 2928379 = 4392569) B4392569
theorem B9883417 : Blo 1735068 9883417 := bstep (se 2 (by rfl) ⟨3706281, by rfl⟩ : syracuseStep 9883417 = 7412563) B7412563
theorem B2928521 : Blo 1735068 2928521 := bstep (se 2 (by rfl) ⟨1098195, by rfl⟩ : syracuseStep 2928521 = 2196391) B2196391
theorem B10023065 : Blo 1735068 10023065 := bstep (se 2 (by rfl) ⟨3758649, by rfl⟩ : syracuseStep 10023065 = 7517299) B7517299
theorem B44470457 : Blo 1735068 44470457 := bstep (se 2 (by rfl) ⟨16676421, by rfl⟩ : syracuseStep 44470457 = 33352843) B33352843
theorem B7917853 : Blo 1735068 7917853 := bstep (se 3 (by rfl) ⟨1484597, by rfl⟩ : syracuseStep 7917853 = 2969195) B2969195
theorem B6254957 : Blo 1735068 6254957 := bstep (se 3 (by rfl) ⟨1172804, by rfl⟩ : syracuseStep 6254957 = 2345609) B2345609
theorem B3904055 : Blo 1735068 3904055 := bstep (se 1 (by rfl) ⟨2928041, by rfl⟩ : syracuseStep 3904055 = 5856083) B5856083
theorem B9155267 : Blo 1735068 9155267 := bstep (se 1 (by rfl) ⟨6866450, by rfl⟩ : syracuseStep 9155267 = 13732901) B13732901
theorem B6591239 : Blo 1735068 6591239 := bstep (se 1 (by rfl) ⟨4943429, by rfl⟩ : syracuseStep 6591239 = 9886859) B9886859
theorem B3904361 : Blo 1735068 3904361 := bstep (se 2 (by rfl) ⟨1464135, by rfl⟩ : syracuseStep 3904361 = 2928271) B2928271
theorem B4944797 : Blo 1735068 4944797 := bstep (se 3 (by rfl) ⟨927149, by rfl⟩ : syracuseStep 4944797 = 1854299) B1854299
theorem B3904415 : Blo 1735068 3904415 := bstep (se 1 (by rfl) ⟨2928311, by rfl⟩ : syracuseStep 3904415 = 5856623) B5856623
theorem B3904667 : Blo 1735068 3904667 := bstep (se 1 (by rfl) ⟨2928500, by rfl⟩ : syracuseStep 3904667 = 5857001) B5857001
theorem B56325365 : Blo 1735068 56325365 := bstep (se 5 (by rfl) ⟨2640251, by rfl⟩ : syracuseStep 56325365 = 5280503) B5280503
theorem B2930087 : Blo 1735068 2930087 := bstep (se 1 (by rfl) ⟨2197565, by rfl⟩ : syracuseStep 2930087 = 4395131) B4395131
theorem B3905243 : Blo 1735068 3905243 := bstep (se 1 (by rfl) ⟨2928932, by rfl⟩ : syracuseStep 3905243 = 5857865) B5857865
theorem B3905351 : Blo 1735068 3905351 := bstep (se 1 (by rfl) ⟨2929013, by rfl⟩ : syracuseStep 3905351 = 5858027) B5858027
theorem B6682447 : Blo 1735068 6682447 := bstep (se 1 (by rfl) ⟨5011835, by rfl⟩ : syracuseStep 6682447 = 10023671) B10023671
theorem B13178861 : Blo 1735068 13178861 := bstep (se 3 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 13178861 = 4942073) B4942073
theorem B16488563 : Blo 1735068 16488563 := bstep (se 1 (by rfl) ⟨12366422, by rfl⟩ : syracuseStep 16488563 = 24732845) B24732845
theorem B115677341 : Blo 1735068 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B3340523 : Blo 1735068 3340523 := bstep (se 1 (by rfl) ⟨2505392, by rfl⟩ : syracuseStep 3340523 = 5010785) B5010785
theorem B31676663 : Blo 1735068 31676663 := bstep (se 1 (by rfl) ⟨23757497, by rfl⟩ : syracuseStep 31676663 = 47514995) B47514995
theorem B1735071 : Blo 1735068 1735071 := bstep (se 1 (by rfl) ⟨1301303, by rfl⟩ : syracuseStep 1735071 = 2602607) B2602607
theorem B1735119 : Blo 1735068 1735119 := bstep (se 1 (by rfl) ⟨1301339, by rfl⟩ : syracuseStep 1735119 = 2602679) B2602679
theorem B2603471 : Blo 1735068 2603471 := bstep (se 1 (by rfl) ⟨1952603, by rfl⟩ : syracuseStep 2603471 = 3905207) B3905207
theorem B1735143 : Blo 1735068 1735143 := bstep (se 1 (by rfl) ⟨1301357, by rfl⟩ : syracuseStep 1735143 = 2602715) B2602715
theorem B2603561 : Blo 1735068 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B1735259 : Blo 1735068 1735259 := bstep (se 1 (by rfl) ⟨1301444, by rfl⟩ : syracuseStep 1735259 = 2602889) B2602889
theorem B14834285 : Blo 1735068 14834285 := bstep (se 3 (by rfl) ⟨2781428, by rfl⟩ : syracuseStep 14834285 = 5562857) B5562857
theorem B1735327 : Blo 1735068 1735327 := bstep (se 1 (by rfl) ⟨1301495, by rfl⟩ : syracuseStep 1735327 = 2602991) B2602991
theorem B8338135 : Blo 1735068 8338135 := bstep (se 1 (by rfl) ⟨6253601, by rfl⟩ : syracuseStep 8338135 = 12507203) B12507203
theorem B2603753 : Blo 1735068 2603753 := bstep (se 2 (by rfl) ⟨976407, by rfl⟩ : syracuseStep 2603753 = 1952815) B1952815
theorem B3906359 : Blo 1735068 3906359 := bstep (se 1 (by rfl) ⟨2929769, by rfl⟩ : syracuseStep 3906359 = 5859539) B5859539
theorem B1735495 : Blo 1735068 1735495 := bstep (se 1 (by rfl) ⟨1301621, by rfl⟩ : syracuseStep 1735495 = 2603243) B2603243
theorem B1735535 : Blo 1735068 1735535 := bstep (se 1 (by rfl) ⟨1301651, by rfl⟩ : syracuseStep 1735535 = 2603303) B2603303
theorem B1735591 : Blo 1735068 1735591 := bstep (se 1 (by rfl) ⟨1301693, by rfl⟩ : syracuseStep 1735591 = 2603387) B2603387
theorem B3906539 : Blo 1735068 3906539 := bstep (se 1 (by rfl) ⟨2929904, by rfl⟩ : syracuseStep 3906539 = 5859809) B5859809
theorem B1735771 : Blo 1735068 1735771 := bstep (se 1 (by rfl) ⟨1301828, by rfl⟩ : syracuseStep 1735771 = 2603657) B2603657
theorem B5856353 : Blo 1735068 5856353 := bstep (se 2 (by rfl) ⟨2196132, by rfl⟩ : syracuseStep 5856353 = 4392265) B4392265
theorem B7036001 : Blo 1735068 7036001 := bstep (se 2 (by rfl) ⟨2638500, by rfl⟩ : syracuseStep 7036001 = 5277001) B5277001
theorem B2604137 : Blo 1735068 2604137 := bstep (se 2 (by rfl) ⟨976551, by rfl⟩ : syracuseStep 2604137 = 1953103) B1953103
theorem B52108433 : Blo 1735068 52108433 := bstep (se 2 (by rfl) ⟨19540662, by rfl⟩ : syracuseStep 52108433 = 39081325) B39081325
theorem B1735887 : Blo 1735068 1735887 := bstep (se 1 (by rfl) ⟨1301915, by rfl⟩ : syracuseStep 1735887 = 2603831) B2603831
theorem B1735911 : Blo 1735068 1735911 := bstep (se 1 (by rfl) ⟨1301933, by rfl⟩ : syracuseStep 1735911 = 2603867) B2603867
theorem B2604263 : Blo 1735068 2604263 := bstep (se 1 (by rfl) ⟨1953197, by rfl⟩ : syracuseStep 2604263 = 3906395) B3906395
theorem B1736007 : Blo 1735068 1736007 := bstep (se 1 (by rfl) ⟨1302005, by rfl⟩ : syracuseStep 1736007 = 2604011) B2604011
theorem B1736143 : Blo 1735068 1736143 := bstep (se 1 (by rfl) ⟨1302107, by rfl⟩ : syracuseStep 1736143 = 2604215) B2604215
theorem B1736303 : Blo 1735068 1736303 := bstep (se 1 (by rfl) ⟨1302227, by rfl⟩ : syracuseStep 1736303 = 2604455) B2604455
theorem B5856893 : Blo 1735068 5856893 := bstep (se 3 (by rfl) ⟨1098167, by rfl⟩ : syracuseStep 5856893 = 2196335) B2196335
theorem B1736359 : Blo 1735068 1736359 := bstep (se 1 (by rfl) ⟨1302269, by rfl⟩ : syracuseStep 1736359 = 2604539) B2604539
theorem B50069177 : Blo 1735068 50069177 := bstep (se 2 (by rfl) ⟨18775941, by rfl⟩ : syracuseStep 50069177 = 37551883) B37551883
theorem B2604767 : Blo 1735068 2604767 := bstep (se 1 (by rfl) ⟨1953575, by rfl⟩ : syracuseStep 2604767 = 3907151) B3907151
theorem B1736423 : Blo 1735068 1736423 := bstep (se 1 (by rfl) ⟨1302317, by rfl⟩ : syracuseStep 1736423 = 2604635) B2604635
theorem B2604809 : Blo 1735068 2604809 := bstep (se 2 (by rfl) ⟨976803, by rfl⟩ : syracuseStep 2604809 = 1953607) B1953607
theorem B5857055 : Blo 1735068 5857055 := bstep (se 1 (by rfl) ⟨4392791, by rfl⟩ : syracuseStep 5857055 = 8785583) B8785583
theorem B1736479 : Blo 1735068 1736479 := bstep (se 1 (by rfl) ⟨1302359, by rfl⟩ : syracuseStep 1736479 = 2604719) B2604719
theorem B1736559 : Blo 1735068 1736559 := bstep (se 1 (by rfl) ⟨1302419, by rfl⟩ : syracuseStep 1736559 = 2604839) B2604839
theorem B5857163 : Blo 1735068 5857163 := bstep (se 1 (by rfl) ⟨4392872, by rfl⟩ : syracuseStep 5857163 = 8785745) B8785745
theorem B29646971 : Blo 1735068 29646971 := bstep (se 1 (by rfl) ⟨22235228, by rfl⟩ : syracuseStep 29646971 = 44470457) B44470457
theorem B4169971 : Blo 1735068 4169971 := bstep (se 1 (by rfl) ⟨3127478, by rfl⟩ : syracuseStep 4169971 = 6254957) B6254957
theorem B6103511 : Blo 1735068 6103511 := bstep (se 1 (by rfl) ⟨4577633, by rfl⟩ : syracuseStep 6103511 = 9155267) B9155267
theorem B11117513 : Blo 1735068 11117513 := bstep (se 2 (by rfl) ⟨4169067, by rfl⟩ : syracuseStep 11117513 = 8338135) B8338135
theorem B44483579 : Blo 1735068 44483579 := bstep (se 1 (by rfl) ⟨33362684, by rfl⟩ : syracuseStep 44483579 = 66725369) B66725369
theorem B5858729 : Blo 1735068 5858729 := bstep (se 2 (by rfl) ⟨2197023, by rfl⟩ : syracuseStep 5858729 = 4394047) B4394047
theorem B5637563 : Blo 1735068 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B14272175 : Blo 1735068 14272175 := bstep (se 1 (by rfl) ⟨10704131, by rfl⟩ : syracuseStep 14272175 = 21408263) B21408263
theorem B8341211 : Blo 1735068 8341211 := bstep (se 1 (by rfl) ⟨6255908, by rfl⟩ : syracuseStep 8341211 = 12511817) B12511817
theorem B9889523 : Blo 1735068 9889523 := bstep (se 1 (by rfl) ⟨7417142, by rfl⟩ : syracuseStep 9889523 = 14834285) B14834285
theorem B1952347 : Blo 1735068 1952347 := bstep (se 1 (by rfl) ⟨1464260, by rfl⟩ : syracuseStep 1952347 = 2928521) B2928521
theorem B5860187 : Blo 1735068 5860187 := bstep (se 1 (by rfl) ⟨4395140, by rfl⟩ : syracuseStep 5860187 = 8790281) B8790281
theorem B43969501 : Blo 1735068 43969501 := bstep (se 3 (by rfl) ⟨8244281, by rfl⟩ : syracuseStep 43969501 = 16488563) B16488563
theorem B3959803 : Blo 1735068 3959803 := bstep (se 1 (by rfl) ⟨2969852, by rfl⟩ : syracuseStep 3959803 = 5939705) B5939705
theorem B4394159 : Blo 1735068 4394159 := bstep (se 1 (by rfl) ⟨3295619, by rfl⟩ : syracuseStep 4394159 = 6591239) B6591239
theorem B4394209 : Blo 1735068 4394209 := bstep (se 2 (by rfl) ⟨1647828, by rfl⟩ : syracuseStep 4394209 = 3295657) B3295657
theorem B3296531 : Blo 1735068 3296531 := bstep (se 1 (by rfl) ⟨2472398, by rfl⟩ : syracuseStep 3296531 = 4944797) B4944797
theorem B8908061 : Blo 1735068 8908061 := bstep (se 3 (by rfl) ⟨1670261, by rfl⟩ : syracuseStep 8908061 = 3340523) B3340523
theorem B16682345 : Blo 1735068 16682345 := bstep (se 2 (by rfl) ⟨6255879, by rfl⟩ : syracuseStep 16682345 = 12511759) B12511759
theorem B1953391 : Blo 1735068 1953391 := bstep (se 1 (by rfl) ⟨1465043, by rfl⟩ : syracuseStep 1953391 = 2930087) B2930087
theorem B4943531 : Blo 1735068 4943531 := bstep (se 1 (by rfl) ⟨3707648, by rfl⟩ : syracuseStep 4943531 = 7415297) B7415297
theorem B8785907 : Blo 1735068 8785907 := bstep (se 1 (by rfl) ⟨6589430, by rfl⟩ : syracuseStep 8785907 = 13178861) B13178861
theorem B60100697 : Blo 1735068 60100697 := bstep (se 2 (by rfl) ⟨22537761, by rfl⟩ : syracuseStep 60100697 = 45075523) B45075523
theorem B9384167 : Blo 1735068 9384167 := bstep (se 1 (by rfl) ⟨7038125, by rfl⟩ : syracuseStep 9384167 = 14076251) B14076251
theorem B2928953 : Blo 1735068 2928953 := bstep (se 2 (by rfl) ⟨1098357, by rfl⟩ : syracuseStep 2928953 = 2196715) B2196715
theorem B56324443 : Blo 1735068 56324443 := bstep (se 1 (by rfl) ⟨42243332, by rfl⟩ : syracuseStep 56324443 = 84486665) B84486665
theorem B9384295 : Blo 1735068 9384295 := bstep (se 1 (by rfl) ⟨7038221, by rfl⟩ : syracuseStep 9384295 = 14076443) B14076443
theorem B3904235 : Blo 1735068 3904235 := bstep (se 1 (by rfl) ⟨2928176, by rfl⟩ : syracuseStep 3904235 = 5856353) B5856353
theorem B4690667 : Blo 1735068 4690667 := bstep (se 1 (by rfl) ⟨3518000, by rfl⟩ : syracuseStep 4690667 = 7036001) B7036001
theorem B43381511 : Blo 1735068 43381511 := bstep (se 1 (by rfl) ⟨32536133, by rfl⟩ : syracuseStep 43381511 = 65072267) B65072267
theorem B34738955 : Blo 1735068 34738955 := bstep (se 1 (by rfl) ⟨26054216, by rfl⟩ : syracuseStep 34738955 = 52108433) B52108433
theorem B2929567 : Blo 1735068 2929567 := bstep (se 1 (by rfl) ⟨2197175, by rfl⟩ : syracuseStep 2929567 = 4394351) B4394351
theorem B3904505 : Blo 1735068 3904505 := bstep (se 2 (by rfl) ⟨1464189, by rfl⟩ : syracuseStep 3904505 = 2928379) B2928379
theorem B13177889 : Blo 1735068 13177889 := bstep (se 2 (by rfl) ⟨4941708, by rfl⟩ : syracuseStep 13177889 = 9883417) B9883417
theorem B3904595 : Blo 1735068 3904595 := bstep (se 1 (by rfl) ⟨2928446, by rfl⟩ : syracuseStep 3904595 = 5856893) B5856893
theorem B8909929 : Blo 1735068 8909929 := bstep (se 2 (by rfl) ⟨3341223, by rfl⟩ : syracuseStep 8909929 = 6682447) B6682447
theorem B33379451 : Blo 1735068 33379451 := bstep (se 1 (by rfl) ⟨25034588, by rfl⟩ : syracuseStep 33379451 = 50069177) B50069177
theorem B3904703 : Blo 1735068 3904703 := bstep (se 1 (by rfl) ⟨2928527, by rfl⟩ : syracuseStep 3904703 = 5857055) B5857055
theorem B3904775 : Blo 1735068 3904775 := bstep (se 1 (by rfl) ⟨2928581, by rfl⟩ : syracuseStep 3904775 = 5857163) B5857163
theorem B6682043 : Blo 1735068 6682043 := bstep (se 1 (by rfl) ⟨5011532, by rfl⟩ : syracuseStep 6682043 = 10023065) B10023065
theorem B8787527 : Blo 1735068 8787527 := bstep (se 1 (by rfl) ⟨6590645, by rfl⟩ : syracuseStep 8787527 = 13181291) B13181291
theorem B3905135 : Blo 1735068 3905135 := bstep (se 1 (by rfl) ⟨2928851, by rfl⟩ : syracuseStep 3905135 = 5857703) B5857703
theorem B2602703 : Blo 1735068 2602703 := bstep (se 1 (by rfl) ⟨1952027, by rfl⟩ : syracuseStep 2602703 = 3904055) B3904055
theorem B10557137 : Blo 1735068 10557137 := bstep (se 2 (by rfl) ⟨3958926, by rfl⟩ : syracuseStep 10557137 = 7917853) B7917853
theorem B4691803 : Blo 1735068 4691803 := bstep (se 1 (by rfl) ⟨3518852, by rfl⟩ : syracuseStep 4691803 = 7037705) B7037705
theorem B2602907 : Blo 1735068 2602907 := bstep (se 1 (by rfl) ⟨1952180, by rfl⟩ : syracuseStep 2602907 = 3904361) B3904361
theorem B2602943 : Blo 1735068 2602943 := bstep (se 1 (by rfl) ⟨1952207, by rfl⟩ : syracuseStep 2602943 = 3904415) B3904415
theorem B2603111 : Blo 1735068 2603111 := bstep (se 1 (by rfl) ⟨1952333, by rfl⟩ : syracuseStep 2603111 = 3904667) B3904667
theorem B37550243 : Blo 1735068 37550243 := bstep (se 1 (by rfl) ⟨28162682, by rfl⟩ : syracuseStep 37550243 = 56325365) B56325365
theorem B2603495 : Blo 1735068 2603495 := bstep (se 1 (by rfl) ⟨1952621, by rfl⟩ : syracuseStep 2603495 = 3905243) B3905243
theorem B2603567 : Blo 1735068 2603567 := bstep (se 1 (by rfl) ⟨1952675, by rfl⟩ : syracuseStep 2603567 = 3905351) B3905351
theorem B548690689 : Blo 1735068 548690689 := bstep (se 2 (by rfl) ⟨205759008, by rfl⟩ : syracuseStep 548690689 = 411518017) B411518017
theorem B77118227 : Blo 1735068 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B21117775 : Blo 1735068 21117775 := bstep (se 1 (by rfl) ⟨15838331, by rfl⟩ : syracuseStep 21117775 = 31676663) B31676663
theorem B11123561 : Blo 1735068 11123561 := bstep (se 2 (by rfl) ⟨4171335, by rfl⟩ : syracuseStep 11123561 = 8342671) B8342671
theorem B1735647 : Blo 1735068 1735647 := bstep (se 1 (by rfl) ⟨1301735, by rfl⟩ : syracuseStep 1735647 = 2603471) B2603471
theorem B1735707 : Blo 1735068 1735707 := bstep (se 1 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 1735707 = 2603561) B2603561
theorem B1735835 : Blo 1735068 1735835 := bstep (se 1 (by rfl) ⟨1301876, by rfl⟩ : syracuseStep 1735835 = 2603753) B2603753
theorem B2604239 : Blo 1735068 2604239 := bstep (se 1 (by rfl) ⟨1953179, by rfl⟩ : syracuseStep 2604239 = 3906359) B3906359
theorem B2604329 : Blo 1735068 2604329 := bstep (se 2 (by rfl) ⟨976623, by rfl⟩ : syracuseStep 2604329 = 1953247) B1953247
theorem B2604359 : Blo 1735068 2604359 := bstep (se 1 (by rfl) ⟨1953269, by rfl⟩ : syracuseStep 2604359 = 3906539) B3906539
theorem B1736091 : Blo 1735068 1736091 := bstep (se 1 (by rfl) ⟨1302068, by rfl⟩ : syracuseStep 1736091 = 2604137) B2604137
theorem B1736175 : Blo 1735068 1736175 := bstep (se 1 (by rfl) ⟨1302131, by rfl⟩ : syracuseStep 1736175 = 2604263) B2604263
theorem B85614097 : Blo 1735068 85614097 := bstep (se 2 (by rfl) ⟨32105286, by rfl⟩ : syracuseStep 85614097 = 64210573) B64210573
theorem B1736511 : Blo 1735068 1736511 := bstep (se 1 (by rfl) ⟨1302383, by rfl⟩ : syracuseStep 1736511 = 2604767) B2604767
theorem B1736539 : Blo 1735068 1736539 := bstep (se 1 (by rfl) ⟨1302404, by rfl⟩ : syracuseStep 1736539 = 2604809) B2604809
theorem B40067131 : Blo 1735068 40067131 := bstep (se 1 (by rfl) ⟨30050348, by rfl⟩ : syracuseStep 40067131 = 60100697) B60100697
theorem B23159303 : Blo 1735068 23159303 := bstep (se 1 (by rfl) ⟨17369477, by rfl⟩ : syracuseStep 23159303 = 34738955) B34738955
theorem B29655719 : Blo 1735068 29655719 := bstep (se 1 (by rfl) ⟨22241789, by rfl⟩ : syracuseStep 29655719 = 44483579) B44483579
theorem B731587585 : Blo 1735068 731587585 := bstep (se 2 (by rfl) ⟨274345344, by rfl⟩ : syracuseStep 731587585 = 548690689) B548690689
theorem B5858351 : Blo 1735068 5858351 := bstep (se 1 (by rfl) ⟨4393763, by rfl⟩ : syracuseStep 5858351 = 8787527) B8787527
theorem B28157033 : Blo 1735068 28157033 := bstep (se 2 (by rfl) ⟨10558887, by rfl⟩ : syracuseStep 28157033 = 21117775) B21117775
theorem B7038091 : Blo 1735068 7038091 := bstep (se 1 (by rfl) ⟨5278568, by rfl⟩ : syracuseStep 7038091 = 10557137) B10557137
theorem B11879905 : Blo 1735068 11879905 := bstep (se 2 (by rfl) ⟨4454964, by rfl⟩ : syracuseStep 11879905 = 8909929) B8909929
theorem B5858945 : Blo 1735068 5858945 := bstep (se 2 (by rfl) ⟨2197104, by rfl⟩ : syracuseStep 5858945 = 4394209) B4394209
theorem B13182749 : Blo 1735068 13182749 := bstep (se 3 (by rfl) ⟨2471765, by rfl⟩ : syracuseStep 13182749 = 4943531) B4943531
theorem B7415707 : Blo 1735068 7415707 := bstep (se 1 (by rfl) ⟨5561780, by rfl⟩ : syracuseStep 7415707 = 11123561) B11123561
theorem B2197687 : Blo 1735068 2197687 := bstep (se 1 (by rfl) ⟨1648265, by rfl⟩ : syracuseStep 2197687 = 3296531) B3296531
theorem B1952635 : Blo 1735068 1952635 := bstep (se 1 (by rfl) ⟨1464476, by rfl⟩ : syracuseStep 1952635 = 2928953) B2928953
theorem B75099257 : Blo 1735068 75099257 := bstep (se 2 (by rfl) ⟨28162221, by rfl⟩ : syracuseStep 75099257 = 56324443) B56324443
theorem B12512393 : Blo 1735068 12512393 := bstep (se 2 (by rfl) ⟨4692147, by rfl⟩ : syracuseStep 12512393 = 9384295) B9384295
theorem B28921007 : Blo 1735068 28921007 := bstep (se 1 (by rfl) ⟨21690755, by rfl⟩ : syracuseStep 28921007 = 43381511) B43381511
theorem B8785259 : Blo 1735068 8785259 := bstep (se 1 (by rfl) ⟨6588944, by rfl⟩ : syracuseStep 8785259 = 13177889) B13177889
theorem B22252967 : Blo 1735068 22252967 := bstep (se 1 (by rfl) ⟨16689725, by rfl⟩ : syracuseStep 22252967 = 33379451) B33379451
theorem B9514783 : Blo 1735068 9514783 := bstep (se 1 (by rfl) ⟨7136087, by rfl⟩ : syracuseStep 9514783 = 14272175) B14272175
theorem B58626001 : Blo 1735068 58626001 := bstep (se 2 (by rfl) ⟨21984750, by rfl⟩ : syracuseStep 58626001 = 43969501) B43969501
theorem B5279737 : Blo 1735068 5279737 := bstep (se 2 (by rfl) ⟨1979901, by rfl⟩ : syracuseStep 5279737 = 3959803) B3959803
theorem B114152129 : Blo 1735068 114152129 := bstep (se 2 (by rfl) ⟨42807048, by rfl⟩ : syracuseStep 114152129 = 85614097) B85614097
theorem B2929439 : Blo 1735068 2929439 := bstep (se 1 (by rfl) ⟨2197079, by rfl⟩ : syracuseStep 2929439 = 4394159) B4394159
theorem B11121563 : Blo 1735068 11121563 := bstep (se 1 (by rfl) ⟨8341172, by rfl⟩ : syracuseStep 11121563 = 16682345) B16682345
theorem B6255737 : Blo 1735068 6255737 := bstep (se 2 (by rfl) ⟨2345901, by rfl⟩ : syracuseStep 6255737 = 4691803) B4691803
theorem B19764647 : Blo 1735068 19764647 := bstep (se 1 (by rfl) ⟨14823485, by rfl⟩ : syracuseStep 19764647 = 29646971) B29646971
theorem B6256111 : Blo 1735068 6256111 := bstep (se 1 (by rfl) ⟨4692083, by rfl⟩ : syracuseStep 6256111 = 9384167) B9384167
theorem B4069007 : Blo 1735068 4069007 := bstep (se 1 (by rfl) ⟨3051755, by rfl⟩ : syracuseStep 4069007 = 6103511) B6103511
theorem B2602823 : Blo 1735068 2602823 := bstep (se 1 (by rfl) ⟨1952117, by rfl⟩ : syracuseStep 2602823 = 3904235) B3904235
theorem B7411675 : Blo 1735068 7411675 := bstep (se 1 (by rfl) ⟨5558756, by rfl⟩ : syracuseStep 7411675 = 11117513) B11117513
theorem B2603003 : Blo 1735068 2603003 := bstep (se 1 (by rfl) ⟨1952252, by rfl⟩ : syracuseStep 2603003 = 3904505) B3904505
theorem B2603063 : Blo 1735068 2603063 := bstep (se 1 (by rfl) ⟨1952297, by rfl⟩ : syracuseStep 2603063 = 3904595) B3904595
theorem B23754829 : Blo 1735068 23754829 := bstep (se 3 (by rfl) ⟨4454030, by rfl⟩ : syracuseStep 23754829 = 8908061) B8908061
theorem B2603129 : Blo 1735068 2603129 := bstep (se 2 (by rfl) ⟨976173, by rfl⟩ : syracuseStep 2603129 = 1952347) B1952347
theorem B2603135 : Blo 1735068 2603135 := bstep (se 1 (by rfl) ⟨1952351, by rfl⟩ : syracuseStep 2603135 = 3904703) B3904703
theorem B2603183 : Blo 1735068 2603183 := bstep (se 1 (by rfl) ⟨1952387, by rfl⟩ : syracuseStep 2603183 = 3904775) B3904775
theorem B3905819 : Blo 1735068 3905819 := bstep (se 1 (by rfl) ⟨2929364, by rfl⟩ : syracuseStep 3905819 = 5858729) B5858729
theorem B3758375 : Blo 1735068 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B4454695 : Blo 1735068 4454695 := bstep (se 1 (by rfl) ⟨3341021, by rfl⟩ : syracuseStep 4454695 = 6682043) B6682043
theorem B2603423 : Blo 1735068 2603423 := bstep (se 1 (by rfl) ⟨1952567, by rfl⟩ : syracuseStep 2603423 = 3905135) B3905135
theorem B1735135 : Blo 1735068 1735135 := bstep (se 1 (by rfl) ⟨1301351, by rfl⟩ : syracuseStep 1735135 = 2602703) B2602703
theorem B5560807 : Blo 1735068 5560807 := bstep (se 1 (by rfl) ⟨4170605, by rfl⟩ : syracuseStep 5560807 = 8341211) B8341211
theorem B6593015 : Blo 1735068 6593015 := bstep (se 1 (by rfl) ⟨4944761, by rfl⟩ : syracuseStep 6593015 = 9889523) B9889523
theorem B3906089 : Blo 1735068 3906089 := bstep (se 2 (by rfl) ⟨1464783, by rfl⟩ : syracuseStep 3906089 = 2929567) B2929567
theorem B22239845 : Blo 1735068 22239845 := bstep (se 4 (by rfl) ⟨2084985, by rfl⟩ : syracuseStep 22239845 = 4169971) B4169971
theorem B1735271 : Blo 1735068 1735271 := bstep (se 1 (by rfl) ⟨1301453, by rfl⟩ : syracuseStep 1735271 = 2602907) B2602907
theorem B1735295 : Blo 1735068 1735295 := bstep (se 1 (by rfl) ⟨1301471, by rfl⟩ : syracuseStep 1735295 = 2602943) B2602943
theorem B1735407 : Blo 1735068 1735407 := bstep (se 1 (by rfl) ⟨1301555, by rfl⟩ : syracuseStep 1735407 = 2603111) B2603111
theorem B25033495 : Blo 1735068 25033495 := bstep (se 1 (by rfl) ⟨18775121, by rfl⟩ : syracuseStep 25033495 = 37550243) B37550243
theorem B1735663 : Blo 1735068 1735663 := bstep (se 1 (by rfl) ⟨1301747, by rfl⟩ : syracuseStep 1735663 = 2603495) B2603495
theorem B1735711 : Blo 1735068 1735711 := bstep (se 1 (by rfl) ⟨1301783, by rfl⟩ : syracuseStep 1735711 = 2603567) B2603567
theorem B51412151 : Blo 1735068 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B3906791 : Blo 1735068 3906791 := bstep (se 1 (by rfl) ⟨2930093, by rfl⟩ : syracuseStep 3906791 = 5860187) B5860187
theorem B12508445 : Blo 1735068 12508445 := bstep (se 3 (by rfl) ⟨2345333, by rfl⟩ : syracuseStep 12508445 = 4690667) B4690667
theorem B1736159 : Blo 1735068 1736159 := bstep (se 1 (by rfl) ⟨1302119, by rfl⟩ : syracuseStep 1736159 = 2604239) B2604239
theorem B2604521 : Blo 1735068 2604521 := bstep (se 2 (by rfl) ⟨976695, by rfl⟩ : syracuseStep 2604521 = 1953391) B1953391
theorem B1736219 : Blo 1735068 1736219 := bstep (se 1 (by rfl) ⟨1302164, by rfl⟩ : syracuseStep 1736219 = 2604329) B2604329
theorem B1736239 : Blo 1735068 1736239 := bstep (se 1 (by rfl) ⟨1302179, by rfl⟩ : syracuseStep 1736239 = 2604359) B2604359
theorem B5857271 : Blo 1735068 5857271 := bstep (se 1 (by rfl) ⟨4392953, by rfl⟩ : syracuseStep 5857271 = 8785907) B8785907
theorem B7414375 : Blo 1735068 7414375 := bstep (se 1 (by rfl) ⟨5560781, by rfl⟩ : syracuseStep 7414375 = 11121563) B11121563
theorem B7414409 : Blo 1735068 7414409 := bstep (se 2 (by rfl) ⟨2780403, by rfl⟩ : syracuseStep 7414409 = 5560807) B5560807
theorem B4170491 : Blo 1735068 4170491 := bstep (se 1 (by rfl) ⟨3127868, by rfl⟩ : syracuseStep 4170491 = 6255737) B6255737
theorem B2712671 : Blo 1735068 2712671 := bstep (se 1 (by rfl) ⟨2034503, by rfl⟩ : syracuseStep 2712671 = 4069007) B4069007
theorem B23758373 : Blo 1735068 23758373 := bstep (se 4 (by rfl) ⟨2227347, by rfl⟩ : syracuseStep 23758373 = 4454695) B4454695
theorem B8341481 : Blo 1735068 8341481 := bstep (se 2 (by rfl) ⟨3128055, by rfl⟩ : syracuseStep 8341481 = 6256111) B6256111
theorem B8341595 : Blo 1735068 8341595 := bstep (se 1 (by rfl) ⟨6256196, by rfl⟩ : syracuseStep 8341595 = 12512393) B12512393
theorem B9882233 : Blo 1735068 9882233 := bstep (se 2 (by rfl) ⟨3705837, by rfl⟩ : syracuseStep 9882233 = 7411675) B7411675
theorem B7039649 : Blo 1735068 7039649 := bstep (se 2 (by rfl) ⟨2639868, by rfl⟩ : syracuseStep 7039649 = 5279737) B5279737
theorem B53422841 : Blo 1735068 53422841 := bstep (se 2 (by rfl) ⟨20033565, by rfl⟩ : syracuseStep 53422841 = 40067131) B40067131
theorem B31673105 : Blo 1735068 31673105 := bstep (se 2 (by rfl) ⟨11877414, by rfl⟩ : syracuseStep 31673105 = 23754829) B23754829
theorem B19770479 : Blo 1735068 19770479 := bstep (se 1 (by rfl) ⟨14827859, by rfl⟩ : syracuseStep 19770479 = 29655719) B29655719
theorem B77122685 : Blo 1735068 77122685 := bstep (se 3 (by rfl) ⟨14460503, by rfl⟩ : syracuseStep 77122685 = 28921007) B28921007
theorem B1952959 : Blo 1735068 1952959 := bstep (se 1 (by rfl) ⟨1464719, by rfl⟩ : syracuseStep 1952959 = 2929439) B2929439
theorem B18771355 : Blo 1735068 18771355 := bstep (se 1 (by rfl) ⟨14078516, by rfl⟩ : syracuseStep 18771355 = 28157033) B28157033
theorem B13176431 : Blo 1735068 13176431 := bstep (se 1 (by rfl) ⟨9882323, by rfl⟩ : syracuseStep 13176431 = 19764647) B19764647
theorem B33377993 : Blo 1735068 33377993 := bstep (se 2 (by rfl) ⟨12516747, by rfl⟩ : syracuseStep 33377993 = 25033495) B25033495
theorem B975450113 : Blo 1735068 975450113 := bstep (se 2 (by rfl) ⟨365793792, by rfl⟩ : syracuseStep 975450113 = 731587585) B731587585
theorem B9384121 : Blo 1735068 9384121 := bstep (se 2 (by rfl) ⟨3519045, by rfl⟩ : syracuseStep 9384121 = 7038091) B7038091
theorem B4395343 : Blo 1735068 4395343 := bstep (se 1 (by rfl) ⟨3296507, by rfl⟩ : syracuseStep 4395343 = 6593015) B6593015
theorem B15839873 : Blo 1735068 15839873 := bstep (se 2 (by rfl) ⟨5939952, by rfl⟩ : syracuseStep 15839873 = 11879905) B11879905
theorem B50066171 : Blo 1735068 50066171 := bstep (se 1 (by rfl) ⟨37549628, by rfl⟩ : syracuseStep 50066171 = 75099257) B75099257
theorem B12686377 : Blo 1735068 12686377 := bstep (se 2 (by rfl) ⟨4757391, by rfl⟩ : syracuseStep 12686377 = 9514783) B9514783
theorem B3904847 : Blo 1735068 3904847 := bstep (se 1 (by rfl) ⟨2928635, by rfl⟩ : syracuseStep 3904847 = 5857271) B5857271
theorem B2930249 : Blo 1735068 2930249 := bstep (se 2 (by rfl) ⟨1098843, by rfl⟩ : syracuseStep 2930249 = 2197687) B2197687
theorem B15439535 : Blo 1735068 15439535 := bstep (se 1 (by rfl) ⟨11579651, by rfl⟩ : syracuseStep 15439535 = 23159303) B23159303
theorem B76101419 : Blo 1735068 76101419 := bstep (se 1 (by rfl) ⟨57076064, by rfl⟩ : syracuseStep 76101419 = 114152129) B114152129
theorem B3905567 : Blo 1735068 3905567 := bstep (se 1 (by rfl) ⟨2929175, by rfl⟩ : syracuseStep 3905567 = 5858351) B5858351
theorem B3905963 : Blo 1735068 3905963 := bstep (se 1 (by rfl) ⟨2929472, by rfl⟩ : syracuseStep 3905963 = 5858945) B5858945
theorem B2603513 : Blo 1735068 2603513 := bstep (se 2 (by rfl) ⟨976317, by rfl⟩ : syracuseStep 2603513 = 1952635) B1952635
theorem B8788499 : Blo 1735068 8788499 := bstep (se 1 (by rfl) ⟨6591374, by rfl⟩ : syracuseStep 8788499 = 13182749) B13182749
theorem B1735215 : Blo 1735068 1735215 := bstep (se 1 (by rfl) ⟨1301411, by rfl⟩ : syracuseStep 1735215 = 2602823) B2602823
theorem B1735335 : Blo 1735068 1735335 := bstep (se 1 (by rfl) ⟨1301501, by rfl⟩ : syracuseStep 1735335 = 2603003) B2603003
theorem B1735375 : Blo 1735068 1735375 := bstep (se 1 (by rfl) ⟨1301531, by rfl⟩ : syracuseStep 1735375 = 2603063) B2603063
theorem B1735419 : Blo 1735068 1735419 := bstep (se 1 (by rfl) ⟨1301564, by rfl⟩ : syracuseStep 1735419 = 2603129) B2603129
theorem B1735423 : Blo 1735068 1735423 := bstep (se 1 (by rfl) ⟨1301567, by rfl⟩ : syracuseStep 1735423 = 2603135) B2603135
theorem B1735455 : Blo 1735068 1735455 := bstep (se 1 (by rfl) ⟨1301591, by rfl⟩ : syracuseStep 1735455 = 2603183) B2603183
theorem B2603879 : Blo 1735068 2603879 := bstep (se 1 (by rfl) ⟨1952909, by rfl⟩ : syracuseStep 2603879 = 3905819) B3905819
theorem B2505583 : Blo 1735068 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B1735615 : Blo 1735068 1735615 := bstep (se 1 (by rfl) ⟨1301711, by rfl⟩ : syracuseStep 1735615 = 2603423) B2603423
theorem B2604059 : Blo 1735068 2604059 := bstep (se 1 (by rfl) ⟨1953044, by rfl⟩ : syracuseStep 2604059 = 3906089) B3906089
theorem B14826563 : Blo 1735068 14826563 := bstep (se 1 (by rfl) ⟨11119922, by rfl⟩ : syracuseStep 14826563 = 22239845) B22239845
theorem B34274767 : Blo 1735068 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B2604527 : Blo 1735068 2604527 := bstep (se 1 (by rfl) ⟨1953395, by rfl⟩ : syracuseStep 2604527 = 3906791) B3906791
theorem B8338963 : Blo 1735068 8338963 := bstep (se 1 (by rfl) ⟨6254222, by rfl⟩ : syracuseStep 8338963 = 12508445) B12508445
theorem B5856839 : Blo 1735068 5856839 := bstep (se 1 (by rfl) ⟨4392629, by rfl⟩ : syracuseStep 5856839 = 8785259) B8785259
theorem B14835311 : Blo 1735068 14835311 := bstep (se 1 (by rfl) ⟨11126483, by rfl⟩ : syracuseStep 14835311 = 22252967) B22252967
theorem B1736347 : Blo 1735068 1736347 := bstep (se 1 (by rfl) ⟨1302260, by rfl⟩ : syracuseStep 1736347 = 2604521) B2604521
theorem B9887609 : Blo 1735068 9887609 := bstep (se 2 (by rfl) ⟨3707853, by rfl⟩ : syracuseStep 9887609 = 7415707) B7415707
theorem B78168001 : Blo 1735068 78168001 := bstep (se 2 (by rfl) ⟨29313000, by rfl⟩ : syracuseStep 78168001 = 58626001) B58626001
theorem B10559915 : Blo 1735068 10559915 := bstep (se 1 (by rfl) ⟨7919936, by rfl⟩ : syracuseStep 10559915 = 15839873) B15839873
theorem B50734279 : Blo 1735068 50734279 := bstep (se 1 (by rfl) ⟨38050709, by rfl⟩ : syracuseStep 50734279 = 76101419) B76101419
theorem B5858999 : Blo 1735068 5858999 := bstep (se 1 (by rfl) ⟨4394249, by rfl⟩ : syracuseStep 5858999 = 8788499) B8788499
theorem B6588155 : Blo 1735068 6588155 := bstep (se 1 (by rfl) ⟨4941116, by rfl⟩ : syracuseStep 6588155 = 9882233) B9882233
theorem B25028473 : Blo 1735068 25028473 := bstep (se 2 (by rfl) ⟨9385677, by rfl⟩ : syracuseStep 25028473 = 18771355) B18771355
theorem B11118617 : Blo 1735068 11118617 := bstep (se 2 (by rfl) ⟨4169481, by rfl⟩ : syracuseStep 11118617 = 8338963) B8338963
theorem B51415123 : Blo 1735068 51415123 := bstep (se 1 (by rfl) ⟨38561342, by rfl⟩ : syracuseStep 51415123 = 77122685) B77122685
theorem B8784287 : Blo 1735068 8784287 := bstep (se 1 (by rfl) ⟨6588215, by rfl⟩ : syracuseStep 8784287 = 13176431) B13176431
theorem B9890207 : Blo 1735068 9890207 := bstep (se 1 (by rfl) ⟨7417655, by rfl⟩ : syracuseStep 9890207 = 14835311) B14835311
theorem B22251995 : Blo 1735068 22251995 := bstep (se 1 (by rfl) ⟨16688996, by rfl⟩ : syracuseStep 22251995 = 33377993) B33377993
theorem B650300075 : Blo 1735068 650300075 := bstep (se 1 (by rfl) ⟨487725056, by rfl⟩ : syracuseStep 650300075 = 975450113) B975450113
theorem B12512161 : Blo 1735068 12512161 := bstep (se 2 (by rfl) ⟨4692060, by rfl⟩ : syracuseStep 12512161 = 9384121) B9384121
theorem B4942939 : Blo 1735068 4942939 := bstep (se 1 (by rfl) ⟨3707204, by rfl⟩ : syracuseStep 4942939 = 7414409) B7414409
theorem B5860457 : Blo 1735068 5860457 := bstep (se 2 (by rfl) ⟨2197671, by rfl⟩ : syracuseStep 5860457 = 4395343) B4395343
theorem B2780327 : Blo 1735068 2780327 := bstep (se 1 (by rfl) ⟨2085245, by rfl⟩ : syracuseStep 2780327 = 4170491) B4170491
theorem B33377447 : Blo 1735068 33377447 := bstep (se 1 (by rfl) ⟨25033085, by rfl⟩ : syracuseStep 33377447 = 50066171) B50066171
theorem B15838915 : Blo 1735068 15838915 := bstep (se 1 (by rfl) ⟨11879186, by rfl⟩ : syracuseStep 15838915 = 23758373) B23758373
theorem B1953499 : Blo 1735068 1953499 := bstep (se 1 (by rfl) ⟨1465124, by rfl⟩ : syracuseStep 1953499 = 2930249) B2930249
theorem B10293023 : Blo 1735068 10293023 := bstep (se 1 (by rfl) ⟨7719767, by rfl⟩ : syracuseStep 10293023 = 15439535) B15439535
theorem B18772397 : Blo 1735068 18772397 := bstep (se 3 (by rfl) ⟨3519824, by rfl⟩ : syracuseStep 18772397 = 7039649) B7039649
theorem B35615227 : Blo 1735068 35615227 := bstep (se 1 (by rfl) ⟨26711420, by rfl⟩ : syracuseStep 35615227 = 53422841) B53422841
theorem B21115403 : Blo 1735068 21115403 := bstep (se 1 (by rfl) ⟨15836552, by rfl⟩ : syracuseStep 21115403 = 31673105) B31673105
theorem B45699689 : Blo 1735068 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B9884375 : Blo 1735068 9884375 := bstep (se 1 (by rfl) ⟨7413281, by rfl⟩ : syracuseStep 9884375 = 14826563) B14826563
theorem B3904559 : Blo 1735068 3904559 := bstep (se 1 (by rfl) ⟨2928419, by rfl⟩ : syracuseStep 3904559 = 5856839) B5856839
theorem B6591739 : Blo 1735068 6591739 := bstep (se 1 (by rfl) ⟨4943804, by rfl⟩ : syracuseStep 6591739 = 9887609) B9887609
theorem B104224001 : Blo 1735068 104224001 := bstep (se 2 (by rfl) ⟨39084000, by rfl⟩ : syracuseStep 104224001 = 78168001) B78168001
theorem B1808447 : Blo 1735068 1808447 := bstep (se 1 (by rfl) ⟨1356335, by rfl⟩ : syracuseStep 1808447 = 2712671) B2712671
theorem B9885833 : Blo 1735068 9885833 := bstep (se 2 (by rfl) ⟨3707187, by rfl⟩ : syracuseStep 9885833 = 7414375) B7414375
theorem B2603231 : Blo 1735068 2603231 := bstep (se 1 (by rfl) ⟨1952423, by rfl⟩ : syracuseStep 2603231 = 3904847) B3904847
theorem B3340777 : Blo 1735068 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B5560987 : Blo 1735068 5560987 := bstep (se 1 (by rfl) ⟨4170740, by rfl⟩ : syracuseStep 5560987 = 8341481) B8341481
theorem B2603711 : Blo 1735068 2603711 := bstep (se 1 (by rfl) ⟨1952783, by rfl⟩ : syracuseStep 2603711 = 3905567) B3905567
theorem B16915169 : Blo 1735068 16915169 := bstep (se 2 (by rfl) ⟨6343188, by rfl⟩ : syracuseStep 16915169 = 12686377) B12686377
theorem B5561063 : Blo 1735068 5561063 := bstep (se 1 (by rfl) ⟨4170797, by rfl⟩ : syracuseStep 5561063 = 8341595) B8341595
theorem B2603945 : Blo 1735068 2603945 := bstep (se 2 (by rfl) ⟨976479, by rfl⟩ : syracuseStep 2603945 = 1952959) B1952959
theorem B2603975 : Blo 1735068 2603975 := bstep (se 1 (by rfl) ⟨1952981, by rfl⟩ : syracuseStep 2603975 = 3905963) B3905963
theorem B1735675 : Blo 1735068 1735675 := bstep (se 1 (by rfl) ⟨1301756, by rfl⟩ : syracuseStep 1735675 = 2603513) B2603513
theorem B1735919 : Blo 1735068 1735919 := bstep (se 1 (by rfl) ⟨1301939, by rfl⟩ : syracuseStep 1735919 = 2603879) B2603879
theorem B1736039 : Blo 1735068 1736039 := bstep (se 1 (by rfl) ⟨1302029, by rfl⟩ : syracuseStep 1736039 = 2604059) B2604059
theorem B13180319 : Blo 1735068 13180319 := bstep (se 1 (by rfl) ⟨9885239, by rfl⟩ : syracuseStep 13180319 = 19770479) B19770479
theorem B1736351 : Blo 1735068 1736351 := bstep (se 1 (by rfl) ⟨1302263, by rfl⟩ : syracuseStep 1736351 = 2604527) B2604527
theorem B30466459 : Blo 1735068 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B7414649 : Blo 1735068 7414649 := bstep (se 2 (by rfl) ⟨2780493, by rfl⟩ : syracuseStep 7414649 = 5560987) B5560987
theorem B4392103 : Blo 1735068 4392103 := bstep (se 1 (by rfl) ⟨3294077, by rfl⟩ : syracuseStep 4392103 = 6588155) B6588155
theorem B45107117 : Blo 1735068 45107117 := bstep (se 3 (by rfl) ⟨8457584, by rfl⟩ : syracuseStep 45107117 = 16915169) B16915169
theorem B1853551 : Blo 1735068 1853551 := bstep (se 1 (by rfl) ⟨1390163, by rfl⟩ : syracuseStep 1853551 = 2780327) B2780327
theorem B22251631 : Blo 1735068 22251631 := bstep (se 1 (by rfl) ⟨16688723, by rfl⟩ : syracuseStep 22251631 = 33377447) B33377447
theorem B1111722677 : Blo 1735068 1111722677 := bstep (se 5 (by rfl) ⟨52112000, by rfl⟩ : syracuseStep 1111722677 = 104224001) B104224001
theorem B68553497 : Blo 1735068 68553497 := bstep (se 2 (by rfl) ⟨25707561, by rfl⟩ : syracuseStep 68553497 = 51415123) B51415123
theorem B7039943 : Blo 1735068 7039943 := bstep (se 1 (by rfl) ⟨5279957, by rfl⟩ : syracuseStep 7039943 = 10559915) B10559915
theorem B14076935 : Blo 1735068 14076935 := bstep (se 1 (by rfl) ⟨10557701, by rfl⟩ : syracuseStep 14076935 = 21115403) B21115403
theorem B6589583 : Blo 1735068 6589583 := bstep (se 1 (by rfl) ⟨4942187, by rfl⟩ : syracuseStep 6589583 = 9884375) B9884375
theorem B16682881 : Blo 1735068 16682881 := bstep (se 2 (by rfl) ⟨6256080, by rfl⟩ : syracuseStep 16682881 = 12512161) B12512161
theorem B6590555 : Blo 1735068 6590555 := bstep (se 1 (by rfl) ⟨4942916, by rfl⟩ : syracuseStep 6590555 = 9885833) B9885833
theorem B6590585 : Blo 1735068 6590585 := bstep (se 2 (by rfl) ⟨2471469, by rfl⟩ : syracuseStep 6590585 = 4942939) B4942939
theorem B67645705 : Blo 1735068 67645705 := bstep (se 2 (by rfl) ⟨25367139, by rfl⟩ : syracuseStep 67645705 = 50734279) B50734279
theorem B433533383 : Blo 1735068 433533383 := bstep (se 1 (by rfl) ⟨325150037, by rfl⟩ : syracuseStep 433533383 = 650300075) B650300075
theorem B3707375 : Blo 1735068 3707375 := bstep (se 1 (by rfl) ⟨2780531, by rfl⟩ : syracuseStep 3707375 = 5561063) B5561063
theorem B8786879 : Blo 1735068 8786879 := bstep (se 1 (by rfl) ⟨6590159, by rfl⟩ : syracuseStep 8786879 = 13180319) B13180319
theorem B33371297 : Blo 1735068 33371297 := bstep (se 2 (by rfl) ⟨12514236, by rfl⟩ : syracuseStep 33371297 = 25028473) B25028473
theorem B6862015 : Blo 1735068 6862015 := bstep (se 1 (by rfl) ⟨5146511, by rfl⟩ : syracuseStep 6862015 = 10293023) B10293023
theorem B4822525 : Blo 1735068 4822525 := bstep (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) B1808447
theorem B12514931 : Blo 1735068 12514931 := bstep (se 1 (by rfl) ⟨9386198, by rfl⟩ : syracuseStep 12514931 = 18772397) B18772397
theorem B4454369 : Blo 1735068 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B47486969 : Blo 1735068 47486969 := bstep (se 2 (by rfl) ⟨17807613, by rfl⟩ : syracuseStep 47486969 = 35615227) B35615227
theorem B2603039 : Blo 1735068 2603039 := bstep (se 1 (by rfl) ⟨1952279, by rfl⟩ : syracuseStep 2603039 = 3904559) B3904559
theorem B3905999 : Blo 1735068 3905999 := bstep (se 1 (by rfl) ⟨2929499, by rfl⟩ : syracuseStep 3905999 = 5858999) B5858999
theorem B7412411 : Blo 1735068 7412411 := bstep (se 1 (by rfl) ⟨5559308, by rfl⟩ : syracuseStep 7412411 = 11118617) B11118617
theorem B1735487 : Blo 1735068 1735487 := bstep (se 1 (by rfl) ⟨1301615, by rfl⟩ : syracuseStep 1735487 = 2603231) B2603231
theorem B5856191 : Blo 1735068 5856191 := bstep (se 1 (by rfl) ⟨4392143, by rfl⟩ : syracuseStep 5856191 = 8784287) B8784287
theorem B6593471 : Blo 1735068 6593471 := bstep (se 1 (by rfl) ⟨4945103, by rfl⟩ : syracuseStep 6593471 = 9890207) B9890207
theorem B14834663 : Blo 1735068 14834663 := bstep (se 1 (by rfl) ⟨11125997, by rfl⟩ : syracuseStep 14834663 = 22251995) B22251995
theorem B8788985 : Blo 1735068 8788985 := bstep (se 2 (by rfl) ⟨3295869, by rfl⟩ : syracuseStep 8788985 = 6591739) B6591739
theorem B1735807 : Blo 1735068 1735807 := bstep (se 1 (by rfl) ⟨1301855, by rfl⟩ : syracuseStep 1735807 = 2603711) B2603711
theorem B1735963 : Blo 1735068 1735963 := bstep (se 1 (by rfl) ⟨1301972, by rfl⟩ : syracuseStep 1735963 = 2603945) B2603945
theorem B1735983 : Blo 1735068 1735983 := bstep (se 1 (by rfl) ⟨1301987, by rfl⟩ : syracuseStep 1735983 = 2603975) B2603975
theorem B3906971 : Blo 1735068 3906971 := bstep (se 1 (by rfl) ⟨2930228, by rfl⟩ : syracuseStep 3906971 = 5860457) B5860457
theorem B21118553 : Blo 1735068 21118553 := bstep (se 2 (by rfl) ⟨7919457, by rfl⟩ : syracuseStep 21118553 = 15838915) B15838915
theorem B2604665 : Blo 1735068 2604665 := bstep (se 2 (by rfl) ⟨976749, by rfl⟩ : syracuseStep 2604665 = 1953499) B1953499
theorem B289022255 : Blo 1735068 289022255 := bstep (se 1 (by rfl) ⟨216766691, by rfl⟩ : syracuseStep 289022255 = 433533383) B433533383
theorem B90194273 : Blo 1735068 90194273 := bstep (se 2 (by rfl) ⟨33822852, by rfl⟩ : syracuseStep 90194273 = 67645705) B67645705
theorem B5857919 : Blo 1735068 5857919 := bstep (se 1 (by rfl) ⟨4393439, by rfl⟩ : syracuseStep 5857919 = 8786879) B8786879
theorem B741148451 : Blo 1735068 741148451 := bstep (se 1 (by rfl) ⟨555861338, by rfl⟩ : syracuseStep 741148451 = 1111722677) B1111722677
theorem B4941607 : Blo 1735068 4941607 := bstep (se 1 (by rfl) ⟨3706205, by rfl⟩ : syracuseStep 4941607 = 7412411) B7412411
theorem B9889775 : Blo 1735068 9889775 := bstep (se 1 (by rfl) ⟨7417331, by rfl⟩ : syracuseStep 9889775 = 14834663) B14834663
theorem B5859323 : Blo 1735068 5859323 := bstep (se 1 (by rfl) ⟨4394492, by rfl⟩ : syracuseStep 5859323 = 8788985) B8788985
theorem B4393055 : Blo 1735068 4393055 := bstep (se 1 (by rfl) ⟨3294791, by rfl⟩ : syracuseStep 4393055 = 6589583) B6589583
theorem B22243841 : Blo 1735068 22243841 := bstep (se 2 (by rfl) ⟨8341440, by rfl⟩ : syracuseStep 22243841 = 16682881) B16682881
theorem B4393703 : Blo 1735068 4393703 := bstep (se 1 (by rfl) ⟨3295277, by rfl⟩ : syracuseStep 4393703 = 6590555) B6590555
theorem B4393723 : Blo 1735068 4393723 := bstep (se 1 (by rfl) ⟨3295292, by rfl⟩ : syracuseStep 4393723 = 6590585) B6590585
theorem B4943099 : Blo 1735068 4943099 := bstep (se 1 (by rfl) ⟨3707324, by rfl⟩ : syracuseStep 4943099 = 7414649) B7414649
theorem B36597413 : Blo 1735068 36597413 := bstep (se 4 (by rfl) ⟨3431007, by rfl⟩ : syracuseStep 36597413 = 6862015) B6862015
theorem B8343287 : Blo 1735068 8343287 := bstep (se 1 (by rfl) ⟨6257465, by rfl⟩ : syracuseStep 8343287 = 12514931) B12514931
theorem B2969579 : Blo 1735068 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B31657979 : Blo 1735068 31657979 := bstep (se 1 (by rfl) ⟨23743484, by rfl⟩ : syracuseStep 31657979 = 47486969) B47486969
theorem B3904127 : Blo 1735068 3904127 := bstep (se 1 (by rfl) ⟨2928095, by rfl⟩ : syracuseStep 3904127 = 5856191) B5856191
theorem B4395647 : Blo 1735068 4395647 := bstep (se 1 (by rfl) ⟨3296735, by rfl⟩ : syracuseStep 4395647 = 6593471) B6593471
theorem B9384623 : Blo 1735068 9384623 := bstep (se 1 (by rfl) ⟨7038467, by rfl⟩ : syracuseStep 9384623 = 14076935) B14076935
theorem B182809325 : Blo 1735068 182809325 := bstep (se 3 (by rfl) ⟨34276748, by rfl⟩ : syracuseStep 182809325 = 68553497) B68553497
theorem B14079035 : Blo 1735068 14079035 := bstep (se 1 (by rfl) ⟨10559276, by rfl⟩ : syracuseStep 14079035 = 21118553) B21118553
theorem B2471401 : Blo 1735068 2471401 := bstep (se 2 (by rfl) ⟨926775, by rfl⟩ : syracuseStep 2471401 = 1853551) B1853551
theorem B29668841 : Blo 1735068 29668841 := bstep (se 2 (by rfl) ⟨11125815, by rfl⟩ : syracuseStep 29668841 = 22251631) B22251631
theorem B22247531 : Blo 1735068 22247531 := bstep (se 1 (by rfl) ⟨16685648, by rfl⟩ : syracuseStep 22247531 = 33371297) B33371297
theorem B30071411 : Blo 1735068 30071411 := bstep (se 1 (by rfl) ⟨22553558, by rfl⟩ : syracuseStep 30071411 = 45107117) B45107117
theorem B9886333 : Blo 1735068 9886333 := bstep (se 3 (by rfl) ⟨1853687, by rfl⟩ : syracuseStep 9886333 = 3707375) B3707375
theorem B1735359 : Blo 1735068 1735359 := bstep (se 1 (by rfl) ⟨1301519, by rfl⟩ : syracuseStep 1735359 = 2603039) B2603039
theorem B5856137 : Blo 1735068 5856137 := bstep (se 2 (by rfl) ⟨2196051, by rfl⟩ : syracuseStep 5856137 = 4392103) B4392103
theorem B2603999 : Blo 1735068 2603999 := bstep (se 1 (by rfl) ⟨1952999, by rfl⟩ : syracuseStep 2603999 = 3905999) B3905999
theorem B4693295 : Blo 1735068 4693295 := bstep (se 1 (by rfl) ⟨3519971, by rfl⟩ : syracuseStep 4693295 = 7039943) B7039943
theorem B6430033 : Blo 1735068 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B162487781 : Blo 1735068 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B2604647 : Blo 1735068 2604647 := bstep (se 1 (by rfl) ⟨1953485, by rfl⟩ : syracuseStep 2604647 = 3906971) B3906971
theorem B1736443 : Blo 1735068 1736443 := bstep (se 1 (by rfl) ⟨1302332, by rfl⟩ : syracuseStep 1736443 = 2604665) B2604665
theorem B37544093 : Blo 1735068 37544093 := bstep (se 3 (by rfl) ⟨7039517, by rfl⟩ : syracuseStep 37544093 = 14079035) B14079035
theorem B60129515 : Blo 1735068 60129515 := bstep (se 1 (by rfl) ⟨45097136, by rfl⟩ : syracuseStep 60129515 = 90194273) B90194273
theorem B121872883 : Blo 1735068 121872883 := bstep (se 1 (by rfl) ⟨91404662, by rfl⟩ : syracuseStep 121872883 = 182809325) B182809325
theorem B13181777 : Blo 1735068 13181777 := bstep (se 2 (by rfl) ⟨4943166, by rfl⟩ : syracuseStep 13181777 = 9886333) B9886333
theorem B5858297 : Blo 1735068 5858297 := bstep (se 2 (by rfl) ⟨2196861, by rfl⟩ : syracuseStep 5858297 = 4393723) B4393723
theorem B14829227 : Blo 1735068 14829227 := bstep (se 1 (by rfl) ⟨11121920, by rfl⟩ : syracuseStep 14829227 = 22243841) B22243841
theorem B20047607 : Blo 1735068 20047607 := bstep (se 1 (by rfl) ⟨15035705, by rfl⟩ : syracuseStep 20047607 = 30071411) B30071411
theorem B3295399 : Blo 1735068 3295399 := bstep (se 1 (by rfl) ⟨2471549, by rfl⟩ : syracuseStep 3295399 = 4943099) B4943099
theorem B108325187 : Blo 1735068 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B6588809 : Blo 1735068 6588809 := bstep (se 2 (by rfl) ⟨2470803, by rfl⟩ : syracuseStep 6588809 = 4941607) B4941607
theorem B24398275 : Blo 1735068 24398275 := bstep (se 1 (by rfl) ⟨18298706, by rfl⟩ : syracuseStep 24398275 = 36597413) B36597413
theorem B84421277 : Blo 1735068 84421277 := bstep (se 3 (by rfl) ⟨15828989, by rfl⟩ : syracuseStep 84421277 = 31657979) B31657979
theorem B19779227 : Blo 1735068 19779227 := bstep (se 1 (by rfl) ⟨14834420, by rfl⟩ : syracuseStep 19779227 = 29668841) B29668841
theorem B2928703 : Blo 1735068 2928703 := bstep (se 1 (by rfl) ⟨2196527, by rfl⟩ : syracuseStep 2928703 = 4393055) B4393055
theorem B14831687 : Blo 1735068 14831687 := bstep (se 1 (by rfl) ⟨11123765, by rfl⟩ : syracuseStep 14831687 = 22247531) B22247531
theorem B8573377 : Blo 1735068 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B2929135 : Blo 1735068 2929135 := bstep (se 1 (by rfl) ⟨2196851, by rfl⟩ : syracuseStep 2929135 = 4393703) B4393703
theorem B3904091 : Blo 1735068 3904091 := bstep (se 1 (by rfl) ⟨2928068, by rfl⟩ : syracuseStep 3904091 = 5856137) B5856137
theorem B7918877 : Blo 1735068 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B192681503 : Blo 1735068 192681503 := bstep (se 1 (by rfl) ⟨144511127, by rfl⟩ : syracuseStep 192681503 = 289022255) B289022255
theorem B2602751 : Blo 1735068 2602751 := bstep (se 1 (by rfl) ⟨1952063, by rfl⟩ : syracuseStep 2602751 = 3904127) B3904127
theorem B3905279 : Blo 1735068 3905279 := bstep (se 1 (by rfl) ⟨2928959, by rfl⟩ : syracuseStep 3905279 = 5857919) B5857919
theorem B2930431 : Blo 1735068 2930431 := bstep (se 1 (by rfl) ⟨2197823, by rfl⟩ : syracuseStep 2930431 = 4395647) B4395647
theorem B6256415 : Blo 1735068 6256415 := bstep (se 1 (by rfl) ⟨4692311, by rfl⟩ : syracuseStep 6256415 = 9384623) B9384623
theorem B494098967 : Blo 1735068 494098967 := bstep (se 1 (by rfl) ⟨370574225, by rfl⟩ : syracuseStep 494098967 = 741148451) B741148451
theorem B6593183 : Blo 1735068 6593183 := bstep (se 1 (by rfl) ⟨4944887, by rfl⟩ : syracuseStep 6593183 = 9889775) B9889775
theorem B3906215 : Blo 1735068 3906215 := bstep (se 1 (by rfl) ⟨2929661, by rfl⟩ : syracuseStep 3906215 = 5859323) B5859323
theorem B1735999 : Blo 1735068 1735999 := bstep (se 1 (by rfl) ⟨1301999, by rfl⟩ : syracuseStep 1735999 = 2603999) B2603999
theorem B3128863 : Blo 1735068 3128863 := bstep (se 1 (by rfl) ⟨2346647, by rfl⟩ : syracuseStep 3128863 = 4693295) B4693295
theorem B1736431 : Blo 1735068 1736431 := bstep (se 1 (by rfl) ⟨1302323, by rfl⟩ : syracuseStep 1736431 = 2604647) B2604647
theorem B5562191 : Blo 1735068 5562191 := bstep (se 1 (by rfl) ⟨4171643, by rfl⟩ : syracuseStep 5562191 = 8343287) B8343287
theorem B13180805 : Blo 1735068 13180805 := bstep (se 4 (by rfl) ⟨1235700, by rfl⟩ : syracuseStep 13180805 = 2471401) B2471401
theorem B9887791 : Blo 1735068 9887791 := bstep (se 1 (by rfl) ⟨7415843, by rfl⟩ : syracuseStep 9887791 = 14831687) B14831687
theorem B32531033 : Blo 1735068 32531033 := bstep (se 2 (by rfl) ⟨12199137, by rfl⟩ : syracuseStep 32531033 = 24398275) B24398275
theorem B162497177 : Blo 1735068 162497177 := bstep (se 2 (by rfl) ⟨60936441, by rfl⟩ : syracuseStep 162497177 = 121872883) B121872883
theorem B4170943 : Blo 1735068 4170943 := bstep (se 1 (by rfl) ⟨3128207, by rfl⟩ : syracuseStep 4170943 = 6256415) B6256415
theorem B4392539 : Blo 1735068 4392539 := bstep (se 1 (by rfl) ⟨3294404, by rfl⟩ : syracuseStep 4392539 = 6588809) B6588809
theorem B56280851 : Blo 1735068 56280851 := bstep (se 1 (by rfl) ⟨42210638, by rfl⟩ : syracuseStep 56280851 = 84421277) B84421277
theorem B4171817 : Blo 1735068 4171817 := bstep (se 2 (by rfl) ⟨1564431, by rfl⟩ : syracuseStep 4171817 = 3128863) B3128863
theorem B25029395 : Blo 1735068 25029395 := bstep (se 1 (by rfl) ⟨18772046, by rfl⟩ : syracuseStep 25029395 = 37544093) B37544093
theorem B40086343 : Blo 1735068 40086343 := bstep (se 1 (by rfl) ⟨30064757, by rfl⟩ : syracuseStep 40086343 = 60129515) B60129515
theorem B4393865 : Blo 1735068 4393865 := bstep (se 2 (by rfl) ⟨1647699, by rfl⟩ : syracuseStep 4393865 = 3295399) B3295399
theorem B11431169 : Blo 1735068 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B5279251 : Blo 1735068 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B128454335 : Blo 1735068 128454335 := bstep (se 1 (by rfl) ⟨96340751, by rfl⟩ : syracuseStep 128454335 = 192681503) B192681503
theorem B13365071 : Blo 1735068 13365071 := bstep (se 1 (by rfl) ⟨10023803, by rfl⟩ : syracuseStep 13365071 = 20047607) B20047607
theorem B72216791 : Blo 1735068 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B4395455 : Blo 1735068 4395455 := bstep (se 1 (by rfl) ⟨3296591, by rfl⟩ : syracuseStep 4395455 = 6593183) B6593183
theorem B13186151 : Blo 1735068 13186151 := bstep (se 1 (by rfl) ⟨9889613, by rfl⟩ : syracuseStep 13186151 = 19779227) B19779227
theorem B3708127 : Blo 1735068 3708127 := bstep (se 1 (by rfl) ⟨2781095, by rfl⟩ : syracuseStep 3708127 = 5562191) B5562191
theorem B8787203 : Blo 1735068 8787203 := bstep (se 1 (by rfl) ⟨6590402, by rfl⟩ : syracuseStep 8787203 = 13180805) B13180805
theorem B3904937 : Blo 1735068 3904937 := bstep (se 2 (by rfl) ⟨1464351, by rfl⟩ : syracuseStep 3904937 = 2928703) B2928703
theorem B2602727 : Blo 1735068 2602727 := bstep (se 1 (by rfl) ⟨1952045, by rfl⟩ : syracuseStep 2602727 = 3904091) B3904091
theorem B8787851 : Blo 1735068 8787851 := bstep (se 1 (by rfl) ⟨6590888, by rfl⟩ : syracuseStep 8787851 = 13181777) B13181777
theorem B3905513 : Blo 1735068 3905513 := bstep (se 2 (by rfl) ⟨1464567, by rfl⟩ : syracuseStep 3905513 = 2929135) B2929135
theorem B3905531 : Blo 1735068 3905531 := bstep (se 1 (by rfl) ⟨2929148, by rfl⟩ : syracuseStep 3905531 = 5858297) B5858297
theorem B9886151 : Blo 1735068 9886151 := bstep (se 1 (by rfl) ⟨7414613, by rfl⟩ : syracuseStep 9886151 = 14829227) B14829227
theorem B1735167 : Blo 1735068 1735167 := bstep (se 1 (by rfl) ⟨1301375, by rfl⟩ : syracuseStep 1735167 = 2602751) B2602751
theorem B2603519 : Blo 1735068 2603519 := bstep (se 1 (by rfl) ⟨1952639, by rfl⟩ : syracuseStep 2603519 = 3905279) B3905279
theorem B329399311 : Blo 1735068 329399311 := bstep (se 1 (by rfl) ⟨247049483, by rfl⟩ : syracuseStep 329399311 = 494098967) B494098967
theorem B2604143 : Blo 1735068 2604143 := bstep (se 1 (by rfl) ⟨1953107, by rfl⟩ : syracuseStep 2604143 = 3906215) B3906215
theorem B3907241 : Blo 1735068 3907241 := bstep (se 2 (by rfl) ⟨1465215, by rfl⟩ : syracuseStep 3907241 = 2930431) B2930431
theorem B48144527 : Blo 1735068 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B108331451 : Blo 1735068 108331451 := bstep (se 1 (by rfl) ⟨81248588, by rfl⟩ : syracuseStep 108331451 = 162497177) B162497177
theorem B8790767 : Blo 1735068 8790767 := bstep (se 1 (by rfl) ⟨6593075, by rfl⟩ : syracuseStep 8790767 = 13186151) B13186151
theorem B5858135 : Blo 1735068 5858135 := bstep (se 1 (by rfl) ⟨4393601, by rfl⟩ : syracuseStep 5858135 = 8787203) B8787203
theorem B37520567 : Blo 1735068 37520567 := bstep (se 1 (by rfl) ⟨28140425, by rfl⟩ : syracuseStep 37520567 = 56280851) B56280851
theorem B5858567 : Blo 1735068 5858567 := bstep (se 1 (by rfl) ⟨4393925, by rfl⟩ : syracuseStep 5858567 = 8787851) B8787851
theorem B439199081 : Blo 1735068 439199081 := bstep (se 2 (by rfl) ⟨164699655, by rfl⟩ : syracuseStep 439199081 = 329399311) B329399311
theorem B7039001 : Blo 1735068 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B7620779 : Blo 1735068 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B13183721 : Blo 1735068 13183721 := bstep (se 2 (by rfl) ⟨4943895, by rfl⟩ : syracuseStep 13183721 = 9887791) B9887791
theorem B21687355 : Blo 1735068 21687355 := bstep (se 1 (by rfl) ⟨16265516, by rfl⟩ : syracuseStep 21687355 = 32531033) B32531033
theorem B2928359 : Blo 1735068 2928359 := bstep (se 1 (by rfl) ⟨2196269, by rfl⟩ : syracuseStep 2928359 = 4392539) B4392539
theorem B2781211 : Blo 1735068 2781211 := bstep (se 1 (by rfl) ⟨2085908, by rfl⟩ : syracuseStep 2781211 = 4171817) B4171817
theorem B4944169 : Blo 1735068 4944169 := bstep (se 2 (by rfl) ⟨1854063, by rfl⟩ : syracuseStep 4944169 = 3708127) B3708127
theorem B6590767 : Blo 1735068 6590767 := bstep (se 1 (by rfl) ⟨4943075, by rfl⟩ : syracuseStep 6590767 = 9886151) B9886151
theorem B2929243 : Blo 1735068 2929243 := bstep (se 1 (by rfl) ⟨2196932, by rfl⟩ : syracuseStep 2929243 = 4393865) B4393865
theorem B85636223 : Blo 1735068 85636223 := bstep (se 1 (by rfl) ⟨64227167, by rfl⟩ : syracuseStep 85636223 = 128454335) B128454335
theorem B8910047 : Blo 1735068 8910047 := bstep (se 1 (by rfl) ⟨6682535, by rfl⟩ : syracuseStep 8910047 = 13365071) B13365071
theorem B2930303 : Blo 1735068 2930303 := bstep (se 1 (by rfl) ⟨2197727, by rfl⟩ : syracuseStep 2930303 = 4395455) B4395455
theorem B2603291 : Blo 1735068 2603291 := bstep (se 1 (by rfl) ⟨1952468, by rfl⟩ : syracuseStep 2603291 = 3904937) B3904937
theorem B1735151 : Blo 1735068 1735151 := bstep (se 1 (by rfl) ⟨1301363, by rfl⟩ : syracuseStep 1735151 = 2602727) B2602727
theorem B2603675 : Blo 1735068 2603675 := bstep (se 1 (by rfl) ⟨1952756, by rfl⟩ : syracuseStep 2603675 = 3905513) B3905513
theorem B2603687 : Blo 1735068 2603687 := bstep (se 1 (by rfl) ⟨1952765, by rfl⟩ : syracuseStep 2603687 = 3905531) B3905531
theorem B5561257 : Blo 1735068 5561257 := bstep (se 2 (by rfl) ⟨2085471, by rfl⟩ : syracuseStep 5561257 = 4170943) B4170943
theorem B1735679 : Blo 1735068 1735679 := bstep (se 1 (by rfl) ⟨1301759, by rfl⟩ : syracuseStep 1735679 = 2603519) B2603519
theorem B213793829 : Blo 1735068 213793829 := bstep (se 4 (by rfl) ⟨20043171, by rfl⟩ : syracuseStep 213793829 = 40086343) B40086343
theorem B16686263 : Blo 1735068 16686263 := bstep (se 1 (by rfl) ⟨12514697, by rfl⟩ : syracuseStep 16686263 = 25029395) B25029395
theorem B1736095 : Blo 1735068 1736095 := bstep (se 1 (by rfl) ⟨1302071, by rfl⟩ : syracuseStep 1736095 = 2604143) B2604143
theorem B2604827 : Blo 1735068 2604827 := bstep (se 1 (by rfl) ⟨1953620, by rfl⟩ : syracuseStep 2604827 = 3907241) B3907241
theorem B32096351 : Blo 1735068 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B72220967 : Blo 1735068 72220967 := bstep (se 1 (by rfl) ⟨54165725, by rfl⟩ : syracuseStep 72220967 = 108331451) B108331451
theorem B57090815 : Blo 1735068 57090815 := bstep (se 1 (by rfl) ⟨42818111, by rfl⟩ : syracuseStep 57090815 = 85636223) B85636223
theorem B292799387 : Blo 1735068 292799387 := bstep (se 1 (by rfl) ⟨219599540, by rfl⟩ : syracuseStep 292799387 = 439199081) B439199081
theorem B7415009 : Blo 1735068 7415009 := bstep (se 2 (by rfl) ⟨2780628, by rfl⟩ : syracuseStep 7415009 = 5561257) B5561257
theorem B5080519 : Blo 1735068 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B1952239 : Blo 1735068 1952239 := bstep (se 1 (by rfl) ⟨1464179, by rfl⟩ : syracuseStep 1952239 = 2928359) B2928359
theorem B5860511 : Blo 1735068 5860511 := bstep (se 1 (by rfl) ⟨4395383, by rfl⟩ : syracuseStep 5860511 = 8790767) B8790767
theorem B23760125 : Blo 1735068 23760125 := bstep (se 3 (by rfl) ⟨4455023, by rfl⟩ : syracuseStep 23760125 = 8910047) B8910047
theorem B25013711 : Blo 1735068 25013711 := bstep (se 1 (by rfl) ⟨18760283, by rfl⟩ : syracuseStep 25013711 = 37520567) B37520567
theorem B1953535 : Blo 1735068 1953535 := bstep (se 1 (by rfl) ⟨1465151, by rfl⟩ : syracuseStep 1953535 = 2930303) B2930303
theorem B142529219 : Blo 1735068 142529219 := bstep (se 1 (by rfl) ⟨106896914, by rfl⟩ : syracuseStep 142529219 = 213793829) B213793829
theorem B3708281 : Blo 1735068 3708281 := bstep (se 2 (by rfl) ⟨1390605, by rfl⟩ : syracuseStep 3708281 = 2781211) B2781211
theorem B6592225 : Blo 1735068 6592225 := bstep (se 2 (by rfl) ⟨2472084, by rfl⟩ : syracuseStep 6592225 = 4944169) B4944169
theorem B8787689 : Blo 1735068 8787689 := bstep (se 2 (by rfl) ⟨3295383, by rfl⟩ : syracuseStep 8787689 = 6590767) B6590767
theorem B44496701 : Blo 1735068 44496701 := bstep (se 3 (by rfl) ⟨8343131, by rfl⟩ : syracuseStep 44496701 = 16686263) B16686263
theorem B3905423 : Blo 1735068 3905423 := bstep (se 1 (by rfl) ⟨2929067, by rfl⟩ : syracuseStep 3905423 = 5858135) B5858135
theorem B3905657 : Blo 1735068 3905657 := bstep (se 2 (by rfl) ⟨1464621, by rfl⟩ : syracuseStep 3905657 = 2929243) B2929243
theorem B3905711 : Blo 1735068 3905711 := bstep (se 1 (by rfl) ⟨2929283, by rfl⟩ : syracuseStep 3905711 = 5858567) B5858567
theorem B4692667 : Blo 1735068 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B28916473 : Blo 1735068 28916473 := bstep (se 2 (by rfl) ⟨10843677, by rfl⟩ : syracuseStep 28916473 = 21687355) B21687355
theorem B1735527 : Blo 1735068 1735527 := bstep (se 1 (by rfl) ⟨1301645, by rfl⟩ : syracuseStep 1735527 = 2603291) B2603291
theorem B1735783 : Blo 1735068 1735783 := bstep (se 1 (by rfl) ⟨1301837, by rfl⟩ : syracuseStep 1735783 = 2603675) B2603675
theorem B1735791 : Blo 1735068 1735791 := bstep (se 1 (by rfl) ⟨1301843, by rfl⟩ : syracuseStep 1735791 = 2603687) B2603687
theorem B8789147 : Blo 1735068 8789147 := bstep (se 1 (by rfl) ⟨6591860, by rfl⟩ : syracuseStep 8789147 = 13183721) B13183721
theorem B1736551 : Blo 1735068 1736551 := bstep (se 1 (by rfl) ⟨1302413, by rfl⟩ : syracuseStep 1736551 = 2604827) B2604827
theorem B21397567 : Blo 1735068 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B95019479 : Blo 1735068 95019479 := bstep (se 1 (by rfl) ⟨71264609, by rfl⟩ : syracuseStep 95019479 = 142529219) B142529219
theorem B38060543 : Blo 1735068 38060543 := bstep (se 1 (by rfl) ⟨28545407, by rfl⟩ : syracuseStep 38060543 = 57090815) B57090815
theorem B9888749 : Blo 1735068 9888749 := bstep (se 3 (by rfl) ⟨1854140, by rfl⟩ : syracuseStep 9888749 = 3708281) B3708281
theorem B5858459 : Blo 1735068 5858459 := bstep (se 1 (by rfl) ⟨4393844, by rfl⟩ : syracuseStep 5858459 = 8787689) B8787689
theorem B29664467 : Blo 1735068 29664467 := bstep (se 1 (by rfl) ⟨22248350, by rfl⟩ : syracuseStep 29664467 = 44496701) B44496701
theorem B5859431 : Blo 1735068 5859431 := bstep (se 1 (by rfl) ⟨4394573, by rfl⟩ : syracuseStep 5859431 = 8789147) B8789147
theorem B780798365 : Blo 1735068 780798365 := bstep (se 3 (by rfl) ⟨146399693, by rfl⟩ : syracuseStep 780798365 = 292799387) B292799387
theorem B48147311 : Blo 1735068 48147311 := bstep (se 1 (by rfl) ⟨36110483, by rfl⟩ : syracuseStep 48147311 = 72220967) B72220967
theorem B4943339 : Blo 1735068 4943339 := bstep (se 1 (by rfl) ⟨3707504, by rfl⟩ : syracuseStep 4943339 = 7415009) B7415009
theorem B38555297 : Blo 1735068 38555297 := bstep (se 2 (by rfl) ⟨14458236, by rfl⟩ : syracuseStep 38555297 = 28916473) B28916473
theorem B15840083 : Blo 1735068 15840083 := bstep (se 1 (by rfl) ⟨11880062, by rfl⟩ : syracuseStep 15840083 = 23760125) B23760125
theorem B16675807 : Blo 1735068 16675807 := bstep (se 1 (by rfl) ⟨12506855, by rfl⟩ : syracuseStep 16675807 = 25013711) B25013711
theorem B2602985 : Blo 1735068 2602985 := bstep (se 2 (by rfl) ⟨976119, by rfl⟩ : syracuseStep 2602985 = 1952239) B1952239
theorem B6256889 : Blo 1735068 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B2603615 : Blo 1735068 2603615 := bstep (se 1 (by rfl) ⟨1952711, by rfl⟩ : syracuseStep 2603615 = 3905423) B3905423
theorem B2603771 : Blo 1735068 2603771 := bstep (se 1 (by rfl) ⟨1952828, by rfl⟩ : syracuseStep 2603771 = 3905657) B3905657
theorem B2603807 : Blo 1735068 2603807 := bstep (se 1 (by rfl) ⟨1952855, by rfl⟩ : syracuseStep 2603807 = 3905711) B3905711
theorem B6774025 : Blo 1735068 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B3907007 : Blo 1735068 3907007 := bstep (se 1 (by rfl) ⟨2930255, by rfl⟩ : syracuseStep 3907007 = 5860511) B5860511
theorem B8789633 : Blo 1735068 8789633 := bstep (se 2 (by rfl) ⟨3296112, by rfl⟩ : syracuseStep 8789633 = 6592225) B6592225
theorem B2604713 : Blo 1735068 2604713 := bstep (se 2 (by rfl) ⟨976767, by rfl⟩ : syracuseStep 2604713 = 1953535) B1953535
theorem B10560055 : Blo 1735068 10560055 := bstep (se 1 (by rfl) ⟨7920041, by rfl⟩ : syracuseStep 10560055 = 15840083) B15840083
theorem B19776311 : Blo 1735068 19776311 := bstep (se 1 (by rfl) ⟨14832233, by rfl⟩ : syracuseStep 19776311 = 29664467) B29664467
theorem B22234409 : Blo 1735068 22234409 := bstep (se 2 (by rfl) ⟨8337903, by rfl⟩ : syracuseStep 22234409 = 16675807) B16675807
theorem B4171259 : Blo 1735068 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B32098207 : Blo 1735068 32098207 := bstep (se 1 (by rfl) ⟨24073655, by rfl⟩ : syracuseStep 32098207 = 48147311) B48147311
theorem B3295559 : Blo 1735068 3295559 := bstep (se 1 (by rfl) ⟨2471669, by rfl⟩ : syracuseStep 3295559 = 4943339) B4943339
theorem B5859755 : Blo 1735068 5859755 := bstep (se 1 (by rfl) ⟨4394816, by rfl⟩ : syracuseStep 5859755 = 8789633) B8789633
theorem B25373695 : Blo 1735068 25373695 := bstep (se 1 (by rfl) ⟨19030271, by rfl⟩ : syracuseStep 25373695 = 38060543) B38060543
theorem B520532243 : Blo 1735068 520532243 := bstep (se 1 (by rfl) ⟨390399182, by rfl⟩ : syracuseStep 520532243 = 780798365) B780798365
theorem B9032033 : Blo 1735068 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B25703531 : Blo 1735068 25703531 := bstep (se 1 (by rfl) ⟨19277648, by rfl⟩ : syracuseStep 25703531 = 38555297) B38555297
theorem B28530089 : Blo 1735068 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B63346319 : Blo 1735068 63346319 := bstep (se 1 (by rfl) ⟨47509739, by rfl⟩ : syracuseStep 63346319 = 95019479) B95019479
theorem B6592499 : Blo 1735068 6592499 := bstep (se 1 (by rfl) ⟨4944374, by rfl⟩ : syracuseStep 6592499 = 9888749) B9888749
theorem B3905639 : Blo 1735068 3905639 := bstep (se 1 (by rfl) ⟨2929229, by rfl⟩ : syracuseStep 3905639 = 5858459) B5858459
theorem B1735323 : Blo 1735068 1735323 := bstep (se 1 (by rfl) ⟨1301492, by rfl⟩ : syracuseStep 1735323 = 2602985) B2602985
theorem B3906287 : Blo 1735068 3906287 := bstep (se 1 (by rfl) ⟨2929715, by rfl⟩ : syracuseStep 3906287 = 5859431) B5859431
theorem B1735743 : Blo 1735068 1735743 := bstep (se 1 (by rfl) ⟨1301807, by rfl⟩ : syracuseStep 1735743 = 2603615) B2603615
theorem B1735847 : Blo 1735068 1735847 := bstep (se 1 (by rfl) ⟨1301885, by rfl⟩ : syracuseStep 1735847 = 2603771) B2603771
theorem B1735871 : Blo 1735068 1735871 := bstep (se 1 (by rfl) ⟨1301903, by rfl⟩ : syracuseStep 1735871 = 2603807) B2603807
theorem B2604671 : Blo 1735068 2604671 := bstep (se 1 (by rfl) ⟨1953503, by rfl⟩ : syracuseStep 2604671 = 3907007) B3907007
theorem B1736475 : Blo 1735068 1736475 := bstep (se 1 (by rfl) ⟨1302356, by rfl⟩ : syracuseStep 1736475 = 2604713) B2604713
theorem B347021495 : Blo 1735068 347021495 := bstep (se 1 (by rfl) ⟨260266121, by rfl⟩ : syracuseStep 347021495 = 520532243) B520532243
theorem B24085421 : Blo 1735068 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B42230879 : Blo 1735068 42230879 := bstep (se 1 (by rfl) ⟨31673159, by rfl⟩ : syracuseStep 42230879 = 63346319) B63346319
theorem B2197039 : Blo 1735068 2197039 := bstep (se 1 (by rfl) ⟨1647779, by rfl⟩ : syracuseStep 2197039 = 3295559) B3295559
theorem B42797609 : Blo 1735068 42797609 := bstep (se 2 (by rfl) ⟨16049103, by rfl⟩ : syracuseStep 42797609 = 32098207) B32098207
theorem B13184207 : Blo 1735068 13184207 := bstep (se 1 (by rfl) ⟨9888155, by rfl⟩ : syracuseStep 13184207 = 19776311) B19776311
theorem B14822939 : Blo 1735068 14822939 := bstep (se 1 (by rfl) ⟨11117204, by rfl⟩ : syracuseStep 14822939 = 22234409) B22234409
theorem B2780839 : Blo 1735068 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B4394999 : Blo 1735068 4394999 := bstep (se 1 (by rfl) ⟨3296249, by rfl⟩ : syracuseStep 4394999 = 6592499) B6592499
theorem B17135687 : Blo 1735068 17135687 := bstep (se 1 (by rfl) ⟨12851765, by rfl⟩ : syracuseStep 17135687 = 25703531) B25703531
theorem B14080073 : Blo 1735068 14080073 := bstep (se 2 (by rfl) ⟨5280027, by rfl⟩ : syracuseStep 14080073 = 10560055) B10560055
theorem B19020059 : Blo 1735068 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B33831593 : Blo 1735068 33831593 := bstep (se 2 (by rfl) ⟨12686847, by rfl⟩ : syracuseStep 33831593 = 25373695) B25373695
theorem B2603759 : Blo 1735068 2603759 := bstep (se 1 (by rfl) ⟨1952819, by rfl⟩ : syracuseStep 2603759 = 3905639) B3905639
theorem B3906503 : Blo 1735068 3906503 := bstep (se 1 (by rfl) ⟨2929877, by rfl⟩ : syracuseStep 3906503 = 5859755) B5859755
theorem B2604191 : Blo 1735068 2604191 := bstep (se 1 (by rfl) ⟨1953143, by rfl⟩ : syracuseStep 2604191 = 3906287) B3906287
theorem B1736447 : Blo 1735068 1736447 := bstep (se 1 (by rfl) ⟨1302335, by rfl⟩ : syracuseStep 1736447 = 2604671) B2604671
theorem B16056947 : Blo 1735068 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B22554395 : Blo 1735068 22554395 := bstep (se 1 (by rfl) ⟨16915796, by rfl⟩ : syracuseStep 22554395 = 33831593) B33831593
theorem B9881959 : Blo 1735068 9881959 := bstep (se 1 (by rfl) ⟨7411469, by rfl⟩ : syracuseStep 9881959 = 14822939) B14822939
theorem B37546861 : Blo 1735068 37546861 := bstep (se 3 (by rfl) ⟨7040036, by rfl⟩ : syracuseStep 37546861 = 14080073) B14080073
theorem B11423791 : Blo 1735068 11423791 := bstep (se 1 (by rfl) ⟨8567843, by rfl⟩ : syracuseStep 11423791 = 17135687) B17135687
theorem B2929385 : Blo 1735068 2929385 := bstep (se 2 (by rfl) ⟨1098519, by rfl⟩ : syracuseStep 2929385 = 2197039) B2197039
theorem B3707785 : Blo 1735068 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B2929999 : Blo 1735068 2929999 := bstep (se 1 (by rfl) ⟨2197499, by rfl⟩ : syracuseStep 2929999 = 4394999) B4394999
theorem B231347663 : Blo 1735068 231347663 := bstep (se 1 (by rfl) ⟨173510747, by rfl⟩ : syracuseStep 231347663 = 347021495) B347021495
theorem B28153919 : Blo 1735068 28153919 := bstep (se 1 (by rfl) ⟨21115439, by rfl⟩ : syracuseStep 28153919 = 42230879) B42230879
theorem B12680039 : Blo 1735068 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B28531739 : Blo 1735068 28531739 := bstep (se 1 (by rfl) ⟨21398804, by rfl⟩ : syracuseStep 28531739 = 42797609) B42797609
theorem B1735839 : Blo 1735068 1735839 := bstep (se 1 (by rfl) ⟨1301879, by rfl⟩ : syracuseStep 1735839 = 2603759) B2603759
theorem B2604335 : Blo 1735068 2604335 := bstep (se 1 (by rfl) ⟨1953251, by rfl⟩ : syracuseStep 2604335 = 3906503) B3906503
theorem B1736127 : Blo 1735068 1736127 := bstep (se 1 (by rfl) ⟨1302095, by rfl⟩ : syracuseStep 1736127 = 2604191) B2604191
theorem B8789471 : Blo 1735068 8789471 := bstep (se 1 (by rfl) ⟨6592103, by rfl⟩ : syracuseStep 8789471 = 13184207) B13184207
theorem B154231775 : Blo 1735068 154231775 := bstep (se 1 (by rfl) ⟨115673831, by rfl⟩ : syracuseStep 154231775 = 231347663) B231347663
theorem B50062481 : Blo 1735068 50062481 := bstep (se 2 (by rfl) ⟨18773430, by rfl⟩ : syracuseStep 50062481 = 37546861) B37546861
theorem B18769279 : Blo 1735068 18769279 := bstep (se 1 (by rfl) ⟨14076959, by rfl⟩ : syracuseStep 18769279 = 28153919) B28153919
theorem B5859647 : Blo 1735068 5859647 := bstep (se 1 (by rfl) ⟨4394735, by rfl⟩ : syracuseStep 5859647 = 8789471) B8789471
theorem B15231721 : Blo 1735068 15231721 := bstep (se 2 (by rfl) ⟨5711895, by rfl⟩ : syracuseStep 15231721 = 11423791) B11423791
theorem B13175945 : Blo 1735068 13175945 := bstep (se 2 (by rfl) ⟨4940979, by rfl⟩ : syracuseStep 13175945 = 9881959) B9881959
theorem B1952923 : Blo 1735068 1952923 := bstep (se 1 (by rfl) ⟨1464692, by rfl⟩ : syracuseStep 1952923 = 2929385) B2929385
theorem B15036263 : Blo 1735068 15036263 := bstep (se 1 (by rfl) ⟨11277197, by rfl⟩ : syracuseStep 15036263 = 22554395) B22554395
theorem B10704631 : Blo 1735068 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B3906665 : Blo 1735068 3906665 := bstep (se 2 (by rfl) ⟨1464999, by rfl⟩ : syracuseStep 3906665 = 2929999) B2929999
theorem B8453359 : Blo 1735068 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B19021159 : Blo 1735068 19021159 := bstep (se 1 (by rfl) ⟨14265869, by rfl⟩ : syracuseStep 19021159 = 28531739) B28531739
theorem B19774853 : Blo 1735068 19774853 := bstep (se 4 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 19774853 = 3707785) B3707785
theorem B1736223 : Blo 1735068 1736223 := bstep (se 1 (by rfl) ⟨1302167, by rfl⟩ : syracuseStep 1736223 = 2604335) B2604335
theorem B33374987 : Blo 1735068 33374987 := bstep (se 1 (by rfl) ⟨25031240, by rfl⟩ : syracuseStep 33374987 = 50062481) B50062481
theorem B20308961 : Blo 1735068 20308961 := bstep (se 2 (by rfl) ⟨7615860, by rfl⟩ : syracuseStep 20308961 = 15231721) B15231721
theorem B8783963 : Blo 1735068 8783963 := bstep (se 1 (by rfl) ⟨6587972, by rfl⟩ : syracuseStep 8783963 = 13175945) B13175945
theorem B13183235 : Blo 1735068 13183235 := bstep (se 1 (by rfl) ⟨9887426, by rfl⟩ : syracuseStep 13183235 = 19774853) B19774853
theorem B14272841 : Blo 1735068 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B102821183 : Blo 1735068 102821183 := bstep (se 1 (by rfl) ⟨77115887, by rfl⟩ : syracuseStep 102821183 = 154231775) B154231775
theorem B101446181 : Blo 1735068 101446181 := bstep (se 4 (by rfl) ⟨9510579, by rfl⟩ : syracuseStep 101446181 = 19021159) B19021159
theorem B10024175 : Blo 1735068 10024175 := bstep (se 1 (by rfl) ⟨7518131, by rfl⟩ : syracuseStep 10024175 = 15036263) B15036263
theorem B2603897 : Blo 1735068 2603897 := bstep (se 2 (by rfl) ⟨976461, by rfl⟩ : syracuseStep 2603897 = 1952923) B1952923
theorem B3906431 : Blo 1735068 3906431 := bstep (se 1 (by rfl) ⟨2929823, by rfl⟩ : syracuseStep 3906431 = 5859647) B5859647
theorem B11271145 : Blo 1735068 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B25025705 : Blo 1735068 25025705 := bstep (se 2 (by rfl) ⟨9384639, by rfl⟩ : syracuseStep 25025705 = 18769279) B18769279
theorem B2604443 : Blo 1735068 2604443 := bstep (se 1 (by rfl) ⟨1953332, by rfl⟩ : syracuseStep 2604443 = 3906665) B3906665
theorem B22249991 : Blo 1735068 22249991 := bstep (se 1 (by rfl) ⟨16687493, by rfl⟩ : syracuseStep 22249991 = 33374987) B33374987
theorem B26731133 : Blo 1735068 26731133 := bstep (se 3 (by rfl) ⟨5012087, by rfl⟩ : syracuseStep 26731133 = 10024175) B10024175
theorem B15028193 : Blo 1735068 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B9515227 : Blo 1735068 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B16683803 : Blo 1735068 16683803 := bstep (se 1 (by rfl) ⟨12512852, by rfl⟩ : syracuseStep 16683803 = 25025705) B25025705
theorem B68547455 : Blo 1735068 68547455 := bstep (se 1 (by rfl) ⟨51410591, by rfl⟩ : syracuseStep 68547455 = 102821183) B102821183
theorem B67630787 : Blo 1735068 67630787 := bstep (se 1 (by rfl) ⟨50723090, by rfl⟩ : syracuseStep 67630787 = 101446181) B101446181
theorem B13539307 : Blo 1735068 13539307 := bstep (se 1 (by rfl) ⟨10154480, by rfl⟩ : syracuseStep 13539307 = 20308961) B20308961
theorem B5855975 : Blo 1735068 5855975 := bstep (se 1 (by rfl) ⟨4391981, by rfl⟩ : syracuseStep 5855975 = 8783963) B8783963
theorem B8788823 : Blo 1735068 8788823 := bstep (se 1 (by rfl) ⟨6591617, by rfl⟩ : syracuseStep 8788823 = 13183235) B13183235
theorem B1735931 : Blo 1735068 1735931 := bstep (se 1 (by rfl) ⟨1301948, by rfl⟩ : syracuseStep 1735931 = 2603897) B2603897
theorem B2604287 : Blo 1735068 2604287 := bstep (se 1 (by rfl) ⟨1953215, by rfl⟩ : syracuseStep 2604287 = 3906431) B3906431
theorem B1736295 : Blo 1735068 1736295 := bstep (se 1 (by rfl) ⟨1302221, by rfl⟩ : syracuseStep 1736295 = 2604443) B2604443
theorem B5859215 : Blo 1735068 5859215 := bstep (se 1 (by rfl) ⟨4394411, by rfl⟩ : syracuseStep 5859215 = 8788823) B8788823
theorem B17820755 : Blo 1735068 17820755 := bstep (se 1 (by rfl) ⟨13365566, by rfl⟩ : syracuseStep 17820755 = 26731133) B26731133
theorem B45698303 : Blo 1735068 45698303 := bstep (se 1 (by rfl) ⟨34273727, by rfl⟩ : syracuseStep 45698303 = 68547455) B68547455
theorem B3903983 : Blo 1735068 3903983 := bstep (se 1 (by rfl) ⟨2927987, by rfl⟩ : syracuseStep 3903983 = 5855975) B5855975
theorem B18052409 : Blo 1735068 18052409 := bstep (se 2 (by rfl) ⟨6769653, by rfl⟩ : syracuseStep 18052409 = 13539307) B13539307
theorem B12686969 : Blo 1735068 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B14833327 : Blo 1735068 14833327 := bstep (se 1 (by rfl) ⟨11124995, by rfl⟩ : syracuseStep 14833327 = 22249991) B22249991
theorem B11122535 : Blo 1735068 11122535 := bstep (se 1 (by rfl) ⟨8341901, by rfl⟩ : syracuseStep 11122535 = 16683803) B16683803
theorem B45087191 : Blo 1735068 45087191 := bstep (se 1 (by rfl) ⟨33815393, by rfl⟩ : syracuseStep 45087191 = 67630787) B67630787
theorem B1736191 : Blo 1735068 1736191 := bstep (se 1 (by rfl) ⟨1302143, by rfl⟩ : syracuseStep 1736191 = 2604287) B2604287
theorem B40075181 : Blo 1735068 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B12034939 : Blo 1735068 12034939 := bstep (se 1 (by rfl) ⟨9026204, by rfl⟩ : syracuseStep 12034939 = 18052409) B18052409
theorem B30058127 : Blo 1735068 30058127 := bstep (se 1 (by rfl) ⟨22543595, by rfl⟩ : syracuseStep 30058127 = 45087191) B45087191
theorem B11880503 : Blo 1735068 11880503 := bstep (se 1 (by rfl) ⟨8910377, by rfl⟩ : syracuseStep 11880503 = 17820755) B17820755
theorem B19777769 : Blo 1735068 19777769 := bstep (se 2 (by rfl) ⟨7416663, by rfl⟩ : syracuseStep 19777769 = 14833327) B14833327
theorem B26716787 : Blo 1735068 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B8457979 : Blo 1735068 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B29660093 : Blo 1735068 29660093 := bstep (se 3 (by rfl) ⟨5561267, by rfl⟩ : syracuseStep 29660093 = 11122535) B11122535
theorem B2602655 : Blo 1735068 2602655 := bstep (se 1 (by rfl) ⟨1951991, by rfl⟩ : syracuseStep 2602655 = 3903983) B3903983
theorem B3906143 : Blo 1735068 3906143 := bstep (se 1 (by rfl) ⟨2929607, by rfl⟩ : syracuseStep 3906143 = 5859215) B5859215
theorem B30465535 : Blo 1735068 30465535 := bstep (se 1 (by rfl) ⟨22849151, by rfl⟩ : syracuseStep 30465535 = 45698303) B45698303
theorem B20038751 : Blo 1735068 20038751 := bstep (se 1 (by rfl) ⟨15029063, by rfl⟩ : syracuseStep 20038751 = 30058127) B30058127
theorem B17811191 : Blo 1735068 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B13185179 : Blo 1735068 13185179 := bstep (se 1 (by rfl) ⟨9888884, by rfl⟩ : syracuseStep 13185179 = 19777769) B19777769
theorem B40620713 : Blo 1735068 40620713 := bstep (se 2 (by rfl) ⟨15232767, by rfl⟩ : syracuseStep 40620713 = 30465535) B30465535
theorem B11277305 : Blo 1735068 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B19773395 : Blo 1735068 19773395 := bstep (se 1 (by rfl) ⟨14830046, by rfl⟩ : syracuseStep 19773395 = 29660093) B29660093
theorem B1735103 : Blo 1735068 1735103 := bstep (se 1 (by rfl) ⟨1301327, by rfl⟩ : syracuseStep 1735103 = 2602655) B2602655
theorem B16046585 : Blo 1735068 16046585 := bstep (se 2 (by rfl) ⟨6017469, by rfl⟩ : syracuseStep 16046585 = 12034939) B12034939
theorem B7920335 : Blo 1735068 7920335 := bstep (se 1 (by rfl) ⟨5940251, by rfl⟩ : syracuseStep 7920335 = 11880503) B11880503
theorem B2604095 : Blo 1735068 2604095 := bstep (se 1 (by rfl) ⟨1953071, by rfl⟩ : syracuseStep 2604095 = 3906143) B3906143
theorem B8790119 : Blo 1735068 8790119 := bstep (se 1 (by rfl) ⟨6592589, by rfl⟩ : syracuseStep 8790119 = 13185179) B13185179
theorem B13182263 : Blo 1735068 13182263 := bstep (se 1 (by rfl) ⟨9886697, by rfl⟩ : syracuseStep 13182263 = 19773395) B19773395
theorem B11874127 : Blo 1735068 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B433287605 : Blo 1735068 433287605 := bstep (se 5 (by rfl) ⟨20310356, by rfl⟩ : syracuseStep 433287605 = 40620713) B40620713
theorem B5280223 : Blo 1735068 5280223 := bstep (se 1 (by rfl) ⟨3960167, by rfl⟩ : syracuseStep 5280223 = 7920335) B7920335
theorem B7518203 : Blo 1735068 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B13359167 : Blo 1735068 13359167 := bstep (se 1 (by rfl) ⟨10019375, by rfl⟩ : syracuseStep 13359167 = 20038751) B20038751
theorem B10697723 : Blo 1735068 10697723 := bstep (se 1 (by rfl) ⟨8023292, by rfl⟩ : syracuseStep 10697723 = 16046585) B16046585
theorem B1736063 : Blo 1735068 1736063 := bstep (se 1 (by rfl) ⟨1302047, by rfl⟩ : syracuseStep 1736063 = 2604095) B2604095
theorem B288858403 : Blo 1735068 288858403 := bstep (se 1 (by rfl) ⟨216643802, by rfl⟩ : syracuseStep 288858403 = 433287605) B433287605
theorem B8906111 : Blo 1735068 8906111 := bstep (se 1 (by rfl) ⟨6679583, by rfl⟩ : syracuseStep 8906111 = 13359167) B13359167
theorem B5860079 : Blo 1735068 5860079 := bstep (se 1 (by rfl) ⟨4395059, by rfl⟩ : syracuseStep 5860079 = 8790119) B8790119
theorem B7040297 : Blo 1735068 7040297 := bstep (se 2 (by rfl) ⟨2640111, by rfl⟩ : syracuseStep 7040297 = 5280223) B5280223
theorem B7131815 : Blo 1735068 7131815 := bstep (se 1 (by rfl) ⟨5348861, by rfl⟩ : syracuseStep 7131815 = 10697723) B10697723
theorem B15832169 : Blo 1735068 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B8788175 : Blo 1735068 8788175 := bstep (se 1 (by rfl) ⟨6591131, by rfl⟩ : syracuseStep 8788175 = 13182263) B13182263
theorem B5012135 : Blo 1735068 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B5858783 : Blo 1735068 5858783 := bstep (se 1 (by rfl) ⟨4394087, by rfl⟩ : syracuseStep 5858783 = 8788175) B8788175
theorem B4754543 : Blo 1735068 4754543 := bstep (se 1 (by rfl) ⟨3565907, by rfl⟩ : syracuseStep 4754543 = 7131815) B7131815
theorem B10554779 : Blo 1735068 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B18774125 : Blo 1735068 18774125 := bstep (se 3 (by rfl) ⟨3520148, by rfl⟩ : syracuseStep 18774125 = 7040297) B7040297
theorem B5937407 : Blo 1735068 5937407 := bstep (se 1 (by rfl) ⟨4453055, by rfl⟩ : syracuseStep 5937407 = 8906111) B8906111
theorem B1540578149 : Blo 1735068 1540578149 := bstep (se 4 (by rfl) ⟨144429201, by rfl⟩ : syracuseStep 1540578149 = 288858403) B288858403
theorem B3341423 : Blo 1735068 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B3906719 : Blo 1735068 3906719 := bstep (se 1 (by rfl) ⟨2930039, by rfl⟩ : syracuseStep 3906719 = 5860079) B5860079
theorem B3958271 : Blo 1735068 3958271 := bstep (se 1 (by rfl) ⟨2968703, by rfl⟩ : syracuseStep 3958271 = 5937407) B5937407
theorem B1027052099 : Blo 1735068 1027052099 := bstep (se 1 (by rfl) ⟨770289074, by rfl⟩ : syracuseStep 1027052099 = 1540578149) B1540578149
theorem B12678781 : Blo 1735068 12678781 := bstep (se 3 (by rfl) ⟨2377271, by rfl⟩ : syracuseStep 12678781 = 4754543) B4754543
theorem B8910461 : Blo 1735068 8910461 := bstep (se 3 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 8910461 = 3341423) B3341423
theorem B3905855 : Blo 1735068 3905855 := bstep (se 1 (by rfl) ⟨2929391, by rfl⟩ : syracuseStep 3905855 = 5858783) B5858783
theorem B12516083 : Blo 1735068 12516083 := bstep (se 1 (by rfl) ⟨9387062, by rfl⟩ : syracuseStep 12516083 = 18774125) B18774125
theorem B2604479 : Blo 1735068 2604479 := bstep (se 1 (by rfl) ⟨1953359, by rfl⟩ : syracuseStep 2604479 = 3906719) B3906719
theorem B7036519 : Blo 1735068 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B2638847 : Blo 1735068 2638847 := bstep (se 1 (by rfl) ⟨1979135, by rfl⟩ : syracuseStep 2638847 = 3958271) B3958271
theorem B5940307 : Blo 1735068 5940307 := bstep (se 1 (by rfl) ⟨4455230, by rfl⟩ : syracuseStep 5940307 = 8910461) B8910461
theorem B9382025 : Blo 1735068 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B8344055 : Blo 1735068 8344055 := bstep (se 1 (by rfl) ⟨6258041, by rfl⟩ : syracuseStep 8344055 = 12516083) B12516083
theorem B16905041 : Blo 1735068 16905041 := bstep (se 2 (by rfl) ⟨6339390, by rfl⟩ : syracuseStep 16905041 = 12678781) B12678781
theorem B684701399 : Blo 1735068 684701399 := bstep (se 1 (by rfl) ⟨513526049, by rfl⟩ : syracuseStep 684701399 = 1027052099) B1027052099
theorem B2603903 : Blo 1735068 2603903 := bstep (se 1 (by rfl) ⟨1952927, by rfl⟩ : syracuseStep 2603903 = 3905855) B3905855
theorem B1736319 : Blo 1735068 1736319 := bstep (se 1 (by rfl) ⟨1302239, by rfl⟩ : syracuseStep 1736319 = 2604479) B2604479
theorem B5562703 : Blo 1735068 5562703 := bstep (se 1 (by rfl) ⟨4172027, by rfl⟩ : syracuseStep 5562703 = 8344055) B8344055
theorem B25018733 : Blo 1735068 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B456467599 : Blo 1735068 456467599 := bstep (se 1 (by rfl) ⟨342350699, by rfl⟩ : syracuseStep 456467599 = 684701399) B684701399
theorem B11270027 : Blo 1735068 11270027 := bstep (se 1 (by rfl) ⟨8452520, by rfl⟩ : syracuseStep 11270027 = 16905041) B16905041
theorem B1759231 : Blo 1735068 1759231 := bstep (se 1 (by rfl) ⟨1319423, by rfl⟩ : syracuseStep 1759231 = 2638847) B2638847
theorem B7920409 : Blo 1735068 7920409 := bstep (se 2 (by rfl) ⟨2970153, by rfl⟩ : syracuseStep 7920409 = 5940307) B5940307
theorem B1735935 : Blo 1735068 1735935 := bstep (se 1 (by rfl) ⟨1301951, by rfl⟩ : syracuseStep 1735935 = 2603903) B2603903
theorem B16679155 : Blo 1735068 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B10560545 : Blo 1735068 10560545 := bstep (se 2 (by rfl) ⟨3960204, by rfl⟩ : syracuseStep 10560545 = 7920409) B7920409
theorem B2345641 : Blo 1735068 2345641 := bstep (se 2 (by rfl) ⟨879615, by rfl⟩ : syracuseStep 2345641 = 1759231) B1759231
theorem B7416937 : Blo 1735068 7416937 := bstep (se 2 (by rfl) ⟨2781351, by rfl⟩ : syracuseStep 7416937 = 5562703) B5562703
theorem B30053405 : Blo 1735068 30053405 := bstep (se 3 (by rfl) ⟨5635013, by rfl⟩ : syracuseStep 30053405 = 11270027) B11270027
theorem B608623465 : Blo 1735068 608623465 := bstep (se 2 (by rfl) ⟨228233799, by rfl⟩ : syracuseStep 608623465 = 456467599) B456467599
theorem B12510085 : Blo 1735068 12510085 := bstep (se 4 (by rfl) ⟨1172820, by rfl⟩ : syracuseStep 12510085 = 2345641) B2345641
theorem B9889249 : Blo 1735068 9889249 := bstep (se 2 (by rfl) ⟨3708468, by rfl⟩ : syracuseStep 9889249 = 7416937) B7416937
theorem B7040363 : Blo 1735068 7040363 := bstep (se 1 (by rfl) ⟨5280272, by rfl⟩ : syracuseStep 7040363 = 10560545) B10560545
theorem B22238873 : Blo 1735068 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B20035603 : Blo 1735068 20035603 := bstep (se 1 (by rfl) ⟨15026702, by rfl⟩ : syracuseStep 20035603 = 30053405) B30053405
theorem B811497953 : Blo 1735068 811497953 := bstep (se 2 (by rfl) ⟨304311732, by rfl⟩ : syracuseStep 811497953 = 608623465) B608623465
theorem B26714137 : Blo 1735068 26714137 := bstep (se 2 (by rfl) ⟨10017801, by rfl⟩ : syracuseStep 26714137 = 20035603) B20035603
theorem B16680113 : Blo 1735068 16680113 := bstep (se 2 (by rfl) ⟨6255042, by rfl⟩ : syracuseStep 16680113 = 12510085) B12510085
theorem B13185665 : Blo 1735068 13185665 := bstep (se 2 (by rfl) ⟨4944624, by rfl⟩ : syracuseStep 13185665 = 9889249) B9889249
theorem B18774301 : Blo 1735068 18774301 := bstep (se 3 (by rfl) ⟨3520181, by rfl⟩ : syracuseStep 18774301 = 7040363) B7040363
theorem B14825915 : Blo 1735068 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B540998635 : Blo 1735068 540998635 := bstep (se 1 (by rfl) ⟨405748976, by rfl⟩ : syracuseStep 540998635 = 811497953) B811497953
theorem B35618849 : Blo 1735068 35618849 := bstep (se 2 (by rfl) ⟨13357068, by rfl⟩ : syracuseStep 35618849 = 26714137) B26714137
theorem B8790443 : Blo 1735068 8790443 := bstep (se 1 (by rfl) ⟨6592832, by rfl⟩ : syracuseStep 8790443 = 13185665) B13185665
theorem B721331513 : Blo 1735068 721331513 := bstep (se 2 (by rfl) ⟨270499317, by rfl⟩ : syracuseStep 721331513 = 540998635) B540998635
theorem B11120075 : Blo 1735068 11120075 := bstep (se 1 (by rfl) ⟨8340056, by rfl⟩ : syracuseStep 11120075 = 16680113) B16680113
theorem B9883943 : Blo 1735068 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B25032401 : Blo 1735068 25032401 := bstep (se 2 (by rfl) ⟨9387150, by rfl⟩ : syracuseStep 25032401 = 18774301) B18774301
theorem B480887675 : Blo 1735068 480887675 := bstep (se 1 (by rfl) ⟨360665756, by rfl⟩ : syracuseStep 480887675 = 721331513) B721331513
theorem B16688267 : Blo 1735068 16688267 := bstep (se 1 (by rfl) ⟨12516200, by rfl⟩ : syracuseStep 16688267 = 25032401) B25032401
theorem B6589295 : Blo 1735068 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B5860295 : Blo 1735068 5860295 := bstep (se 1 (by rfl) ⟨4395221, by rfl⟩ : syracuseStep 5860295 = 8790443) B8790443
theorem B23745899 : Blo 1735068 23745899 := bstep (se 1 (by rfl) ⟨17809424, by rfl⟩ : syracuseStep 23745899 = 35618849) B35618849
theorem B7413383 : Blo 1735068 7413383 := bstep (se 1 (by rfl) ⟨5560037, by rfl⟩ : syracuseStep 7413383 = 11120075) B11120075
theorem B11125511 : Blo 1735068 11125511 := bstep (se 1 (by rfl) ⟨8344133, by rfl⟩ : syracuseStep 11125511 = 16688267) B16688267
theorem B19769021 : Blo 1735068 19769021 := bstep (se 3 (by rfl) ⟨3706691, by rfl⟩ : syracuseStep 19769021 = 7413383) B7413383
theorem B4392863 : Blo 1735068 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B320591783 : Blo 1735068 320591783 := bstep (se 1 (by rfl) ⟨240443837, by rfl⟩ : syracuseStep 320591783 = 480887675) B480887675
theorem B63322397 : Blo 1735068 63322397 := bstep (se 3 (by rfl) ⟨11872949, by rfl⟩ : syracuseStep 63322397 = 23745899) B23745899
theorem B3906863 : Blo 1735068 3906863 := bstep (se 1 (by rfl) ⟨2930147, by rfl⟩ : syracuseStep 3906863 = 5860295) B5860295
theorem B42214931 : Blo 1735068 42214931 := bstep (se 1 (by rfl) ⟨31661198, by rfl⟩ : syracuseStep 42214931 = 63322397) B63322397
theorem B7417007 : Blo 1735068 7417007 := bstep (se 1 (by rfl) ⟨5562755, by rfl⟩ : syracuseStep 7417007 = 11125511) B11125511
theorem B2928575 : Blo 1735068 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B13179347 : Blo 1735068 13179347 := bstep (se 1 (by rfl) ⟨9884510, by rfl⟩ : syracuseStep 13179347 = 19769021) B19769021
theorem B213727855 : Blo 1735068 213727855 := bstep (se 1 (by rfl) ⟨160295891, by rfl⟩ : syracuseStep 213727855 = 320591783) B320591783
theorem B2604575 : Blo 1735068 2604575 := bstep (se 1 (by rfl) ⟨1953431, by rfl⟩ : syracuseStep 2604575 = 3906863) B3906863
theorem B1952383 : Blo 1735068 1952383 := bstep (se 1 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 1952383 = 2928575) B2928575
theorem B284970473 : Blo 1735068 284970473 := bstep (se 2 (by rfl) ⟨106863927, by rfl⟩ : syracuseStep 284970473 = 213727855) B213727855
theorem B28143287 : Blo 1735068 28143287 := bstep (se 1 (by rfl) ⟨21107465, by rfl⟩ : syracuseStep 28143287 = 42214931) B42214931
theorem B8786231 : Blo 1735068 8786231 := bstep (se 1 (by rfl) ⟨6589673, by rfl⟩ : syracuseStep 8786231 = 13179347) B13179347
theorem B4944671 : Blo 1735068 4944671 := bstep (se 1 (by rfl) ⟨3708503, by rfl⟩ : syracuseStep 4944671 = 7417007) B7417007
theorem B1736383 : Blo 1735068 1736383 := bstep (se 1 (by rfl) ⟨1302287, by rfl⟩ : syracuseStep 1736383 = 2604575) B2604575
theorem B5857487 : Blo 1735068 5857487 := bstep (se 1 (by rfl) ⟨4393115, by rfl⟩ : syracuseStep 5857487 = 8786231) B8786231
theorem B18762191 : Blo 1735068 18762191 := bstep (se 1 (by rfl) ⟨14071643, by rfl⟩ : syracuseStep 18762191 = 28143287) B28143287
theorem B3296447 : Blo 1735068 3296447 := bstep (se 1 (by rfl) ⟨2472335, by rfl⟩ : syracuseStep 3296447 = 4944671) B4944671
theorem B2603177 : Blo 1735068 2603177 := bstep (se 2 (by rfl) ⟨976191, by rfl⟩ : syracuseStep 2603177 = 1952383) B1952383
theorem B189980315 : Blo 1735068 189980315 := bstep (se 1 (by rfl) ⟨142485236, by rfl⟩ : syracuseStep 189980315 = 284970473) B284970473
theorem B2197631 : Blo 1735068 2197631 := bstep (se 1 (by rfl) ⟨1648223, by rfl⟩ : syracuseStep 2197631 = 3296447) B3296447
theorem B126653543 : Blo 1735068 126653543 := bstep (se 1 (by rfl) ⟨94990157, by rfl⟩ : syracuseStep 126653543 = 189980315) B189980315
theorem B3904991 : Blo 1735068 3904991 := bstep (se 1 (by rfl) ⟨2928743, by rfl⟩ : syracuseStep 3904991 = 5857487) B5857487
theorem B1735451 : Blo 1735068 1735451 := bstep (se 1 (by rfl) ⟨1301588, by rfl⟩ : syracuseStep 1735451 = 2603177) B2603177
theorem B12508127 : Blo 1735068 12508127 := bstep (se 1 (by rfl) ⟨9381095, by rfl⟩ : syracuseStep 12508127 = 18762191) B18762191
theorem B84435695 : Blo 1735068 84435695 := bstep (se 1 (by rfl) ⟨63326771, by rfl⟩ : syracuseStep 84435695 = 126653543) B126653543
theorem B5860349 : Blo 1735068 5860349 := bstep (se 3 (by rfl) ⟨1098815, by rfl⟩ : syracuseStep 5860349 = 2197631) B2197631
theorem B2603327 : Blo 1735068 2603327 := bstep (se 1 (by rfl) ⟨1952495, by rfl⟩ : syracuseStep 2603327 = 3904991) B3904991
theorem B8338751 : Blo 1735068 8338751 := bstep (se 1 (by rfl) ⟨6254063, by rfl⟩ : syracuseStep 8338751 = 12508127) B12508127
theorem B56290463 : Blo 1735068 56290463 := bstep (se 1 (by rfl) ⟨42217847, by rfl⟩ : syracuseStep 56290463 = 84435695) B84435695
theorem B5559167 : Blo 1735068 5559167 := bstep (se 1 (by rfl) ⟨4169375, by rfl⟩ : syracuseStep 5559167 = 8338751) B8338751
theorem B1735551 : Blo 1735068 1735551 := bstep (se 1 (by rfl) ⟨1301663, by rfl⟩ : syracuseStep 1735551 = 2603327) B2603327
theorem B3906899 : Blo 1735068 3906899 := bstep (se 1 (by rfl) ⟨2930174, by rfl⟩ : syracuseStep 3906899 = 5860349) B5860349
theorem B3706111 : Blo 1735068 3706111 := bstep (se 1 (by rfl) ⟨2779583, by rfl⟩ : syracuseStep 3706111 = 5559167) B5559167
theorem B37526975 : Blo 1735068 37526975 := bstep (se 1 (by rfl) ⟨28145231, by rfl⟩ : syracuseStep 37526975 = 56290463) B56290463
theorem B2604599 : Blo 1735068 2604599 := bstep (se 1 (by rfl) ⟨1953449, by rfl⟩ : syracuseStep 2604599 = 3906899) B3906899
theorem B4941481 : Blo 1735068 4941481 := bstep (se 2 (by rfl) ⟨1853055, by rfl⟩ : syracuseStep 4941481 = 3706111) B3706111
theorem B25017983 : Blo 1735068 25017983 := bstep (se 1 (by rfl) ⟨18763487, by rfl⟩ : syracuseStep 25017983 = 37526975) B37526975
theorem B1736399 : Blo 1735068 1736399 := bstep (se 1 (by rfl) ⟨1302299, by rfl⟩ : syracuseStep 1736399 = 2604599) B2604599
theorem B6588641 : Blo 1735068 6588641 := bstep (se 2 (by rfl) ⟨2470740, by rfl⟩ : syracuseStep 6588641 = 4941481) B4941481
theorem B16678655 : Blo 1735068 16678655 := bstep (se 1 (by rfl) ⟨12508991, by rfl⟩ : syracuseStep 16678655 = 25017983) B25017983
theorem B4392427 : Blo 1735068 4392427 := bstep (se 1 (by rfl) ⟨3294320, by rfl⟩ : syracuseStep 4392427 = 6588641) B6588641
theorem B11119103 : Blo 1735068 11119103 := bstep (se 1 (by rfl) ⟨8339327, by rfl⟩ : syracuseStep 11119103 = 16678655) B16678655
theorem B7412735 : Blo 1735068 7412735 := bstep (se 1 (by rfl) ⟨5559551, by rfl⟩ : syracuseStep 7412735 = 11119103) B11119103
theorem B5856569 : Blo 1735068 5856569 := bstep (se 2 (by rfl) ⟨2196213, by rfl⟩ : syracuseStep 5856569 = 4392427) B4392427
theorem B4941823 : Blo 1735068 4941823 := bstep (se 1 (by rfl) ⟨3706367, by rfl⟩ : syracuseStep 4941823 = 7412735) B7412735
theorem B3904379 : Blo 1735068 3904379 := bstep (se 1 (by rfl) ⟨2928284, by rfl⟩ : syracuseStep 3904379 = 5856569) B5856569
theorem B6589097 : Blo 1735068 6589097 := bstep (se 2 (by rfl) ⟨2470911, by rfl⟩ : syracuseStep 6589097 = 4941823) B4941823
theorem B2602919 : Blo 1735068 2602919 := bstep (se 1 (by rfl) ⟨1952189, by rfl⟩ : syracuseStep 2602919 = 3904379) B3904379
theorem B4392731 : Blo 1735068 4392731 := bstep (se 1 (by rfl) ⟨3294548, by rfl⟩ : syracuseStep 4392731 = 6589097) B6589097
theorem B1735279 : Blo 1735068 1735279 := bstep (se 1 (by rfl) ⟨1301459, by rfl⟩ : syracuseStep 1735279 = 2602919) B2602919
theorem B2928487 : Blo 1735068 2928487 := bstep (se 1 (by rfl) ⟨2196365, by rfl⟩ : syracuseStep 2928487 = 4392731) B4392731
theorem B3904649 : Blo 1735068 3904649 := bstep (se 2 (by rfl) ⟨1464243, by rfl⟩ : syracuseStep 3904649 = 2928487) B2928487
theorem B2603099 : Blo 1735068 2603099 := bstep (se 1 (by rfl) ⟨1952324, by rfl⟩ : syracuseStep 2603099 = 3904649) B3904649
theorem B1735399 : Blo 1735068 1735399 := bstep (se 1 (by rfl) ⟨1301549, by rfl⟩ : syracuseStep 1735399 = 2603099) B2603099

theorem C0 (j : ℕ) (h1 : 433767 ≤ j) (h2 : j ≤ 434141) : Blo 1735068 (4 * j + 3) := by
  interval_cases j
  · exact B1735071
  · exact B1735075
  · exact B1735079
  · exact B1735083
  · exact B1735087
  · exact B1735091
  · exact B1735095
  · exact B1735099
  · exact B1735103
  · exact B1735107
  · exact B1735111
  · exact B1735115
  · exact B1735119
  · exact B1735123
  · exact B1735127
  · exact B1735131
  · exact B1735135
  · exact B1735139
  · exact B1735143
  · exact B1735147
  · exact B1735151
  · exact B1735155
  · exact B1735159
  · exact B1735163
  · exact B1735167
  · exact B1735171
  · exact B1735175
  · exact B1735179
  · exact B1735183
  · exact B1735187
  · exact B1735191
  · exact B1735195
  · exact B1735199
  · exact B1735203
  · exact B1735207
  · exact B1735211
  · exact B1735215
  · exact B1735219
  · exact B1735223
  · exact B1735227
  · exact B1735231
  · exact B1735235
  · exact B1735239
  · exact B1735243
  · exact B1735247
  · exact B1735251
  · exact B1735255
  · exact B1735259
  · exact B1735263
  · exact B1735267
  · exact B1735271
  · exact B1735275
  · exact B1735279
  · exact B1735283
  · exact B1735287
  · exact B1735291
  · exact B1735295
  · exact B1735299
  · exact B1735303
  · exact B1735307
  · exact B1735311
  · exact B1735315
  · exact B1735319
  · exact B1735323
  · exact B1735327
  · exact B1735331
  · exact B1735335
  · exact B1735339
  · exact B1735343
  · exact B1735347
  · exact B1735351
  · exact B1735355
  · exact B1735359
  · exact B1735363
  · exact B1735367
  · exact B1735371
  · exact B1735375
  · exact B1735379
  · exact B1735383
  · exact B1735387
  · exact B1735391
  · exact B1735395
  · exact B1735399
  · exact B1735403
  · exact B1735407
  · exact B1735411
  · exact B1735415
  · exact B1735419
  · exact B1735423
  · exact B1735427
  · exact B1735431
  · exact B1735435
  · exact B1735439
  · exact B1735443
  · exact B1735447
  · exact B1735451
  · exact B1735455
  · exact B1735459
  · exact B1735463
  · exact B1735467
  · exact B1735471
  · exact B1735475
  · exact B1735479
  · exact B1735483
  · exact B1735487
  · exact B1735491
  · exact B1735495
  · exact B1735499
  · exact B1735503
  · exact B1735507
  · exact B1735511
  · exact B1735515
  · exact B1735519
  · exact B1735523
  · exact B1735527
  · exact B1735531
  · exact B1735535
  · exact B1735539
  · exact B1735543
  · exact B1735547
  · exact B1735551
  · exact B1735555
  · exact B1735559
  · exact B1735563
  · exact B1735567
  · exact B1735571
  · exact B1735575
  · exact B1735579
  · exact B1735583
  · exact B1735587
  · exact B1735591
  · exact B1735595
  · exact B1735599
  · exact B1735603
  · exact B1735607
  · exact B1735611
  · exact B1735615
  · exact B1735619
  · exact B1735623
  · exact B1735627
  · exact B1735631
  · exact B1735635
  · exact B1735639
  · exact B1735643
  · exact B1735647
  · exact B1735651
  · exact B1735655
  · exact B1735659
  · exact B1735663
  · exact B1735667
  · exact B1735671
  · exact B1735675
  · exact B1735679
  · exact B1735683
  · exact B1735687
  · exact B1735691
  · exact B1735695
  · exact B1735699
  · exact B1735703
  · exact B1735707
  · exact B1735711
  · exact B1735715
  · exact B1735719
  · exact B1735723
  · exact B1735727
  · exact B1735731
  · exact B1735735
  · exact B1735739
  · exact B1735743
  · exact B1735747
  · exact B1735751
  · exact B1735755
  · exact B1735759
  · exact B1735763
  · exact B1735767
  · exact B1735771
  · exact B1735775
  · exact B1735779
  · exact B1735783
  · exact B1735787
  · exact B1735791
  · exact B1735795
  · exact B1735799
  · exact B1735803
  · exact B1735807
  · exact B1735811
  · exact B1735815
  · exact B1735819
  · exact B1735823
  · exact B1735827
  · exact B1735831
  · exact B1735835
  · exact B1735839
  · exact B1735843
  · exact B1735847
  · exact B1735851
  · exact B1735855
  · exact B1735859
  · exact B1735863
  · exact B1735867
  · exact B1735871
  · exact B1735875
  · exact B1735879
  · exact B1735883
  · exact B1735887
  · exact B1735891
  · exact B1735895
  · exact B1735899
  · exact B1735903
  · exact B1735907
  · exact B1735911
  · exact B1735915
  · exact B1735919
  · exact B1735923
  · exact B1735927
  · exact B1735931
  · exact B1735935
  · exact B1735939
  · exact B1735943
  · exact B1735947
  · exact B1735951
  · exact B1735955
  · exact B1735959
  · exact B1735963
  · exact B1735967
  · exact B1735971
  · exact B1735975
  · exact B1735979
  · exact B1735983
  · exact B1735987
  · exact B1735991
  · exact B1735995
  · exact B1735999
  · exact B1736003
  · exact B1736007
  · exact B1736011
  · exact B1736015
  · exact B1736019
  · exact B1736023
  · exact B1736027
  · exact B1736031
  · exact B1736035
  · exact B1736039
  · exact B1736043
  · exact B1736047
  · exact B1736051
  · exact B1736055
  · exact B1736059
  · exact B1736063
  · exact B1736067
  · exact B1736071
  · exact B1736075
  · exact B1736079
  · exact B1736083
  · exact B1736087
  · exact B1736091
  · exact B1736095
  · exact B1736099
  · exact B1736103
  · exact B1736107
  · exact B1736111
  · exact B1736115
  · exact B1736119
  · exact B1736123
  · exact B1736127
  · exact B1736131
  · exact B1736135
  · exact B1736139
  · exact B1736143
  · exact B1736147
  · exact B1736151
  · exact B1736155
  · exact B1736159
  · exact B1736163
  · exact B1736167
  · exact B1736171
  · exact B1736175
  · exact B1736179
  · exact B1736183
  · exact B1736187
  · exact B1736191
  · exact B1736195
  · exact B1736199
  · exact B1736203
  · exact B1736207
  · exact B1736211
  · exact B1736215
  · exact B1736219
  · exact B1736223
  · exact B1736227
  · exact B1736231
  · exact B1736235
  · exact B1736239
  · exact B1736243
  · exact B1736247
  · exact B1736251
  · exact B1736255
  · exact B1736259
  · exact B1736263
  · exact B1736267
  · exact B1736271
  · exact B1736275
  · exact B1736279
  · exact B1736283
  · exact B1736287
  · exact B1736291
  · exact B1736295
  · exact B1736299
  · exact B1736303
  · exact B1736307
  · exact B1736311
  · exact B1736315
  · exact B1736319
  · exact B1736323
  · exact B1736327
  · exact B1736331
  · exact B1736335
  · exact B1736339
  · exact B1736343
  · exact B1736347
  · exact B1736351
  · exact B1736355
  · exact B1736359
  · exact B1736363
  · exact B1736367
  · exact B1736371
  · exact B1736375
  · exact B1736379
  · exact B1736383
  · exact B1736387
  · exact B1736391
  · exact B1736395
  · exact B1736399
  · exact B1736403
  · exact B1736407
  · exact B1736411
  · exact B1736415
  · exact B1736419
  · exact B1736423
  · exact B1736427
  · exact B1736431
  · exact B1736435
  · exact B1736439
  · exact B1736443
  · exact B1736447
  · exact B1736451
  · exact B1736455
  · exact B1736459
  · exact B1736463
  · exact B1736467
  · exact B1736471
  · exact B1736475
  · exact B1736479
  · exact B1736483
  · exact B1736487
  · exact B1736491
  · exact B1736495
  · exact B1736499
  · exact B1736503
  · exact B1736507
  · exact B1736511
  · exact B1736515
  · exact B1736519
  · exact B1736523
  · exact B1736527
  · exact B1736531
  · exact B1736535
  · exact B1736539
  · exact B1736543
  · exact B1736547
  · exact B1736551
  · exact B1736555
  · exact B1736559
  · exact B1736563
  · exact B1736567

theorem solution (m : ℕ) (hlo : 1735068 ≤ m) (hhi : m ≤ 1736568) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 433767 ≤ j := by omega
    have hj2 : j ≤ 434141 := by omega
    have hb : Blo 1735068 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
