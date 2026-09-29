-- Prove2me | solution 1 for syracuse_descends_range_1431535_1433535
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:42:02.749573+00:00
-- url     : https://prove2.me/submissions/d8a9c5fa-690e-4ed7-942d-2c95110c29fc

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


theorem B4079621 : Blo 1431535 4079621 := bbase (se 4 (by rfl) ⟨382464, by rfl⟩ : syracuseStep 4079621 = 764929) (by norm_num)
theorem B2039845 : Blo 1431535 2039845 := bbase (se 4 (by rfl) ⟨191235, by rfl⟩ : syracuseStep 2039845 = 382471) (by norm_num)
theorem B2416709 : Blo 1431535 2416709 := bbase (se 4 (by rfl) ⟨226566, by rfl⟩ : syracuseStep 2416709 = 453133) (by norm_num)
theorem B2179253 : Blo 1431535 2179253 := bbase (se 5 (by rfl) ⟨102152, by rfl⟩ : syracuseStep 2179253 = 204305) (by norm_num)
theorem B2416837 : Blo 1431535 2416837 := bbase (se 4 (by rfl) ⟨226578, by rfl⟩ : syracuseStep 2416837 = 453157) (by norm_num)
theorem B6119621 : Blo 1431535 6119621 := bbase (se 4 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 6119621 = 1147429) (by norm_num)
theorem B1745137 : Blo 1431535 1745137 := bbase (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) (by norm_num)
theorem B2040061 : Blo 1431535 2040061 := bbase (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) (by norm_num)
theorem B2416925 : Blo 1431535 2416925 := bbase (se 3 (by rfl) ⟨453173, by rfl⟩ : syracuseStep 2416925 = 906347) (by norm_num)
theorem B9806197 : Blo 1431535 9806197 := bbase (se 5 (by rfl) ⟨459665, by rfl⟩ : syracuseStep 9806197 = 919331) (by norm_num)
theorem B7250309 : Blo 1431535 7250309 := bbase (se 4 (by rfl) ⟨679716, by rfl⟩ : syracuseStep 7250309 = 1359433) (by norm_num)
theorem B1720721 : Blo 1431535 1720721 := bbase (se 2 (by rfl) ⟨645270, by rfl⟩ : syracuseStep 1720721 = 1290541) (by norm_num)
theorem B2417053 : Blo 1431535 2417053 := bbase (se 3 (by rfl) ⟨453197, by rfl⟩ : syracuseStep 2417053 = 906395) (by norm_num)
theorem B4833701 : Blo 1431535 4833701 := bbase (se 4 (by rfl) ⟨453159, by rfl⟩ : syracuseStep 4833701 = 906319) (by norm_num)
theorem B2417141 : Blo 1431535 2417141 := bbase (se 5 (by rfl) ⟨113303, by rfl⟩ : syracuseStep 2417141 = 226607) (by norm_num)
theorem B15483413 : Blo 1431535 15483413 := bbase (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) (by norm_num)
theorem B3269173 : Blo 1431535 3269173 := bbase (se 5 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 3269173 = 306485) (by norm_num)
theorem B2720317 : Blo 1431535 2720317 := bbase (se 3 (by rfl) ⟨510059, by rfl⟩ : syracuseStep 2720317 = 1020119) (by norm_num)
theorem B27927125 : Blo 1431535 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B2417269 : Blo 1431535 2417269 := bbase (se 5 (by rfl) ⟨113309, by rfl⟩ : syracuseStep 2417269 = 226619) (by norm_num)
theorem B2040437 : Blo 1431535 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B1721029 : Blo 1431535 1721029 := bbase (se 4 (by rfl) ⟨161346, by rfl⟩ : syracuseStep 1721029 = 322693) (by norm_num)
theorem B2417357 : Blo 1431535 2417357 := bbase (se 3 (by rfl) ⟨453254, by rfl⟩ : syracuseStep 2417357 = 906509) (by norm_num)
theorem B2720461 : Blo 1431535 2720461 := bbase (se 3 (by rfl) ⟨510086, by rfl⟩ : syracuseStep 2720461 = 1020173) (by norm_num)
theorem B2417485 : Blo 1431535 2417485 := bbase (se 3 (by rfl) ⟨453278, by rfl⟩ : syracuseStep 2417485 = 906557) (by norm_num)
theorem B4834133 : Blo 1431535 4834133 := bbase (se 9 (by rfl) ⟨14162, by rfl⟩ : syracuseStep 4834133 = 28325) (by norm_num)
theorem B2720621 : Blo 1431535 2720621 := bbase (se 3 (by rfl) ⟨510116, by rfl⟩ : syracuseStep 2720621 = 1020233) (by norm_num)
theorem B5440405 : Blo 1431535 5440405 := bbase (se 6 (by rfl) ⟨127509, by rfl⟩ : syracuseStep 5440405 = 255019) (by norm_num)
theorem B2417573 : Blo 1431535 2417573 := bbase (se 4 (by rfl) ⟨226647, by rfl⟩ : syracuseStep 2417573 = 453295) (by norm_num)
theorem B3490781 : Blo 1431535 3490781 := bbase (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) (by norm_num)
theorem B2147309 : Blo 1431535 2147309 := bbase (se 3 (by rfl) ⟨402620, by rfl⟩ : syracuseStep 2147309 = 805241) (by norm_num)
theorem B2450429 : Blo 1431535 2450429 := bbase (se 3 (by rfl) ⟨459455, by rfl⟩ : syracuseStep 2450429 = 918911) (by norm_num)
theorem B2720765 : Blo 1431535 2720765 := bbase (se 3 (by rfl) ⟨510143, by rfl⟩ : syracuseStep 2720765 = 1020287) (by norm_num)
theorem B2147333 : Blo 1431535 2147333 := bbase (se 4 (by rfl) ⟨201312, by rfl⟩ : syracuseStep 2147333 = 402625) (by norm_num)
theorem B2147357 : Blo 1431535 2147357 := bbase (se 3 (by rfl) ⟨402629, by rfl⟩ : syracuseStep 2147357 = 805259) (by norm_num)
theorem B2294813 : Blo 1431535 2294813 := bbase (se 3 (by rfl) ⟨430277, by rfl⟩ : syracuseStep 2294813 = 860555) (by norm_num)
theorem B2417701 : Blo 1431535 2417701 := bbase (se 4 (by rfl) ⟨226659, by rfl⟩ : syracuseStep 2417701 = 453319) (by norm_num)
theorem B2147381 : Blo 1431535 2147381 := bbase (se 5 (by rfl) ⟨100658, by rfl⟩ : syracuseStep 2147381 = 201317) (by norm_num)
theorem B1721417 : Blo 1431535 1721417 := bbase (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) (by norm_num)
theorem B2147405 : Blo 1431535 2147405 := bbase (se 3 (by rfl) ⟨402638, by rfl⟩ : syracuseStep 2147405 = 805277) (by norm_num)
theorem B2147429 : Blo 1431535 2147429 := bbase (se 4 (by rfl) ⟨201321, by rfl⟩ : syracuseStep 2147429 = 402643) (by norm_num)
theorem B6882421 : Blo 1431535 6882421 := bbase (se 5 (by rfl) ⟨322613, by rfl⟩ : syracuseStep 6882421 = 645227) (by norm_num)
theorem B2147453 : Blo 1431535 2147453 := bbase (se 3 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 2147453 = 805295) (by norm_num)
theorem B2417789 : Blo 1431535 2417789 := bbase (se 3 (by rfl) ⟨453335, by rfl⟩ : syracuseStep 2417789 = 906671) (by norm_num)
theorem B2147477 : Blo 1431535 2147477 := bbase (se 6 (by rfl) ⟨50331, by rfl⟩ : syracuseStep 2147477 = 100663) (by norm_num)
theorem B1451177 : Blo 1431535 1451177 := bbase (se 2 (by rfl) ⟨544191, by rfl⟩ : syracuseStep 1451177 = 1088383) (by norm_num)
theorem B2147501 : Blo 1431535 2147501 := bbase (se 3 (by rfl) ⟨402656, by rfl⟩ : syracuseStep 2147501 = 805313) (by norm_num)
theorem B6120629 : Blo 1431535 6120629 := bbase (se 5 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 6120629 = 573809) (by norm_num)
theorem B2147525 : Blo 1431535 2147525 := bbase (se 4 (by rfl) ⟨201330, by rfl⟩ : syracuseStep 2147525 = 402661) (by norm_num)
theorem B5440709 : Blo 1431535 5440709 := bbase (se 4 (by rfl) ⟨510066, by rfl⟩ : syracuseStep 5440709 = 1020133) (by norm_num)
theorem B2147549 : Blo 1431535 2147549 := bbase (se 3 (by rfl) ⟨402665, by rfl⟩ : syracuseStep 2147549 = 805331) (by norm_num)
theorem B2147573 : Blo 1431535 2147573 := bbase (se 5 (by rfl) ⟨100667, by rfl⟩ : syracuseStep 2147573 = 201335) (by norm_num)
theorem B2417917 : Blo 1431535 2417917 := bbase (se 3 (by rfl) ⟨453359, by rfl⟩ : syracuseStep 2417917 = 906719) (by norm_num)
theorem B4588805 : Blo 1431535 4588805 := bbase (se 4 (by rfl) ⟨430200, by rfl⟩ : syracuseStep 4588805 = 860401) (by norm_num)
theorem B4834565 : Blo 1431535 4834565 := bbase (se 4 (by rfl) ⟨453240, by rfl⟩ : syracuseStep 4834565 = 906481) (by norm_num)
theorem B2147597 : Blo 1431535 2147597 := bbase (se 3 (by rfl) ⟨402674, by rfl⟩ : syracuseStep 2147597 = 805349) (by norm_num)
theorem B16540949 : Blo 1431535 16540949 := bbase (se 6 (by rfl) ⟨387678, by rfl⟩ : syracuseStep 16540949 = 775357) (by norm_num)
theorem B2721053 : Blo 1431535 2721053 := bbase (se 3 (by rfl) ⟨510197, by rfl⟩ : syracuseStep 2721053 = 1020395) (by norm_num)
theorem B2147621 : Blo 1431535 2147621 := bbase (se 4 (by rfl) ⟨201339, by rfl⟩ : syracuseStep 2147621 = 402679) (by norm_num)
theorem B2147645 : Blo 1431535 2147645 := bbase (se 3 (by rfl) ⟨402683, by rfl⟩ : syracuseStep 2147645 = 805367) (by norm_num)
theorem B3441989 : Blo 1431535 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B2581837 : Blo 1431535 2581837 := bbase (se 3 (by rfl) ⟨484094, by rfl⟩ : syracuseStep 2581837 = 968189) (by norm_num)
theorem B2147669 : Blo 1431535 2147669 := bbase (se 12 (by rfl) ⟨786, by rfl⟩ : syracuseStep 2147669 = 1573) (by norm_num)
theorem B19596629 : Blo 1431535 19596629 := bbase (se 12 (by rfl) ⟨7176, by rfl⟩ : syracuseStep 19596629 = 14353) (by norm_num)
theorem B2418005 : Blo 1431535 2418005 := bbase (se 12 (by rfl) ⟨885, by rfl⟩ : syracuseStep 2418005 = 1771) (by norm_num)
theorem B2147693 : Blo 1431535 2147693 := bbase (se 3 (by rfl) ⟨402692, by rfl⟩ : syracuseStep 2147693 = 805385) (by norm_num)
theorem B2147717 : Blo 1431535 2147717 := bbase (se 4 (by rfl) ⟨201348, by rfl⟩ : syracuseStep 2147717 = 402697) (by norm_num)
theorem B2147741 : Blo 1431535 2147741 := bbase (se 3 (by rfl) ⟨402701, by rfl⟩ : syracuseStep 2147741 = 805403) (by norm_num)
theorem B1721773 : Blo 1431535 1721773 := bbase (se 3 (by rfl) ⟨322832, by rfl⟩ : syracuseStep 1721773 = 645665) (by norm_num)
theorem B2147765 : Blo 1431535 2147765 := bbase (se 5 (by rfl) ⟨100676, by rfl⟩ : syracuseStep 2147765 = 201353) (by norm_num)
theorem B2721205 : Blo 1431535 2721205 := bbase (se 5 (by rfl) ⟨127556, by rfl⟩ : syracuseStep 2721205 = 255113) (by norm_num)
theorem B1451449 : Blo 1431535 1451449 := bbase (se 2 (by rfl) ⟨544293, by rfl⟩ : syracuseStep 1451449 = 1088587) (by norm_num)
theorem B1811909 : Blo 1431535 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B2147789 : Blo 1431535 2147789 := bbase (se 3 (by rfl) ⟨402710, by rfl⟩ : syracuseStep 2147789 = 805421) (by norm_num)
theorem B3442133 : Blo 1431535 3442133 := bbase (se 7 (by rfl) ⟨40337, by rfl⟩ : syracuseStep 3442133 = 80675) (by norm_num)
theorem B2418133 : Blo 1431535 2418133 := bbase (se 7 (by rfl) ⟨28337, by rfl⟩ : syracuseStep 2418133 = 56675) (by norm_num)
theorem B2147813 : Blo 1431535 2147813 := bbase (se 4 (by rfl) ⟨201357, by rfl⟩ : syracuseStep 2147813 = 402715) (by norm_num)
theorem B3220973 : Blo 1431535 3220973 := bbase (se 3 (by rfl) ⟨603932, by rfl⟩ : syracuseStep 3220973 = 1207865) (by norm_num)
theorem B1811965 : Blo 1431535 1811965 := bbase (se 3 (by rfl) ⟨339743, by rfl⟩ : syracuseStep 1811965 = 679487) (by norm_num)
theorem B2147837 : Blo 1431535 2147837 := bbase (se 3 (by rfl) ⟨402719, by rfl⟩ : syracuseStep 2147837 = 805439) (by norm_num)
theorem B2147861 : Blo 1431535 2147861 := bbase (se 6 (by rfl) ⟨50340, by rfl⟩ : syracuseStep 2147861 = 100681) (by norm_num)
theorem B2295325 : Blo 1431535 2295325 := bbase (se 3 (by rfl) ⟨430373, by rfl⟩ : syracuseStep 2295325 = 860747) (by norm_num)
theorem B2147885 : Blo 1431535 2147885 := bbase (se 3 (by rfl) ⟨402728, by rfl⟩ : syracuseStep 2147885 = 805457) (by norm_num)
theorem B2418221 : Blo 1431535 2418221 := bbase (se 3 (by rfl) ⟨453416, by rfl⟩ : syracuseStep 2418221 = 906833) (by norm_num)
theorem B3221045 : Blo 1431535 3221045 := bbase (se 5 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 3221045 = 301973) (by norm_num)
theorem B4081205 : Blo 1431535 4081205 := bbase (se 5 (by rfl) ⟨191306, by rfl⟩ : syracuseStep 4081205 = 382613) (by norm_num)
theorem B2147909 : Blo 1431535 2147909 := bbase (se 4 (by rfl) ⟨201366, by rfl⟩ : syracuseStep 2147909 = 402733) (by norm_num)
theorem B6530645 : Blo 1431535 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B1812061 : Blo 1431535 1812061 := bbase (se 3 (by rfl) ⟨339761, by rfl⟩ : syracuseStep 1812061 = 679523) (by norm_num)
theorem B2147933 : Blo 1431535 2147933 := bbase (se 3 (by rfl) ⟨402737, by rfl⟩ : syracuseStep 2147933 = 805475) (by norm_num)
theorem B2147957 : Blo 1431535 2147957 := bbase (se 5 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 2147957 = 201371) (by norm_num)
theorem B3221117 : Blo 1431535 3221117 := bbase (se 3 (by rfl) ⟨603959, by rfl⟩ : syracuseStep 3221117 = 1207919) (by norm_num)
theorem B2147981 : Blo 1431535 2147981 := bbase (se 3 (by rfl) ⟨402746, by rfl⟩ : syracuseStep 2147981 = 805493) (by norm_num)
theorem B7251605 : Blo 1431535 7251605 := bbase (se 6 (by rfl) ⟨169959, by rfl⟩ : syracuseStep 7251605 = 339919) (by norm_num)
theorem B2148005 : Blo 1431535 2148005 := bbase (se 4 (by rfl) ⟨201375, by rfl⟩ : syracuseStep 2148005 = 402751) (by norm_num)
theorem B2418349 : Blo 1431535 2418349 := bbase (se 3 (by rfl) ⟨453440, by rfl⟩ : syracuseStep 2418349 = 906881) (by norm_num)
theorem B4834997 : Blo 1431535 4834997 := bbase (se 5 (by rfl) ⟨226640, by rfl⟩ : syracuseStep 4834997 = 453281) (by norm_num)
theorem B2148029 : Blo 1431535 2148029 := bbase (se 3 (by rfl) ⟨402755, by rfl⟩ : syracuseStep 2148029 = 805511) (by norm_num)
theorem B3221189 : Blo 1431535 3221189 := bbase (se 4 (by rfl) ⟨301986, by rfl⟩ : syracuseStep 3221189 = 603973) (by norm_num)
theorem B2148053 : Blo 1431535 2148053 := bbase (se 7 (by rfl) ⟨25172, by rfl⟩ : syracuseStep 2148053 = 50345) (by norm_num)
theorem B9176789 : Blo 1431535 9176789 := bbase (se 7 (by rfl) ⟨107540, by rfl⟩ : syracuseStep 9176789 = 215081) (by norm_num)
theorem B2148077 : Blo 1431535 2148077 := bbase (se 3 (by rfl) ⟨402764, by rfl⟩ : syracuseStep 2148077 = 805529) (by norm_num)
theorem B1722109 : Blo 1431535 1722109 := bbase (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) (by norm_num)
theorem B2148101 : Blo 1431535 2148101 := bbase (se 4 (by rfl) ⟨201384, by rfl⟩ : syracuseStep 2148101 = 402769) (by norm_num)
theorem B2418437 : Blo 1431535 2418437 := bbase (se 4 (by rfl) ⟨226728, by rfl⟩ : syracuseStep 2418437 = 453457) (by norm_num)
theorem B1812233 : Blo 1431535 1812233 := bbase (se 2 (by rfl) ⟨679587, by rfl⟩ : syracuseStep 1812233 = 1359175) (by norm_num)
theorem B3221261 : Blo 1431535 3221261 := bbase (se 3 (by rfl) ⟨603986, by rfl⟩ : syracuseStep 3221261 = 1207973) (by norm_num)
theorem B2582293 : Blo 1431535 2582293 := bbase (se 6 (by rfl) ⟨60522, by rfl⟩ : syracuseStep 2582293 = 121045) (by norm_num)
theorem B2148125 : Blo 1431535 2148125 := bbase (se 3 (by rfl) ⟨402773, by rfl⟩ : syracuseStep 2148125 = 805547) (by norm_num)
theorem B2148149 : Blo 1431535 2148149 := bbase (se 5 (by rfl) ⟨100694, by rfl⟩ : syracuseStep 2148149 = 201389) (by norm_num)
theorem B1812289 : Blo 1431535 1812289 := bbase (se 2 (by rfl) ⟨679608, by rfl⟩ : syracuseStep 1812289 = 1359217) (by norm_num)
theorem B2148173 : Blo 1431535 2148173 := bbase (se 3 (by rfl) ⟨402782, by rfl⟩ : syracuseStep 2148173 = 805565) (by norm_num)
theorem B3221333 : Blo 1431535 3221333 := bbase (se 9 (by rfl) ⟨9437, by rfl⟩ : syracuseStep 3221333 = 18875) (by norm_num)
theorem B2148197 : Blo 1431535 2148197 := bbase (se 4 (by rfl) ⟨201393, by rfl⟩ : syracuseStep 2148197 = 402787) (by norm_num)
theorem B2148221 : Blo 1431535 2148221 := bbase (se 3 (by rfl) ⟨402791, by rfl⟩ : syracuseStep 2148221 = 805583) (by norm_num)
theorem B2418565 : Blo 1431535 2418565 := bbase (se 4 (by rfl) ⟨226740, by rfl⟩ : syracuseStep 2418565 = 453481) (by norm_num)
theorem B1836949 : Blo 1431535 1836949 := bbase (se 6 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 1836949 = 86107) (by norm_num)
theorem B2148245 : Blo 1431535 2148245 := bbase (se 6 (by rfl) ⟨50349, by rfl⟩ : syracuseStep 2148245 = 100699) (by norm_num)
theorem B3221405 : Blo 1431535 3221405 := bbase (se 3 (by rfl) ⟨604013, by rfl⟩ : syracuseStep 3221405 = 1208027) (by norm_num)
theorem B1812385 : Blo 1431535 1812385 := bbase (se 2 (by rfl) ⟨679644, by rfl⟩ : syracuseStep 1812385 = 1359289) (by norm_num)
theorem B3057581 : Blo 1431535 3057581 := bbase (se 3 (by rfl) ⟨573296, by rfl⟩ : syracuseStep 3057581 = 1146593) (by norm_num)
theorem B2148269 : Blo 1431535 2148269 := bbase (se 3 (by rfl) ⟨402800, by rfl⟩ : syracuseStep 2148269 = 805601) (by norm_num)
theorem B2148293 : Blo 1431535 2148293 := bbase (se 4 (by rfl) ⟨201402, by rfl⟩ : syracuseStep 2148293 = 402805) (by norm_num)
theorem B8153045 : Blo 1431535 8153045 := bbase (se 7 (by rfl) ⟨95543, by rfl⟩ : syracuseStep 8153045 = 191087) (by norm_num)
theorem B2148317 : Blo 1431535 2148317 := bbase (se 3 (by rfl) ⟨402809, by rfl⟩ : syracuseStep 2148317 = 805619) (by norm_num)
theorem B2418653 : Blo 1431535 2418653 := bbase (se 3 (by rfl) ⟨453497, by rfl⟩ : syracuseStep 2418653 = 906995) (by norm_num)
theorem B3221477 : Blo 1431535 3221477 := bbase (se 4 (by rfl) ⟨302013, by rfl⟩ : syracuseStep 3221477 = 604027) (by norm_num)
theorem B2148341 : Blo 1431535 2148341 := bbase (se 5 (by rfl) ⟨100703, by rfl⟩ : syracuseStep 2148341 = 201407) (by norm_num)
theorem B2148365 : Blo 1431535 2148365 := bbase (se 3 (by rfl) ⟨402818, by rfl⟩ : syracuseStep 2148365 = 805637) (by norm_num)
theorem B2148389 : Blo 1431535 2148389 := bbase (se 4 (by rfl) ⟨201411, by rfl⟩ : syracuseStep 2148389 = 402823) (by norm_num)
theorem B3221549 : Blo 1431535 3221549 := bbase (se 3 (by rfl) ⟨604040, by rfl⟩ : syracuseStep 3221549 = 1208081) (by norm_num)
theorem B2148413 : Blo 1431535 2148413 := bbase (se 3 (by rfl) ⟨402827, by rfl⟩ : syracuseStep 2148413 = 805655) (by norm_num)
theorem B1812557 : Blo 1431535 1812557 := bbase (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) (by norm_num)
theorem B2148437 : Blo 1431535 2148437 := bbase (se 8 (by rfl) ⟨12588, by rfl⟩ : syracuseStep 2148437 = 25177) (by norm_num)
theorem B2418781 : Blo 1431535 2418781 := bbase (se 3 (by rfl) ⟨453521, by rfl⟩ : syracuseStep 2418781 = 907043) (by norm_num)
theorem B4835429 : Blo 1431535 4835429 := bbase (se 4 (by rfl) ⟨453321, by rfl⟩ : syracuseStep 4835429 = 906643) (by norm_num)
theorem B2148461 : Blo 1431535 2148461 := bbase (se 3 (by rfl) ⟨402836, by rfl⟩ : syracuseStep 2148461 = 805673) (by norm_num)
theorem B3221621 : Blo 1431535 3221621 := bbase (se 5 (by rfl) ⟨151013, by rfl⟩ : syracuseStep 3221621 = 302027) (by norm_num)
theorem B1812613 : Blo 1431535 1812613 := bbase (se 4 (by rfl) ⟨169932, by rfl⟩ : syracuseStep 1812613 = 339865) (by norm_num)
theorem B2148485 : Blo 1431535 2148485 := bbase (se 4 (by rfl) ⟨201420, by rfl⟩ : syracuseStep 2148485 = 402841) (by norm_num)
theorem B2148509 : Blo 1431535 2148509 := bbase (se 3 (by rfl) ⟨402845, by rfl⟩ : syracuseStep 2148509 = 805691) (by norm_num)
theorem B2148533 : Blo 1431535 2148533 := bbase (se 5 (by rfl) ⟨100712, by rfl⟩ : syracuseStep 2148533 = 201425) (by norm_num)
theorem B2418869 : Blo 1431535 2418869 := bbase (se 5 (by rfl) ⟨113384, by rfl⟩ : syracuseStep 2418869 = 226769) (by norm_num)
theorem B3221693 : Blo 1431535 3221693 := bbase (se 3 (by rfl) ⟨604067, by rfl⟩ : syracuseStep 3221693 = 1208135) (by norm_num)
theorem B2615485 : Blo 1431535 2615485 := bbase (se 3 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 2615485 = 980807) (by norm_num)
theorem B2148557 : Blo 1431535 2148557 := bbase (se 3 (by rfl) ⟨402854, by rfl⟩ : syracuseStep 2148557 = 805709) (by norm_num)
theorem B4081877 : Blo 1431535 4081877 := bbase (se 7 (by rfl) ⟨47834, by rfl⟩ : syracuseStep 4081877 = 95669) (by norm_num)
theorem B1812709 : Blo 1431535 1812709 := bbase (se 4 (by rfl) ⟨169941, by rfl⟩ : syracuseStep 1812709 = 339883) (by norm_num)
theorem B2148581 : Blo 1431535 2148581 := bbase (se 4 (by rfl) ⟨201429, by rfl⟩ : syracuseStep 2148581 = 402859) (by norm_num)
theorem B2148605 : Blo 1431535 2148605 := bbase (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) (by norm_num)
theorem B3221765 : Blo 1431535 3221765 := bbase (se 4 (by rfl) ⟨302040, by rfl⟩ : syracuseStep 3221765 = 604081) (by norm_num)
theorem B2148629 : Blo 1431535 2148629 := bbase (se 6 (by rfl) ⟨50358, by rfl⟩ : syracuseStep 2148629 = 100717) (by norm_num)
theorem B2148653 : Blo 1431535 2148653 := bbase (se 3 (by rfl) ⟨402872, by rfl⟩ : syracuseStep 2148653 = 805745) (by norm_num)
theorem B2418997 : Blo 1431535 2418997 := bbase (se 5 (by rfl) ⟨113390, by rfl⟩ : syracuseStep 2418997 = 226781) (by norm_num)
theorem B2148677 : Blo 1431535 2148677 := bbase (se 4 (by rfl) ⟨201438, by rfl⟩ : syracuseStep 2148677 = 402877) (by norm_num)
theorem B3221837 : Blo 1431535 3221837 := bbase (se 3 (by rfl) ⟨604094, by rfl⟩ : syracuseStep 3221837 = 1208189) (by norm_num)
theorem B2148701 : Blo 1431535 2148701 := bbase (se 3 (by rfl) ⟨402881, by rfl⟩ : syracuseStep 2148701 = 805763) (by norm_num)
theorem B2148725 : Blo 1431535 2148725 := bbase (se 5 (by rfl) ⟨100721, by rfl⟩ : syracuseStep 2148725 = 201443) (by norm_num)
theorem B2148749 : Blo 1431535 2148749 := bbase (se 3 (by rfl) ⟨402890, by rfl⟩ : syracuseStep 2148749 = 805781) (by norm_num)
theorem B2419085 : Blo 1431535 2419085 := bbase (se 3 (by rfl) ⟨453578, by rfl⟩ : syracuseStep 2419085 = 907157) (by norm_num)
theorem B1812881 : Blo 1431535 1812881 := bbase (se 2 (by rfl) ⟨679830, by rfl⟩ : syracuseStep 1812881 = 1359661) (by norm_num)
theorem B3221909 : Blo 1431535 3221909 := bbase (se 6 (by rfl) ⟨75513, by rfl⟩ : syracuseStep 3221909 = 151027) (by norm_num)
theorem B2148773 : Blo 1431535 2148773 := bbase (se 4 (by rfl) ⟨201447, by rfl⟩ : syracuseStep 2148773 = 402895) (by norm_num)
theorem B2148797 : Blo 1431535 2148797 := bbase (se 3 (by rfl) ⟨402899, by rfl⟩ : syracuseStep 2148797 = 805799) (by norm_num)
theorem B1837513 : Blo 1431535 1837513 := bbase (se 2 (by rfl) ⟨689067, by rfl⟩ : syracuseStep 1837513 = 1378135) (by norm_num)
theorem B1812937 : Blo 1431535 1812937 := bbase (se 2 (by rfl) ⟨679851, by rfl⟩ : syracuseStep 1812937 = 1359703) (by norm_num)
theorem B10463701 : Blo 1431535 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B2148821 : Blo 1431535 2148821 := bbase (se 7 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 2148821 = 50363) (by norm_num)
theorem B3221981 : Blo 1431535 3221981 := bbase (se 3 (by rfl) ⟨604121, by rfl⟩ : syracuseStep 3221981 = 1208243) (by norm_num)
theorem B1837549 : Blo 1431535 1837549 := bbase (se 3 (by rfl) ⟨344540, by rfl⟩ : syracuseStep 1837549 = 689081) (by norm_num)
theorem B2148845 : Blo 1431535 2148845 := bbase (se 3 (by rfl) ⟨402908, by rfl⟩ : syracuseStep 2148845 = 805817) (by norm_num)
theorem B2148869 : Blo 1431535 2148869 := bbase (se 4 (by rfl) ⟨201456, by rfl⟩ : syracuseStep 2148869 = 402913) (by norm_num)
theorem B4835861 : Blo 1431535 4835861 := bbase (se 6 (by rfl) ⟨113340, by rfl⟩ : syracuseStep 4835861 = 226681) (by norm_num)
theorem B2148893 : Blo 1431535 2148893 := bbase (se 3 (by rfl) ⟨402917, by rfl⟩ : syracuseStep 2148893 = 805835) (by norm_num)
theorem B3222053 : Blo 1431535 3222053 := bbase (se 4 (by rfl) ⟨302067, by rfl⟩ : syracuseStep 3222053 = 604135) (by norm_num)
theorem B1813033 : Blo 1431535 1813033 := bbase (se 2 (by rfl) ⟨679887, by rfl⟩ : syracuseStep 1813033 = 1359775) (by norm_num)
theorem B2148917 : Blo 1431535 2148917 := bbase (se 5 (by rfl) ⟨100730, by rfl⟩ : syracuseStep 2148917 = 201461) (by norm_num)
theorem B2148941 : Blo 1431535 2148941 := bbase (se 3 (by rfl) ⟨402926, by rfl⟩ : syracuseStep 2148941 = 805853) (by norm_num)
theorem B2148965 : Blo 1431535 2148965 := bbase (se 4 (by rfl) ⟨201465, by rfl⟩ : syracuseStep 2148965 = 402931) (by norm_num)
theorem B3222125 : Blo 1431535 3222125 := bbase (se 3 (by rfl) ⟨604148, by rfl⟩ : syracuseStep 3222125 = 1208297) (by norm_num)
theorem B2148989 : Blo 1431535 2148989 := bbase (se 3 (by rfl) ⟨402935, by rfl⟩ : syracuseStep 2148989 = 805871) (by norm_num)
theorem B1452673 : Blo 1431535 1452673 := bbase (se 2 (by rfl) ⟨544752, by rfl⟩ : syracuseStep 1452673 = 1089505) (by norm_num)
theorem B2149013 : Blo 1431535 2149013 := bbase (se 6 (by rfl) ⟨50367, by rfl⟩ : syracuseStep 2149013 = 100735) (by norm_num)
theorem B4590229 : Blo 1431535 4590229 := bbase (se 6 (by rfl) ⟨107583, by rfl⟩ : syracuseStep 4590229 = 215167) (by norm_num)
theorem B2149037 : Blo 1431535 2149037 := bbase (se 3 (by rfl) ⟨402944, by rfl⟩ : syracuseStep 2149037 = 805889) (by norm_num)
theorem B3222197 : Blo 1431535 3222197 := bbase (se 5 (by rfl) ⟨151040, by rfl⟩ : syracuseStep 3222197 = 302081) (by norm_num)
theorem B2149061 : Blo 1431535 2149061 := bbase (se 4 (by rfl) ⟨201474, by rfl⟩ : syracuseStep 2149061 = 402949) (by norm_num)
theorem B1813205 : Blo 1431535 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B2149085 : Blo 1431535 2149085 := bbase (se 3 (by rfl) ⟨402953, by rfl⟩ : syracuseStep 2149085 = 805907) (by norm_num)
theorem B2149109 : Blo 1431535 2149109 := bbase (se 5 (by rfl) ⟨100739, by rfl⟩ : syracuseStep 2149109 = 201479) (by norm_num)
theorem B3222269 : Blo 1431535 3222269 := bbase (se 3 (by rfl) ⟨604175, by rfl⟩ : syracuseStep 3222269 = 1208351) (by norm_num)
theorem B1813261 : Blo 1431535 1813261 := bbase (se 3 (by rfl) ⟨339986, by rfl⟩ : syracuseStep 1813261 = 679973) (by norm_num)
theorem B2149133 : Blo 1431535 2149133 := bbase (se 3 (by rfl) ⟨402962, by rfl⟩ : syracuseStep 2149133 = 805925) (by norm_num)
theorem B3623717 : Blo 1431535 3623717 := bbase (se 4 (by rfl) ⟨339723, by rfl⟩ : syracuseStep 3623717 = 679447) (by norm_num)
theorem B3058469 : Blo 1431535 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B2149157 : Blo 1431535 2149157 := bbase (se 4 (by rfl) ⟨201483, by rfl⟩ : syracuseStep 2149157 = 402967) (by norm_num)
theorem B2149181 : Blo 1431535 2149181 := bbase (se 3 (by rfl) ⟨402971, by rfl⟩ : syracuseStep 2149181 = 805943) (by norm_num)
theorem B3222341 : Blo 1431535 3222341 := bbase (se 4 (by rfl) ⟨302094, by rfl⟩ : syracuseStep 3222341 = 604189) (by norm_num)
theorem B2149205 : Blo 1431535 2149205 := bbase (se 9 (by rfl) ⟨6296, by rfl⟩ : syracuseStep 2149205 = 12593) (by norm_num)
theorem B1813357 : Blo 1431535 1813357 := bbase (se 3 (by rfl) ⟨340004, by rfl⟩ : syracuseStep 1813357 = 680009) (by norm_num)
theorem B2149229 : Blo 1431535 2149229 := bbase (se 3 (by rfl) ⟨402980, by rfl⟩ : syracuseStep 2149229 = 805961) (by norm_num)
theorem B2149253 : Blo 1431535 2149253 := bbase (se 4 (by rfl) ⟨201492, by rfl⟩ : syracuseStep 2149253 = 402985) (by norm_num)
theorem B3222413 : Blo 1431535 3222413 := bbase (se 3 (by rfl) ⟨604202, by rfl⟩ : syracuseStep 3222413 = 1208405) (by norm_num)
theorem B1633181 : Blo 1431535 1633181 := bbase (se 3 (by rfl) ⟨306221, by rfl⟩ : syracuseStep 1633181 = 612443) (by norm_num)
theorem B2149277 : Blo 1431535 2149277 := bbase (se 3 (by rfl) ⟨402989, by rfl⟩ : syracuseStep 2149277 = 805979) (by norm_num)
theorem B7252901 : Blo 1431535 7252901 := bbase (se 4 (by rfl) ⟨679959, by rfl⟩ : syracuseStep 7252901 = 1359919) (by norm_num)
theorem B6122405 : Blo 1431535 6122405 := bbase (se 4 (by rfl) ⟨573975, by rfl⟩ : syracuseStep 6122405 = 1147951) (by norm_num)
theorem B2149301 : Blo 1431535 2149301 := bbase (se 5 (by rfl) ⟨100748, by rfl⟩ : syracuseStep 2149301 = 201497) (by norm_num)
theorem B4836293 : Blo 1431535 4836293 := bbase (se 4 (by rfl) ⟨453402, by rfl⟩ : syracuseStep 4836293 = 906805) (by norm_num)
theorem B2149325 : Blo 1431535 2149325 := bbase (se 3 (by rfl) ⟨402998, by rfl⟩ : syracuseStep 2149325 = 805997) (by norm_num)
theorem B3222485 : Blo 1431535 3222485 := bbase (se 7 (by rfl) ⟨37763, by rfl⟩ : syracuseStep 3222485 = 75527) (by norm_num)
theorem B2149349 : Blo 1431535 2149349 := bbase (se 4 (by rfl) ⟨201501, by rfl⟩ : syracuseStep 2149349 = 403003) (by norm_num)
theorem B2149373 : Blo 1431535 2149373 := bbase (se 3 (by rfl) ⟨403007, by rfl⟩ : syracuseStep 2149373 = 806015) (by norm_num)
theorem B2149397 : Blo 1431535 2149397 := bbase (se 6 (by rfl) ⟨50376, by rfl⟩ : syracuseStep 2149397 = 100753) (by norm_num)
theorem B1813529 : Blo 1431535 1813529 := bbase (se 2 (by rfl) ⟨680073, by rfl⟩ : syracuseStep 1813529 = 1360147) (by norm_num)
theorem B3058717 : Blo 1431535 3058717 := bbase (se 3 (by rfl) ⟨573509, by rfl⟩ : syracuseStep 3058717 = 1147019) (by norm_num)
theorem B3222557 : Blo 1431535 3222557 := bbase (se 3 (by rfl) ⟨604229, by rfl⟩ : syracuseStep 3222557 = 1208459) (by norm_num)
theorem B2149421 : Blo 1431535 2149421 := bbase (se 3 (by rfl) ⟨403016, by rfl⟩ : syracuseStep 2149421 = 806033) (by norm_num)
theorem B2149445 : Blo 1431535 2149445 := bbase (se 4 (by rfl) ⟨201510, by rfl⟩ : syracuseStep 2149445 = 403021) (by norm_num)
theorem B1813585 : Blo 1431535 1813585 := bbase (se 2 (by rfl) ⟨680094, by rfl⟩ : syracuseStep 1813585 = 1360189) (by norm_num)
theorem B3673181 : Blo 1431535 3673181 := bbase (se 3 (by rfl) ⟨688721, by rfl⟩ : syracuseStep 3673181 = 1377443) (by norm_num)
theorem B2149469 : Blo 1431535 2149469 := bbase (se 3 (by rfl) ⟨403025, by rfl⟩ : syracuseStep 2149469 = 806051) (by norm_num)
theorem B3222629 : Blo 1431535 3222629 := bbase (se 4 (by rfl) ⟨302121, by rfl⟩ : syracuseStep 3222629 = 604243) (by norm_num)
theorem B8154229 : Blo 1431535 8154229 := bbase (se 5 (by rfl) ⟨382229, by rfl⟩ : syracuseStep 8154229 = 764459) (by norm_num)
theorem B2149493 : Blo 1431535 2149493 := bbase (se 5 (by rfl) ⟨100757, by rfl⟩ : syracuseStep 2149493 = 201515) (by norm_num)
theorem B3624061 : Blo 1431535 3624061 := bbase (se 3 (by rfl) ⟨679511, by rfl⟩ : syracuseStep 3624061 = 1359023) (by norm_num)
theorem B2149517 : Blo 1431535 2149517 := bbase (se 3 (by rfl) ⟨403034, by rfl⟩ : syracuseStep 2149517 = 806069) (by norm_num)
theorem B2149541 : Blo 1431535 2149541 := bbase (se 4 (by rfl) ⟨201519, by rfl⟩ : syracuseStep 2149541 = 403039) (by norm_num)
theorem B3222701 : Blo 1431535 3222701 := bbase (se 3 (by rfl) ⟨604256, by rfl⟩ : syracuseStep 3222701 = 1208513) (by norm_num)
theorem B1813681 : Blo 1431535 1813681 := bbase (se 2 (by rfl) ⟨680130, by rfl⟩ : syracuseStep 1813681 = 1360261) (by norm_num)
theorem B2149565 : Blo 1431535 2149565 := bbase (se 3 (by rfl) ⟨403043, by rfl⟩ : syracuseStep 2149565 = 806087) (by norm_num)
theorem B2985157 : Blo 1431535 2985157 := bbase (se 4 (by rfl) ⟨279858, by rfl⟩ : syracuseStep 2985157 = 559717) (by norm_num)
theorem B2149589 : Blo 1431535 2149589 := bbase (se 7 (by rfl) ⟨25190, by rfl⟩ : syracuseStep 2149589 = 50381) (by norm_num)
theorem B3624173 : Blo 1431535 3624173 := bbase (se 3 (by rfl) ⟨679532, by rfl⟩ : syracuseStep 3624173 = 1359065) (by norm_num)
theorem B2149613 : Blo 1431535 2149613 := bbase (se 3 (by rfl) ⟨403052, by rfl⟩ : syracuseStep 2149613 = 806105) (by norm_num)
theorem B3222773 : Blo 1431535 3222773 := bbase (se 5 (by rfl) ⟨151067, by rfl⟩ : syracuseStep 3222773 = 302135) (by norm_num)
theorem B2149637 : Blo 1431535 2149637 := bbase (se 4 (by rfl) ⟨201528, by rfl⟩ : syracuseStep 2149637 = 403057) (by norm_num)
theorem B5442821 : Blo 1431535 5442821 := bbase (se 4 (by rfl) ⟨510264, by rfl⟩ : syracuseStep 5442821 = 1020529) (by norm_num)
theorem B2149661 : Blo 1431535 2149661 := bbase (se 3 (by rfl) ⟨403061, by rfl⟩ : syracuseStep 2149661 = 806123) (by norm_num)
theorem B2149685 : Blo 1431535 2149685 := bbase (se 5 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 2149685 = 201533) (by norm_num)
theorem B3222845 : Blo 1431535 3222845 := bbase (se 3 (by rfl) ⟨604283, by rfl⟩ : syracuseStep 3222845 = 1208567) (by norm_num)
theorem B2149709 : Blo 1431535 2149709 := bbase (se 3 (by rfl) ⟨403070, by rfl⟩ : syracuseStep 2149709 = 806141) (by norm_num)
theorem B1813853 : Blo 1431535 1813853 := bbase (se 3 (by rfl) ⟨340097, by rfl⟩ : syracuseStep 1813853 = 680195) (by norm_num)
theorem B2149733 : Blo 1431535 2149733 := bbase (se 4 (by rfl) ⟨201537, by rfl⟩ : syracuseStep 2149733 = 403075) (by norm_num)
theorem B4836725 : Blo 1431535 4836725 := bbase (se 5 (by rfl) ⟨226721, by rfl⟩ : syracuseStep 4836725 = 453443) (by norm_num)
theorem B2149757 : Blo 1431535 2149757 := bbase (se 3 (by rfl) ⟨403079, by rfl⟩ : syracuseStep 2149757 = 806159) (by norm_num)
theorem B3222917 : Blo 1431535 3222917 := bbase (se 4 (by rfl) ⟨302148, by rfl⟩ : syracuseStep 3222917 = 604297) (by norm_num)
theorem B2149781 : Blo 1431535 2149781 := bbase (se 6 (by rfl) ⟨50385, by rfl⟩ : syracuseStep 2149781 = 100771) (by norm_num)
theorem B1813909 : Blo 1431535 1813909 := bbase (se 6 (by rfl) ⟨42513, by rfl⟩ : syracuseStep 1813909 = 85027) (by norm_num)
theorem B3444133 : Blo 1431535 3444133 := bbase (se 4 (by rfl) ⟨322887, by rfl⟩ : syracuseStep 3444133 = 645775) (by norm_num)
theorem B3624365 : Blo 1431535 3624365 := bbase (se 3 (by rfl) ⟨679568, by rfl⟩ : syracuseStep 3624365 = 1359137) (by norm_num)
theorem B2149805 : Blo 1431535 2149805 := bbase (se 3 (by rfl) ⟨403088, by rfl⟩ : syracuseStep 2149805 = 806177) (by norm_num)
theorem B6204869 : Blo 1431535 6204869 := bbase (se 4 (by rfl) ⟨581706, by rfl⟩ : syracuseStep 6204869 = 1163413) (by norm_num)
theorem B2149829 : Blo 1431535 2149829 := bbase (se 4 (by rfl) ⟨201546, by rfl⟩ : syracuseStep 2149829 = 403093) (by norm_num)
theorem B3222989 : Blo 1431535 3222989 := bbase (se 3 (by rfl) ⟨604310, by rfl⟩ : syracuseStep 3222989 = 1208621) (by norm_num)
theorem B2149853 : Blo 1431535 2149853 := bbase (se 3 (by rfl) ⟨403097, by rfl⟩ : syracuseStep 2149853 = 806195) (by norm_num)
theorem B1633765 : Blo 1431535 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B2149877 : Blo 1431535 2149877 := bbase (se 5 (by rfl) ⟨100775, by rfl⟩ : syracuseStep 2149877 = 201551) (by norm_num)
theorem B1814005 : Blo 1431535 1814005 := bbase (se 5 (by rfl) ⟨85031, by rfl⟩ : syracuseStep 1814005 = 170063) (by norm_num)
theorem B2756101 : Blo 1431535 2756101 := bbase (se 4 (by rfl) ⟨258384, by rfl⟩ : syracuseStep 2756101 = 516769) (by norm_num)
theorem B2149901 : Blo 1431535 2149901 := bbase (se 3 (by rfl) ⟨403106, by rfl⟩ : syracuseStep 2149901 = 806213) (by norm_num)
theorem B3059221 : Blo 1431535 3059221 := bbase (se 6 (by rfl) ⟨71700, by rfl⟩ : syracuseStep 3059221 = 143401) (by norm_num)
theorem B3223061 : Blo 1431535 3223061 := bbase (se 6 (by rfl) ⟨75540, by rfl⟩ : syracuseStep 3223061 = 151081) (by norm_num)
theorem B2149925 : Blo 1431535 2149925 := bbase (se 4 (by rfl) ⟨201555, by rfl⟩ : syracuseStep 2149925 = 403111) (by norm_num)
theorem B5164597 : Blo 1431535 5164597 := bbase (se 5 (by rfl) ⟨242090, by rfl⟩ : syracuseStep 5164597 = 484181) (by norm_num)
theorem B2149949 : Blo 1431535 2149949 := bbase (se 3 (by rfl) ⟨403115, by rfl⟩ : syracuseStep 2149949 = 806231) (by norm_num)
theorem B2149973 : Blo 1431535 2149973 := bbase (se 8 (by rfl) ⟨12597, by rfl⟩ : syracuseStep 2149973 = 25195) (by norm_num)
theorem B3223133 : Blo 1431535 3223133 := bbase (se 3 (by rfl) ⟨604337, by rfl⟩ : syracuseStep 3223133 = 1208675) (by norm_num)
theorem B5230181 : Blo 1431535 5230181 := bbase (se 4 (by rfl) ⟨490329, by rfl⟩ : syracuseStep 5230181 = 980659) (by norm_num)
theorem B2149997 : Blo 1431535 2149997 := bbase (se 3 (by rfl) ⟨403124, by rfl⟩ : syracuseStep 2149997 = 806249) (by norm_num)
theorem B2150021 : Blo 1431535 2150021 := bbase (se 4 (by rfl) ⟨201564, by rfl⟩ : syracuseStep 2150021 = 403129) (by norm_num)
theorem B2150045 : Blo 1431535 2150045 := bbase (se 3 (by rfl) ⟨403133, by rfl⟩ : syracuseStep 2150045 = 806267) (by norm_num)
theorem B1814177 : Blo 1431535 1814177 := bbase (se 2 (by rfl) ⟨680316, by rfl⟩ : syracuseStep 1814177 = 1360633) (by norm_num)
theorem B3223205 : Blo 1431535 3223205 := bbase (se 4 (by rfl) ⟨302175, by rfl⟩ : syracuseStep 3223205 = 604351) (by norm_num)
theorem B2150069 : Blo 1431535 2150069 := bbase (se 5 (by rfl) ⟨100784, by rfl⟩ : syracuseStep 2150069 = 201569) (by norm_num)
theorem B2150093 : Blo 1431535 2150093 := bbase (se 3 (by rfl) ⟨403142, by rfl⟩ : syracuseStep 2150093 = 806285) (by norm_num)
theorem B1814233 : Blo 1431535 1814233 := bbase (se 2 (by rfl) ⟨680337, by rfl⟩ : syracuseStep 1814233 = 1360675) (by norm_num)
theorem B2150117 : Blo 1431535 2150117 := bbase (se 4 (by rfl) ⟨201573, by rfl⟩ : syracuseStep 2150117 = 403147) (by norm_num)
theorem B3223277 : Blo 1431535 3223277 := bbase (se 3 (by rfl) ⟨604364, by rfl⟩ : syracuseStep 3223277 = 1208729) (by norm_num)
theorem B2150141 : Blo 1431535 2150141 := bbase (se 3 (by rfl) ⟨403151, by rfl⟩ : syracuseStep 2150141 = 806303) (by norm_num)
theorem B3624709 : Blo 1431535 3624709 := bbase (se 4 (by rfl) ⟨339816, by rfl⟩ : syracuseStep 3624709 = 679633) (by norm_num)
theorem B2150165 : Blo 1431535 2150165 := bbase (se 6 (by rfl) ⟨50394, by rfl⟩ : syracuseStep 2150165 = 100789) (by norm_num)
theorem B4837157 : Blo 1431535 4837157 := bbase (se 4 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 4837157 = 906967) (by norm_num)
theorem B2150189 : Blo 1431535 2150189 := bbase (se 3 (by rfl) ⟨403160, by rfl⟩ : syracuseStep 2150189 = 806321) (by norm_num)
theorem B3223349 : Blo 1431535 3223349 := bbase (se 5 (by rfl) ⟨151094, by rfl⟩ : syracuseStep 3223349 = 302189) (by norm_num)
theorem B5812021 : Blo 1431535 5812021 := bbase (se 5 (by rfl) ⟨272438, by rfl⟩ : syracuseStep 5812021 = 544877) (by norm_num)
theorem B2150213 : Blo 1431535 2150213 := bbase (se 4 (by rfl) ⟨201582, by rfl⟩ : syracuseStep 2150213 = 403165) (by norm_num)
theorem B2150237 : Blo 1431535 2150237 := bbase (se 3 (by rfl) ⟨403169, by rfl⟩ : syracuseStep 2150237 = 806339) (by norm_num)
theorem B2723701 : Blo 1431535 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B3624821 : Blo 1431535 3624821 := bbase (se 5 (by rfl) ⟨169913, by rfl⟩ : syracuseStep 3624821 = 339827) (by norm_num)
theorem B2150261 : Blo 1431535 2150261 := bbase (se 5 (by rfl) ⟨100793, by rfl⟩ : syracuseStep 2150261 = 201587) (by norm_num)
theorem B3223421 : Blo 1431535 3223421 := bbase (se 3 (by rfl) ⟨604391, by rfl⟩ : syracuseStep 3223421 = 1208783) (by norm_num)
theorem B1634185 : Blo 1431535 1634185 := bbase (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) (by norm_num)
theorem B2150285 : Blo 1431535 2150285 := bbase (se 3 (by rfl) ⟨403178, by rfl⟩ : syracuseStep 2150285 = 806357) (by norm_num)
theorem B26480533 : Blo 1431535 26480533 := bbase (se 6 (by rfl) ⟨620637, by rfl⟩ : syracuseStep 26480533 = 1241275) (by norm_num)
theorem B10882997 : Blo 1431535 10882997 := bbase (se 5 (by rfl) ⟨510140, by rfl⟩ : syracuseStep 10882997 = 1020281) (by norm_num)
theorem B3223493 : Blo 1431535 3223493 := bbase (se 4 (by rfl) ⟨302202, by rfl⟩ : syracuseStep 3223493 = 604405) (by norm_num)
theorem B1839073 : Blo 1431535 1839073 := bbase (se 2 (by rfl) ⟨689652, by rfl⟩ : syracuseStep 1839073 = 1379305) (by norm_num)
theorem B5230565 : Blo 1431535 5230565 := bbase (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) (by norm_num)
theorem B3223565 : Blo 1431535 3223565 := bbase (se 3 (by rfl) ⟨604418, by rfl⟩ : syracuseStep 3223565 = 1208837) (by norm_num)
theorem B7745557 : Blo 1431535 7745557 := bbase (se 6 (by rfl) ⟨181536, by rfl⟩ : syracuseStep 7745557 = 363073) (by norm_num)
theorem B3625013 : Blo 1431535 3625013 := bbase (se 5 (by rfl) ⟨169922, by rfl⟩ : syracuseStep 3625013 = 339845) (by norm_num)
theorem B3223637 : Blo 1431535 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B3223709 : Blo 1431535 3223709 := bbase (se 3 (by rfl) ⟨604445, by rfl⟩ : syracuseStep 3223709 = 1208891) (by norm_num)
theorem B7254197 : Blo 1431535 7254197 := bbase (se 5 (by rfl) ⟨340040, by rfl⟩ : syracuseStep 7254197 = 680081) (by norm_num)
theorem B4591829 : Blo 1431535 4591829 := bbase (se 7 (by rfl) ⟨53810, by rfl⟩ : syracuseStep 4591829 = 107621) (by norm_num)
theorem B4837589 : Blo 1431535 4837589 := bbase (se 7 (by rfl) ⟨56690, by rfl⟩ : syracuseStep 4837589 = 113381) (by norm_num)
theorem B3223781 : Blo 1431535 3223781 := bbase (se 4 (by rfl) ⟨302229, by rfl⟩ : syracuseStep 3223781 = 604459) (by norm_num)
theorem B2617589 : Blo 1431535 2617589 := bbase (se 5 (by rfl) ⟨122699, by rfl⟩ : syracuseStep 2617589 = 245399) (by norm_num)
theorem B3223853 : Blo 1431535 3223853 := bbase (se 3 (by rfl) ⟨604472, by rfl⟩ : syracuseStep 3223853 = 1208945) (by norm_num)
theorem B10875221 : Blo 1431535 10875221 := bbase (se 10 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 10875221 = 31861) (by norm_num)
theorem B7352677 : Blo 1431535 7352677 := bbase (se 4 (by rfl) ⟨689313, by rfl⟩ : syracuseStep 7352677 = 1378627) (by norm_num)
theorem B13767029 : Blo 1431535 13767029 := bbase (se 5 (by rfl) ⟨645329, by rfl⟩ : syracuseStep 13767029 = 1290659) (by norm_num)
theorem B3223925 : Blo 1431535 3223925 := bbase (se 5 (by rfl) ⟨151121, by rfl⟩ : syracuseStep 3223925 = 302243) (by norm_num)
theorem B3625357 : Blo 1431535 3625357 := bbase (se 3 (by rfl) ⟨679754, by rfl⟩ : syracuseStep 3625357 = 1359509) (by norm_num)
theorem B3060109 : Blo 1431535 3060109 := bbase (se 3 (by rfl) ⟨573770, by rfl⟩ : syracuseStep 3060109 = 1147541) (by norm_num)
theorem B3223997 : Blo 1431535 3223997 := bbase (se 3 (by rfl) ⟨604499, by rfl⟩ : syracuseStep 3223997 = 1208999) (by norm_num)
theorem B3625469 : Blo 1431535 3625469 := bbase (se 3 (by rfl) ⟨679775, by rfl⟩ : syracuseStep 3625469 = 1359551) (by norm_num)
theorem B3224069 : Blo 1431535 3224069 := bbase (se 4 (by rfl) ⟨302256, by rfl⟩ : syracuseStep 3224069 = 604513) (by norm_num)
theorem B4354613 : Blo 1431535 4354613 := bbase (se 5 (by rfl) ⟨204122, by rfl⟩ : syracuseStep 4354613 = 408245) (by norm_num)
theorem B3265085 : Blo 1431535 3265085 := bbase (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) (by norm_num)
theorem B3224141 : Blo 1431535 3224141 := bbase (se 3 (by rfl) ⟨604526, by rfl⟩ : syracuseStep 3224141 = 1209053) (by norm_num)
theorem B16536149 : Blo 1431535 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B4838021 : Blo 1431535 4838021 := bbase (se 4 (by rfl) ⟨453564, by rfl⟩ : syracuseStep 4838021 = 907129) (by norm_num)
theorem B3224213 : Blo 1431535 3224213 := bbase (se 6 (by rfl) ⟨75567, by rfl⟩ : syracuseStep 3224213 = 151135) (by norm_num)
theorem B3101357 : Blo 1431535 3101357 := bbase (se 3 (by rfl) ⟨581504, by rfl⟩ : syracuseStep 3101357 = 1163009) (by norm_num)
theorem B12235445 : Blo 1431535 12235445 := bbase (se 5 (by rfl) ⟨573536, by rfl⟩ : syracuseStep 12235445 = 1147073) (by norm_num)
theorem B3625661 : Blo 1431535 3625661 := bbase (se 3 (by rfl) ⟨679811, by rfl⟩ : syracuseStep 3625661 = 1359623) (by norm_num)
theorem B6206165 : Blo 1431535 6206165 := bbase (se 7 (by rfl) ⟨72728, by rfl⟩ : syracuseStep 6206165 = 145457) (by norm_num)
theorem B3224285 : Blo 1431535 3224285 := bbase (se 3 (by rfl) ⟨604553, by rfl⟩ : syracuseStep 3224285 = 1209107) (by norm_num)
theorem B7746293 : Blo 1431535 7746293 := bbase (se 5 (by rfl) ⟨363107, by rfl⟩ : syracuseStep 7746293 = 726215) (by norm_num)
theorem B1610509 : Blo 1431535 1610509 := bbase (se 3 (by rfl) ⟨301970, by rfl⟩ : syracuseStep 1610509 = 603941) (by norm_num)
theorem B3224357 : Blo 1431535 3224357 := bbase (se 4 (by rfl) ⟨302283, by rfl⟩ : syracuseStep 3224357 = 604567) (by norm_num)
theorem B1610545 : Blo 1431535 1610545 := bbase (se 2 (by rfl) ⟨603954, by rfl⟩ : syracuseStep 1610545 = 1207909) (by norm_num)
theorem B1610581 : Blo 1431535 1610581 := bbase (se 9 (by rfl) ⟨4718, by rfl⟩ : syracuseStep 1610581 = 9437) (by norm_num)
theorem B3674965 : Blo 1431535 3674965 := bbase (se 9 (by rfl) ⟨10766, by rfl⟩ : syracuseStep 3674965 = 21533) (by norm_num)
theorem B3224429 : Blo 1431535 3224429 := bbase (se 3 (by rfl) ⟨604580, by rfl⟩ : syracuseStep 3224429 = 1209161) (by norm_num)
theorem B1610617 : Blo 1431535 1610617 := bbase (se 2 (by rfl) ⟨603981, by rfl⟩ : syracuseStep 1610617 = 1207963) (by norm_num)
theorem B3060605 : Blo 1431535 3060605 := bbase (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) (by norm_num)
theorem B1610653 : Blo 1431535 1610653 := bbase (se 3 (by rfl) ⟨301997, by rfl⟩ : syracuseStep 1610653 = 603995) (by norm_num)
theorem B3224501 : Blo 1431535 3224501 := bbase (se 5 (by rfl) ⟨151148, by rfl⟩ : syracuseStep 3224501 = 302297) (by norm_num)
theorem B1610689 : Blo 1431535 1610689 := bbase (se 2 (by rfl) ⟨604008, by rfl⟩ : syracuseStep 1610689 = 1208017) (by norm_num)
theorem B1610725 : Blo 1431535 1610725 := bbase (se 4 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 1610725 = 302011) (by norm_num)
theorem B3224573 : Blo 1431535 3224573 := bbase (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) (by norm_num)
theorem B1610761 : Blo 1431535 1610761 := bbase (se 2 (by rfl) ⟨604035, by rfl⟩ : syracuseStep 1610761 = 1208071) (by norm_num)
theorem B3626005 : Blo 1431535 3626005 := bbase (se 6 (by rfl) ⟨84984, by rfl⟩ : syracuseStep 3626005 = 169969) (by norm_num)
theorem B1610797 : Blo 1431535 1610797 := bbase (se 3 (by rfl) ⟨302024, by rfl⟩ : syracuseStep 1610797 = 604049) (by norm_num)
theorem B8156213 : Blo 1431535 8156213 := bbase (se 5 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 8156213 = 764645) (by norm_num)
theorem B3224645 : Blo 1431535 3224645 := bbase (se 4 (by rfl) ⟨302310, by rfl⟩ : syracuseStep 3224645 = 604621) (by norm_num)
theorem B1610833 : Blo 1431535 1610833 := bbase (se 2 (by rfl) ⟨604062, by rfl⟩ : syracuseStep 1610833 = 1208125) (by norm_num)
theorem B5436517 : Blo 1431535 5436517 := bbase (se 4 (by rfl) ⟨509673, by rfl⟩ : syracuseStep 5436517 = 1019347) (by norm_num)
theorem B1610869 : Blo 1431535 1610869 := bbase (se 5 (by rfl) ⟨75509, by rfl⟩ : syracuseStep 1610869 = 151019) (by norm_num)
theorem B1528961 : Blo 1431535 1528961 := bbase (se 2 (by rfl) ⟨573360, by rfl⟩ : syracuseStep 1528961 = 1146721) (by norm_num)
theorem B3626117 : Blo 1431535 3626117 := bbase (se 4 (by rfl) ⟨339948, by rfl⟩ : syracuseStep 3626117 = 679897) (by norm_num)
theorem B3224717 : Blo 1431535 3224717 := bbase (se 3 (by rfl) ⟨604634, by rfl⟩ : syracuseStep 3224717 = 1209269) (by norm_num)
theorem B1610905 : Blo 1431535 1610905 := bbase (se 2 (by rfl) ⟨604089, by rfl⟩ : syracuseStep 1610905 = 1208179) (by norm_num)
theorem B1610941 : Blo 1431535 1610941 := bbase (se 3 (by rfl) ⟨302051, by rfl⟩ : syracuseStep 1610941 = 604103) (by norm_num)
theorem B3224789 : Blo 1431535 3224789 := bbase (se 7 (by rfl) ⟨37790, by rfl⟩ : syracuseStep 3224789 = 75581) (by norm_num)
theorem B1610977 : Blo 1431535 1610977 := bbase (se 2 (by rfl) ⟨604116, by rfl⟩ : syracuseStep 1610977 = 1208233) (by norm_num)
theorem B4412645 : Blo 1431535 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B1611013 : Blo 1431535 1611013 := bbase (se 4 (by rfl) ⟨151032, by rfl⟩ : syracuseStep 1611013 = 302065) (by norm_num)
theorem B6116629 : Blo 1431535 6116629 := bbase (se 6 (by rfl) ⟨143358, by rfl⟩ : syracuseStep 6116629 = 286717) (by norm_num)
theorem B3224861 : Blo 1431535 3224861 := bbase (se 3 (by rfl) ⟨604661, by rfl⟩ : syracuseStep 3224861 = 1209323) (by norm_num)
theorem B1611049 : Blo 1431535 1611049 := bbase (se 2 (by rfl) ⟨604143, by rfl⟩ : syracuseStep 1611049 = 1208287) (by norm_num)
theorem B3626309 : Blo 1431535 3626309 := bbase (se 4 (by rfl) ⟨339966, by rfl⟩ : syracuseStep 3626309 = 679933) (by norm_num)
theorem B1611085 : Blo 1431535 1611085 := bbase (se 3 (by rfl) ⟨302078, by rfl⟩ : syracuseStep 1611085 = 604157) (by norm_num)
theorem B3224933 : Blo 1431535 3224933 := bbase (se 4 (by rfl) ⟨302337, by rfl⟩ : syracuseStep 3224933 = 604675) (by norm_num)
theorem B1611121 : Blo 1431535 1611121 := bbase (se 2 (by rfl) ⟨604170, by rfl⟩ : syracuseStep 1611121 = 1208341) (by norm_num)
theorem B1529209 : Blo 1431535 1529209 := bbase (se 2 (by rfl) ⟨573453, by rfl⟩ : syracuseStep 1529209 = 1146907) (by norm_num)
theorem B5436821 : Blo 1431535 5436821 := bbase (se 6 (by rfl) ⟨127425, by rfl⟩ : syracuseStep 5436821 = 254851) (by norm_num)
theorem B1611157 : Blo 1431535 1611157 := bbase (se 6 (by rfl) ⟨37761, by rfl⟩ : syracuseStep 1611157 = 75523) (by norm_num)
theorem B3225005 : Blo 1431535 3225005 := bbase (se 3 (by rfl) ⟨604688, by rfl⟩ : syracuseStep 3225005 = 1209377) (by norm_num)
theorem B1611193 : Blo 1431535 1611193 := bbase (se 2 (by rfl) ⟨604197, by rfl⟩ : syracuseStep 1611193 = 1208395) (by norm_num)
theorem B7255493 : Blo 1431535 7255493 := bbase (se 4 (by rfl) ⟨680202, by rfl⟩ : syracuseStep 7255493 = 1360405) (by norm_num)
theorem B4077013 : Blo 1431535 4077013 := bbase (se 7 (by rfl) ⟨47777, by rfl⟩ : syracuseStep 4077013 = 95555) (by norm_num)
theorem B1611229 : Blo 1431535 1611229 := bbase (se 3 (by rfl) ⟨302105, by rfl⟩ : syracuseStep 1611229 = 604211) (by norm_num)
theorem B9180661 : Blo 1431535 9180661 := bbase (se 5 (by rfl) ⟨430343, by rfl⟩ : syracuseStep 9180661 = 860687) (by norm_num)
theorem B3225077 : Blo 1431535 3225077 := bbase (se 5 (by rfl) ⟨151175, by rfl⟩ : syracuseStep 3225077 = 302351) (by norm_num)
theorem B1611265 : Blo 1431535 1611265 := bbase (se 2 (by rfl) ⟨604224, by rfl⟩ : syracuseStep 1611265 = 1208449) (by norm_num)
theorem B18355733 : Blo 1431535 18355733 := bbase (se 6 (by rfl) ⟨430212, by rfl⟩ : syracuseStep 18355733 = 860425) (by norm_num)
theorem B1611301 : Blo 1431535 1611301 := bbase (se 4 (by rfl) ⟨151059, by rfl⟩ : syracuseStep 1611301 = 302119) (by norm_num)
theorem B3225149 : Blo 1431535 3225149 := bbase (se 3 (by rfl) ⟨604715, by rfl⟩ : syracuseStep 3225149 = 1209431) (by norm_num)
theorem B1611337 : Blo 1431535 1611337 := bbase (se 2 (by rfl) ⟨604251, by rfl⟩ : syracuseStep 1611337 = 1208503) (by norm_num)
theorem B1611373 : Blo 1431535 1611373 := bbase (se 3 (by rfl) ⟨302132, by rfl⟩ : syracuseStep 1611373 = 604265) (by norm_num)
theorem B3225221 : Blo 1431535 3225221 := bbase (se 4 (by rfl) ⟨302364, by rfl⟩ : syracuseStep 3225221 = 604729) (by norm_num)
theorem B1611409 : Blo 1431535 1611409 := bbase (se 2 (by rfl) ⟨604278, by rfl⟩ : syracuseStep 1611409 = 1208557) (by norm_num)
theorem B2176669 : Blo 1431535 2176669 := bbase (se 3 (by rfl) ⟨408125, by rfl⟩ : syracuseStep 2176669 = 816251) (by norm_num)
theorem B3626653 : Blo 1431535 3626653 := bbase (se 3 (by rfl) ⟨679997, by rfl⟩ : syracuseStep 3626653 = 1359995) (by norm_num)
theorem B1611445 : Blo 1431535 1611445 := bbase (se 5 (by rfl) ⟨75536, by rfl⟩ : syracuseStep 1611445 = 151073) (by norm_num)
theorem B3225293 : Blo 1431535 3225293 := bbase (se 3 (by rfl) ⟨604742, by rfl⟩ : syracuseStep 3225293 = 1209485) (by norm_num)
theorem B1611481 : Blo 1431535 1611481 := bbase (se 2 (by rfl) ⟨604305, by rfl⟩ : syracuseStep 1611481 = 1208611) (by norm_num)
theorem B3061493 : Blo 1431535 3061493 := bbase (se 5 (by rfl) ⟨143507, by rfl⟩ : syracuseStep 3061493 = 287015) (by norm_num)
theorem B1611517 : Blo 1431535 1611517 := bbase (se 3 (by rfl) ⟨302159, by rfl⟩ : syracuseStep 1611517 = 604319) (by norm_num)
theorem B3626765 : Blo 1431535 3626765 := bbase (se 3 (by rfl) ⟨680018, by rfl⟩ : syracuseStep 3626765 = 1360037) (by norm_num)
theorem B3225365 : Blo 1431535 3225365 := bbase (se 6 (by rfl) ⟨75594, by rfl⟩ : syracuseStep 3225365 = 151189) (by norm_num)
theorem B1611553 : Blo 1431535 1611553 := bbase (se 2 (by rfl) ⟨604332, by rfl⟩ : syracuseStep 1611553 = 1208665) (by norm_num)
theorem B1529653 : Blo 1431535 1529653 := bbase (se 5 (by rfl) ⟨71702, by rfl⟩ : syracuseStep 1529653 = 143405) (by norm_num)
theorem B1611589 : Blo 1431535 1611589 := bbase (se 4 (by rfl) ⟨151086, by rfl⟩ : syracuseStep 1611589 = 302173) (by norm_num)
theorem B3225437 : Blo 1431535 3225437 := bbase (se 3 (by rfl) ⟨604769, by rfl⟩ : syracuseStep 3225437 = 1209539) (by norm_num)
theorem B7247717 : Blo 1431535 7247717 := bbase (se 4 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 7247717 = 1358947) (by norm_num)
theorem B1611625 : Blo 1431535 1611625 := bbase (se 2 (by rfl) ⟨604359, by rfl⟩ : syracuseStep 1611625 = 1208719) (by norm_num)
theorem B3676013 : Blo 1431535 3676013 := bbase (se 3 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 3676013 = 1378505) (by norm_num)
theorem B3061613 : Blo 1431535 3061613 := bbase (se 3 (by rfl) ⟨574052, by rfl⟩ : syracuseStep 3061613 = 1148105) (by norm_num)
theorem B1529713 : Blo 1431535 1529713 := bbase (se 2 (by rfl) ⟨573642, by rfl⟩ : syracuseStep 1529713 = 1147285) (by norm_num)
theorem B10327925 : Blo 1431535 10327925 := bbase (se 5 (by rfl) ⟨484121, by rfl⟩ : syracuseStep 10327925 = 968243) (by norm_num)
theorem B1611661 : Blo 1431535 1611661 := bbase (se 3 (by rfl) ⟨302186, by rfl⟩ : syracuseStep 1611661 = 604373) (by norm_num)
theorem B2758549 : Blo 1431535 2758549 := bbase (se 6 (by rfl) ⟨64653, by rfl⟩ : syracuseStep 2758549 = 129307) (by norm_num)
theorem B1611697 : Blo 1431535 1611697 := bbase (se 2 (by rfl) ⟨604386, by rfl⟩ : syracuseStep 1611697 = 1208773) (by norm_num)
theorem B3626957 : Blo 1431535 3626957 := bbase (se 3 (by rfl) ⟨680054, by rfl⟩ : syracuseStep 3626957 = 1360109) (by norm_num)
theorem B1611733 : Blo 1431535 1611733 := bbase (se 7 (by rfl) ⟨18887, by rfl⟩ : syracuseStep 1611733 = 37775) (by norm_num)
theorem B1611769 : Blo 1431535 1611769 := bbase (se 2 (by rfl) ⟨604413, by rfl⟩ : syracuseStep 1611769 = 1208827) (by norm_num)
theorem B1611805 : Blo 1431535 1611805 := bbase (se 3 (by rfl) ⟨302213, by rfl⟩ : syracuseStep 1611805 = 604427) (by norm_num)
theorem B1611841 : Blo 1431535 1611841 := bbase (se 2 (by rfl) ⟨604440, by rfl⟩ : syracuseStep 1611841 = 1208881) (by norm_num)
theorem B5232725 : Blo 1431535 5232725 := bbase (se 8 (by rfl) ⟨30660, by rfl⟩ : syracuseStep 5232725 = 61321) (by norm_num)
theorem B3266653 : Blo 1431535 3266653 := bbase (se 3 (by rfl) ⟨612497, by rfl⟩ : syracuseStep 3266653 = 1224995) (by norm_num)
theorem B1611877 : Blo 1431535 1611877 := bbase (se 4 (by rfl) ⟨151113, by rfl⟩ : syracuseStep 1611877 = 302227) (by norm_num)
theorem B1611913 : Blo 1431535 1611913 := bbase (se 2 (by rfl) ⟨604467, by rfl⟩ : syracuseStep 1611913 = 1208935) (by norm_num)
theorem B1530029 : Blo 1431535 1530029 := bbase (se 3 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 1530029 = 573761) (by norm_num)
theorem B1611949 : Blo 1431535 1611949 := bbase (se 3 (by rfl) ⟨302240, by rfl⟩ : syracuseStep 1611949 = 604481) (by norm_num)
theorem B1611985 : Blo 1431535 1611985 := bbase (se 2 (by rfl) ⟨604494, by rfl⟩ : syracuseStep 1611985 = 1208989) (by norm_num)
theorem B13760725 : Blo 1431535 13760725 := bbase (se 7 (by rfl) ⟨161258, by rfl⟩ : syracuseStep 13760725 = 322517) (by norm_num)
theorem B1612021 : Blo 1431535 1612021 := bbase (se 5 (by rfl) ⟨75563, by rfl⟩ : syracuseStep 1612021 = 151127) (by norm_num)
theorem B1612057 : Blo 1431535 1612057 := bbase (se 2 (by rfl) ⟨604521, by rfl⟩ : syracuseStep 1612057 = 1209043) (by norm_num)
theorem B3627301 : Blo 1431535 3627301 := bbase (se 4 (by rfl) ⟨340059, by rfl⟩ : syracuseStep 3627301 = 680119) (by norm_num)
theorem B4831541 : Blo 1431535 4831541 := bbase (se 5 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 4831541 = 452957) (by norm_num)
theorem B1612093 : Blo 1431535 1612093 := bbase (se 3 (by rfl) ⟨302267, by rfl⟩ : syracuseStep 1612093 = 604535) (by norm_num)
theorem B5511493 : Blo 1431535 5511493 := bbase (se 4 (by rfl) ⟨516702, by rfl⟩ : syracuseStep 5511493 = 1033405) (by norm_num)
theorem B1612129 : Blo 1431535 1612129 := bbase (se 2 (by rfl) ⟨604548, by rfl⟩ : syracuseStep 1612129 = 1209097) (by norm_num)
theorem B1612165 : Blo 1431535 1612165 := bbase (se 4 (by rfl) ⟨151140, by rfl⟩ : syracuseStep 1612165 = 302281) (by norm_num)
theorem B3627413 : Blo 1431535 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B1612201 : Blo 1431535 1612201 := bbase (se 2 (by rfl) ⟨604575, by rfl⟩ : syracuseStep 1612201 = 1209151) (by norm_num)
theorem B1612237 : Blo 1431535 1612237 := bbase (se 3 (by rfl) ⟨302294, by rfl⟩ : syracuseStep 1612237 = 604589) (by norm_num)
theorem B1612273 : Blo 1431535 1612273 := bbase (se 2 (by rfl) ⟨604602, by rfl⟩ : syracuseStep 1612273 = 1209205) (by norm_num)
theorem B1612309 : Blo 1431535 1612309 := bbase (se 6 (by rfl) ⟨37788, by rfl⟩ : syracuseStep 1612309 = 75577) (by norm_num)
theorem B4078117 : Blo 1431535 4078117 := bbase (se 4 (by rfl) ⟨382323, by rfl⟩ : syracuseStep 4078117 = 764647) (by norm_num)
theorem B1612345 : Blo 1431535 1612345 := bbase (se 2 (by rfl) ⟨604629, by rfl⟩ : syracuseStep 1612345 = 1209259) (by norm_num)
theorem B3627605 : Blo 1431535 3627605 := bbase (se 8 (by rfl) ⟨21255, by rfl⟩ : syracuseStep 3627605 = 42511) (by norm_num)
theorem B1612381 : Blo 1431535 1612381 := bbase (se 3 (by rfl) ⟨302321, by rfl⟩ : syracuseStep 1612381 = 604643) (by norm_num)
theorem B1530473 : Blo 1431535 1530473 := bbase (se 2 (by rfl) ⟨573927, by rfl⟩ : syracuseStep 1530473 = 1147855) (by norm_num)
theorem B1612417 : Blo 1431535 1612417 := bbase (se 2 (by rfl) ⟨604656, by rfl⟩ : syracuseStep 1612417 = 1209313) (by norm_num)
theorem B2718373 : Blo 1431535 2718373 := bbase (se 4 (by rfl) ⟨254847, by rfl⟩ : syracuseStep 2718373 = 509695) (by norm_num)
theorem B1530533 : Blo 1431535 1530533 := bbase (se 4 (by rfl) ⟨143487, by rfl⟩ : syracuseStep 1530533 = 286975) (by norm_num)
theorem B1612453 : Blo 1431535 1612453 := bbase (se 4 (by rfl) ⟨151167, by rfl⟩ : syracuseStep 1612453 = 302335) (by norm_num)
theorem B1612489 : Blo 1431535 1612489 := bbase (se 2 (by rfl) ⟨604683, by rfl⟩ : syracuseStep 1612489 = 1209367) (by norm_num)
theorem B7256789 : Blo 1431535 7256789 := bbase (se 7 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 7256789 = 170081) (by norm_num)
theorem B4831973 : Blo 1431535 4831973 := bbase (se 4 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 4831973 = 905995) (by norm_num)
theorem B1612525 : Blo 1431535 1612525 := bbase (se 3 (by rfl) ⟨302348, by rfl⟩ : syracuseStep 1612525 = 604697) (by norm_num)
theorem B1612561 : Blo 1431535 1612561 := bbase (se 2 (by rfl) ⟨604710, by rfl⟩ : syracuseStep 1612561 = 1209421) (by norm_num)
theorem B1530661 : Blo 1431535 1530661 := bbase (se 4 (by rfl) ⟨143499, by rfl⟩ : syracuseStep 1530661 = 286999) (by norm_num)
theorem B2718517 : Blo 1431535 2718517 := bbase (se 5 (by rfl) ⟨127430, by rfl⟩ : syracuseStep 2718517 = 254861) (by norm_num)
theorem B1612597 : Blo 1431535 1612597 := bbase (se 5 (by rfl) ⟨75590, by rfl⟩ : syracuseStep 1612597 = 151181) (by norm_num)
theorem B4356949 : Blo 1431535 4356949 := bbase (se 9 (by rfl) ⟨12764, by rfl⟩ : syracuseStep 4356949 = 25529) (by norm_num)
theorem B1612633 : Blo 1431535 1612633 := bbase (se 2 (by rfl) ⟨604737, by rfl⟩ : syracuseStep 1612633 = 1209475) (by norm_num)
theorem B1612669 : Blo 1431535 1612669 := bbase (se 3 (by rfl) ⟨302375, by rfl⟩ : syracuseStep 1612669 = 604751) (by norm_num)
theorem B1612705 : Blo 1431535 1612705 := bbase (se 2 (by rfl) ⟨604764, by rfl⟩ : syracuseStep 1612705 = 1209529) (by norm_num)
theorem B3627949 : Blo 1431535 3627949 := bbase (se 3 (by rfl) ⟨680240, by rfl⟩ : syracuseStep 3627949 = 1360481) (by norm_num)
theorem B2038717 : Blo 1431535 2038717 := bbase (se 3 (by rfl) ⟨382259, by rfl⟩ : syracuseStep 2038717 = 764519) (by norm_num)
theorem B9796565 : Blo 1431535 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B2718677 : Blo 1431535 2718677 := bbase (se 7 (by rfl) ⟨31859, by rfl⟩ : syracuseStep 2718677 = 63719) (by norm_num)
theorem B3439597 : Blo 1431535 3439597 := bbase (se 3 (by rfl) ⟨644924, by rfl⟩ : syracuseStep 3439597 = 1289849) (by norm_num)
theorem B3628061 : Blo 1431535 3628061 := bbase (se 3 (by rfl) ⟨680261, by rfl⟩ : syracuseStep 3628061 = 1360523) (by norm_num)
theorem B2178085 : Blo 1431535 2178085 := bbase (se 4 (by rfl) ⟨204195, by rfl⟩ : syracuseStep 2178085 = 408391) (by norm_num)
theorem B4586549 : Blo 1431535 4586549 := bbase (se 5 (by rfl) ⟨214994, by rfl⟩ : syracuseStep 4586549 = 429989) (by norm_num)
theorem B1637465 : Blo 1431535 1637465 := bbase (se 2 (by rfl) ⟨614049, by rfl⟩ : syracuseStep 1637465 = 1228099) (by norm_num)
theorem B2718821 : Blo 1431535 2718821 := bbase (se 4 (by rfl) ⟨254889, by rfl⟩ : syracuseStep 2718821 = 509779) (by norm_num)
theorem B7249013 : Blo 1431535 7249013 := bbase (se 5 (by rfl) ⟨339797, by rfl⟩ : syracuseStep 7249013 = 679595) (by norm_num)
theorem B2415757 : Blo 1431535 2415757 := bbase (se 3 (by rfl) ⟨452954, by rfl⟩ : syracuseStep 2415757 = 905909) (by norm_num)
theorem B4832405 : Blo 1431535 4832405 := bbase (se 6 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 4832405 = 226519) (by norm_num)
theorem B8158421 : Blo 1431535 8158421 := bbase (se 7 (by rfl) ⟨95606, by rfl⟩ : syracuseStep 8158421 = 191213) (by norm_num)
theorem B3628253 : Blo 1431535 3628253 := bbase (se 3 (by rfl) ⟨680297, by rfl⟩ : syracuseStep 3628253 = 1360595) (by norm_num)
theorem B2415845 : Blo 1431535 2415845 := bbase (se 4 (by rfl) ⟨226485, by rfl⟩ : syracuseStep 2415845 = 452971) (by norm_num)
theorem B12401909 : Blo 1431535 12401909 := bbase (se 5 (by rfl) ⟨581339, by rfl⟩ : syracuseStep 12401909 = 1162679) (by norm_num)
theorem B2178341 : Blo 1431535 2178341 := bbase (se 4 (by rfl) ⟨204219, by rfl⟩ : syracuseStep 2178341 = 408439) (by norm_num)
theorem B2415973 : Blo 1431535 2415973 := bbase (se 4 (by rfl) ⟨226497, by rfl⟩ : syracuseStep 2415973 = 452995) (by norm_num)
theorem B2719109 : Blo 1431535 2719109 := bbase (se 4 (by rfl) ⟨254916, by rfl⟩ : syracuseStep 2719109 = 509833) (by norm_num)
theorem B2416061 : Blo 1431535 2416061 := bbase (se 3 (by rfl) ⟨453011, by rfl⟩ : syracuseStep 2416061 = 906023) (by norm_num)
theorem B5438933 : Blo 1431535 5438933 := bbase (se 7 (by rfl) ⟨63737, by rfl⟩ : syracuseStep 5438933 = 127475) (by norm_num)
theorem B2653717 : Blo 1431535 2653717 := bbase (se 6 (by rfl) ⟨62196, by rfl⟩ : syracuseStep 2653717 = 124393) (by norm_num)
theorem B2719261 : Blo 1431535 2719261 := bbase (se 3 (by rfl) ⟨509861, by rfl⟩ : syracuseStep 2719261 = 1019723) (by norm_num)
theorem B1719841 : Blo 1431535 1719841 := bbase (se 2 (by rfl) ⟨644940, by rfl⟩ : syracuseStep 1719841 = 1289881) (by norm_num)
theorem B3628597 : Blo 1431535 3628597 := bbase (se 5 (by rfl) ⟨170090, by rfl⟩ : syracuseStep 3628597 = 340181) (by norm_num)
theorem B2416189 : Blo 1431535 2416189 := bbase (se 3 (by rfl) ⟨453035, by rfl⟩ : syracuseStep 2416189 = 906071) (by norm_num)
theorem B4832837 : Blo 1431535 4832837 := bbase (se 4 (by rfl) ⟨453078, by rfl⟩ : syracuseStep 4832837 = 906157) (by norm_num)
theorem B5103173 : Blo 1431535 5103173 := bbase (se 4 (by rfl) ⟨478422, by rfl⟩ : syracuseStep 5103173 = 956845) (by norm_num)
theorem B3538525 : Blo 1431535 3538525 := bbase (se 3 (by rfl) ⟨663473, by rfl⟩ : syracuseStep 3538525 = 1326947) (by norm_num)
theorem B1719937 : Blo 1431535 1719937 := bbase (se 2 (by rfl) ⟨644976, by rfl⟩ : syracuseStep 1719937 = 1289953) (by norm_num)
theorem B2416277 : Blo 1431535 2416277 := bbase (se 6 (by rfl) ⟨56631, by rfl⟩ : syracuseStep 2416277 = 113263) (by norm_num)
theorem B2293429 : Blo 1431535 2293429 := bbase (se 5 (by rfl) ⟨107504, by rfl⟩ : syracuseStep 2293429 = 215009) (by norm_num)
theorem B2039509 : Blo 1431535 2039509 := bbase (se 7 (by rfl) ⟨23900, by rfl⟩ : syracuseStep 2039509 = 47801) (by norm_num)
theorem B5439221 : Blo 1431535 5439221 := bbase (se 5 (by rfl) ⟨254963, by rfl⟩ : syracuseStep 5439221 = 509927) (by norm_num)
theorem B2293525 : Blo 1431535 2293525 := bbase (se 6 (by rfl) ⟨53754, by rfl⟩ : syracuseStep 2293525 = 107509) (by norm_num)
theorem B2416405 : Blo 1431535 2416405 := bbase (se 6 (by rfl) ⟨56634, by rfl⟩ : syracuseStep 2416405 = 113269) (by norm_num)
theorem B1744705 : Blo 1431535 1744705 := bbase (se 2 (by rfl) ⟨654264, by rfl⟩ : syracuseStep 1744705 = 1308529) (by norm_num)
theorem B2719565 : Blo 1431535 2719565 := bbase (se 3 (by rfl) ⟨509918, by rfl⟩ : syracuseStep 2719565 = 1019837) (by norm_num)
theorem B2416493 : Blo 1431535 2416493 := bbase (se 3 (by rfl) ⟨453092, by rfl⟩ : syracuseStep 2416493 = 906185) (by norm_num)
theorem B2293685 : Blo 1431535 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B4358069 : Blo 1431535 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B4587461 : Blo 1431535 4587461 := bbase (se 4 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 4587461 = 860149) (by norm_num)
theorem B1679305 : Blo 1431535 1679305 := bbase (se 2 (by rfl) ⟨629739, by rfl⟩ : syracuseStep 1679305 = 1259479) (by norm_num)
theorem B2416621 : Blo 1431535 2416621 := bbase (se 3 (by rfl) ⟨453116, by rfl⟩ : syracuseStep 2416621 = 906233) (by norm_num)
theorem B4833269 : Blo 1431535 4833269 := bbase (se 5 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 4833269 = 453119) (by norm_num)
theorem B2719747 : Blo 1431535 2719747 := bstep (se 1 (by rfl) ⟨2039810, by rfl⟩ : syracuseStep 2719747 = 4079621) B4079621
theorem B2416675 : Blo 1431535 2416675 := bstep (se 1 (by rfl) ⟨1812506, by rfl⟩ : syracuseStep 2416675 = 3625013) B3625013
theorem B2719793 : Blo 1431535 2719793 := bstep (se 2 (by rfl) ⟨1019922, by rfl⟩ : syracuseStep 2719793 = 2039845) B2039845
theorem B4079747 : Blo 1431535 4079747 := bstep (se 1 (by rfl) ⟨3059810, by rfl⟩ : syracuseStep 4079747 = 6119621) B6119621
theorem B12230797 : Blo 1431535 12230797 := bstep (se 3 (by rfl) ⟨2293274, by rfl⟩ : syracuseStep 12230797 = 4586549) B4586549
theorem B1745059 : Blo 1431535 1745059 := bstep (se 1 (by rfl) ⟨1308794, by rfl⟩ : syracuseStep 1745059 = 2617589) B2617589
theorem B2416817 : Blo 1431535 2416817 := bstep (se 2 (by rfl) ⟨906306, by rfl⟩ : syracuseStep 2416817 = 1812613) B1812613
theorem B4833485 : Blo 1431535 4833485 := bstep (se 3 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 4833485 = 1812557) B1812557
theorem B7250147 : Blo 1431535 7250147 := bstep (se 1 (by rfl) ⟨5437610, by rfl⟩ : syracuseStep 7250147 = 10875221) B10875221
theorem B4833539 : Blo 1431535 4833539 := bstep (se 1 (by rfl) ⟨3625154, by rfl⟩ : syracuseStep 4833539 = 7250309) B7250309
theorem B2416945 : Blo 1431535 2416945 := bstep (se 2 (by rfl) ⟨906354, by rfl⟩ : syracuseStep 2416945 = 1812709) B1812709
theorem B2326849 : Blo 1431535 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B2720081 : Blo 1431535 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B2416979 : Blo 1431535 2416979 := bstep (se 1 (by rfl) ⟨1812734, by rfl⟩ : syracuseStep 2416979 = 3625469) B3625469
theorem B10322275 : Blo 1431535 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B7348657 : Blo 1431535 7348657 := bstep (se 2 (by rfl) ⟨2755746, by rfl⟩ : syracuseStep 7348657 = 5511493) B5511493
theorem B4080077 : Blo 1431535 4080077 := bstep (se 3 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 4080077 = 1530029) B1530029
theorem B2417107 : Blo 1431535 2417107 := bstep (se 1 (by rfl) ⟨1812830, by rfl⟩ : syracuseStep 2417107 = 3625661) B3625661
theorem B4137443 : Blo 1431535 4137443 := bstep (se 1 (by rfl) ⟨3103082, by rfl⟩ : syracuseStep 4137443 = 6206165) B6206165
theorem B13074929 : Blo 1431535 13074929 := bstep (se 2 (by rfl) ⟨4903098, by rfl⟩ : syracuseStep 13074929 = 9806197) B9806197
theorem B4833809 : Blo 1431535 4833809 := bstep (se 2 (by rfl) ⟨1812678, by rfl⟩ : syracuseStep 4833809 = 3625357) B3625357
theorem B4080145 : Blo 1431535 4080145 := bstep (se 2 (by rfl) ⟨1530054, by rfl⟩ : syracuseStep 4080145 = 3060109) B3060109
theorem B2040403 : Blo 1431535 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B2450017 : Blo 1431535 2450017 := bstep (se 2 (by rfl) ⟨918756, by rfl⟩ : syracuseStep 2450017 = 1837513) B1837513
theorem B2417249 : Blo 1431535 2417249 := bstep (se 2 (by rfl) ⟨906468, by rfl⟩ : syracuseStep 2417249 = 1812937) B1812937
theorem B13951601 : Blo 1431535 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B2417377 : Blo 1431535 2417377 := bstep (se 2 (by rfl) ⟨906516, by rfl⟩ : syracuseStep 2417377 = 1813033) B1813033
theorem B4358897 : Blo 1431535 4358897 := bstep (se 2 (by rfl) ⟨1634586, by rfl⟩ : syracuseStep 4358897 = 3269173) B3269173
theorem B2417411 : Blo 1431535 2417411 := bstep (se 1 (by rfl) ⟨1813058, by rfl⟩ : syracuseStep 2417411 = 3626117) B3626117
theorem B4080419 : Blo 1431535 4080419 := bstep (se 1 (by rfl) ⟨3060314, by rfl⟩ : syracuseStep 4080419 = 6120629) B6120629
theorem B2941763 : Blo 1431535 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B11027299 : Blo 1431535 11027299 := bstep (se 1 (by rfl) ⟨8270474, by rfl⟩ : syracuseStep 11027299 = 16540949) B16540949
theorem B6120305 : Blo 1431535 6120305 := bstep (se 2 (by rfl) ⟨2295114, by rfl⟩ : syracuseStep 6120305 = 4590229) B4590229
theorem B2294659 : Blo 1431535 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B2417539 : Blo 1431535 2417539 := bstep (se 1 (by rfl) ⟨1813154, by rfl⟩ : syracuseStep 2417539 = 3626309) B3626309
theorem B2294705 : Blo 1431535 2294705 := bstep (se 2 (by rfl) ⟨860514, by rfl⟩ : syracuseStep 2294705 = 1721029) B1721029
theorem B17466293 : Blo 1431535 17466293 := bstep (se 5 (by rfl) ⟨818732, by rfl⟩ : syracuseStep 17466293 = 1637465) B1637465
theorem B2147315 : Blo 1431535 2147315 := bstep (se 1 (by rfl) ⟨1610486, by rfl⟩ : syracuseStep 2147315 = 3220973) B3220973
theorem B7250957 : Blo 1431535 7250957 := bstep (se 3 (by rfl) ⟨1359554, by rfl⟩ : syracuseStep 7250957 = 2719109) B2719109
theorem B2147345 : Blo 1431535 2147345 := bstep (se 2 (by rfl) ⟨805254, by rfl⟩ : syracuseStep 2147345 = 1610509) B1610509
theorem B2417681 : Blo 1431535 2417681 := bstep (se 2 (by rfl) ⟨906630, by rfl⟩ : syracuseStep 2417681 = 1813261) B1813261
theorem B2147363 : Blo 1431535 2147363 := bstep (se 1 (by rfl) ⟨1610522, by rfl⟩ : syracuseStep 2147363 = 3221045) B3221045
theorem B2720803 : Blo 1431535 2720803 := bstep (se 1 (by rfl) ⟨2040602, by rfl⟩ : syracuseStep 2720803 = 4081205) B4081205
theorem B4588589 : Blo 1431535 4588589 := bstep (se 3 (by rfl) ⟨860360, by rfl⟩ : syracuseStep 4588589 = 1720721) B1720721
theorem B4834349 : Blo 1431535 4834349 := bstep (se 3 (by rfl) ⟨906440, by rfl⟩ : syracuseStep 4834349 = 1812881) B1812881
theorem B2040881 : Blo 1431535 2040881 := bstep (se 2 (by rfl) ⟨765330, by rfl⟩ : syracuseStep 2040881 = 1530661) B1530661
theorem B2147393 : Blo 1431535 2147393 := bstep (se 2 (by rfl) ⟨805272, by rfl⟩ : syracuseStep 2147393 = 1610545) B1610545
theorem B2147411 : Blo 1431535 2147411 := bstep (se 1 (by rfl) ⟨1610558, by rfl⟩ : syracuseStep 2147411 = 3221117) B3221117
theorem B4834403 : Blo 1431535 4834403 := bstep (se 1 (by rfl) ⟨3625802, by rfl⟩ : syracuseStep 4834403 = 7251605) B7251605
theorem B2147441 : Blo 1431535 2147441 := bstep (se 2 (by rfl) ⟨805290, by rfl⟩ : syracuseStep 2147441 = 1610581) B1610581
theorem B4899953 : Blo 1431535 4899953 := bstep (se 2 (by rfl) ⟨1837482, by rfl⟩ : syracuseStep 4899953 = 3674965) B3674965
theorem B5809265 : Blo 1431535 5809265 := bstep (se 2 (by rfl) ⟨2178474, by rfl⟩ : syracuseStep 5809265 = 4356949) B4356949
theorem B2147459 : Blo 1431535 2147459 := bstep (se 1 (by rfl) ⟨1610594, by rfl⟩ : syracuseStep 2147459 = 3221189) B3221189
theorem B2417809 : Blo 1431535 2417809 := bstep (se 2 (by rfl) ⟨906678, by rfl⟩ : syracuseStep 2417809 = 1813357) B1813357
theorem B2147489 : Blo 1431535 2147489 := bstep (se 2 (by rfl) ⟨805308, by rfl⟩ : syracuseStep 2147489 = 1610617) B1610617
theorem B2040995 : Blo 1431535 2040995 := bstep (se 1 (by rfl) ⟨1530746, by rfl⟩ : syracuseStep 2040995 = 3061493) B3061493
theorem B2147507 : Blo 1431535 2147507 := bstep (se 1 (by rfl) ⟨1610630, by rfl⟩ : syracuseStep 2147507 = 3221261) B3221261
theorem B2417843 : Blo 1431535 2417843 := bstep (se 1 (by rfl) ⟨1813382, by rfl⟩ : syracuseStep 2417843 = 3626765) B3626765
theorem B2147537 : Blo 1431535 2147537 := bstep (se 2 (by rfl) ⟨805326, by rfl⟩ : syracuseStep 2147537 = 1610653) B1610653
theorem B2147555 : Blo 1431535 2147555 := bstep (se 1 (by rfl) ⟨1610666, by rfl⟩ : syracuseStep 2147555 = 3221333) B3221333
theorem B2450675 : Blo 1431535 2450675 := bstep (se 1 (by rfl) ⟨1838006, by rfl⟩ : syracuseStep 2450675 = 3676013) B3676013
theorem B2041075 : Blo 1431535 2041075 := bstep (se 1 (by rfl) ⟨1530806, by rfl⟩ : syracuseStep 2041075 = 3061613) B3061613
theorem B2147585 : Blo 1431535 2147585 := bstep (se 2 (by rfl) ⟨805344, by rfl⟩ : syracuseStep 2147585 = 1610689) B1610689
theorem B2147603 : Blo 1431535 2147603 := bstep (se 1 (by rfl) ⟨1610702, by rfl⟩ : syracuseStep 2147603 = 3221405) B3221405
theorem B2147633 : Blo 1431535 2147633 := bstep (se 2 (by rfl) ⟨805362, by rfl⟩ : syracuseStep 2147633 = 1610725) B1610725
theorem B2417971 : Blo 1431535 2417971 := bstep (se 1 (by rfl) ⟨1813478, by rfl⟩ : syracuseStep 2417971 = 3626957) B3626957
theorem B2147651 : Blo 1431535 2147651 := bstep (se 1 (by rfl) ⟨1610738, by rfl⟩ : syracuseStep 2147651 = 3221477) B3221477
theorem B2147681 : Blo 1431535 2147681 := bstep (se 2 (by rfl) ⟨805380, by rfl⟩ : syracuseStep 2147681 = 1610761) B1610761
theorem B4834673 : Blo 1431535 4834673 := bstep (se 2 (by rfl) ⟨1813002, by rfl⟩ : syracuseStep 4834673 = 3626005) B3626005
theorem B2147699 : Blo 1431535 2147699 := bstep (se 1 (by rfl) ⟨1610774, by rfl⟩ : syracuseStep 2147699 = 3221549) B3221549
theorem B2147729 : Blo 1431535 2147729 := bstep (se 2 (by rfl) ⟨805398, by rfl⟩ : syracuseStep 2147729 = 1610797) B1610797
theorem B2147747 : Blo 1431535 2147747 := bstep (se 1 (by rfl) ⟨1610810, by rfl⟩ : syracuseStep 2147747 = 3221621) B3221621
theorem B2147777 : Blo 1431535 2147777 := bstep (se 2 (by rfl) ⟨805416, by rfl⟩ : syracuseStep 2147777 = 1610833) B1610833
theorem B2418113 : Blo 1431535 2418113 := bstep (se 2 (by rfl) ⟨906792, by rfl⟩ : syracuseStep 2418113 = 1813585) B1813585
theorem B12232133 : Blo 1431535 12232133 := bstep (se 4 (by rfl) ⟨1146762, by rfl⟩ : syracuseStep 12232133 = 2293525) B2293525
theorem B2147795 : Blo 1431535 2147795 := bstep (se 1 (by rfl) ⟨1610846, by rfl⟩ : syracuseStep 2147795 = 3221693) B3221693
theorem B2721251 : Blo 1431535 2721251 := bstep (se 1 (by rfl) ⟨2040938, by rfl⟩ : syracuseStep 2721251 = 4081877) B4081877
theorem B10872305 : Blo 1431535 10872305 := bstep (se 2 (by rfl) ⟨4077114, by rfl⟩ : syracuseStep 10872305 = 8154229) B8154229
theorem B2147825 : Blo 1431535 2147825 := bstep (se 2 (by rfl) ⟨805434, by rfl⟩ : syracuseStep 2147825 = 1610869) B1610869
theorem B9176561 : Blo 1431535 9176561 := bstep (se 2 (by rfl) ⟨3441210, by rfl⟩ : syracuseStep 9176561 = 6882421) B6882421
theorem B2147843 : Blo 1431535 2147843 := bstep (se 1 (by rfl) ⟨1610882, by rfl⟩ : syracuseStep 2147843 = 3221765) B3221765
theorem B13608461 : Blo 1431535 13608461 := bstep (se 3 (by rfl) ⟨2551586, by rfl⟩ : syracuseStep 13608461 = 5103173) B5103173
theorem B3221009 : Blo 1431535 3221009 := bstep (se 2 (by rfl) ⟨1207878, by rfl⟩ : syracuseStep 3221009 = 2415757) B2415757
theorem B2147873 : Blo 1431535 2147873 := bstep (se 2 (by rfl) ⟨805452, by rfl⟩ : syracuseStep 2147873 = 1610905) B1610905
theorem B3221027 : Blo 1431535 3221027 := bstep (se 1 (by rfl) ⟨2415770, by rfl⟩ : syracuseStep 3221027 = 4831541) B4831541
theorem B2147891 : Blo 1431535 2147891 := bstep (se 1 (by rfl) ⟨1610918, by rfl⟩ : syracuseStep 2147891 = 3221837) B3221837
theorem B2418241 : Blo 1431535 2418241 := bstep (se 2 (by rfl) ⟨906840, by rfl⟩ : syracuseStep 2418241 = 1813681) B1813681
theorem B2147921 : Blo 1431535 2147921 := bstep (se 2 (by rfl) ⟨805470, by rfl⟩ : syracuseStep 2147921 = 1610941) B1610941
theorem B2147939 : Blo 1431535 2147939 := bstep (se 1 (by rfl) ⟨1610954, by rfl⟩ : syracuseStep 2147939 = 3221909) B3221909
theorem B2418275 : Blo 1431535 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B4081261 : Blo 1431535 4081261 := bstep (se 3 (by rfl) ⟨765236, by rfl⟩ : syracuseStep 4081261 = 1530473) B1530473
theorem B2147969 : Blo 1431535 2147969 := bstep (se 2 (by rfl) ⟨805488, by rfl⟩ : syracuseStep 2147969 = 1610977) B1610977
theorem B5441165 : Blo 1431535 5441165 := bstep (se 3 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 5441165 = 2040437) B2040437
theorem B2147987 : Blo 1431535 2147987 := bstep (se 1 (by rfl) ⟨1610990, by rfl⟩ : syracuseStep 2147987 = 3221981) B3221981
theorem B2148017 : Blo 1431535 2148017 := bstep (se 2 (by rfl) ⟨805506, by rfl⟩ : syracuseStep 2148017 = 1611013) B1611013
theorem B2148035 : Blo 1431535 2148035 := bstep (se 1 (by rfl) ⟨1611026, by rfl⟩ : syracuseStep 2148035 = 3222053) B3222053
theorem B2148065 : Blo 1431535 2148065 := bstep (se 2 (by rfl) ⟨805524, by rfl⟩ : syracuseStep 2148065 = 1611049) B1611049
theorem B2418403 : Blo 1431535 2418403 := bstep (se 1 (by rfl) ⟨1813802, by rfl⟩ : syracuseStep 2418403 = 3627605) B3627605
theorem B2148083 : Blo 1431535 2148083 := bstep (se 1 (by rfl) ⟨1611062, by rfl⟩ : syracuseStep 2148083 = 3222125) B3222125
theorem B4081421 : Blo 1431535 4081421 := bstep (se 3 (by rfl) ⟨765266, by rfl⟩ : syracuseStep 4081421 = 1530533) B1530533
theorem B2148113 : Blo 1431535 2148113 := bstep (se 2 (by rfl) ⟨805542, by rfl⟩ : syracuseStep 2148113 = 1611085) B1611085
theorem B2148131 : Blo 1431535 2148131 := bstep (se 1 (by rfl) ⟨1611098, by rfl⟩ : syracuseStep 2148131 = 3222197) B3222197
theorem B3221297 : Blo 1431535 3221297 := bstep (se 2 (by rfl) ⟨1207986, by rfl⟩ : syracuseStep 3221297 = 2415973) B2415973
theorem B2148161 : Blo 1431535 2148161 := bstep (se 2 (by rfl) ⟨805560, by rfl⟩ : syracuseStep 2148161 = 1611121) B1611121
theorem B3221315 : Blo 1431535 3221315 := bstep (se 1 (by rfl) ⟨2415986, by rfl⟩ : syracuseStep 3221315 = 4831973) B4831973
theorem B2148179 : Blo 1431535 2148179 := bstep (se 1 (by rfl) ⟨1611134, by rfl⟩ : syracuseStep 2148179 = 3222269) B3222269
theorem B2148209 : Blo 1431535 2148209 := bstep (se 2 (by rfl) ⟨805578, by rfl⟩ : syracuseStep 2148209 = 1611157) B1611157
theorem B2418545 : Blo 1431535 2418545 := bstep (se 2 (by rfl) ⟨906954, by rfl⟩ : syracuseStep 2418545 = 1813909) B1813909
theorem B2148227 : Blo 1431535 2148227 := bstep (se 1 (by rfl) ⟨1611170, by rfl⟩ : syracuseStep 2148227 = 3222341) B3222341
theorem B4835213 : Blo 1431535 4835213 := bstep (se 3 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 4835213 = 1813205) B1813205
theorem B2295697 : Blo 1431535 2295697 := bstep (se 2 (by rfl) ⟨860886, by rfl⟩ : syracuseStep 2295697 = 1721773) B1721773
theorem B1935265 : Blo 1431535 1935265 := bstep (se 2 (by rfl) ⟨725724, by rfl⟩ : syracuseStep 1935265 = 1451449) B1451449
theorem B2148257 : Blo 1431535 2148257 := bstep (se 2 (by rfl) ⟨805596, by rfl⟩ : syracuseStep 2148257 = 1611193) B1611193
theorem B2148275 : Blo 1431535 2148275 := bstep (se 1 (by rfl) ⟨1611206, by rfl⟩ : syracuseStep 2148275 = 3222413) B3222413
theorem B4835267 : Blo 1431535 4835267 := bstep (se 1 (by rfl) ⟨3626450, by rfl⟩ : syracuseStep 4835267 = 7252901) B7252901
theorem B4081603 : Blo 1431535 4081603 := bstep (se 1 (by rfl) ⟨3061202, by rfl⟩ : syracuseStep 4081603 = 6122405) B6122405
theorem B2148305 : Blo 1431535 2148305 := bstep (se 2 (by rfl) ⟨805614, by rfl⟩ : syracuseStep 2148305 = 1611229) B1611229
theorem B6531043 : Blo 1431535 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B1812451 : Blo 1431535 1812451 := bstep (se 1 (by rfl) ⟨1359338, by rfl⟩ : syracuseStep 1812451 = 2718677) B2718677
theorem B2148323 : Blo 1431535 2148323 := bstep (se 1 (by rfl) ⟨1611242, by rfl⟩ : syracuseStep 2148323 = 3222485) B3222485
theorem B12240881 : Blo 1431535 12240881 := bstep (se 2 (by rfl) ⟨4590330, by rfl⟩ : syracuseStep 12240881 = 9180661) B9180661
theorem B2418673 : Blo 1431535 2418673 := bstep (se 2 (by rfl) ⟨907002, by rfl⟩ : syracuseStep 2418673 = 1814005) B1814005
theorem B2148353 : Blo 1431535 2148353 := bstep (se 2 (by rfl) ⟨805632, by rfl⟩ : syracuseStep 2148353 = 1611265) B1611265
theorem B2148371 : Blo 1431535 2148371 := bstep (se 1 (by rfl) ⟨1611278, by rfl⟩ : syracuseStep 2148371 = 3222557) B3222557
theorem B2418707 : Blo 1431535 2418707 := bstep (se 1 (by rfl) ⟨1814030, by rfl⟩ : syracuseStep 2418707 = 3628061) B3628061
theorem B2148401 : Blo 1431535 2148401 := bstep (se 2 (by rfl) ⟨805650, by rfl⟩ : syracuseStep 2148401 = 1611301) B1611301
theorem B1812547 : Blo 1431535 1812547 := bstep (se 1 (by rfl) ⟨1359410, by rfl⟩ : syracuseStep 1812547 = 2718821) B2718821
theorem B2148419 : Blo 1431535 2148419 := bstep (se 1 (by rfl) ⟨1611314, by rfl⟩ : syracuseStep 2148419 = 3222629) B3222629
theorem B3221585 : Blo 1431535 3221585 := bstep (se 2 (by rfl) ⟨1208094, by rfl⟩ : syracuseStep 3221585 = 2416189) B2416189
theorem B2148449 : Blo 1431535 2148449 := bstep (se 2 (by rfl) ⟨805668, by rfl⟩ : syracuseStep 2148449 = 1611337) B1611337
theorem B3221603 : Blo 1431535 3221603 := bstep (se 1 (by rfl) ⟨2416202, by rfl⟩ : syracuseStep 3221603 = 4832405) B4832405
theorem B2148467 : Blo 1431535 2148467 := bstep (se 1 (by rfl) ⟨1611350, by rfl⟩ : syracuseStep 2148467 = 3222701) B3222701
theorem B2148497 : Blo 1431535 2148497 := bstep (se 2 (by rfl) ⟨805686, by rfl⟩ : syracuseStep 2148497 = 1611373) B1611373
theorem B2418835 : Blo 1431535 2418835 := bstep (se 1 (by rfl) ⟨1814126, by rfl⟩ : syracuseStep 2418835 = 3628253) B3628253
theorem B8267939 : Blo 1431535 8267939 := bstep (se 1 (by rfl) ⟨6200954, by rfl⟩ : syracuseStep 8267939 = 12401909) B12401909
theorem B2148515 : Blo 1431535 2148515 := bstep (se 1 (by rfl) ⟨1611386, by rfl⟩ : syracuseStep 2148515 = 3222773) B3222773
theorem B2148545 : Blo 1431535 2148545 := bstep (se 2 (by rfl) ⟨805704, by rfl⟩ : syracuseStep 2148545 = 1611409) B1611409
theorem B1452227 : Blo 1431535 1452227 := bstep (se 1 (by rfl) ⟨1089170, by rfl⟩ : syracuseStep 1452227 = 2178341) B2178341
theorem B2902225 : Blo 1431535 2902225 := bstep (se 2 (by rfl) ⟨1088334, by rfl⟩ : syracuseStep 2902225 = 2176669) B2176669
theorem B2148563 : Blo 1431535 2148563 := bstep (se 1 (by rfl) ⟨1611422, by rfl⟩ : syracuseStep 2148563 = 3222845) B3222845
theorem B4835537 : Blo 1431535 4835537 := bstep (se 2 (by rfl) ⟨1813326, by rfl⟩ : syracuseStep 4835537 = 3626653) B3626653
theorem B3057905 : Blo 1431535 3057905 := bstep (se 2 (by rfl) ⟨1146714, by rfl⟩ : syracuseStep 3057905 = 2293429) B2293429
theorem B2148593 : Blo 1431535 2148593 := bstep (se 2 (by rfl) ⟨805722, by rfl⟩ : syracuseStep 2148593 = 1611445) B1611445
theorem B2148611 : Blo 1431535 2148611 := bstep (se 1 (by rfl) ⟨1611458, by rfl⟩ : syracuseStep 2148611 = 3222917) B3222917
theorem B2148641 : Blo 1431535 2148641 := bstep (se 2 (by rfl) ⟨805740, by rfl⟩ : syracuseStep 2148641 = 1611481) B1611481
theorem B2418977 : Blo 1431535 2418977 := bstep (se 2 (by rfl) ⟨907116, by rfl⟩ : syracuseStep 2418977 = 1814233) B1814233
theorem B2148659 : Blo 1431535 2148659 := bstep (se 1 (by rfl) ⟨1611494, by rfl⟩ : syracuseStep 2148659 = 3222989) B3222989
theorem B37234997 : Blo 1431535 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B2148689 : Blo 1431535 2148689 := bstep (se 2 (by rfl) ⟨805758, by rfl⟩ : syracuseStep 2148689 = 1611517) B1611517
theorem B2296145 : Blo 1431535 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B2148707 : Blo 1431535 2148707 := bstep (se 1 (by rfl) ⟨1611530, by rfl⟩ : syracuseStep 2148707 = 3223061) B3223061
theorem B3221873 : Blo 1431535 3221873 := bstep (se 2 (by rfl) ⟨1208202, by rfl⟩ : syracuseStep 3221873 = 2416405) B2416405
theorem B3443057 : Blo 1431535 3443057 := bstep (se 2 (by rfl) ⟨1291146, by rfl⟩ : syracuseStep 3443057 = 2582293) B2582293
theorem B2148737 : Blo 1431535 2148737 := bstep (se 2 (by rfl) ⟨805776, by rfl⟩ : syracuseStep 2148737 = 1611553) B1611553
theorem B3221891 : Blo 1431535 3221891 := bstep (se 1 (by rfl) ⟨2416418, by rfl⟩ : syracuseStep 3221891 = 4832837) B4832837
theorem B2148755 : Blo 1431535 2148755 := bstep (se 1 (by rfl) ⟨1611566, by rfl⟩ : syracuseStep 2148755 = 3223133) B3223133
theorem B2148785 : Blo 1431535 2148785 := bstep (se 2 (by rfl) ⟨805794, by rfl⟩ : syracuseStep 2148785 = 1611589) B1611589
theorem B2148803 : Blo 1431535 2148803 := bstep (se 1 (by rfl) ⟨1611602, by rfl⟩ : syracuseStep 2148803 = 3223205) B3223205
theorem B2148833 : Blo 1431535 2148833 := bstep (se 2 (by rfl) ⟨805812, by rfl⟩ : syracuseStep 2148833 = 1611625) B1611625
theorem B3631601 : Blo 1431535 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B2148851 : Blo 1431535 2148851 := bstep (se 1 (by rfl) ⟨1611638, by rfl⟩ : syracuseStep 2148851 = 3223277) B3223277
theorem B2148881 : Blo 1431535 2148881 := bstep (se 2 (by rfl) ⟨805830, by rfl⟩ : syracuseStep 2148881 = 1611661) B1611661
theorem B2148899 : Blo 1431535 2148899 := bstep (se 1 (by rfl) ⟨1611674, by rfl⟩ : syracuseStep 2148899 = 3223349) B3223349
theorem B1813043 : Blo 1431535 1813043 := bstep (se 1 (by rfl) ⟨1359782, by rfl⟩ : syracuseStep 1813043 = 2719565) B2719565
theorem B2148929 : Blo 1431535 2148929 := bstep (se 2 (by rfl) ⟨805848, by rfl⟩ : syracuseStep 2148929 = 1611697) B1611697
theorem B9800261 : Blo 1431535 9800261 := bstep (se 4 (by rfl) ⟨918774, by rfl⟩ : syracuseStep 9800261 = 1837549) B1837549
theorem B2148947 : Blo 1431535 2148947 := bstep (se 1 (by rfl) ⟨1611710, by rfl⟩ : syracuseStep 2148947 = 3223421) B3223421
theorem B2239073 : Blo 1431535 2239073 := bstep (se 2 (by rfl) ⟨839652, by rfl⟩ : syracuseStep 2239073 = 1679305) B1679305
theorem B2148977 : Blo 1431535 2148977 := bstep (se 2 (by rfl) ⟨805866, by rfl⟩ : syracuseStep 2148977 = 1611733) B1611733
theorem B3058307 : Blo 1431535 3058307 := bstep (se 1 (by rfl) ⟨2293730, by rfl⟩ : syracuseStep 3058307 = 4587461) B4587461
theorem B2148995 : Blo 1431535 2148995 := bstep (se 1 (by rfl) ⟨1611746, by rfl⟩ : syracuseStep 2148995 = 3223493) B3223493
theorem B2452097 : Blo 1431535 2452097 := bstep (se 2 (by rfl) ⟨919536, by rfl⟩ : syracuseStep 2452097 = 1839073) B1839073
theorem B3222161 : Blo 1431535 3222161 := bstep (se 2 (by rfl) ⟨1208310, by rfl⟩ : syracuseStep 3222161 = 2416621) B2416621
theorem B2149025 : Blo 1431535 2149025 := bstep (se 2 (by rfl) ⟨805884, by rfl⟩ : syracuseStep 2149025 = 1611769) B1611769
theorem B3222179 : Blo 1431535 3222179 := bstep (se 1 (by rfl) ⟨2416634, by rfl⟩ : syracuseStep 3222179 = 4833269) B4833269
theorem B2149043 : Blo 1431535 2149043 := bstep (se 1 (by rfl) ⟨1611782, by rfl⟩ : syracuseStep 2149043 = 3223565) B3223565
theorem B2149073 : Blo 1431535 2149073 := bstep (se 2 (by rfl) ⟨805902, by rfl⟩ : syracuseStep 2149073 = 1611805) B1611805
theorem B2149091 : Blo 1431535 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B4836077 : Blo 1431535 4836077 := bstep (se 3 (by rfl) ⟨906764, by rfl⟩ : syracuseStep 4836077 = 1813529) B1813529
theorem B2149121 : Blo 1431535 2149121 := bstep (se 2 (by rfl) ⟨805920, by rfl⟩ : syracuseStep 2149121 = 1611841) B1611841
theorem B2149139 : Blo 1431535 2149139 := bstep (se 1 (by rfl) ⟨1611854, by rfl⟩ : syracuseStep 2149139 = 3223709) B3223709
theorem B4836131 : Blo 1431535 4836131 := bstep (se 1 (by rfl) ⟨3627098, by rfl⟩ : syracuseStep 4836131 = 7254197) B7254197
theorem B1452835 : Blo 1431535 1452835 := bstep (se 1 (by rfl) ⟨1089626, by rfl⟩ : syracuseStep 1452835 = 2179253) B2179253
theorem B2149169 : Blo 1431535 2149169 := bstep (se 2 (by rfl) ⟨805938, by rfl⟩ : syracuseStep 2149169 = 1611877) B1611877
theorem B2149187 : Blo 1431535 2149187 := bstep (se 1 (by rfl) ⟨1611890, by rfl⟩ : syracuseStep 2149187 = 3223781) B3223781
theorem B2149217 : Blo 1431535 2149217 := bstep (se 2 (by rfl) ⟨805956, by rfl⟩ : syracuseStep 2149217 = 1611913) B1611913
theorem B4590445 : Blo 1431535 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B2149235 : Blo 1431535 2149235 := bstep (se 1 (by rfl) ⟨1611926, by rfl⟩ : syracuseStep 2149235 = 3223853) B3223853
theorem B2149265 : Blo 1431535 2149265 := bstep (se 2 (by rfl) ⟨805974, by rfl⟩ : syracuseStep 2149265 = 1611949) B1611949
theorem B9178019 : Blo 1431535 9178019 := bstep (se 1 (by rfl) ⟨6883514, by rfl⟩ : syracuseStep 9178019 = 13767029) B13767029
theorem B2149283 : Blo 1431535 2149283 := bstep (se 1 (by rfl) ⟨1611962, by rfl⟩ : syracuseStep 2149283 = 3223925) B3223925
theorem B3222449 : Blo 1431535 3222449 := bstep (se 2 (by rfl) ⟨1208418, by rfl⟩ : syracuseStep 3222449 = 2416837) B2416837
theorem B2149313 : Blo 1431535 2149313 := bstep (se 2 (by rfl) ⟨805992, by rfl⟩ : syracuseStep 2149313 = 1611985) B1611985
theorem B3222467 : Blo 1431535 3222467 := bstep (se 1 (by rfl) ⟨2416850, by rfl⟩ : syracuseStep 3222467 = 4833701) B4833701
theorem B2149331 : Blo 1431535 2149331 := bstep (se 1 (by rfl) ⟨1611998, by rfl⟩ : syracuseStep 2149331 = 3223997) B3223997
theorem B2149361 : Blo 1431535 2149361 := bstep (se 2 (by rfl) ⟨806010, by rfl⟩ : syracuseStep 2149361 = 1612021) B1612021
theorem B2149379 : Blo 1431535 2149379 := bstep (se 1 (by rfl) ⟨1612034, by rfl⟩ : syracuseStep 2149379 = 3224069) B3224069
theorem B2149409 : Blo 1431535 2149409 := bstep (se 2 (by rfl) ⟨806028, by rfl⟩ : syracuseStep 2149409 = 1612057) B1612057
theorem B2903075 : Blo 1431535 2903075 := bstep (se 1 (by rfl) ⟨2177306, by rfl⟩ : syracuseStep 2903075 = 4354613) B4354613
theorem B4836401 : Blo 1431535 4836401 := bstep (se 2 (by rfl) ⟨1813650, by rfl⟩ : syracuseStep 4836401 = 3627301) B3627301
theorem B2149427 : Blo 1431535 2149427 := bstep (se 1 (by rfl) ⟨1612070, by rfl⟩ : syracuseStep 2149427 = 3224141) B3224141
theorem B2149457 : Blo 1431535 2149457 := bstep (se 2 (by rfl) ⟨806046, by rfl⟩ : syracuseStep 2149457 = 1612093) B1612093
theorem B2149475 : Blo 1431535 2149475 := bstep (se 1 (by rfl) ⟨1612106, by rfl⟩ : syracuseStep 2149475 = 3224213) B3224213
theorem B2067571 : Blo 1431535 2067571 := bstep (se 1 (by rfl) ⟨1550678, by rfl⟩ : syracuseStep 2067571 = 3101357) B3101357
theorem B2149505 : Blo 1431535 2149505 := bstep (se 2 (by rfl) ⟨806064, by rfl⟩ : syracuseStep 2149505 = 1612129) B1612129
theorem B2149523 : Blo 1431535 2149523 := bstep (se 1 (by rfl) ⟨1612142, by rfl⟩ : syracuseStep 2149523 = 3224285) B3224285
theorem B5164195 : Blo 1431535 5164195 := bstep (se 1 (by rfl) ⟨3873146, by rfl⟩ : syracuseStep 5164195 = 7746293) B7746293
theorem B2149553 : Blo 1431535 2149553 := bstep (se 2 (by rfl) ⟨806082, by rfl⟩ : syracuseStep 2149553 = 1612165) B1612165
theorem B2149571 : Blo 1431535 2149571 := bstep (se 1 (by rfl) ⟨1612178, by rfl⟩ : syracuseStep 2149571 = 3224357) B3224357
theorem B3222737 : Blo 1431535 3222737 := bstep (se 2 (by rfl) ⟨1208526, by rfl⟩ : syracuseStep 3222737 = 2417053) B2417053
theorem B2149601 : Blo 1431535 2149601 := bstep (se 2 (by rfl) ⟨806100, by rfl⟩ : syracuseStep 2149601 = 1612201) B1612201
theorem B3222755 : Blo 1431535 3222755 := bstep (se 1 (by rfl) ⟨2417066, by rfl⟩ : syracuseStep 3222755 = 4834133) B4834133
theorem B2149619 : Blo 1431535 2149619 := bstep (se 1 (by rfl) ⟨1612214, by rfl⟩ : syracuseStep 2149619 = 3224429) B3224429
theorem B1813747 : Blo 1431535 1813747 := bstep (se 1 (by rfl) ⟨1360310, by rfl⟩ : syracuseStep 1813747 = 2720621) B2720621
theorem B2149649 : Blo 1431535 2149649 := bstep (se 2 (by rfl) ⟨806118, by rfl⟩ : syracuseStep 2149649 = 1612237) B1612237
theorem B2149667 : Blo 1431535 2149667 := bstep (se 1 (by rfl) ⟨1612250, by rfl⟩ : syracuseStep 2149667 = 3224501) B3224501
theorem B2149697 : Blo 1431535 2149697 := bstep (se 2 (by rfl) ⟨806136, by rfl⟩ : syracuseStep 2149697 = 1612273) B1612273
theorem B1633619 : Blo 1431535 1633619 := bstep (se 1 (by rfl) ⟨1225214, by rfl⟩ : syracuseStep 1633619 = 2450429) B2450429
theorem B2149715 : Blo 1431535 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B1813843 : Blo 1431535 1813843 := bstep (se 1 (by rfl) ⟨1360382, by rfl⟩ : syracuseStep 1813843 = 2720765) B2720765
theorem B2149745 : Blo 1431535 2149745 := bstep (se 2 (by rfl) ⟨806154, by rfl⟩ : syracuseStep 2149745 = 1612309) B1612309
theorem B2149763 : Blo 1431535 2149763 := bstep (se 1 (by rfl) ⟨1612322, by rfl⟩ : syracuseStep 2149763 = 3224645) B3224645
theorem B2149793 : Blo 1431535 2149793 := bstep (se 2 (by rfl) ⟨806172, by rfl⟩ : syracuseStep 2149793 = 1612345) B1612345
theorem B2149811 : Blo 1431535 2149811 := bstep (se 1 (by rfl) ⟨1612358, by rfl⟩ : syracuseStep 2149811 = 3224717) B3224717
theorem B2149841 : Blo 1431535 2149841 := bstep (se 2 (by rfl) ⟨806190, by rfl⟩ : syracuseStep 2149841 = 1612381) B1612381
theorem B2149859 : Blo 1431535 2149859 := bstep (se 1 (by rfl) ⟨1612394, by rfl⟩ : syracuseStep 2149859 = 3224789) B3224789
theorem B3223025 : Blo 1431535 3223025 := bstep (se 2 (by rfl) ⟨1208634, by rfl⟩ : syracuseStep 3223025 = 2417269) B2417269
theorem B2149889 : Blo 1431535 2149889 := bstep (se 2 (by rfl) ⟨806208, by rfl⟩ : syracuseStep 2149889 = 1612417) B1612417
theorem B3059203 : Blo 1431535 3059203 := bstep (se 1 (by rfl) ⟨2294402, by rfl⟩ : syracuseStep 3059203 = 4588805) B4588805
theorem B3223043 : Blo 1431535 3223043 := bstep (se 1 (by rfl) ⟨2417282, by rfl⟩ : syracuseStep 3223043 = 4834565) B4834565
theorem B2149907 : Blo 1431535 2149907 := bstep (se 1 (by rfl) ⟨1612430, by rfl⟩ : syracuseStep 2149907 = 3224861) B3224861
theorem B3624497 : Blo 1431535 3624497 := bstep (se 2 (by rfl) ⟨1359186, by rfl⟩ : syracuseStep 3624497 = 2718373) B2718373
theorem B2149937 : Blo 1431535 2149937 := bstep (se 2 (by rfl) ⟨806226, by rfl⟩ : syracuseStep 2149937 = 1612453) B1612453
theorem B2149955 : Blo 1431535 2149955 := bstep (se 1 (by rfl) ⟨1612466, by rfl⟩ : syracuseStep 2149955 = 3224933) B3224933
theorem B4836941 : Blo 1431535 4836941 := bstep (se 3 (by rfl) ⟨906926, by rfl⟩ : syracuseStep 4836941 = 1813853) B1813853
theorem B2149985 : Blo 1431535 2149985 := bstep (se 2 (by rfl) ⟨806244, by rfl⟩ : syracuseStep 2149985 = 1612489) B1612489
theorem B3624547 : Blo 1431535 3624547 := bstep (se 1 (by rfl) ⟨2718410, by rfl⟩ : syracuseStep 3624547 = 5436821) B5436821
theorem B2150003 : Blo 1431535 2150003 := bstep (se 1 (by rfl) ⟨1612502, by rfl⟩ : syracuseStep 2150003 = 3225005) B3225005
theorem B4836995 : Blo 1431535 4836995 := bstep (se 1 (by rfl) ⟨3627746, by rfl⟩ : syracuseStep 4836995 = 7255493) B7255493
theorem B2150033 : Blo 1431535 2150033 := bstep (se 2 (by rfl) ⟨806262, by rfl⟩ : syracuseStep 2150033 = 1612525) B1612525
theorem B2150051 : Blo 1431535 2150051 := bstep (se 1 (by rfl) ⟨1612538, by rfl⟩ : syracuseStep 2150051 = 3225077) B3225077
theorem B2150081 : Blo 1431535 2150081 := bstep (se 2 (by rfl) ⟨806280, by rfl⟩ : syracuseStep 2150081 = 1612561) B1612561
theorem B2150099 : Blo 1431535 2150099 := bstep (se 1 (by rfl) ⟨1612574, by rfl⟩ : syracuseStep 2150099 = 3225149) B3225149
theorem B4353763 : Blo 1431535 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B3624689 : Blo 1431535 3624689 := bstep (se 2 (by rfl) ⟨1359258, by rfl⟩ : syracuseStep 3624689 = 2718517) B2718517
theorem B2150129 : Blo 1431535 2150129 := bstep (se 2 (by rfl) ⟨806298, by rfl⟩ : syracuseStep 2150129 = 1612597) B1612597
theorem B2150147 : Blo 1431535 2150147 := bstep (se 1 (by rfl) ⟨1612610, by rfl⟩ : syracuseStep 2150147 = 3225221) B3225221
theorem B3223313 : Blo 1431535 3223313 := bstep (se 2 (by rfl) ⟨1208742, by rfl⟩ : syracuseStep 3223313 = 2417485) B2417485
theorem B2150177 : Blo 1431535 2150177 := bstep (se 2 (by rfl) ⟨806316, by rfl⟩ : syracuseStep 2150177 = 1612633) B1612633
theorem B3223331 : Blo 1431535 3223331 := bstep (se 1 (by rfl) ⟨2417498, by rfl⟩ : syracuseStep 3223331 = 4834997) B4834997
theorem B2150195 : Blo 1431535 2150195 := bstep (se 1 (by rfl) ⟨1612646, by rfl⟩ : syracuseStep 2150195 = 3225293) B3225293
theorem B2150225 : Blo 1431535 2150225 := bstep (se 2 (by rfl) ⟨806334, by rfl⟩ : syracuseStep 2150225 = 1612669) B1612669
theorem B2150243 : Blo 1431535 2150243 := bstep (se 1 (by rfl) ⟨1612682, by rfl⟩ : syracuseStep 2150243 = 3225365) B3225365
theorem B7253873 : Blo 1431535 7253873 := bstep (se 2 (by rfl) ⟨2720202, by rfl⟩ : syracuseStep 7253873 = 5440405) B5440405
theorem B2150273 : Blo 1431535 2150273 := bstep (se 2 (by rfl) ⟨806352, by rfl⟩ : syracuseStep 2150273 = 1612705) B1612705
theorem B9179021 : Blo 1431535 9179021 := bstep (se 3 (by rfl) ⟨1721066, by rfl⟩ : syracuseStep 9179021 = 3442133) B3442133
theorem B4837265 : Blo 1431535 4837265 := bstep (se 2 (by rfl) ⟨1813974, by rfl⟩ : syracuseStep 4837265 = 3627949) B3627949
theorem B2150291 : Blo 1431535 2150291 := bstep (se 1 (by rfl) ⟨1612718, by rfl⟩ : syracuseStep 2150291 = 3225437) B3225437
theorem B5435363 : Blo 1431535 5435363 := bstep (se 1 (by rfl) ⟨4076522, by rfl⟩ : syracuseStep 5435363 = 8153045) B8153045
theorem B2904113 : Blo 1431535 2904113 := bstep (se 2 (by rfl) ⟨1089042, by rfl⟩ : syracuseStep 2904113 = 2178085) B2178085
theorem B3223601 : Blo 1431535 3223601 := bstep (se 2 (by rfl) ⟨1208850, by rfl⟩ : syracuseStep 3223601 = 2417701) B2417701
theorem B3223619 : Blo 1431535 3223619 := bstep (se 1 (by rfl) ⟨2417714, by rfl⟩ : syracuseStep 3223619 = 4835429) B4835429
theorem B13947149 : Blo 1431535 13947149 := bstep (se 3 (by rfl) ⟨2615090, by rfl⟩ : syracuseStep 13947149 = 5230181) B5230181
theorem B3223889 : Blo 1431535 3223889 := bstep (se 2 (by rfl) ⟨1208958, by rfl⟩ : syracuseStep 3223889 = 2417917) B2417917
theorem B3223907 : Blo 1431535 3223907 := bstep (se 1 (by rfl) ⟨2417930, by rfl⟩ : syracuseStep 3223907 = 4835861) B4835861
theorem B8155505 : Blo 1431535 8155505 := bstep (se 2 (by rfl) ⟨3058314, by rfl⟩ : syracuseStep 8155505 = 6116629) B6116629
theorem B4837805 : Blo 1431535 4837805 := bstep (se 3 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 4837805 = 1814177) B1814177
theorem B15479221 : Blo 1431535 15479221 := bstep (se 5 (by rfl) ⟨725588, by rfl⟩ : syracuseStep 15479221 = 1451177) B1451177
theorem B4837859 : Blo 1431535 4837859 := bstep (se 1 (by rfl) ⟨3628394, by rfl⟩ : syracuseStep 4837859 = 7256789) B7256789
theorem B4592177 : Blo 1431535 4592177 := bstep (se 2 (by rfl) ⟨1722066, by rfl⟩ : syracuseStep 4592177 = 3444133) B3444133
theorem B5436017 : Blo 1431535 5436017 := bstep (se 2 (by rfl) ⟨2038506, by rfl⟩ : syracuseStep 5436017 = 4077013) B4077013
theorem B3224177 : Blo 1431535 3224177 := bstep (se 2 (by rfl) ⟨1209066, by rfl⟩ : syracuseStep 3224177 = 2418133) B2418133
theorem B3224195 : Blo 1431535 3224195 := bstep (se 1 (by rfl) ⟨2418146, by rfl⟩ : syracuseStep 3224195 = 4836293) B4836293
theorem B3674801 : Blo 1431535 3674801 := bstep (se 2 (by rfl) ⟨1378050, by rfl⟩ : syracuseStep 3674801 = 2756101) B2756101
theorem B3625681 : Blo 1431535 3625681 := bstep (se 2 (by rfl) ⟨1359630, by rfl⟩ : syracuseStep 3625681 = 2719261) B2719261
theorem B3060433 : Blo 1431535 3060433 := bstep (se 2 (by rfl) ⟨1147662, by rfl⟩ : syracuseStep 3060433 = 2295325) B2295325
theorem B6886129 : Blo 1431535 6886129 := bstep (se 2 (by rfl) ⟨2582298, by rfl⟩ : syracuseStep 6886129 = 5164597) B5164597
theorem B4838129 : Blo 1431535 4838129 := bstep (se 2 (by rfl) ⟨1814298, by rfl⟩ : syracuseStep 4838129 = 3628597) B3628597
theorem B1610563 : Blo 1431535 1610563 := bstep (se 1 (by rfl) ⟨1207922, by rfl⟩ : syracuseStep 1610563 = 2415845) B2415845
theorem B3224465 : Blo 1431535 3224465 := bstep (se 2 (by rfl) ⟨1209174, by rfl⟩ : syracuseStep 3224465 = 2418349) B2418349
theorem B3224483 : Blo 1431535 3224483 := bstep (se 1 (by rfl) ⟨2418362, by rfl⟩ : syracuseStep 3224483 = 4836725) B4836725
theorem B1610707 : Blo 1431535 1610707 := bstep (se 1 (by rfl) ⟨1208030, by rfl⟩ : syracuseStep 1610707 = 2416061) B2416061
theorem B3625955 : Blo 1431535 3625955 := bstep (se 1 (by rfl) ⟨2719466, by rfl⟩ : syracuseStep 3625955 = 5438933) B5438933
theorem B4355149 : Blo 1431535 4355149 := bstep (se 3 (by rfl) ⟨816590, by rfl⟩ : syracuseStep 4355149 = 1633181) B1633181
theorem B1610851 : Blo 1431535 1610851 := bstep (se 1 (by rfl) ⟨1208138, by rfl⟩ : syracuseStep 1610851 = 2416277) B2416277
theorem B3626147 : Blo 1431535 3626147 := bstep (se 1 (by rfl) ⟨2719610, by rfl⟩ : syracuseStep 3626147 = 5439221) B5439221
theorem B3224753 : Blo 1431535 3224753 := bstep (se 2 (by rfl) ⟨1209282, by rfl⟩ : syracuseStep 3224753 = 2418565) B2418565
theorem B3224771 : Blo 1431535 3224771 := bstep (se 1 (by rfl) ⟨2418578, by rfl⟩ : syracuseStep 3224771 = 4837157) B4837157
theorem B1610995 : Blo 1431535 1610995 := bstep (se 1 (by rfl) ⟨1208246, by rfl⟩ : syracuseStep 1610995 = 2416493) B2416493
theorem B1529123 : Blo 1431535 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B2905379 : Blo 1431535 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B7255331 : Blo 1431535 7255331 := bstep (se 1 (by rfl) ⟨5441498, by rfl⟩ : syracuseStep 7255331 = 10882997) B10882997
theorem B3487043 : Blo 1431535 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B10327409 : Blo 1431535 10327409 := bstep (se 2 (by rfl) ⟨3872778, by rfl⟩ : syracuseStep 10327409 = 7745557) B7745557
theorem B1611139 : Blo 1431535 1611139 := bstep (se 1 (by rfl) ⟨1208354, by rfl⟩ : syracuseStep 1611139 = 2416709) B2416709
theorem B4355537 : Blo 1431535 4355537 := bstep (se 2 (by rfl) ⟨1633326, by rfl⟩ : syracuseStep 4355537 = 3266653) B3266653
theorem B3225041 : Blo 1431535 3225041 := bstep (se 2 (by rfl) ⟨1209390, by rfl⟩ : syracuseStep 3225041 = 2418781) B2418781
theorem B3225059 : Blo 1431535 3225059 := bstep (se 1 (by rfl) ⟨2418794, by rfl⟩ : syracuseStep 3225059 = 4837589) B4837589
theorem B1611283 : Blo 1431535 1611283 := bstep (se 1 (by rfl) ⟨1208462, by rfl⟩ : syracuseStep 1611283 = 2416925) B2416925
theorem B3487313 : Blo 1431535 3487313 := bstep (se 2 (by rfl) ⟨1307742, by rfl⟩ : syracuseStep 3487313 = 2615485) B2615485
theorem B18347633 : Blo 1431535 18347633 := bstep (se 2 (by rfl) ⟨6880362, by rfl⟩ : syracuseStep 18347633 = 13760725) B13760725
theorem B1611427 : Blo 1431535 1611427 := bstep (se 1 (by rfl) ⟨1208570, by rfl⟩ : syracuseStep 1611427 = 2417141) B2417141
theorem B4077229 : Blo 1431535 4077229 := bstep (se 3 (by rfl) ⟨764480, by rfl⟩ : syracuseStep 4077229 = 1528961) B1528961
theorem B2176723 : Blo 1431535 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B11024099 : Blo 1431535 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B18618083 : Blo 1431535 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B3225329 : Blo 1431535 3225329 := bstep (se 2 (by rfl) ⟨1209498, by rfl⟩ : syracuseStep 3225329 = 2418997) B2418997
theorem B3225347 : Blo 1431535 3225347 := bstep (se 1 (by rfl) ⟨2419010, by rfl⟩ : syracuseStep 3225347 = 4838021) B4838021
theorem B8156963 : Blo 1431535 8156963 := bstep (se 1 (by rfl) ⟨6117722, by rfl⟩ : syracuseStep 8156963 = 12235445) B12235445
theorem B1611571 : Blo 1431535 1611571 := bstep (se 1 (by rfl) ⟨1208678, by rfl⟩ : syracuseStep 1611571 = 2417357) B2417357
theorem B12244877 : Blo 1431535 12244877 := bstep (se 3 (by rfl) ⟨2295914, by rfl⟩ : syracuseStep 12244877 = 4591829) B4591829
theorem B1611715 : Blo 1431535 1611715 := bstep (se 1 (by rfl) ⟨1208786, by rfl⟩ : syracuseStep 1611715 = 2417573) B2417573
theorem B1431539 : Blo 1431535 1431539 := bstep (se 1 (by rfl) ⟨1073654, by rfl⟩ : syracuseStep 1431539 = 2147309) B2147309
theorem B1431555 : Blo 1431535 1431555 := bstep (se 1 (by rfl) ⟨1073666, by rfl⟩ : syracuseStep 1431555 = 2147333) B2147333
theorem B9172997 : Blo 1431535 9172997 := bstep (se 4 (by rfl) ⟨859968, by rfl⟩ : syracuseStep 9172997 = 1719937) B1719937
theorem B7747589 : Blo 1431535 7747589 := bstep (se 4 (by rfl) ⟨726336, by rfl⟩ : syracuseStep 7747589 = 1452673) B1452673
theorem B1431571 : Blo 1431535 1431571 := bstep (se 1 (by rfl) ⟨1073678, by rfl⟩ : syracuseStep 1431571 = 2147357) B2147357
theorem B1529875 : Blo 1431535 1529875 := bstep (se 1 (by rfl) ⟨1147406, by rfl⟩ : syracuseStep 1529875 = 2294813) B2294813
theorem B1431587 : Blo 1431535 1431587 := bstep (se 1 (by rfl) ⟨1073690, by rfl⟩ : syracuseStep 1431587 = 2147381) B2147381
theorem B5437475 : Blo 1431535 5437475 := bstep (se 1 (by rfl) ⟨4078106, by rfl⟩ : syracuseStep 5437475 = 8156213) B8156213
theorem B5437489 : Blo 1431535 5437489 := bstep (se 2 (by rfl) ⟨2039058, by rfl⟩ : syracuseStep 5437489 = 4078117) B4078117
theorem B1431603 : Blo 1431535 1431603 := bstep (se 1 (by rfl) ⟨1073702, by rfl⟩ : syracuseStep 1431603 = 2147405) B2147405
theorem B1431619 : Blo 1431535 1431619 := bstep (se 1 (by rfl) ⟨1073714, by rfl⟩ : syracuseStep 1431619 = 2147429) B2147429
theorem B7256141 : Blo 1431535 7256141 := bstep (se 3 (by rfl) ⟨1360526, by rfl⟩ : syracuseStep 7256141 = 2721053) B2721053
theorem B3627089 : Blo 1431535 3627089 := bstep (se 2 (by rfl) ⟨1360158, by rfl⟩ : syracuseStep 3627089 = 2720317) B2720317
theorem B1431635 : Blo 1431535 1431635 := bstep (se 1 (by rfl) ⟨1073726, by rfl⟩ : syracuseStep 1431635 = 2147453) B2147453
theorem B1611859 : Blo 1431535 1611859 := bstep (se 1 (by rfl) ⟨1208894, by rfl⟩ : syracuseStep 1611859 = 2417789) B2417789
theorem B1431651 : Blo 1431535 1431651 := bstep (se 1 (by rfl) ⟨1073738, by rfl⟩ : syracuseStep 1431651 = 2147477) B2147477
theorem B1431667 : Blo 1431535 1431667 := bstep (se 1 (by rfl) ⟨1073750, by rfl⟩ : syracuseStep 1431667 = 2147501) B2147501
theorem B1431683 : Blo 1431535 1431683 := bstep (se 1 (by rfl) ⟨1073762, by rfl⟩ : syracuseStep 1431683 = 2147525) B2147525
theorem B3627139 : Blo 1431535 3627139 := bstep (se 1 (by rfl) ⟨2720354, by rfl⟩ : syracuseStep 3627139 = 5440709) B5440709
theorem B1431699 : Blo 1431535 1431699 := bstep (se 1 (by rfl) ⟨1073774, by rfl⟩ : syracuseStep 1431699 = 2147549) B2147549
theorem B1431715 : Blo 1431535 1431715 := bstep (se 1 (by rfl) ⟨1073786, by rfl⟩ : syracuseStep 1431715 = 2147573) B2147573
theorem B1431731 : Blo 1431535 1431731 := bstep (se 1 (by rfl) ⟨1073798, by rfl⟩ : syracuseStep 1431731 = 2147597) B2147597
theorem B1431747 : Blo 1431535 1431747 := bstep (se 1 (by rfl) ⟨1073810, by rfl⟩ : syracuseStep 1431747 = 2147621) B2147621
theorem B1431763 : Blo 1431535 1431763 := bstep (se 1 (by rfl) ⟨1073822, by rfl⟩ : syracuseStep 1431763 = 2147645) B2147645
theorem B1431779 : Blo 1431535 1431779 := bstep (se 1 (by rfl) ⟨1073834, by rfl⟩ : syracuseStep 1431779 = 2147669) B2147669
theorem B13064419 : Blo 1431535 13064419 := bstep (se 1 (by rfl) ⟨9798314, by rfl⟩ : syracuseStep 13064419 = 19596629) B19596629
theorem B1612003 : Blo 1431535 1612003 := bstep (se 1 (by rfl) ⟨1209002, by rfl⟩ : syracuseStep 1612003 = 2418005) B2418005
theorem B1431795 : Blo 1431535 1431795 := bstep (se 1 (by rfl) ⟨1073846, by rfl⟩ : syracuseStep 1431795 = 2147693) B2147693
theorem B1431811 : Blo 1431535 1431811 := bstep (se 1 (by rfl) ⟨1073858, by rfl⟩ : syracuseStep 1431811 = 2147717) B2147717
theorem B3627281 : Blo 1431535 3627281 := bstep (se 2 (by rfl) ⟨1360230, by rfl⟩ : syracuseStep 3627281 = 2720461) B2720461
theorem B1431827 : Blo 1431535 1431827 := bstep (se 1 (by rfl) ⟨1073870, by rfl⟩ : syracuseStep 1431827 = 2147741) B2147741
theorem B1431843 : Blo 1431535 1431843 := bstep (se 1 (by rfl) ⟨1073882, by rfl⟩ : syracuseStep 1431843 = 2147765) B2147765
theorem B1431859 : Blo 1431535 1431859 := bstep (se 1 (by rfl) ⟨1073894, by rfl⟩ : syracuseStep 1431859 = 2147789) B2147789
theorem B1431875 : Blo 1431535 1431875 := bstep (se 1 (by rfl) ⟨1073906, by rfl⟩ : syracuseStep 1431875 = 2147813) B2147813
theorem B1431891 : Blo 1431535 1431891 := bstep (se 1 (by rfl) ⟨1073918, by rfl⟩ : syracuseStep 1431891 = 2147837) B2147837
theorem B1431907 : Blo 1431535 1431907 := bstep (se 1 (by rfl) ⟨1073930, by rfl⟩ : syracuseStep 1431907 = 2147861) B2147861
theorem B12237155 : Blo 1431535 12237155 := bstep (se 1 (by rfl) ⟨9177866, by rfl⟩ : syracuseStep 12237155 = 18355733) B18355733
theorem B1431923 : Blo 1431535 1431923 := bstep (se 1 (by rfl) ⟨1073942, by rfl⟩ : syracuseStep 1431923 = 2147885) B2147885
theorem B1612147 : Blo 1431535 1612147 := bstep (se 1 (by rfl) ⟨1209110, by rfl⟩ : syracuseStep 1612147 = 2418221) B2418221
theorem B1431939 : Blo 1431535 1431939 := bstep (se 1 (by rfl) ⟨1073954, by rfl⟩ : syracuseStep 1431939 = 2147909) B2147909
theorem B1431955 : Blo 1431535 1431955 := bstep (se 1 (by rfl) ⟨1073966, by rfl⟩ : syracuseStep 1431955 = 2147933) B2147933
theorem B1431971 : Blo 1431535 1431971 := bstep (se 1 (by rfl) ⟨1073978, by rfl⟩ : syracuseStep 1431971 = 2147957) B2147957
theorem B1431987 : Blo 1431535 1431987 := bstep (se 1 (by rfl) ⟨1073990, by rfl⟩ : syracuseStep 1431987 = 2147981) B2147981
theorem B1432003 : Blo 1431535 1432003 := bstep (se 1 (by rfl) ⟨1074002, by rfl⟩ : syracuseStep 1432003 = 2148005) B2148005
theorem B1432019 : Blo 1431535 1432019 := bstep (se 1 (by rfl) ⟨1074014, by rfl⟩ : syracuseStep 1432019 = 2148029) B2148029
theorem B1432035 : Blo 1431535 1432035 := bstep (se 1 (by rfl) ⟨1074026, by rfl⟩ : syracuseStep 1432035 = 2148053) B2148053
theorem B6117859 : Blo 1431535 6117859 := bstep (se 1 (by rfl) ⟨4588394, by rfl⟩ : syracuseStep 6117859 = 9176789) B9176789
theorem B1432051 : Blo 1431535 1432051 := bstep (se 1 (by rfl) ⟨1074038, by rfl⟩ : syracuseStep 1432051 = 2148077) B2148077
theorem B1432067 : Blo 1431535 1432067 := bstep (se 1 (by rfl) ⟨1074050, by rfl⟩ : syracuseStep 1432067 = 2148101) B2148101
theorem B1612291 : Blo 1431535 1612291 := bstep (se 1 (by rfl) ⟨1209218, by rfl⟩ : syracuseStep 1612291 = 2418437) B2418437
theorem B4831757 : Blo 1431535 4831757 := bstep (se 3 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 4831757 = 1811909) B1811909
theorem B1432083 : Blo 1431535 1432083 := bstep (se 1 (by rfl) ⟨1074062, by rfl⟩ : syracuseStep 1432083 = 2148125) B2148125
theorem B1432099 : Blo 1431535 1432099 := bstep (se 1 (by rfl) ⟨1074074, by rfl⟩ : syracuseStep 1432099 = 2148149) B2148149
theorem B1432115 : Blo 1431535 1432115 := bstep (se 1 (by rfl) ⟨1074086, by rfl⟩ : syracuseStep 1432115 = 2148173) B2148173
theorem B4831811 : Blo 1431535 4831811 := bstep (se 1 (by rfl) ⟨3623858, by rfl⟩ : syracuseStep 4831811 = 7247717) B7247717
theorem B1432131 : Blo 1431535 1432131 := bstep (se 1 (by rfl) ⟨1074098, by rfl⟩ : syracuseStep 1432131 = 2148197) B2148197
theorem B2718289 : Blo 1431535 2718289 := bstep (se 2 (by rfl) ⟨1019358, by rfl⟩ : syracuseStep 2718289 = 2038717) B2038717
theorem B1432147 : Blo 1431535 1432147 := bstep (se 1 (by rfl) ⟨1074110, by rfl⟩ : syracuseStep 1432147 = 2148221) B2148221
theorem B1432163 : Blo 1431535 1432163 := bstep (se 1 (by rfl) ⟨1074122, by rfl⟩ : syracuseStep 1432163 = 2148245) B2148245
theorem B2038387 : Blo 1431535 2038387 := bstep (se 1 (by rfl) ⟨1528790, by rfl⟩ : syracuseStep 2038387 = 3057581) B3057581
theorem B1432179 : Blo 1431535 1432179 := bstep (se 1 (by rfl) ⟨1074134, by rfl⟩ : syracuseStep 1432179 = 2148269) B2148269
theorem B1432195 : Blo 1431535 1432195 := bstep (se 1 (by rfl) ⟨1074146, by rfl⟩ : syracuseStep 1432195 = 2148293) B2148293
theorem B4586129 : Blo 1431535 4586129 := bstep (se 2 (by rfl) ⟨1719798, by rfl⟩ : syracuseStep 4586129 = 3439597) B3439597
theorem B1432211 : Blo 1431535 1432211 := bstep (se 1 (by rfl) ⟨1074158, by rfl⟩ : syracuseStep 1432211 = 2148317) B2148317
theorem B1612435 : Blo 1431535 1612435 := bstep (se 1 (by rfl) ⟨1209326, by rfl⟩ : syracuseStep 1612435 = 2418653) B2418653
theorem B1432227 : Blo 1431535 1432227 := bstep (se 1 (by rfl) ⟨1074170, by rfl⟩ : syracuseStep 1432227 = 2148341) B2148341
theorem B1432243 : Blo 1431535 1432243 := bstep (se 1 (by rfl) ⟨1074182, by rfl⟩ : syracuseStep 1432243 = 2148365) B2148365
theorem B1432259 : Blo 1431535 1432259 := bstep (se 1 (by rfl) ⟨1074194, by rfl⟩ : syracuseStep 1432259 = 2148389) B2148389
theorem B4078289 : Blo 1431535 4078289 := bstep (se 2 (by rfl) ⟨1529358, by rfl⟩ : syracuseStep 4078289 = 3058717) B3058717
theorem B1432275 : Blo 1431535 1432275 := bstep (se 1 (by rfl) ⟨1074206, by rfl⟩ : syracuseStep 1432275 = 2148413) B2148413
theorem B1432291 : Blo 1431535 1432291 := bstep (se 1 (by rfl) ⟨1074218, by rfl⟩ : syracuseStep 1432291 = 2148437) B2148437
theorem B3488483 : Blo 1431535 3488483 := bstep (se 1 (by rfl) ⟨2616362, by rfl⟩ : syracuseStep 3488483 = 5232725) B5232725
theorem B1432307 : Blo 1431535 1432307 := bstep (se 1 (by rfl) ⟨1074230, by rfl⟩ : syracuseStep 1432307 = 2148461) B2148461
theorem B1432323 : Blo 1431535 1432323 := bstep (se 1 (by rfl) ⟨1074242, by rfl⟩ : syracuseStep 1432323 = 2148485) B2148485
theorem B1432339 : Blo 1431535 1432339 := bstep (se 1 (by rfl) ⟨1074254, by rfl⟩ : syracuseStep 1432339 = 2148509) B2148509
theorem B1432355 : Blo 1431535 1432355 := bstep (se 1 (by rfl) ⟨1074266, by rfl⟩ : syracuseStep 1432355 = 2148533) B2148533
theorem B1612579 : Blo 1431535 1612579 := bstep (se 1 (by rfl) ⟨1209434, by rfl⟩ : syracuseStep 1612579 = 2418869) B2418869
theorem B7248689 : Blo 1431535 7248689 := bstep (se 2 (by rfl) ⟨2718258, by rfl⟩ : syracuseStep 7248689 = 5436517) B5436517
theorem B1432371 : Blo 1431535 1432371 := bstep (se 1 (by rfl) ⟨1074278, by rfl⟩ : syracuseStep 1432371 = 2148557) B2148557
theorem B1432387 : Blo 1431535 1432387 := bstep (se 1 (by rfl) ⟨1074290, by rfl⟩ : syracuseStep 1432387 = 2148581) B2148581
theorem B4832081 : Blo 1431535 4832081 := bstep (se 2 (by rfl) ⟨1812030, by rfl⟩ : syracuseStep 4832081 = 3624061) B3624061
theorem B1432403 : Blo 1431535 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B1432419 : Blo 1431535 1432419 := bstep (se 1 (by rfl) ⟨1074314, by rfl⟩ : syracuseStep 1432419 = 2148629) B2148629
theorem B1432435 : Blo 1431535 1432435 := bstep (se 1 (by rfl) ⟨1074326, by rfl⟩ : syracuseStep 1432435 = 2148653) B2148653
theorem B1432451 : Blo 1431535 1432451 := bstep (se 1 (by rfl) ⟨1074338, by rfl⟩ : syracuseStep 1432451 = 2148677) B2148677
theorem B1432467 : Blo 1431535 1432467 := bstep (se 1 (by rfl) ⟨1074350, by rfl⟩ : syracuseStep 1432467 = 2148701) B2148701
theorem B1432483 : Blo 1431535 1432483 := bstep (se 1 (by rfl) ⟨1074362, by rfl⟩ : syracuseStep 1432483 = 2148725) B2148725
theorem B3980209 : Blo 1431535 3980209 := bstep (se 2 (by rfl) ⟨1492578, by rfl⟩ : syracuseStep 3980209 = 2985157) B2985157
theorem B1432499 : Blo 1431535 1432499 := bstep (se 1 (by rfl) ⟨1074374, by rfl⟩ : syracuseStep 1432499 = 2148749) B2148749
theorem B1612723 : Blo 1431535 1612723 := bstep (se 1 (by rfl) ⟨1209542, by rfl⟩ : syracuseStep 1612723 = 2419085) B2419085
theorem B1432515 : Blo 1431535 1432515 := bstep (se 1 (by rfl) ⟨1074386, by rfl⟩ : syracuseStep 1432515 = 2148773) B2148773
theorem B1432531 : Blo 1431535 1432531 := bstep (se 1 (by rfl) ⟨1074398, by rfl⟩ : syracuseStep 1432531 = 2148797) B2148797
theorem B1432547 : Blo 1431535 1432547 := bstep (se 1 (by rfl) ⟨1074410, by rfl⟩ : syracuseStep 1432547 = 2148821) B2148821
theorem B1432563 : Blo 1431535 1432563 := bstep (se 1 (by rfl) ⟨1074422, by rfl⟩ : syracuseStep 1432563 = 2148845) B2148845
theorem B1432579 : Blo 1431535 1432579 := bstep (se 1 (by rfl) ⟨1074434, by rfl⟩ : syracuseStep 1432579 = 2148869) B2148869
theorem B9305093 : Blo 1431535 9305093 := bstep (se 4 (by rfl) ⟨872352, by rfl⟩ : syracuseStep 9305093 = 1744705) B1744705
theorem B1432595 : Blo 1431535 1432595 := bstep (se 1 (by rfl) ⟨1074446, by rfl⟩ : syracuseStep 1432595 = 2148893) B2148893
theorem B1432611 : Blo 1431535 1432611 := bstep (se 1 (by rfl) ⟨1074458, by rfl⟩ : syracuseStep 1432611 = 2148917) B2148917
theorem B1432627 : Blo 1431535 1432627 := bstep (se 1 (by rfl) ⟨1074470, by rfl⟩ : syracuseStep 1432627 = 2148941) B2148941
theorem B1432643 : Blo 1431535 1432643 := bstep (se 1 (by rfl) ⟨1074482, by rfl⟩ : syracuseStep 1432643 = 2148965) B2148965
theorem B13769797 : Blo 1431535 13769797 := bstep (se 4 (by rfl) ⟨1290918, by rfl⟩ : syracuseStep 13769797 = 2581837) B2581837
theorem B1432659 : Blo 1431535 1432659 := bstep (se 1 (by rfl) ⟨1074494, by rfl⟩ : syracuseStep 1432659 = 2148989) B2148989
theorem B1432675 : Blo 1431535 1432675 := bstep (se 1 (by rfl) ⟨1074506, by rfl⟩ : syracuseStep 1432675 = 2149013) B2149013
theorem B1432691 : Blo 1431535 1432691 := bstep (se 1 (by rfl) ⟨1074518, by rfl⟩ : syracuseStep 1432691 = 2149037) B2149037
theorem B1432707 : Blo 1431535 1432707 := bstep (se 1 (by rfl) ⟨1074530, by rfl⟩ : syracuseStep 1432707 = 2149061) B2149061
theorem B1432723 : Blo 1431535 1432723 := bstep (se 1 (by rfl) ⟨1074542, by rfl⟩ : syracuseStep 1432723 = 2149085) B2149085
theorem B2038945 : Blo 1431535 2038945 := bstep (se 2 (by rfl) ⟨764604, by rfl⟩ : syracuseStep 2038945 = 1529209) B1529209
theorem B1432739 : Blo 1431535 1432739 := bstep (se 1 (by rfl) ⟨1074554, by rfl⟩ : syracuseStep 1432739 = 2149109) B2149109
theorem B1432755 : Blo 1431535 1432755 := bstep (se 1 (by rfl) ⟨1074566, by rfl⟩ : syracuseStep 1432755 = 2149133) B2149133
theorem B2415811 : Blo 1431535 2415811 := bstep (se 1 (by rfl) ⟨1811858, by rfl⟩ : syracuseStep 2415811 = 3623717) B3623717
theorem B2038979 : Blo 1431535 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B1432771 : Blo 1431535 1432771 := bstep (se 1 (by rfl) ⟨1074578, by rfl⟩ : syracuseStep 1432771 = 2149157) B2149157
theorem B39214277 : Blo 1431535 39214277 := bstep (se 4 (by rfl) ⟨3676338, by rfl⟩ : syracuseStep 39214277 = 7352677) B7352677
theorem B1432787 : Blo 1431535 1432787 := bstep (se 1 (by rfl) ⟨1074590, by rfl⟩ : syracuseStep 1432787 = 2149181) B2149181
theorem B1432803 : Blo 1431535 1432803 := bstep (se 1 (by rfl) ⟨1074602, by rfl⟩ : syracuseStep 1432803 = 2149205) B2149205
theorem B3628273 : Blo 1431535 3628273 := bstep (se 2 (by rfl) ⟨1360602, by rfl⟩ : syracuseStep 3628273 = 2721205) B2721205
theorem B1432819 : Blo 1431535 1432819 := bstep (se 1 (by rfl) ⟨1074614, by rfl⟩ : syracuseStep 1432819 = 2149229) B2149229
theorem B1432835 : Blo 1431535 1432835 := bstep (se 1 (by rfl) ⟨1074626, by rfl⟩ : syracuseStep 1432835 = 2149253) B2149253
theorem B1432851 : Blo 1431535 1432851 := bstep (se 1 (by rfl) ⟨1074638, by rfl⟩ : syracuseStep 1432851 = 2149277) B2149277
theorem B1432867 : Blo 1431535 1432867 := bstep (se 1 (by rfl) ⟨1074650, by rfl⟩ : syracuseStep 1432867 = 2149301) B2149301
theorem B2178353 : Blo 1431535 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B1432883 : Blo 1431535 1432883 := bstep (se 1 (by rfl) ⟨1074662, by rfl⟩ : syracuseStep 1432883 = 2149325) B2149325
theorem B1432899 : Blo 1431535 1432899 := bstep (se 1 (by rfl) ⟨1074674, by rfl⟩ : syracuseStep 1432899 = 2149349) B2149349
theorem B2415953 : Blo 1431535 2415953 := bstep (se 2 (by rfl) ⟨905982, by rfl⟩ : syracuseStep 2415953 = 1811965) B1811965
theorem B1432915 : Blo 1431535 1432915 := bstep (se 1 (by rfl) ⟨1074686, by rfl⟩ : syracuseStep 1432915 = 2149373) B2149373
theorem B1432931 : Blo 1431535 1432931 := bstep (se 1 (by rfl) ⟨1074698, by rfl⟩ : syracuseStep 1432931 = 2149397) B2149397
theorem B4832621 : Blo 1431535 4832621 := bstep (se 3 (by rfl) ⟨906116, by rfl⟩ : syracuseStep 4832621 = 1812233) B1812233
theorem B4078961 : Blo 1431535 4078961 := bstep (se 2 (by rfl) ⟨1529610, by rfl⟩ : syracuseStep 4078961 = 3059221) B3059221
theorem B1432947 : Blo 1431535 1432947 := bstep (se 1 (by rfl) ⟨1074710, by rfl⟩ : syracuseStep 1432947 = 2149421) B2149421
theorem B3538289 : Blo 1431535 3538289 := bstep (se 2 (by rfl) ⟨1326858, by rfl⟩ : syracuseStep 3538289 = 2653717) B2653717
theorem B2293121 : Blo 1431535 2293121 := bstep (se 2 (by rfl) ⟨859920, by rfl⟩ : syracuseStep 2293121 = 1719841) B1719841
theorem B1432963 : Blo 1431535 1432963 := bstep (se 1 (by rfl) ⟨1074722, by rfl⟩ : syracuseStep 1432963 = 2149445) B2149445
theorem B2448787 : Blo 1431535 2448787 := bstep (se 1 (by rfl) ⟨1836590, by rfl⟩ : syracuseStep 2448787 = 3673181) B3673181
theorem B1432979 : Blo 1431535 1432979 := bstep (se 1 (by rfl) ⟨1074734, by rfl⟩ : syracuseStep 1432979 = 2149469) B2149469
theorem B4832675 : Blo 1431535 4832675 := bstep (se 1 (by rfl) ⟨3624506, by rfl⟩ : syracuseStep 4832675 = 7249013) B7249013
theorem B1432995 : Blo 1431535 1432995 := bstep (se 1 (by rfl) ⟨1074746, by rfl⟩ : syracuseStep 1432995 = 2149493) B2149493
theorem B1433011 : Blo 1431535 1433011 := bstep (se 1 (by rfl) ⟨1074758, by rfl⟩ : syracuseStep 1433011 = 2149517) B2149517
theorem B1433027 : Blo 1431535 1433027 := bstep (se 1 (by rfl) ⟨1074770, by rfl⟩ : syracuseStep 1433027 = 2149541) B2149541
theorem B2416081 : Blo 1431535 2416081 := bstep (se 2 (by rfl) ⟨906030, by rfl⟩ : syracuseStep 2416081 = 1812061) B1812061
theorem B4718033 : Blo 1431535 4718033 := bstep (se 2 (by rfl) ⟨1769262, by rfl⟩ : syracuseStep 4718033 = 3538525) B3538525
theorem B1433043 : Blo 1431535 1433043 := bstep (se 1 (by rfl) ⟨1074782, by rfl⟩ : syracuseStep 1433043 = 2149565) B2149565
theorem B5438947 : Blo 1431535 5438947 := bstep (se 1 (by rfl) ⟨4079210, by rfl⟩ : syracuseStep 5438947 = 8158421) B8158421
theorem B1433059 : Blo 1431535 1433059 := bstep (se 1 (by rfl) ⟨1074794, by rfl⟩ : syracuseStep 1433059 = 2149589) B2149589
theorem B2416115 : Blo 1431535 2416115 := bstep (se 1 (by rfl) ⟨1812086, by rfl⟩ : syracuseStep 2416115 = 3624173) B3624173
theorem B1433075 : Blo 1431535 1433075 := bstep (se 1 (by rfl) ⟨1074806, by rfl⟩ : syracuseStep 1433075 = 2149613) B2149613
theorem B1433091 : Blo 1431535 1433091 := bstep (se 1 (by rfl) ⟨1074818, by rfl⟩ : syracuseStep 1433091 = 2149637) B2149637
theorem B3628547 : Blo 1431535 3628547 := bstep (se 1 (by rfl) ⟨2721410, by rfl⟩ : syracuseStep 3628547 = 5442821) B5442821
theorem B1433107 : Blo 1431535 1433107 := bstep (se 1 (by rfl) ⟨1074830, by rfl⟩ : syracuseStep 1433107 = 2149661) B2149661
theorem B1433123 : Blo 1431535 1433123 := bstep (se 1 (by rfl) ⟨1074842, by rfl⟩ : syracuseStep 1433123 = 2149685) B2149685
theorem B1433139 : Blo 1431535 1433139 := bstep (se 1 (by rfl) ⟨1074854, by rfl⟩ : syracuseStep 1433139 = 2149709) B2149709
theorem B1433155 : Blo 1431535 1433155 := bstep (se 1 (by rfl) ⟨1074866, by rfl⟩ : syracuseStep 1433155 = 2149733) B2149733
theorem B1433171 : Blo 1431535 1433171 := bstep (se 1 (by rfl) ⟨1074878, by rfl⟩ : syracuseStep 1433171 = 2149757) B2149757
theorem B1433187 : Blo 1431535 1433187 := bstep (se 1 (by rfl) ⟨1074890, by rfl⟩ : syracuseStep 1433187 = 2149781) B2149781
theorem B2719345 : Blo 1431535 2719345 := bstep (se 2 (by rfl) ⟨1019754, by rfl⟩ : syracuseStep 2719345 = 2039509) B2039509
theorem B2416243 : Blo 1431535 2416243 := bstep (se 1 (by rfl) ⟨1812182, by rfl⟩ : syracuseStep 2416243 = 3624365) B3624365
theorem B1433203 : Blo 1431535 1433203 := bstep (se 1 (by rfl) ⟨1074902, by rfl⟩ : syracuseStep 1433203 = 2149805) B2149805
theorem B4136579 : Blo 1431535 4136579 := bstep (se 1 (by rfl) ⟨3102434, by rfl⟩ : syracuseStep 4136579 = 6204869) B6204869
theorem B1433219 : Blo 1431535 1433219 := bstep (se 1 (by rfl) ⟨1074914, by rfl⟩ : syracuseStep 1433219 = 2149829) B2149829
theorem B27541133 : Blo 1431535 27541133 := bstep (se 3 (by rfl) ⟨5163962, by rfl⟩ : syracuseStep 27541133 = 10327925) B10327925
theorem B1433235 : Blo 1431535 1433235 := bstep (se 1 (by rfl) ⟨1074926, by rfl⟩ : syracuseStep 1433235 = 2149853) B2149853
theorem B1433251 : Blo 1431535 1433251 := bstep (se 1 (by rfl) ⟨1074938, by rfl⟩ : syracuseStep 1433251 = 2149877) B2149877
theorem B4832945 : Blo 1431535 4832945 := bstep (se 2 (by rfl) ⟨1812354, by rfl⟩ : syracuseStep 4832945 = 3624709) B3624709
theorem B1433267 : Blo 1431535 1433267 := bstep (se 1 (by rfl) ⟨1074950, by rfl⟩ : syracuseStep 1433267 = 2149901) B2149901
theorem B1433283 : Blo 1431535 1433283 := bstep (se 1 (by rfl) ⟨1074962, by rfl⟩ : syracuseStep 1433283 = 2149925) B2149925
theorem B1433299 : Blo 1431535 1433299 := bstep (se 1 (by rfl) ⟨1074974, by rfl⟩ : syracuseStep 1433299 = 2149949) B2149949
theorem B1433315 : Blo 1431535 1433315 := bstep (se 1 (by rfl) ⟨1074986, by rfl⟩ : syracuseStep 1433315 = 2149973) B2149973
theorem B2039537 : Blo 1431535 2039537 := bstep (se 2 (by rfl) ⟨764826, by rfl⟩ : syracuseStep 2039537 = 1529653) B1529653
theorem B7749361 : Blo 1431535 7749361 := bstep (se 2 (by rfl) ⟨2906010, by rfl⟩ : syracuseStep 7749361 = 5812021) B5812021
theorem B1433331 : Blo 1431535 1433331 := bstep (se 1 (by rfl) ⟨1074998, by rfl⟩ : syracuseStep 1433331 = 2149997) B2149997
theorem B2416385 : Blo 1431535 2416385 := bstep (se 2 (by rfl) ⟨906144, by rfl⟩ : syracuseStep 2416385 = 1812289) B1812289
theorem B1433347 : Blo 1431535 1433347 := bstep (se 1 (by rfl) ⟨1075010, by rfl⟩ : syracuseStep 1433347 = 2150021) B2150021
theorem B1433363 : Blo 1431535 1433363 := bstep (se 1 (by rfl) ⟨1075022, by rfl⟩ : syracuseStep 1433363 = 2150045) B2150045
theorem B1433379 : Blo 1431535 1433379 := bstep (se 1 (by rfl) ⟨1075034, by rfl⟩ : syracuseStep 1433379 = 2150069) B2150069
theorem B1433395 : Blo 1431535 1433395 := bstep (se 1 (by rfl) ⟨1075046, by rfl⟩ : syracuseStep 1433395 = 2150093) B2150093
theorem B2039617 : Blo 1431535 2039617 := bstep (se 2 (by rfl) ⟨764856, by rfl⟩ : syracuseStep 2039617 = 1529713) B1529713
theorem B1433411 : Blo 1431535 1433411 := bstep (se 1 (by rfl) ⟨1075058, by rfl⟩ : syracuseStep 1433411 = 2150117) B2150117
theorem B1433427 : Blo 1431535 1433427 := bstep (se 1 (by rfl) ⟨1075070, by rfl⟩ : syracuseStep 1433427 = 2150141) B2150141
theorem B2178913 : Blo 1431535 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B1433443 : Blo 1431535 1433443 := bstep (se 1 (by rfl) ⟨1075082, by rfl⟩ : syracuseStep 1433443 = 2150165) B2150165
theorem B35307377 : Blo 1431535 35307377 := bstep (se 2 (by rfl) ⟨13240266, by rfl⟩ : syracuseStep 35307377 = 26480533) B26480533
theorem B2449265 : Blo 1431535 2449265 := bstep (se 2 (by rfl) ⟨918474, by rfl⟩ : syracuseStep 2449265 = 1836949) B1836949
theorem B1433459 : Blo 1431535 1433459 := bstep (se 1 (by rfl) ⟨1075094, by rfl⟩ : syracuseStep 1433459 = 2150189) B2150189
theorem B3678065 : Blo 1431535 3678065 := bstep (se 2 (by rfl) ⟨1379274, by rfl⟩ : syracuseStep 3678065 = 2758549) B2758549
theorem B2416513 : Blo 1431535 2416513 := bstep (se 2 (by rfl) ⟨906192, by rfl⟩ : syracuseStep 2416513 = 1812385) B1812385
theorem B1433475 : Blo 1431535 1433475 := bstep (se 1 (by rfl) ⟨1075106, by rfl⟩ : syracuseStep 1433475 = 2150213) B2150213
theorem B1433491 : Blo 1431535 1433491 := bstep (se 1 (by rfl) ⟨1075118, by rfl⟩ : syracuseStep 1433491 = 2150237) B2150237
theorem B2416547 : Blo 1431535 2416547 := bstep (se 1 (by rfl) ⟨1812410, by rfl⟩ : syracuseStep 2416547 = 3624821) B3624821
theorem B1433507 : Blo 1431535 1433507 := bstep (se 1 (by rfl) ⟨1075130, by rfl⟩ : syracuseStep 1433507 = 2150261) B2150261
theorem B1433523 : Blo 1431535 1433523 := bstep (se 1 (by rfl) ⟨1075142, by rfl⟩ : syracuseStep 1433523 = 2150285) B2150285
theorem B2039833 : Blo 1431535 2039833 := bstep (se 2 (by rfl) ⟨764937, by rfl⟩ : syracuseStep 2039833 = 1529875) B1529875
theorem B7249985 : Blo 1431535 7249985 := bstep (se 2 (by rfl) ⟨2718744, by rfl⟩ : syracuseStep 7249985 = 5437489) B5437489
theorem B2719831 : Blo 1431535 2719831 := bstep (se 1 (by rfl) ⟨2039873, by rfl⟩ : syracuseStep 2719831 = 4079747) B4079747
theorem B2416729 : Blo 1431535 2416729 := bstep (se 2 (by rfl) ⟨906273, by rfl⟩ : syracuseStep 2416729 = 1812547) B1812547
theorem B4833431 : Blo 1431535 4833431 := bstep (se 1 (by rfl) ⟨3625073, by rfl⟩ : syracuseStep 4833431 = 7250147) B7250147
theorem B9298099 : Blo 1431535 9298099 := bstep (se 1 (by rfl) ⟨6973574, by rfl⟩ : syracuseStep 9298099 = 13947149) B13947149
theorem B2326745 : Blo 1431535 2326745 := bstep (se 2 (by rfl) ⟨872529, by rfl⟩ : syracuseStep 2326745 = 1745059) B1745059
theorem B13066541 : Blo 1431535 13066541 := bstep (se 3 (by rfl) ⟨2449976, by rfl⟩ : syracuseStep 13066541 = 4899953) B4899953
theorem B2720051 : Blo 1431535 2720051 := bstep (se 1 (by rfl) ⟨2040038, by rfl⟩ : syracuseStep 2720051 = 4080077) B4080077
theorem B8716619 : Blo 1431535 8716619 := bstep (se 1 (by rfl) ⟨6537464, by rfl⟩ : syracuseStep 8716619 = 13074929) B13074929
theorem B16310645 : Blo 1431535 16310645 := bstep (se 5 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 16310645 = 1529123) B1529123
theorem B13763033 : Blo 1431535 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B13066757 : Blo 1431535 13066757 := bstep (se 4 (by rfl) ⟨1225008, by rfl⟩ : syracuseStep 13066757 = 2450017) B2450017
theorem B2720279 : Blo 1431535 2720279 := bstep (se 1 (by rfl) ⟨2040209, by rfl⟩ : syracuseStep 2720279 = 4080419) B4080419
theorem B9798209 : Blo 1431535 9798209 := bstep (se 2 (by rfl) ⟨3674328, by rfl⟩ : syracuseStep 9798209 = 7348657) B7348657
theorem B4080203 : Blo 1431535 4080203 := bstep (se 1 (by rfl) ⟨3060152, by rfl⟩ : syracuseStep 4080203 = 6120305) B6120305
theorem B11027045 : Blo 1431535 11027045 := bstep (se 4 (by rfl) ⟨1033785, by rfl⟩ : syracuseStep 11027045 = 2067571) B2067571
theorem B2417303 : Blo 1431535 2417303 := bstep (se 1 (by rfl) ⟨1812977, by rfl⟩ : syracuseStep 2417303 = 3625955) B3625955
theorem B4833971 : Blo 1431535 4833971 := bstep (se 1 (by rfl) ⟨3625478, by rfl⟩ : syracuseStep 4833971 = 7250957) B7250957
theorem B5440193 : Blo 1431535 5440193 := bstep (se 2 (by rfl) ⟨2040072, by rfl⟩ : syracuseStep 5440193 = 4080145) B4080145
theorem B2417431 : Blo 1431535 2417431 := bstep (se 1 (by rfl) ⟨1813073, by rfl⟩ : syracuseStep 2417431 = 3626147) B3626147
theorem B2720537 : Blo 1431535 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B5808941 : Blo 1431535 5808941 := bstep (se 3 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 5808941 = 2178353) B2178353
theorem B4834241 : Blo 1431535 4834241 := bstep (se 2 (by rfl) ⟨1812840, by rfl⟩ : syracuseStep 4834241 = 3625681) B3625681
theorem B2147339 : Blo 1431535 2147339 := bstep (se 1 (by rfl) ⟨1610504, by rfl⟩ : syracuseStep 2147339 = 3221009) B3221009
theorem B2147351 : Blo 1431535 2147351 := bstep (se 1 (by rfl) ⟨1610513, by rfl⟩ : syracuseStep 2147351 = 3221027) B3221027
theorem B12231755 : Blo 1431535 12231755 := bstep (se 1 (by rfl) ⟨9173816, by rfl⟩ : syracuseStep 12231755 = 18347633) B18347633
theorem B2147417 : Blo 1431535 2147417 := bstep (se 2 (by rfl) ⟨805281, by rfl⟩ : syracuseStep 2147417 = 1610563) B1610563
theorem B11609189 : Blo 1431535 11609189 := bstep (se 4 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 11609189 = 2176723) B2176723
theorem B6120593 : Blo 1431535 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B7349399 : Blo 1431535 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B12412055 : Blo 1431535 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B2720947 : Blo 1431535 2720947 := bstep (se 1 (by rfl) ⟨2040710, by rfl⟩ : syracuseStep 2720947 = 4081421) B4081421
theorem B2147531 : Blo 1431535 2147531 := bstep (se 1 (by rfl) ⟨1610648, by rfl⟩ : syracuseStep 2147531 = 3221297) B3221297
theorem B2147543 : Blo 1431535 2147543 := bstep (se 1 (by rfl) ⟨1610657, by rfl⟩ : syracuseStep 2147543 = 3221315) B3221315
theorem B41329925 : Blo 1431535 41329925 := bstep (se 4 (by rfl) ⟨3874680, by rfl⟩ : syracuseStep 41329925 = 7749361) B7749361
theorem B2147609 : Blo 1431535 2147609 := bstep (se 2 (by rfl) ⟨805353, by rfl⟩ : syracuseStep 2147609 = 1610707) B1610707
theorem B8160587 : Blo 1431535 8160587 := bstep (se 1 (by rfl) ⟨6120440, by rfl⟩ : syracuseStep 8160587 = 12240881) B12240881
theorem B2147723 : Blo 1431535 2147723 := bstep (se 1 (by rfl) ⟨1610792, by rfl⟩ : syracuseStep 2147723 = 3221585) B3221585
theorem B2418059 : Blo 1431535 2418059 := bstep (se 1 (by rfl) ⟨1813544, by rfl⟩ : syracuseStep 2418059 = 3627089) B3627089
theorem B2147735 : Blo 1431535 2147735 := bstep (se 1 (by rfl) ⟨1610801, by rfl⟩ : syracuseStep 2147735 = 3221603) B3221603
theorem B18359729 : Blo 1431535 18359729 := bstep (se 2 (by rfl) ⟨6884898, by rfl⟩ : syracuseStep 18359729 = 13769797) B13769797
theorem B2147801 : Blo 1431535 2147801 := bstep (se 2 (by rfl) ⟨805425, by rfl⟩ : syracuseStep 2147801 = 1610851) B1610851
theorem B4834781 : Blo 1431535 4834781 := bstep (se 3 (by rfl) ⟨906521, by rfl⟩ : syracuseStep 4834781 = 1813043) B1813043
theorem B2418187 : Blo 1431535 2418187 := bstep (se 1 (by rfl) ⟨1813640, by rfl⟩ : syracuseStep 2418187 = 3627281) B3627281
theorem B24823331 : Blo 1431535 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B9299501 : Blo 1431535 9299501 := bstep (se 3 (by rfl) ⟨1743656, by rfl⟩ : syracuseStep 9299501 = 3487313) B3487313
theorem B2147915 : Blo 1431535 2147915 := bstep (se 1 (by rfl) ⟨1610936, by rfl⟩ : syracuseStep 2147915 = 3221873) B3221873
theorem B2295371 : Blo 1431535 2295371 := bstep (se 1 (by rfl) ⟨1721528, by rfl⟩ : syracuseStep 2295371 = 3443057) B3443057
theorem B2147927 : Blo 1431535 2147927 := bstep (se 1 (by rfl) ⟨1610945, by rfl⟩ : syracuseStep 2147927 = 3221891) B3221891
theorem B3221081 : Blo 1431535 3221081 := bstep (se 2 (by rfl) ⟨1207905, by rfl⟩ : syracuseStep 3221081 = 2415811) B2415811
theorem B2147993 : Blo 1431535 2147993 := bstep (se 2 (by rfl) ⟨805497, by rfl⟩ : syracuseStep 2147993 = 1610995) B1610995
theorem B2418329 : Blo 1431535 2418329 := bstep (se 2 (by rfl) ⟨906873, by rfl⟩ : syracuseStep 2418329 = 1813747) B1813747
theorem B2721433 : Blo 1431535 2721433 := bstep (se 2 (by rfl) ⟨1020537, by rfl⟩ : syracuseStep 2721433 = 2041075) B2041075
theorem B6538925 : Blo 1431535 6538925 := bstep (se 3 (by rfl) ⟨1226048, by rfl⟩ : syracuseStep 6538925 = 2452097) B2452097
theorem B3221171 : Blo 1431535 3221171 := bstep (se 1 (by rfl) ⟨2415878, by rfl⟩ : syracuseStep 3221171 = 4831757) B4831757
theorem B3221207 : Blo 1431535 3221207 := bstep (se 1 (by rfl) ⟨2415905, by rfl⟩ : syracuseStep 3221207 = 4831811) B4831811
theorem B1492715 : Blo 1431535 1492715 := bstep (se 1 (by rfl) ⟨1119536, by rfl⟩ : syracuseStep 1492715 = 2239073) B2239073
theorem B3057419 : Blo 1431535 3057419 := bstep (se 1 (by rfl) ⟨2293064, by rfl⟩ : syracuseStep 3057419 = 4586129) B4586129
theorem B2148107 : Blo 1431535 2148107 := bstep (se 1 (by rfl) ⟨1611080, by rfl⟩ : syracuseStep 2148107 = 3222161) B3222161
theorem B2148119 : Blo 1431535 2148119 := bstep (se 1 (by rfl) ⟨1611089, by rfl⟩ : syracuseStep 2148119 = 3222179) B3222179
theorem B2418457 : Blo 1431535 2418457 := bstep (se 2 (by rfl) ⟨906921, by rfl⟩ : syracuseStep 2418457 = 1813843) B1813843
theorem B9799469 : Blo 1431535 9799469 := bstep (se 3 (by rfl) ⟨1837400, by rfl⟩ : syracuseStep 9799469 = 3674801) B3674801
theorem B2148185 : Blo 1431535 2148185 := bstep (se 2 (by rfl) ⟨805569, by rfl⟩ : syracuseStep 2148185 = 1611139) B1611139
theorem B3221387 : Blo 1431535 3221387 := bstep (se 1 (by rfl) ⟨2416040, by rfl⟩ : syracuseStep 3221387 = 4832081) B4832081
theorem B3221441 : Blo 1431535 3221441 := bstep (se 2 (by rfl) ⟨1208040, by rfl⟩ : syracuseStep 3221441 = 2416081) B2416081
theorem B2148299 : Blo 1431535 2148299 := bstep (se 1 (by rfl) ⟨1611224, by rfl⟩ : syracuseStep 2148299 = 3222449) B3222449
theorem B2148311 : Blo 1431535 2148311 := bstep (se 1 (by rfl) ⟨1611233, by rfl⟩ : syracuseStep 2148311 = 3222467) B3222467
theorem B7251929 : Blo 1431535 7251929 := bstep (se 2 (by rfl) ⟨2719473, by rfl⟩ : syracuseStep 7251929 = 5438947) B5438947
theorem B6203395 : Blo 1431535 6203395 := bstep (se 1 (by rfl) ⟨4652546, by rfl⟩ : syracuseStep 6203395 = 9305093) B9305093
theorem B1935383 : Blo 1431535 1935383 := bstep (se 1 (by rfl) ⟨1451537, by rfl⟩ : syracuseStep 1935383 = 2903075) B2903075
theorem B2148377 : Blo 1431535 2148377 := bstep (se 2 (by rfl) ⟨805641, by rfl⟩ : syracuseStep 2148377 = 1611283) B1611283
theorem B26142851 : Blo 1431535 26142851 := bstep (se 1 (by rfl) ⟨19607138, by rfl⟩ : syracuseStep 26142851 = 39214277) B39214277
theorem B2148491 : Blo 1431535 2148491 := bstep (se 1 (by rfl) ⟨1611368, by rfl⟩ : syracuseStep 2148491 = 3222737) B3222737
theorem B5441681 : Blo 1431535 5441681 := bstep (se 2 (by rfl) ⟨2040630, by rfl⟩ : syracuseStep 5441681 = 4081261) B4081261
theorem B2148503 : Blo 1431535 2148503 := bstep (se 1 (by rfl) ⟨1611377, by rfl⟩ : syracuseStep 2148503 = 3222755) B3222755
theorem B3221657 : Blo 1431535 3221657 := bstep (se 2 (by rfl) ⟨1208121, by rfl⟩ : syracuseStep 3221657 = 2416243) B2416243
theorem B2148569 : Blo 1431535 2148569 := bstep (se 2 (by rfl) ⟨805713, by rfl⟩ : syracuseStep 2148569 = 1611427) B1611427
theorem B3221747 : Blo 1431535 3221747 := bstep (se 1 (by rfl) ⟨2416310, by rfl⟩ : syracuseStep 3221747 = 4832621) B4832621
theorem B3221783 : Blo 1431535 3221783 := bstep (se 1 (by rfl) ⟨2416337, by rfl⟩ : syracuseStep 3221783 = 4832675) B4832675
theorem B6531373 : Blo 1431535 6531373 := bstep (se 3 (by rfl) ⟨1224632, by rfl⟩ : syracuseStep 6531373 = 2449265) B2449265
theorem B2148683 : Blo 1431535 2148683 := bstep (se 1 (by rfl) ⟨1611512, by rfl⟩ : syracuseStep 2148683 = 3223025) B3223025
theorem B2148695 : Blo 1431535 2148695 := bstep (se 1 (by rfl) ⟨1611521, by rfl⟩ : syracuseStep 2148695 = 3223043) B3223043
theorem B2419031 : Blo 1431535 2419031 := bstep (se 1 (by rfl) ⟨1814273, by rfl⟩ : syracuseStep 2419031 = 3628547) B3628547
theorem B2148761 : Blo 1431535 2148761 := bstep (se 2 (by rfl) ⟨805785, by rfl⟩ : syracuseStep 2148761 = 1611571) B1611571
theorem B18360755 : Blo 1431535 18360755 := bstep (se 1 (by rfl) ⟨13770566, by rfl⟩ : syracuseStep 18360755 = 27541133) B27541133
theorem B3221963 : Blo 1431535 3221963 := bstep (se 1 (by rfl) ⟨2416472, by rfl⟩ : syracuseStep 3221963 = 4832945) B4832945
theorem B3222017 : Blo 1431535 3222017 := bstep (se 2 (by rfl) ⟨1208256, by rfl⟩ : syracuseStep 3222017 = 2416513) B2416513
theorem B2148875 : Blo 1431535 2148875 := bstep (se 1 (by rfl) ⟨1611656, by rfl⟩ : syracuseStep 2148875 = 3223313) B3223313
theorem B2148887 : Blo 1431535 2148887 := bstep (se 1 (by rfl) ⟨1611665, by rfl⟩ : syracuseStep 2148887 = 3223331) B3223331
theorem B23538251 : Blo 1431535 23538251 := bstep (se 1 (by rfl) ⟨17653688, by rfl⟩ : syracuseStep 23538251 = 35307377) B35307377
theorem B4835915 : Blo 1431535 4835915 := bstep (se 1 (by rfl) ⟨3626936, by rfl⟩ : syracuseStep 4835915 = 7253873) B7253873
theorem B2452043 : Blo 1431535 2452043 := bstep (se 1 (by rfl) ⟨1839032, by rfl⟩ : syracuseStep 2452043 = 3678065) B3678065
theorem B2148953 : Blo 1431535 2148953 := bstep (se 2 (by rfl) ⟨805857, by rfl⟩ : syracuseStep 2148953 = 1611715) B1611715
theorem B5442137 : Blo 1431535 5442137 := bstep (se 2 (by rfl) ⟨2040801, by rfl⟩ : syracuseStep 5442137 = 4081603) B4081603
theorem B3623575 : Blo 1431535 3623575 := bstep (se 1 (by rfl) ⟨2717681, by rfl⟩ : syracuseStep 3623575 = 5435363) B5435363
theorem B1813195 : Blo 1431535 1813195 := bstep (se 1 (by rfl) ⟨1359896, by rfl⟩ : syracuseStep 1813195 = 2719793) B2719793
theorem B2149067 : Blo 1431535 2149067 := bstep (se 1 (by rfl) ⟨1611800, by rfl⟩ : syracuseStep 2149067 = 3223601) B3223601
theorem B2149079 : Blo 1431535 2149079 := bstep (se 1 (by rfl) ⟨1611809, by rfl⟩ : syracuseStep 2149079 = 3223619) B3223619
theorem B3222233 : Blo 1431535 3222233 := bstep (se 2 (by rfl) ⟨1208337, by rfl⟩ : syracuseStep 3222233 = 2416675) B2416675
theorem B2149145 : Blo 1431535 2149145 := bstep (se 2 (by rfl) ⟨805929, by rfl⟩ : syracuseStep 2149145 = 1611859) B1611859
theorem B7744301 : Blo 1431535 7744301 := bstep (se 3 (by rfl) ⟨1452056, by rfl⟩ : syracuseStep 7744301 = 2904113) B2904113
theorem B5442349 : Blo 1431535 5442349 := bstep (se 3 (by rfl) ⟨1020440, by rfl⟩ : syracuseStep 5442349 = 2040881) B2040881
theorem B3222323 : Blo 1431535 3222323 := bstep (se 1 (by rfl) ⟨2416742, by rfl⟩ : syracuseStep 3222323 = 4833485) B4833485
theorem B3222359 : Blo 1431535 3222359 := bstep (se 1 (by rfl) ⟨2416769, by rfl⟩ : syracuseStep 3222359 = 4833539) B4833539
theorem B4836185 : Blo 1431535 4836185 := bstep (se 2 (by rfl) ⟨1813569, by rfl⟩ : syracuseStep 4836185 = 3627139) B3627139
theorem B2149259 : Blo 1431535 2149259 := bstep (se 1 (by rfl) ⟨1611944, by rfl⟩ : syracuseStep 2149259 = 3223889) B3223889
theorem B2149271 : Blo 1431535 2149271 := bstep (se 1 (by rfl) ⟨1611953, by rfl⟩ : syracuseStep 2149271 = 3223907) B3223907
theorem B3869633 : Blo 1431535 3869633 := bstep (se 2 (by rfl) ⟨1451112, by rfl⟩ : syracuseStep 3869633 = 2902225) B2902225
theorem B17419225 : Blo 1431535 17419225 := bstep (se 2 (by rfl) ⟨6532209, by rfl⟩ : syracuseStep 17419225 = 13064419) B13064419
theorem B2149337 : Blo 1431535 2149337 := bstep (se 2 (by rfl) ⟨806001, by rfl⟩ : syracuseStep 2149337 = 1612003) B1612003
theorem B3222539 : Blo 1431535 3222539 := bstep (se 1 (by rfl) ⟨2416904, by rfl⟩ : syracuseStep 3222539 = 4833809) B4833809
theorem B3222593 : Blo 1431535 3222593 := bstep (se 2 (by rfl) ⟨1208472, by rfl⟩ : syracuseStep 3222593 = 2416945) B2416945
theorem B3624011 : Blo 1431535 3624011 := bstep (se 1 (by rfl) ⟨2718008, by rfl⟩ : syracuseStep 3624011 = 5436017) B5436017
theorem B9301067 : Blo 1431535 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B2149451 : Blo 1431535 2149451 := bstep (se 1 (by rfl) ⟨1612088, by rfl⟩ : syracuseStep 2149451 = 3224177) B3224177
theorem B2149463 : Blo 1431535 2149463 := bstep (se 1 (by rfl) ⟨1612097, by rfl⟩ : syracuseStep 2149463 = 3224195) B3224195
theorem B5442653 : Blo 1431535 5442653 := bstep (se 3 (by rfl) ⟨1020497, by rfl⟩ : syracuseStep 5442653 = 2040995) B2040995
theorem B2149529 : Blo 1431535 2149529 := bstep (se 2 (by rfl) ⟨806073, by rfl⟩ : syracuseStep 2149529 = 1612147) B1612147
theorem B20638961 : Blo 1431535 20638961 := bstep (se 2 (by rfl) ⟨7739610, by rfl⟩ : syracuseStep 20638961 = 15479221) B15479221
theorem B2149643 : Blo 1431535 2149643 := bstep (se 1 (by rfl) ⟨1612232, by rfl⟩ : syracuseStep 2149643 = 3224465) B3224465
theorem B2149655 : Blo 1431535 2149655 := bstep (se 1 (by rfl) ⟨1612241, by rfl⟩ : syracuseStep 2149655 = 3224483) B3224483
theorem B3222809 : Blo 1431535 3222809 := bstep (se 2 (by rfl) ⟨1208553, by rfl⟩ : syracuseStep 3222809 = 2417107) B2417107
theorem B2149721 : Blo 1431535 2149721 := bstep (se 2 (by rfl) ⟨806145, by rfl⟩ : syracuseStep 2149721 = 1612291) B1612291
theorem B3059059 : Blo 1431535 3059059 := bstep (se 1 (by rfl) ⟨2294294, by rfl⟩ : syracuseStep 3059059 = 4588589) B4588589
theorem B3222899 : Blo 1431535 3222899 := bstep (se 1 (by rfl) ⟨2417174, by rfl⟩ : syracuseStep 3222899 = 4834349) B4834349
theorem B3222935 : Blo 1431535 3222935 := bstep (se 1 (by rfl) ⟨2417201, by rfl⟩ : syracuseStep 3222935 = 4834403) B4834403
theorem B3624385 : Blo 1431535 3624385 := bstep (se 2 (by rfl) ⟨1359144, by rfl⟩ : syracuseStep 3624385 = 2718289) B2718289
theorem B2149835 : Blo 1431535 2149835 := bstep (se 1 (by rfl) ⟨1612376, by rfl⟩ : syracuseStep 2149835 = 3224753) B3224753
theorem B2149847 : Blo 1431535 2149847 := bstep (se 1 (by rfl) ⟨1612385, by rfl⟩ : syracuseStep 2149847 = 3224771) B3224771
theorem B1633783 : Blo 1431535 1633783 := bstep (se 1 (by rfl) ⟨1225337, by rfl⟩ : syracuseStep 1633783 = 2450675) B2450675
theorem B1936919 : Blo 1431535 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B4836887 : Blo 1431535 4836887 := bstep (se 1 (by rfl) ⟨3627665, by rfl⟩ : syracuseStep 4836887 = 7255331) B7255331
theorem B2149913 : Blo 1431535 2149913 := bstep (se 2 (by rfl) ⟨806217, by rfl⟩ : syracuseStep 2149913 = 1612435) B1612435
theorem B7253549 : Blo 1431535 7253549 := bstep (se 3 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 7253549 = 2720081) B2720081
theorem B6123053 : Blo 1431535 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B3223115 : Blo 1431535 3223115 := bstep (se 1 (by rfl) ⟨2417336, by rfl⟩ : syracuseStep 3223115 = 4834673) B4834673
theorem B6884939 : Blo 1431535 6884939 := bstep (se 1 (by rfl) ⟨5163704, by rfl⟩ : syracuseStep 6884939 = 10327409) B10327409
theorem B3223169 : Blo 1431535 3223169 := bstep (se 2 (by rfl) ⟨1208688, by rfl⟩ : syracuseStep 3223169 = 2417377) B2417377
theorem B8154755 : Blo 1431535 8154755 := bstep (se 1 (by rfl) ⟨6116066, by rfl⟩ : syracuseStep 8154755 = 12232133) B12232133
theorem B2150027 : Blo 1431535 2150027 := bstep (se 1 (by rfl) ⟨1612520, by rfl⟩ : syracuseStep 2150027 = 3225041) B3225041
theorem B2150039 : Blo 1431535 2150039 := bstep (se 1 (by rfl) ⟨1612529, by rfl⟩ : syracuseStep 2150039 = 3225059) B3225059
theorem B1814167 : Blo 1431535 1814167 := bstep (se 1 (by rfl) ⟨1360625, by rfl⟩ : syracuseStep 1814167 = 2721251) B2721251
theorem B6114989 : Blo 1431535 6114989 := bstep (se 3 (by rfl) ⟨1146560, by rfl⟩ : syracuseStep 6114989 = 2293121) B2293121
theorem B9072307 : Blo 1431535 9072307 := bstep (se 1 (by rfl) ⟨6804230, by rfl⟩ : syracuseStep 9072307 = 13608461) B13608461
theorem B2150105 : Blo 1431535 2150105 := bstep (se 2 (by rfl) ⟨806289, by rfl⟩ : syracuseStep 2150105 = 1612579) B1612579
theorem B16322309 : Blo 1431535 16322309 := bstep (se 4 (by rfl) ⟨1530216, by rfl⟩ : syracuseStep 16322309 = 3060433) B3060433
theorem B2150219 : Blo 1431535 2150219 := bstep (se 1 (by rfl) ⟨1612664, by rfl⟩ : syracuseStep 2150219 = 3225329) B3225329
theorem B2150231 : Blo 1431535 2150231 := bstep (se 1 (by rfl) ⟨1612673, by rfl⟩ : syracuseStep 2150231 = 3225347) B3225347
theorem B3059545 : Blo 1431535 3059545 := bstep (se 2 (by rfl) ⟨1147329, by rfl⟩ : syracuseStep 3059545 = 2294659) B2294659
theorem B3223385 : Blo 1431535 3223385 := bstep (se 2 (by rfl) ⟨1208769, by rfl⟩ : syracuseStep 3223385 = 2417539) B2417539
theorem B2150297 : Blo 1431535 2150297 := bstep (se 2 (by rfl) ⟨806361, by rfl⟩ : syracuseStep 2150297 = 1612723) B1612723
theorem B3223475 : Blo 1431535 3223475 := bstep (se 1 (by rfl) ⟨2417606, by rfl⟩ : syracuseStep 3223475 = 4835213) B4835213
theorem B8163251 : Blo 1431535 8163251 := bstep (se 1 (by rfl) ⟨6122438, by rfl⟩ : syracuseStep 8163251 = 12244877) B12244877
theorem B3223511 : Blo 1431535 3223511 := bstep (se 1 (by rfl) ⟨2417633, by rfl⟩ : syracuseStep 3223511 = 4835267) B4835267
theorem B6115331 : Blo 1431535 6115331 := bstep (se 1 (by rfl) ⟨4586498, by rfl⟩ : syracuseStep 6115331 = 9172997) B9172997
theorem B5165059 : Blo 1431535 5165059 := bstep (se 1 (by rfl) ⟨3873794, by rfl⟩ : syracuseStep 5165059 = 7747589) B7747589
theorem B3624983 : Blo 1431535 3624983 := bstep (se 1 (by rfl) ⟨2718737, by rfl⟩ : syracuseStep 3624983 = 5437475) B5437475
theorem B4837427 : Blo 1431535 4837427 := bstep (se 1 (by rfl) ⟨3628070, by rfl⟩ : syracuseStep 4837427 = 7256141) B7256141
theorem B3223691 : Blo 1431535 3223691 := bstep (se 1 (by rfl) ⟨2417768, by rfl⟩ : syracuseStep 3223691 = 4835537) B4835537
theorem B3223745 : Blo 1431535 3223745 := bstep (se 2 (by rfl) ⟨1208904, by rfl⟩ : syracuseStep 3223745 = 2417809) B2417809
theorem B6885593 : Blo 1431535 6885593 := bstep (se 2 (by rfl) ⟨2582097, by rfl⟩ : syracuseStep 6885593 = 5164195) B5164195
theorem B4837697 : Blo 1431535 4837697 := bstep (se 2 (by rfl) ⟨1814136, by rfl⟩ : syracuseStep 4837697 = 3628273) B3628273
theorem B2421067 : Blo 1431535 2421067 := bstep (se 1 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 2421067 = 3631601) B3631601
theorem B6533507 : Blo 1431535 6533507 := bstep (se 1 (by rfl) ⟨4900130, by rfl⟩ : syracuseStep 6533507 = 9800261) B9800261
theorem B3223961 : Blo 1431535 3223961 := bstep (se 2 (by rfl) ⟨1208985, by rfl⟩ : syracuseStep 3223961 = 2417971) B2417971
theorem B3224051 : Blo 1431535 3224051 := bstep (se 1 (by rfl) ⟨2418038, by rfl⟩ : syracuseStep 3224051 = 4836077) B4836077
theorem B3224087 : Blo 1431535 3224087 := bstep (se 1 (by rfl) ⟨2418065, by rfl⟩ : syracuseStep 3224087 = 4836131) B4836131
theorem B3265049 : Blo 1431535 3265049 := bstep (se 2 (by rfl) ⟨1224393, by rfl⟩ : syracuseStep 3265049 = 2448787) B2448787
theorem B3224267 : Blo 1431535 3224267 := bstep (se 1 (by rfl) ⟨2418200, by rfl⟩ : syracuseStep 3224267 = 4836401) B4836401
theorem B3224321 : Blo 1431535 3224321 := bstep (se 2 (by rfl) ⟨1209120, by rfl⟩ : syracuseStep 3224321 = 2418241) B2418241
theorem B3625793 : Blo 1431535 3625793 := bstep (se 2 (by rfl) ⟨1359672, by rfl⟩ : syracuseStep 3625793 = 2719345) B2719345
theorem B7844701 : Blo 1431535 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B1610635 : Blo 1431535 1610635 := bstep (se 1 (by rfl) ⟨1207976, by rfl⟩ : syracuseStep 1610635 = 2415953) B2415953
theorem B5436305 : Blo 1431535 5436305 := bstep (se 2 (by rfl) ⟨2038614, by rfl⟩ : syracuseStep 5436305 = 4077229) B4077229
theorem B5805017 : Blo 1431535 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B3224537 : Blo 1431535 3224537 := bstep (se 2 (by rfl) ⟨1209201, by rfl⟩ : syracuseStep 3224537 = 2418403) B2418403
theorem B1610743 : Blo 1431535 1610743 := bstep (se 1 (by rfl) ⟨1208057, by rfl⟩ : syracuseStep 1610743 = 2416115) B2416115
theorem B3224627 : Blo 1431535 3224627 := bstep (se 1 (by rfl) ⟨2418470, by rfl⟩ : syracuseStep 3224627 = 4836941) B4836941
theorem B2757719 : Blo 1431535 2757719 := bstep (se 1 (by rfl) ⟨2068289, by rfl⟩ : syracuseStep 2757719 = 4136579) B4136579
theorem B3224663 : Blo 1431535 3224663 := bstep (se 1 (by rfl) ⟨2418497, by rfl⟩ : syracuseStep 3224663 = 4836995) B4836995
theorem B2905217 : Blo 1431535 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B46576781 : Blo 1431535 46576781 := bstep (se 3 (by rfl) ⟨8733146, by rfl⟩ : syracuseStep 46576781 = 17466293) B17466293
theorem B1610923 : Blo 1431535 1610923 := bstep (se 1 (by rfl) ⟨1208192, by rfl⟩ : syracuseStep 1610923 = 2416385) B2416385
theorem B3060929 : Blo 1431535 3060929 := bstep (se 2 (by rfl) ⟨1147848, by rfl⟩ : syracuseStep 3060929 = 2295697) B2295697
theorem B3224843 : Blo 1431535 3224843 := bstep (se 1 (by rfl) ⟨2418632, by rfl⟩ : syracuseStep 3224843 = 4837265) B4837265
theorem B1611031 : Blo 1431535 1611031 := bstep (se 1 (by rfl) ⟨1208273, by rfl⟩ : syracuseStep 1611031 = 2416547) B2416547
theorem B3224897 : Blo 1431535 3224897 := bstep (se 2 (by rfl) ⟨1209336, by rfl⟩ : syracuseStep 3224897 = 2418673) B2418673
theorem B3626329 : Blo 1431535 3626329 := bstep (se 2 (by rfl) ⟨1359873, by rfl⟩ : syracuseStep 3626329 = 2719747) B2719747
theorem B1611211 : Blo 1431535 1611211 := bstep (se 1 (by rfl) ⟨1208408, by rfl⟩ : syracuseStep 1611211 = 2416817) B2416817
theorem B16307729 : Blo 1431535 16307729 := bstep (se 2 (by rfl) ⟨6115398, by rfl⟩ : syracuseStep 16307729 = 12230797) B12230797
theorem B3225113 : Blo 1431535 3225113 := bstep (se 2 (by rfl) ⟨1209417, by rfl⟩ : syracuseStep 3225113 = 2418835) B2418835
theorem B1611319 : Blo 1431535 1611319 := bstep (se 1 (by rfl) ⟨1208489, by rfl⟩ : syracuseStep 1611319 = 2416979) B2416979
theorem B5437003 : Blo 1431535 5437003 := bstep (se 1 (by rfl) ⟨4077752, by rfl⟩ : syracuseStep 5437003 = 8155505) B8155505
theorem B3225203 : Blo 1431535 3225203 := bstep (se 1 (by rfl) ⟨2418902, by rfl⟩ : syracuseStep 3225203 = 4837805) B4837805
theorem B2758295 : Blo 1431535 2758295 := bstep (se 1 (by rfl) ⟨2068721, by rfl⟩ : syracuseStep 2758295 = 4137443) B4137443
theorem B3225239 : Blo 1431535 3225239 := bstep (se 1 (by rfl) ⟨2418929, by rfl⟩ : syracuseStep 3225239 = 4837859) B4837859
theorem B3061451 : Blo 1431535 3061451 := bstep (se 1 (by rfl) ⟨2296088, by rfl⟩ : syracuseStep 3061451 = 4592177) B4592177
theorem B1611499 : Blo 1431535 1611499 := bstep (se 1 (by rfl) ⟨1208624, by rfl⟩ : syracuseStep 1611499 = 2417249) B2417249
theorem B2905931 : Blo 1431535 2905931 := bstep (se 1 (by rfl) ⟨2179448, by rfl⟩ : syracuseStep 2905931 = 4358897) B4358897
theorem B3225419 : Blo 1431535 3225419 := bstep (se 1 (by rfl) ⟨2419064, by rfl⟩ : syracuseStep 3225419 = 4838129) B4838129
theorem B1611607 : Blo 1431535 1611607 := bstep (se 1 (by rfl) ⟨1208705, by rfl⟩ : syracuseStep 1611607 = 2417411) B2417411
theorem B5437277 : Blo 1431535 5437277 := bstep (se 3 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 5437277 = 2038979) B2038979
theorem B3872605 : Blo 1431535 3872605 := bstep (se 3 (by rfl) ⟨726113, by rfl⟩ : syracuseStep 3872605 = 1452227) B1452227
theorem B1529803 : Blo 1431535 1529803 := bstep (se 1 (by rfl) ⟨1147352, by rfl⟩ : syracuseStep 1529803 = 2294705) B2294705
theorem B8157145 : Blo 1431535 8157145 := bstep (se 2 (by rfl) ⟨3058929, by rfl⟩ : syracuseStep 8157145 = 6117859) B6117859
theorem B1431543 : Blo 1431535 1431543 := bstep (se 1 (by rfl) ⟨1073657, by rfl⟩ : syracuseStep 1431543 = 2147315) B2147315
theorem B1431563 : Blo 1431535 1431563 := bstep (se 1 (by rfl) ⟨1073672, by rfl⟩ : syracuseStep 1431563 = 2147345) B2147345
theorem B1611787 : Blo 1431535 1611787 := bstep (se 1 (by rfl) ⟨1208840, by rfl⟩ : syracuseStep 1611787 = 2417681) B2417681
theorem B1431575 : Blo 1431535 1431575 := bstep (se 1 (by rfl) ⟨1073681, by rfl⟩ : syracuseStep 1431575 = 2147363) B2147363
theorem B1431595 : Blo 1431535 1431595 := bstep (se 1 (by rfl) ⟨1073696, by rfl⟩ : syracuseStep 1431595 = 2147393) B2147393
theorem B1431607 : Blo 1431535 1431607 := bstep (se 1 (by rfl) ⟨1073705, by rfl⟩ : syracuseStep 1431607 = 2147411) B2147411
theorem B1431627 : Blo 1431535 1431627 := bstep (se 1 (by rfl) ⟨1073720, by rfl⟩ : syracuseStep 1431627 = 2147441) B2147441
theorem B3872843 : Blo 1431535 3872843 := bstep (se 1 (by rfl) ⟨2904632, by rfl⟩ : syracuseStep 3872843 = 5809265) B5809265
theorem B1431639 : Blo 1431535 1431639 := bstep (se 1 (by rfl) ⟨1073729, by rfl⟩ : syracuseStep 1431639 = 2147459) B2147459
theorem B1431659 : Blo 1431535 1431659 := bstep (se 1 (by rfl) ⟨1073744, by rfl⟩ : syracuseStep 1431659 = 2147489) B2147489
theorem B1431671 : Blo 1431535 1431671 := bstep (se 1 (by rfl) ⟨1073753, by rfl⟩ : syracuseStep 1431671 = 2147507) B2147507
theorem B1611895 : Blo 1431535 1611895 := bstep (se 1 (by rfl) ⟨1208921, by rfl⟩ : syracuseStep 1611895 = 2417843) B2417843
theorem B1431691 : Blo 1431535 1431691 := bstep (se 1 (by rfl) ⟨1073768, by rfl⟩ : syracuseStep 1431691 = 2147537) B2147537
theorem B1431703 : Blo 1431535 1431703 := bstep (se 1 (by rfl) ⟨1073777, by rfl⟩ : syracuseStep 1431703 = 2147555) B2147555
theorem B2717849 : Blo 1431535 2717849 := bstep (se 2 (by rfl) ⟨1019193, by rfl⟩ : syracuseStep 2717849 = 2038387) B2038387
theorem B1431723 : Blo 1431535 1431723 := bstep (se 1 (by rfl) ⟨1073792, by rfl⟩ : syracuseStep 1431723 = 2147585) B2147585
theorem B1431735 : Blo 1431535 1431735 := bstep (se 1 (by rfl) ⟨1073801, by rfl⟩ : syracuseStep 1431735 = 2147603) B2147603
theorem B1431755 : Blo 1431535 1431755 := bstep (se 1 (by rfl) ⟨1073816, by rfl⟩ : syracuseStep 1431755 = 2147633) B2147633
theorem B2324695 : Blo 1431535 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B1431767 : Blo 1431535 1431767 := bstep (se 1 (by rfl) ⟨1073825, by rfl⟩ : syracuseStep 1431767 = 2147651) B2147651
theorem B4356317 : Blo 1431535 4356317 := bstep (se 3 (by rfl) ⟨816809, by rfl⟩ : syracuseStep 4356317 = 1633619) B1633619
theorem B1431787 : Blo 1431535 1431787 := bstep (se 1 (by rfl) ⟨1073840, by rfl⟩ : syracuseStep 1431787 = 2147681) B2147681
theorem B1431799 : Blo 1431535 1431799 := bstep (se 1 (by rfl) ⟨1073849, by rfl⟩ : syracuseStep 1431799 = 2147699) B2147699
theorem B1431819 : Blo 1431535 1431819 := bstep (se 1 (by rfl) ⟨1073864, by rfl⟩ : syracuseStep 1431819 = 2147729) B2147729
theorem B1431831 : Blo 1431535 1431831 := bstep (se 1 (by rfl) ⟨1073873, by rfl⟩ : syracuseStep 1431831 = 2147747) B2147747
theorem B1431851 : Blo 1431535 1431851 := bstep (se 1 (by rfl) ⟨1073888, by rfl⟩ : syracuseStep 1431851 = 2147777) B2147777
theorem B1612075 : Blo 1431535 1612075 := bstep (se 1 (by rfl) ⟨1209056, by rfl⟩ : syracuseStep 1612075 = 2418113) B2418113
theorem B9435437 : Blo 1431535 9435437 := bstep (se 3 (by rfl) ⟨1769144, by rfl⟩ : syracuseStep 9435437 = 3538289) B3538289
theorem B1431863 : Blo 1431535 1431863 := bstep (se 1 (by rfl) ⟨1073897, by rfl⟩ : syracuseStep 1431863 = 2147795) B2147795
theorem B9181505 : Blo 1431535 9181505 := bstep (se 2 (by rfl) ⟨3443064, by rfl⟩ : syracuseStep 9181505 = 6886129) B6886129
theorem B7248203 : Blo 1431535 7248203 := bstep (se 1 (by rfl) ⟨5436152, by rfl⟩ : syracuseStep 7248203 = 10872305) B10872305
theorem B1431883 : Blo 1431535 1431883 := bstep (se 1 (by rfl) ⟨1073912, by rfl⟩ : syracuseStep 1431883 = 2147825) B2147825
theorem B6117707 : Blo 1431535 6117707 := bstep (se 1 (by rfl) ⟨4588280, by rfl⟩ : syracuseStep 6117707 = 9176561) B9176561
theorem B1431895 : Blo 1431535 1431895 := bstep (se 1 (by rfl) ⟨1073921, by rfl⟩ : syracuseStep 1431895 = 2147843) B2147843
theorem B1431915 : Blo 1431535 1431915 := bstep (se 1 (by rfl) ⟨1073936, by rfl⟩ : syracuseStep 1431915 = 2147873) B2147873
theorem B1431927 : Blo 1431535 1431927 := bstep (se 1 (by rfl) ⟨1073945, by rfl⟩ : syracuseStep 1431927 = 2147891) B2147891
theorem B1431947 : Blo 1431535 1431947 := bstep (se 1 (by rfl) ⟨1073960, by rfl⟩ : syracuseStep 1431947 = 2147921) B2147921
theorem B1431959 : Blo 1431535 1431959 := bstep (se 1 (by rfl) ⟨1073969, by rfl⟩ : syracuseStep 1431959 = 2147939) B2147939
theorem B1612183 : Blo 1431535 1612183 := bstep (se 1 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 1612183 = 2418275) B2418275
theorem B1431979 : Blo 1431535 1431979 := bstep (se 1 (by rfl) ⟨1073984, by rfl⟩ : syracuseStep 1431979 = 2147969) B2147969
theorem B3627443 : Blo 1431535 3627443 := bstep (se 1 (by rfl) ⟨2720582, by rfl⟩ : syracuseStep 3627443 = 5441165) B5441165
theorem B1431991 : Blo 1431535 1431991 := bstep (se 1 (by rfl) ⟨1073993, by rfl⟩ : syracuseStep 1431991 = 2147987) B2147987
theorem B1432011 : Blo 1431535 1432011 := bstep (se 1 (by rfl) ⟨1074008, by rfl⟩ : syracuseStep 1432011 = 2148017) B2148017
theorem B1432023 : Blo 1431535 1432023 := bstep (se 1 (by rfl) ⟨1074017, by rfl⟩ : syracuseStep 1432023 = 2148035) B2148035
theorem B14703065 : Blo 1431535 14703065 := bstep (se 2 (by rfl) ⟨5513649, by rfl⟩ : syracuseStep 14703065 = 11027299) B11027299
theorem B1432043 : Blo 1431535 1432043 := bstep (se 1 (by rfl) ⟨1074032, by rfl⟩ : syracuseStep 1432043 = 2148065) B2148065
theorem B1432055 : Blo 1431535 1432055 := bstep (se 1 (by rfl) ⟨1074041, by rfl⟩ : syracuseStep 1432055 = 2148083) B2148083
theorem B1432075 : Blo 1431535 1432075 := bstep (se 1 (by rfl) ⟨1074056, by rfl⟩ : syracuseStep 1432075 = 2148113) B2148113
theorem B1432087 : Blo 1431535 1432087 := bstep (se 1 (by rfl) ⟨1074065, by rfl⟩ : syracuseStep 1432087 = 2148131) B2148131
theorem B5437975 : Blo 1431535 5437975 := bstep (se 1 (by rfl) ⟨4078481, by rfl⟩ : syracuseStep 5437975 = 8156963) B8156963
theorem B1432107 : Blo 1431535 1432107 := bstep (se 1 (by rfl) ⟨1074080, by rfl⟩ : syracuseStep 1432107 = 2148161) B2148161
theorem B11614765 : Blo 1431535 11614765 := bstep (se 3 (by rfl) ⟨2177768, by rfl⟩ : syracuseStep 11614765 = 4355537) B4355537
theorem B1432119 : Blo 1431535 1432119 := bstep (se 1 (by rfl) ⟨1074089, by rfl⟩ : syracuseStep 1432119 = 2148179) B2148179
theorem B5306945 : Blo 1431535 5306945 := bstep (se 2 (by rfl) ⟨1990104, by rfl⟩ : syracuseStep 5306945 = 3980209) B3980209
theorem B1432139 : Blo 1431535 1432139 := bstep (se 1 (by rfl) ⟨1074104, by rfl⟩ : syracuseStep 1432139 = 2148209) B2148209
theorem B1612363 : Blo 1431535 1612363 := bstep (se 1 (by rfl) ⟨1209272, by rfl⟩ : syracuseStep 1612363 = 2418545) B2418545
theorem B1432151 : Blo 1431535 1432151 := bstep (se 1 (by rfl) ⟨1074113, by rfl⟩ : syracuseStep 1432151 = 2148227) B2148227
theorem B1432171 : Blo 1431535 1432171 := bstep (se 1 (by rfl) ⟨1074128, by rfl⟩ : syracuseStep 1432171 = 2148257) B2148257
theorem B1432183 : Blo 1431535 1432183 := bstep (se 1 (by rfl) ⟨1074137, by rfl⟩ : syracuseStep 1432183 = 2148275) B2148275
theorem B1432203 : Blo 1431535 1432203 := bstep (se 1 (by rfl) ⟨1074152, by rfl⟩ : syracuseStep 1432203 = 2148305) B2148305
theorem B1432215 : Blo 1431535 1432215 := bstep (se 1 (by rfl) ⟨1074161, by rfl⟩ : syracuseStep 1432215 = 2148323) B2148323
theorem B1432235 : Blo 1431535 1432235 := bstep (se 1 (by rfl) ⟨1074176, by rfl⟩ : syracuseStep 1432235 = 2148353) B2148353
theorem B1432247 : Blo 1431535 1432247 := bstep (se 1 (by rfl) ⟨1074185, by rfl⟩ : syracuseStep 1432247 = 2148371) B2148371
theorem B1612471 : Blo 1431535 1612471 := bstep (se 1 (by rfl) ⟨1209353, by rfl⟩ : syracuseStep 1612471 = 2418707) B2418707
theorem B1432267 : Blo 1431535 1432267 := bstep (se 1 (by rfl) ⟨1074200, by rfl⟩ : syracuseStep 1432267 = 2148401) B2148401
theorem B1432279 : Blo 1431535 1432279 := bstep (se 1 (by rfl) ⟨1074209, by rfl⟩ : syracuseStep 1432279 = 2148419) B2148419
theorem B3627737 : Blo 1431535 3627737 := bstep (se 2 (by rfl) ⟨1360401, by rfl⟩ : syracuseStep 3627737 = 2720803) B2720803
theorem B1432299 : Blo 1431535 1432299 := bstep (se 1 (by rfl) ⟨1074224, by rfl⟩ : syracuseStep 1432299 = 2148449) B2148449
theorem B1432311 : Blo 1431535 1432311 := bstep (se 1 (by rfl) ⟨1074233, by rfl⟩ : syracuseStep 1432311 = 2148467) B2148467
theorem B1432331 : Blo 1431535 1432331 := bstep (se 1 (by rfl) ⟨1074248, by rfl⟩ : syracuseStep 1432331 = 2148497) B2148497
theorem B5806865 : Blo 1431535 5806865 := bstep (se 2 (by rfl) ⟨2177574, by rfl⟩ : syracuseStep 5806865 = 4355149) B4355149
theorem B5511959 : Blo 1431535 5511959 := bstep (se 1 (by rfl) ⟨4133969, by rfl⟩ : syracuseStep 5511959 = 8267939) B8267939
theorem B1432343 : Blo 1431535 1432343 := bstep (se 1 (by rfl) ⟨1074257, by rfl⟩ : syracuseStep 1432343 = 2148515) B2148515
theorem B1432363 : Blo 1431535 1432363 := bstep (se 1 (by rfl) ⟨1074272, by rfl⟩ : syracuseStep 1432363 = 2148545) B2148545
theorem B1432375 : Blo 1431535 1432375 := bstep (se 1 (by rfl) ⟨1074281, by rfl⟩ : syracuseStep 1432375 = 2148563) B2148563
theorem B2038603 : Blo 1431535 2038603 := bstep (se 1 (by rfl) ⟨1528952, by rfl⟩ : syracuseStep 2038603 = 3057905) B3057905
theorem B1432395 : Blo 1431535 1432395 := bstep (se 1 (by rfl) ⟨1074296, by rfl⟩ : syracuseStep 1432395 = 2148593) B2148593
theorem B1432407 : Blo 1431535 1432407 := bstep (se 1 (by rfl) ⟨1074305, by rfl⟩ : syracuseStep 1432407 = 2148611) B2148611
theorem B7748453 : Blo 1431535 7748453 := bstep (se 4 (by rfl) ⟨726417, by rfl⟩ : syracuseStep 7748453 = 1452835) B1452835
theorem B1432427 : Blo 1431535 1432427 := bstep (se 1 (by rfl) ⟨1074320, by rfl⟩ : syracuseStep 1432427 = 2148641) B2148641
theorem B1612651 : Blo 1431535 1612651 := bstep (se 1 (by rfl) ⟨1209488, by rfl⟩ : syracuseStep 1612651 = 2418977) B2418977
theorem B1432439 : Blo 1431535 1432439 := bstep (se 1 (by rfl) ⟨1074329, by rfl⟩ : syracuseStep 1432439 = 2148659) B2148659
theorem B2718593 : Blo 1431535 2718593 := bstep (se 2 (by rfl) ⟨1019472, by rfl⟩ : syracuseStep 2718593 = 2038945) B2038945
theorem B1432459 : Blo 1431535 1432459 := bstep (se 1 (by rfl) ⟨1074344, by rfl⟩ : syracuseStep 1432459 = 2148689) B2148689
theorem B8158103 : Blo 1431535 8158103 := bstep (se 1 (by rfl) ⟨6118577, by rfl⟩ : syracuseStep 8158103 = 12237155) B12237155
theorem B1432471 : Blo 1431535 1432471 := bstep (se 1 (by rfl) ⟨1074353, by rfl⟩ : syracuseStep 1432471 = 2148707) B2148707
theorem B1432491 : Blo 1431535 1432491 := bstep (se 1 (by rfl) ⟨1074368, by rfl⟩ : syracuseStep 1432491 = 2148737) B2148737
theorem B1432503 : Blo 1431535 1432503 := bstep (se 1 (by rfl) ⟨1074377, by rfl⟩ : syracuseStep 1432503 = 2148755) B2148755
theorem B1432523 : Blo 1431535 1432523 := bstep (se 1 (by rfl) ⟨1074392, by rfl⟩ : syracuseStep 1432523 = 2148785) B2148785
theorem B1432535 : Blo 1431535 1432535 := bstep (se 1 (by rfl) ⟨1074401, by rfl⟩ : syracuseStep 1432535 = 2148803) B2148803
theorem B1432555 : Blo 1431535 1432555 := bstep (se 1 (by rfl) ⟨1074416, by rfl⟩ : syracuseStep 1432555 = 2148833) B2148833
theorem B1432567 : Blo 1431535 1432567 := bstep (se 1 (by rfl) ⟨1074425, by rfl⟩ : syracuseStep 1432567 = 2148851) B2148851
theorem B12409861 : Blo 1431535 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B1432587 : Blo 1431535 1432587 := bstep (se 1 (by rfl) ⟨1074440, by rfl⟩ : syracuseStep 1432587 = 2148881) B2148881
theorem B1432599 : Blo 1431535 1432599 := bstep (se 1 (by rfl) ⟨1074449, by rfl⟩ : syracuseStep 1432599 = 2148899) B2148899
theorem B1432619 : Blo 1431535 1432619 := bstep (se 1 (by rfl) ⟨1074464, by rfl⟩ : syracuseStep 1432619 = 2148929) B2148929
theorem B1432631 : Blo 1431535 1432631 := bstep (se 1 (by rfl) ⟨1074473, by rfl⟩ : syracuseStep 1432631 = 2148947) B2148947
theorem B1432651 : Blo 1431535 1432651 := bstep (se 1 (by rfl) ⟨1074488, by rfl⟩ : syracuseStep 1432651 = 2148977) B2148977
theorem B2038871 : Blo 1431535 2038871 := bstep (se 1 (by rfl) ⟨1529153, by rfl⟩ : syracuseStep 2038871 = 3058307) B3058307
theorem B1432663 : Blo 1431535 1432663 := bstep (se 1 (by rfl) ⟨1074497, by rfl⟩ : syracuseStep 1432663 = 2148995) B2148995
theorem B1432683 : Blo 1431535 1432683 := bstep (se 1 (by rfl) ⟨1074512, by rfl⟩ : syracuseStep 1432683 = 2149025) B2149025
theorem B1432695 : Blo 1431535 1432695 := bstep (se 1 (by rfl) ⟨1074521, by rfl⟩ : syracuseStep 1432695 = 2149043) B2149043
theorem B2718859 : Blo 1431535 2718859 := bstep (se 1 (by rfl) ⟨2039144, by rfl⟩ : syracuseStep 2718859 = 4078289) B4078289
theorem B1432715 : Blo 1431535 1432715 := bstep (se 1 (by rfl) ⟨1074536, by rfl⟩ : syracuseStep 1432715 = 2149073) B2149073
theorem B2325655 : Blo 1431535 2325655 := bstep (se 1 (by rfl) ⟨1744241, by rfl⟩ : syracuseStep 2325655 = 3488483) B3488483
theorem B1432727 : Blo 1431535 1432727 := bstep (se 1 (by rfl) ⟨1074545, by rfl⟩ : syracuseStep 1432727 = 2149091) B2149091
theorem B1432747 : Blo 1431535 1432747 := bstep (se 1 (by rfl) ⟨1074560, by rfl⟩ : syracuseStep 1432747 = 2149121) B2149121
theorem B1432759 : Blo 1431535 1432759 := bstep (se 1 (by rfl) ⟨1074569, by rfl⟩ : syracuseStep 1432759 = 2149139) B2149139
theorem B4832459 : Blo 1431535 4832459 := bstep (se 1 (by rfl) ⟨3624344, by rfl⟩ : syracuseStep 4832459 = 7248689) B7248689
theorem B1432779 : Blo 1431535 1432779 := bstep (se 1 (by rfl) ⟨1074584, by rfl⟩ : syracuseStep 1432779 = 2149169) B2149169
theorem B1432791 : Blo 1431535 1432791 := bstep (se 1 (by rfl) ⟨1074593, by rfl⟩ : syracuseStep 1432791 = 2149187) B2149187
theorem B1432811 : Blo 1431535 1432811 := bstep (se 1 (by rfl) ⟨1074608, by rfl⟩ : syracuseStep 1432811 = 2149217) B2149217
theorem B1432823 : Blo 1431535 1432823 := bstep (se 1 (by rfl) ⟨1074617, by rfl⟩ : syracuseStep 1432823 = 2149235) B2149235
theorem B1432843 : Blo 1431535 1432843 := bstep (se 1 (by rfl) ⟨1074632, by rfl⟩ : syracuseStep 1432843 = 2149265) B2149265
theorem B6118679 : Blo 1431535 6118679 := bstep (se 1 (by rfl) ⟨4589009, by rfl⟩ : syracuseStep 6118679 = 9178019) B9178019
theorem B1432855 : Blo 1431535 1432855 := bstep (se 1 (by rfl) ⟨1074641, by rfl⟩ : syracuseStep 1432855 = 2149283) B2149283
theorem B1432875 : Blo 1431535 1432875 := bstep (se 1 (by rfl) ⟨1074656, by rfl⟩ : syracuseStep 1432875 = 2149313) B2149313
theorem B5438765 : Blo 1431535 5438765 := bstep (se 3 (by rfl) ⟨1019768, by rfl⟩ : syracuseStep 5438765 = 2039537) B2039537
theorem B1432887 : Blo 1431535 1432887 := bstep (se 1 (by rfl) ⟨1074665, by rfl⟩ : syracuseStep 1432887 = 2149331) B2149331
theorem B1432907 : Blo 1431535 1432907 := bstep (se 1 (by rfl) ⟨1074680, by rfl⟩ : syracuseStep 1432907 = 2149361) B2149361
theorem B1432919 : Blo 1431535 1432919 := bstep (se 1 (by rfl) ⟨1074689, by rfl⟩ : syracuseStep 1432919 = 2149379) B2149379
theorem B4078937 : Blo 1431535 4078937 := bstep (se 2 (by rfl) ⟨1529601, by rfl⟩ : syracuseStep 4078937 = 3059203) B3059203
theorem B1432939 : Blo 1431535 1432939 := bstep (se 1 (by rfl) ⟨1074704, by rfl⟩ : syracuseStep 1432939 = 2149409) B2149409
theorem B1432951 : Blo 1431535 1432951 := bstep (se 1 (by rfl) ⟨1074713, by rfl⟩ : syracuseStep 1432951 = 2149427) B2149427
theorem B1432971 : Blo 1431535 1432971 := bstep (se 1 (by rfl) ⟨1074728, by rfl⟩ : syracuseStep 1432971 = 2149457) B2149457
theorem B1432983 : Blo 1431535 1432983 := bstep (se 1 (by rfl) ⟨1074737, by rfl⟩ : syracuseStep 1432983 = 2149475) B2149475
theorem B1433003 : Blo 1431535 1433003 := bstep (se 1 (by rfl) ⟨1074752, by rfl⟩ : syracuseStep 1433003 = 2149505) B2149505
theorem B1433015 : Blo 1431535 1433015 := bstep (se 1 (by rfl) ⟨1074761, by rfl⟩ : syracuseStep 1433015 = 2149523) B2149523
theorem B1433035 : Blo 1431535 1433035 := bstep (se 1 (by rfl) ⟨1074776, by rfl⟩ : syracuseStep 1433035 = 2149553) B2149553
theorem B1433047 : Blo 1431535 1433047 := bstep (se 1 (by rfl) ⟨1074785, by rfl⟩ : syracuseStep 1433047 = 2149571) B2149571
theorem B4832729 : Blo 1431535 4832729 := bstep (se 2 (by rfl) ⟨1812273, by rfl⟩ : syracuseStep 4832729 = 3624547) B3624547
theorem B1433067 : Blo 1431535 1433067 := bstep (se 1 (by rfl) ⟨1074800, by rfl⟩ : syracuseStep 1433067 = 2149601) B2149601
theorem B1433079 : Blo 1431535 1433079 := bstep (se 1 (by rfl) ⟨1074809, by rfl⟩ : syracuseStep 1433079 = 2149619) B2149619
theorem B1433099 : Blo 1431535 1433099 := bstep (se 1 (by rfl) ⟨1074824, by rfl⟩ : syracuseStep 1433099 = 2149649) B2149649
theorem B1433111 : Blo 1431535 1433111 := bstep (se 1 (by rfl) ⟨1074833, by rfl⟩ : syracuseStep 1433111 = 2149667) B2149667
theorem B1433131 : Blo 1431535 1433131 := bstep (se 1 (by rfl) ⟨1074848, by rfl⟩ : syracuseStep 1433131 = 2149697) B2149697
theorem B1433143 : Blo 1431535 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B2719307 : Blo 1431535 2719307 := bstep (se 1 (by rfl) ⟨2039480, by rfl⟩ : syracuseStep 2719307 = 4078961) B4078961
theorem B1433163 : Blo 1431535 1433163 := bstep (se 1 (by rfl) ⟨1074872, by rfl⟩ : syracuseStep 1433163 = 2149745) B2149745
theorem B1433175 : Blo 1431535 1433175 := bstep (se 1 (by rfl) ⟨1074881, by rfl⟩ : syracuseStep 1433175 = 2149763) B2149763
theorem B1433195 : Blo 1431535 1433195 := bstep (se 1 (by rfl) ⟨1074896, by rfl⟩ : syracuseStep 1433195 = 2149793) B2149793
theorem B1433207 : Blo 1431535 1433207 := bstep (se 1 (by rfl) ⟨1074905, by rfl⟩ : syracuseStep 1433207 = 2149811) B2149811
theorem B1433227 : Blo 1431535 1433227 := bstep (se 1 (by rfl) ⟨1074920, by rfl⟩ : syracuseStep 1433227 = 2149841) B2149841
theorem B3145355 : Blo 1431535 3145355 := bstep (se 1 (by rfl) ⟨2359016, by rfl⟩ : syracuseStep 3145355 = 4718033) B4718033
theorem B1433239 : Blo 1431535 1433239 := bstep (se 1 (by rfl) ⟨1074929, by rfl⟩ : syracuseStep 1433239 = 2149859) B2149859
theorem B1433259 : Blo 1431535 1433259 := bstep (se 1 (by rfl) ⟨1074944, by rfl⟩ : syracuseStep 1433259 = 2149889) B2149889
theorem B1433271 : Blo 1431535 1433271 := bstep (se 1 (by rfl) ⟨1074953, by rfl⟩ : syracuseStep 1433271 = 2149907) B2149907
theorem B2416331 : Blo 1431535 2416331 := bstep (se 1 (by rfl) ⟨1812248, by rfl⟩ : syracuseStep 2416331 = 3624497) B3624497
theorem B1433291 : Blo 1431535 1433291 := bstep (se 1 (by rfl) ⟨1074968, by rfl⟩ : syracuseStep 1433291 = 2149937) B2149937
theorem B1433303 : Blo 1431535 1433303 := bstep (se 1 (by rfl) ⟨1074977, by rfl⟩ : syracuseStep 1433303 = 2149955) B2149955
theorem B1433323 : Blo 1431535 1433323 := bstep (se 1 (by rfl) ⟨1074992, by rfl⟩ : syracuseStep 1433323 = 2149985) B2149985
theorem B1433335 : Blo 1431535 1433335 := bstep (se 1 (by rfl) ⟨1075001, by rfl⟩ : syracuseStep 1433335 = 2150003) B2150003
theorem B2719489 : Blo 1431535 2719489 := bstep (se 2 (by rfl) ⟨1019808, by rfl⟩ : syracuseStep 2719489 = 2039617) B2039617
theorem B1433355 : Blo 1431535 1433355 := bstep (se 1 (by rfl) ⟨1075016, by rfl⟩ : syracuseStep 1433355 = 2150033) B2150033
theorem B1433367 : Blo 1431535 1433367 := bstep (se 1 (by rfl) ⟨1075025, by rfl⟩ : syracuseStep 1433367 = 2150051) B2150051
theorem B1433387 : Blo 1431535 1433387 := bstep (se 1 (by rfl) ⟨1075040, by rfl⟩ : syracuseStep 1433387 = 2150081) B2150081
theorem B1433399 : Blo 1431535 1433399 := bstep (se 1 (by rfl) ⟨1075049, by rfl⟩ : syracuseStep 1433399 = 2150099) B2150099
theorem B2416459 : Blo 1431535 2416459 := bstep (se 1 (by rfl) ⟨1812344, by rfl⟩ : syracuseStep 2416459 = 3624689) B3624689
theorem B1433419 : Blo 1431535 1433419 := bstep (se 1 (by rfl) ⟨1075064, by rfl⟩ : syracuseStep 1433419 = 2150129) B2150129
theorem B1433431 : Blo 1431535 1433431 := bstep (se 1 (by rfl) ⟨1075073, by rfl⟩ : syracuseStep 1433431 = 2150147) B2150147
theorem B1433451 : Blo 1431535 1433451 := bstep (se 1 (by rfl) ⟨1075088, by rfl⟩ : syracuseStep 1433451 = 2150177) B2150177
theorem B1433463 : Blo 1431535 1433463 := bstep (se 1 (by rfl) ⟨1075097, by rfl⟩ : syracuseStep 1433463 = 2150195) B2150195
theorem B2580353 : Blo 1431535 2580353 := bstep (se 2 (by rfl) ⟨967632, by rfl⟩ : syracuseStep 2580353 = 1935265) B1935265
theorem B1433483 : Blo 1431535 1433483 := bstep (se 1 (by rfl) ⟨1075112, by rfl⟩ : syracuseStep 1433483 = 2150225) B2150225
theorem B1433495 : Blo 1431535 1433495 := bstep (se 1 (by rfl) ⟨1075121, by rfl⟩ : syracuseStep 1433495 = 2150243) B2150243
theorem B1433515 : Blo 1431535 1433515 := bstep (se 1 (by rfl) ⟨1075136, by rfl⟩ : syracuseStep 1433515 = 2150273) B2150273
theorem B6119347 : Blo 1431535 6119347 := bstep (se 1 (by rfl) ⟨4589510, by rfl⟩ : syracuseStep 6119347 = 9179021) B9179021
theorem B1433527 : Blo 1431535 1433527 := bstep (se 1 (by rfl) ⟨1075145, by rfl⟩ : syracuseStep 1433527 = 2150291) B2150291
theorem B8708057 : Blo 1431535 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B2416601 : Blo 1431535 2416601 := bstep (se 2 (by rfl) ⟨906225, by rfl⟩ : syracuseStep 2416601 = 1812451) B1812451
theorem B2416655 : Blo 1431535 2416655 := bstep (se 1 (by rfl) ⟨1812491, by rfl⟩ : syracuseStep 2416655 = 3624983) B3624983
theorem B4833323 : Blo 1431535 4833323 := bstep (se 1 (by rfl) ⟨3624992, by rfl⟩ : syracuseStep 4833323 = 7249985) B7249985
theorem B10879109 : Blo 1431535 10879109 := bstep (se 4 (by rfl) ⟨1019916, by rfl⟩ : syracuseStep 10879109 = 2039833) B2039833
theorem B20644085 : Blo 1431535 20644085 := bstep (se 5 (by rfl) ⟨967691, by rfl⟩ : syracuseStep 20644085 = 1935383) B1935383
theorem B9175355 : Blo 1431535 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B69714269 : Blo 1431535 69714269 := bstep (se 3 (by rfl) ⟨13071425, by rfl⟩ : syracuseStep 69714269 = 26142851) B26142851
theorem B2720135 : Blo 1431535 2720135 := bstep (se 1 (by rfl) ⟨2040101, by rfl⟩ : syracuseStep 2720135 = 4080203) B4080203
theorem B3228089 : Blo 1431535 3228089 := bstep (se 2 (by rfl) ⟨1210533, by rfl⟩ : syracuseStep 3228089 = 2421067) B2421067
theorem B2417195 : Blo 1431535 2417195 := bstep (se 1 (by rfl) ⟨1812896, by rfl⟩ : syracuseStep 2417195 = 3625793) B3625793
theorem B7250633 : Blo 1431535 7250633 := bstep (se 2 (by rfl) ⟨2718987, by rfl⟩ : syracuseStep 7250633 = 5437975) B5437975
theorem B4080395 : Blo 1431535 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B4899599 : Blo 1431535 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B8274703 : Blo 1431535 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B5440391 : Blo 1431535 5440391 := bstep (se 1 (by rfl) ⟨4080293, by rfl⟩ : syracuseStep 5440391 = 8160587) B8160587
theorem B2417593 : Blo 1431535 2417593 := bstep (se 2 (by rfl) ⟨906597, by rfl⟩ : syracuseStep 2417593 = 1813195) B1813195
theorem B12239819 : Blo 1431535 12239819 := bstep (se 1 (by rfl) ⟨9179864, by rfl⟩ : syracuseStep 12239819 = 18359729) B18359729
theorem B10871819 : Blo 1431535 10871819 := bstep (se 1 (by rfl) ⟨8153864, by rfl⟩ : syracuseStep 10871819 = 16307729) B16307729
theorem B16548887 : Blo 1431535 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B2147387 : Blo 1431535 2147387 := bstep (se 1 (by rfl) ⟨1610540, by rfl⟩ : syracuseStep 2147387 = 3221081) B3221081
theorem B2147447 : Blo 1431535 2147447 := bstep (se 1 (by rfl) ⟨1610585, by rfl⟩ : syracuseStep 2147447 = 3221171) B3221171
theorem B2040967 : Blo 1431535 2040967 := bstep (se 1 (by rfl) ⟨1530725, by rfl⟩ : syracuseStep 2040967 = 3061451) B3061451
theorem B2147471 : Blo 1431535 2147471 := bstep (se 1 (by rfl) ⟨1610603, by rfl⟩ : syracuseStep 2147471 = 3221207) B3221207
theorem B2147513 : Blo 1431535 2147513 := bstep (se 2 (by rfl) ⟨805317, by rfl⟩ : syracuseStep 2147513 = 1610635) B1610635
theorem B2147591 : Blo 1431535 2147591 := bstep (se 1 (by rfl) ⟨1610693, by rfl⟩ : syracuseStep 2147591 = 3221387) B3221387
theorem B23225633 : Blo 1431535 23225633 := bstep (se 2 (by rfl) ⟨8709612, by rfl⟩ : syracuseStep 23225633 = 17419225) B17419225
theorem B2147627 : Blo 1431535 2147627 := bstep (se 1 (by rfl) ⟨1610720, by rfl⟩ : syracuseStep 2147627 = 3221441) B3221441
theorem B4834619 : Blo 1431535 4834619 := bstep (se 1 (by rfl) ⟨3625964, by rfl⟩ : syracuseStep 4834619 = 7251929) B7251929
theorem B2147657 : Blo 1431535 2147657 := bstep (se 2 (by rfl) ⟨805371, by rfl⟩ : syracuseStep 2147657 = 1610743) B1610743
theorem B2581895 : Blo 1431535 2581895 := bstep (se 1 (by rfl) ⟨1936421, by rfl⟩ : syracuseStep 2581895 = 3872843) B3872843
theorem B1811899 : Blo 1431535 1811899 := bstep (se 1 (by rfl) ⟨1358924, by rfl⟩ : syracuseStep 1811899 = 2717849) B2717849
theorem B2147771 : Blo 1431535 2147771 := bstep (se 1 (by rfl) ⟨1610828, by rfl⟩ : syracuseStep 2147771 = 3221657) B3221657
theorem B16328141 : Blo 1431535 16328141 := bstep (se 3 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 16328141 = 6123053) B6123053
theorem B2147831 : Blo 1431535 2147831 := bstep (se 1 (by rfl) ⟨1610873, by rfl⟩ : syracuseStep 2147831 = 3221747) B3221747
theorem B2147855 : Blo 1431535 2147855 := bstep (se 1 (by rfl) ⟨1610891, by rfl⟩ : syracuseStep 2147855 = 3221783) B3221783
theorem B6538781 : Blo 1431535 6538781 := bstep (se 3 (by rfl) ⟨1226021, by rfl⟩ : syracuseStep 6538781 = 2452043) B2452043
theorem B6121003 : Blo 1431535 6121003 := bstep (se 1 (by rfl) ⟨4590752, by rfl⟩ : syracuseStep 6121003 = 9181505) B9181505
theorem B2147897 : Blo 1431535 2147897 := bstep (se 2 (by rfl) ⟨805461, by rfl⟩ : syracuseStep 2147897 = 1610923) B1610923
theorem B34833989 : Blo 1431535 34833989 := bstep (se 4 (by rfl) ⟨3265686, by rfl⟩ : syracuseStep 34833989 = 6531373) B6531373
theorem B12240503 : Blo 1431535 12240503 := bstep (se 1 (by rfl) ⟨9180377, by rfl⟩ : syracuseStep 12240503 = 18360755) B18360755
theorem B2418295 : Blo 1431535 2418295 := bstep (se 1 (by rfl) ⟨1813721, by rfl⟩ : syracuseStep 2418295 = 3627443) B3627443
theorem B2147975 : Blo 1431535 2147975 := bstep (se 1 (by rfl) ⟨1610981, by rfl⟩ : syracuseStep 2147975 = 3221963) B3221963
theorem B2148011 : Blo 1431535 2148011 := bstep (se 1 (by rfl) ⟨1611008, by rfl⟩ : syracuseStep 2148011 = 3222017) B3222017
theorem B2148041 : Blo 1431535 2148041 := bstep (se 2 (by rfl) ⟨805515, by rfl⟩ : syracuseStep 2148041 = 1611031) B1611031
theorem B4835105 : Blo 1431535 4835105 := bstep (se 2 (by rfl) ⟨1813164, by rfl⟩ : syracuseStep 4835105 = 3626329) B3626329
theorem B2148155 : Blo 1431535 2148155 := bstep (se 1 (by rfl) ⟨1611116, by rfl⟩ : syracuseStep 2148155 = 3222233) B3222233
theorem B2418491 : Blo 1431535 2418491 := bstep (se 1 (by rfl) ⟨1813868, by rfl⟩ : syracuseStep 2418491 = 3627737) B3627737
theorem B5162867 : Blo 1431535 5162867 := bstep (se 1 (by rfl) ⟨3872150, by rfl⟩ : syracuseStep 5162867 = 7744301) B7744301
theorem B2148215 : Blo 1431535 2148215 := bstep (se 1 (by rfl) ⟨1611161, by rfl⟩ : syracuseStep 2148215 = 3222323) B3222323
theorem B2148239 : Blo 1431535 2148239 := bstep (se 1 (by rfl) ⟨1611179, by rfl⟩ : syracuseStep 2148239 = 3222359) B3222359
theorem B1812395 : Blo 1431535 1812395 := bstep (se 1 (by rfl) ⟨1359296, by rfl⟩ : syracuseStep 1812395 = 2718593) B2718593
theorem B2148281 : Blo 1431535 2148281 := bstep (se 2 (by rfl) ⟨805605, by rfl⟩ : syracuseStep 2148281 = 1611211) B1611211
theorem B2148359 : Blo 1431535 2148359 := bstep (se 1 (by rfl) ⟨1611269, by rfl⟩ : syracuseStep 2148359 = 3222539) B3222539
theorem B2148395 : Blo 1431535 2148395 := bstep (se 1 (by rfl) ⟨1611296, by rfl⟩ : syracuseStep 2148395 = 3222593) B3222593
theorem B2148425 : Blo 1431535 2148425 := bstep (se 2 (by rfl) ⟨805659, by rfl⟩ : syracuseStep 2148425 = 1611319) B1611319
theorem B3221639 : Blo 1431535 3221639 := bstep (se 1 (by rfl) ⟨2416229, by rfl⟩ : syracuseStep 3221639 = 4832459) B4832459
theorem B2148539 : Blo 1431535 2148539 := bstep (se 1 (by rfl) ⟨1611404, by rfl⟩ : syracuseStep 2148539 = 3222809) B3222809
theorem B2418889 : Blo 1431535 2418889 := bstep (se 2 (by rfl) ⟨907083, by rfl⟩ : syracuseStep 2418889 = 1814167) B1814167
theorem B2148599 : Blo 1431535 2148599 := bstep (se 1 (by rfl) ⟨1611449, by rfl⟩ : syracuseStep 2148599 = 3222899) B3222899
theorem B2148623 : Blo 1431535 2148623 := bstep (se 1 (by rfl) ⟨1611467, by rfl⟩ : syracuseStep 2148623 = 3222935) B3222935
theorem B2148665 : Blo 1431535 2148665 := bstep (se 2 (by rfl) ⟨805749, by rfl⟩ : syracuseStep 2148665 = 1611499) B1611499
theorem B3221819 : Blo 1431535 3221819 := bstep (se 1 (by rfl) ⟨2416364, by rfl⟩ : syracuseStep 3221819 = 4832729) B4832729
theorem B4835699 : Blo 1431535 4835699 := bstep (se 1 (by rfl) ⟨3626774, by rfl⟩ : syracuseStep 4835699 = 7253549) B7253549
theorem B1812871 : Blo 1431535 1812871 := bstep (se 1 (by rfl) ⟨1359653, by rfl⟩ : syracuseStep 1812871 = 2719307) B2719307
theorem B2148743 : Blo 1431535 2148743 := bstep (se 1 (by rfl) ⟨1611557, by rfl⟩ : syracuseStep 2148743 = 3223115) B3223115
theorem B4589959 : Blo 1431535 4589959 := bstep (se 1 (by rfl) ⟨3442469, by rfl⟩ : syracuseStep 4589959 = 6884939) B6884939
theorem B2148779 : Blo 1431535 2148779 := bstep (se 1 (by rfl) ⟨1611584, by rfl⟩ : syracuseStep 2148779 = 3223169) B3223169
theorem B3221945 : Blo 1431535 3221945 := bstep (se 2 (by rfl) ⟨1208229, by rfl⟩ : syracuseStep 3221945 = 2416459) B2416459
theorem B2148809 : Blo 1431535 2148809 := bstep (se 2 (by rfl) ⟨805803, by rfl⟩ : syracuseStep 2148809 = 1611607) B1611607
theorem B5163473 : Blo 1431535 5163473 := bstep (se 2 (by rfl) ⟨1936302, by rfl⟩ : syracuseStep 5163473 = 3872605) B3872605
theorem B10881539 : Blo 1431535 10881539 := bstep (se 1 (by rfl) ⟨8161154, by rfl⟩ : syracuseStep 10881539 = 16322309) B16322309
theorem B2148923 : Blo 1431535 2148923 := bstep (se 1 (by rfl) ⟨1611692, by rfl⟩ : syracuseStep 2148923 = 3223385) B3223385
theorem B2148983 : Blo 1431535 2148983 := bstep (se 1 (by rfl) ⟨1611737, by rfl⟩ : syracuseStep 2148983 = 3223475) B3223475
theorem B5442167 : Blo 1431535 5442167 := bstep (se 1 (by rfl) ⟨4081625, by rfl⟩ : syracuseStep 5442167 = 8163251) B8163251
theorem B2149007 : Blo 1431535 2149007 := bstep (se 1 (by rfl) ⟨1611755, by rfl⟩ : syracuseStep 2149007 = 3223511) B3223511
theorem B2149049 : Blo 1431535 2149049 := bstep (se 2 (by rfl) ⟨805893, by rfl⟩ : syracuseStep 2149049 = 1611787) B1611787
theorem B2149127 : Blo 1431535 2149127 := bstep (se 1 (by rfl) ⟨1611845, by rfl⟩ : syracuseStep 2149127 = 3223691) B3223691
theorem B3222287 : Blo 1431535 3222287 := bstep (se 1 (by rfl) ⟨2416715, by rfl⟩ : syracuseStep 3222287 = 4833431) B4833431
theorem B3222305 : Blo 1431535 3222305 := bstep (se 2 (by rfl) ⟨1208364, by rfl⟩ : syracuseStep 3222305 = 2416729) B2416729
theorem B2149163 : Blo 1431535 2149163 := bstep (se 1 (by rfl) ⟨1611872, by rfl⟩ : syracuseStep 2149163 = 3223745) B3223745
theorem B4590395 : Blo 1431535 4590395 := bstep (se 1 (by rfl) ⟨3442796, by rfl⟩ : syracuseStep 4590395 = 6885593) B6885593
theorem B2149193 : Blo 1431535 2149193 := bstep (se 2 (by rfl) ⟨805947, by rfl⟩ : syracuseStep 2149193 = 1611895) B1611895
theorem B8711027 : Blo 1431535 8711027 := bstep (se 1 (by rfl) ⟨6533270, by rfl⟩ : syracuseStep 8711027 = 13066541) B13066541
theorem B1813367 : Blo 1431535 1813367 := bstep (se 1 (by rfl) ⟨1360025, by rfl⟩ : syracuseStep 1813367 = 2720051) B2720051
theorem B12397465 : Blo 1431535 12397465 := bstep (se 2 (by rfl) ⟨4649049, by rfl⟩ : syracuseStep 12397465 = 9298099) B9298099
theorem B10873763 : Blo 1431535 10873763 := bstep (se 1 (by rfl) ⟨8155322, by rfl⟩ : syracuseStep 10873763 = 16310645) B16310645
theorem B2149307 : Blo 1431535 2149307 := bstep (se 1 (by rfl) ⟨1611980, by rfl⟩ : syracuseStep 2149307 = 3223961) B3223961
theorem B3099593 : Blo 1431535 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B2149367 : Blo 1431535 2149367 := bstep (se 1 (by rfl) ⟨1612025, by rfl⟩ : syracuseStep 2149367 = 3224051) B3224051
theorem B8711171 : Blo 1431535 8711171 := bstep (se 1 (by rfl) ⟨6533378, by rfl⟩ : syracuseStep 8711171 = 13066757) B13066757
theorem B1813519 : Blo 1431535 1813519 := bstep (se 1 (by rfl) ⟨1360139, by rfl⟩ : syracuseStep 1813519 = 2720279) B2720279
theorem B2149391 : Blo 1431535 2149391 := bstep (se 1 (by rfl) ⟨1612043, by rfl⟩ : syracuseStep 2149391 = 3224087) B3224087
theorem B6532139 : Blo 1431535 6532139 := bstep (se 1 (by rfl) ⟨4899104, by rfl⟩ : syracuseStep 6532139 = 9798209) B9798209
theorem B2149433 : Blo 1431535 2149433 := bstep (se 2 (by rfl) ⟨806037, by rfl⟩ : syracuseStep 2149433 = 1612075) B1612075
theorem B7351363 : Blo 1431535 7351363 := bstep (se 1 (by rfl) ⟨5513522, by rfl⟩ : syracuseStep 7351363 = 11027045) B11027045
theorem B3222647 : Blo 1431535 3222647 := bstep (se 1 (by rfl) ⟨2416985, by rfl⟩ : syracuseStep 3222647 = 4833971) B4833971
theorem B2149511 : Blo 1431535 2149511 := bstep (se 1 (by rfl) ⟨1612133, by rfl⟩ : syracuseStep 2149511 = 3224267) B3224267
theorem B2149547 : Blo 1431535 2149547 := bstep (se 1 (by rfl) ⟨1612160, by rfl⟩ : syracuseStep 2149547 = 3224321) B3224321
theorem B8162477 : Blo 1431535 8162477 := bstep (se 3 (by rfl) ⟨1530464, by rfl⟩ : syracuseStep 8162477 = 3060929) B3060929
theorem B1813691 : Blo 1431535 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B2149577 : Blo 1431535 2149577 := bstep (se 2 (by rfl) ⟨806091, by rfl⟩ : syracuseStep 2149577 = 1612183) B1612183
theorem B6204653 : Blo 1431535 6204653 := bstep (se 3 (by rfl) ⟨1163372, by rfl⟩ : syracuseStep 6204653 = 2326745) B2326745
theorem B3624203 : Blo 1431535 3624203 := bstep (se 1 (by rfl) ⟨2718152, by rfl⟩ : syracuseStep 3624203 = 5436305) B5436305
theorem B3222827 : Blo 1431535 3222827 := bstep (se 1 (by rfl) ⟨2417120, by rfl⟩ : syracuseStep 3222827 = 4834241) B4834241
theorem B3870011 : Blo 1431535 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B2149691 : Blo 1431535 2149691 := bstep (se 1 (by rfl) ⟨1612268, by rfl⟩ : syracuseStep 2149691 = 3224537) B3224537
theorem B2149751 : Blo 1431535 2149751 := bstep (se 1 (by rfl) ⟨1612313, by rfl⟩ : syracuseStep 2149751 = 3224627) B3224627
theorem B8154503 : Blo 1431535 8154503 := bstep (se 1 (by rfl) ⟨6115877, by rfl⟩ : syracuseStep 8154503 = 12231755) B12231755
theorem B1838479 : Blo 1431535 1838479 := bstep (se 1 (by rfl) ⟨1378859, by rfl⟩ : syracuseStep 1838479 = 2757719) B2757719
theorem B15486353 : Blo 1431535 15486353 := bstep (se 2 (by rfl) ⟨5807382, by rfl⟩ : syracuseStep 15486353 = 11614765) B11614765
theorem B2149775 : Blo 1431535 2149775 := bstep (se 1 (by rfl) ⟨1612331, by rfl⟩ : syracuseStep 2149775 = 3224663) B3224663
theorem B1936811 : Blo 1431535 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B31051187 : Blo 1431535 31051187 := bstep (se 1 (by rfl) ⟨23288390, by rfl⟩ : syracuseStep 31051187 = 46576781) B46576781
theorem B2149817 : Blo 1431535 2149817 := bstep (se 2 (by rfl) ⟨806181, by rfl⟩ : syracuseStep 2149817 = 1612363) B1612363
theorem B27553283 : Blo 1431535 27553283 := bstep (se 1 (by rfl) ⟨20664962, by rfl⟩ : syracuseStep 27553283 = 41329925) B41329925
theorem B2149895 : Blo 1431535 2149895 := bstep (se 1 (by rfl) ⟨1612421, by rfl⟩ : syracuseStep 2149895 = 3224843) B3224843
theorem B23244317 : Blo 1431535 23244317 := bstep (se 3 (by rfl) ⟨4358309, by rfl⟩ : syracuseStep 23244317 = 8716619) B8716619
theorem B2149931 : Blo 1431535 2149931 := bstep (se 1 (by rfl) ⟨1612448, by rfl⟩ : syracuseStep 2149931 = 3224897) B3224897
theorem B2149961 : Blo 1431535 2149961 := bstep (se 2 (by rfl) ⟨806235, by rfl⟩ : syracuseStep 2149961 = 1612471) B1612471
theorem B48385637 : Blo 1431535 48385637 := bstep (se 4 (by rfl) ⟨4536153, by rfl⟩ : syracuseStep 48385637 = 9072307) B9072307
theorem B3223187 : Blo 1431535 3223187 := bstep (se 1 (by rfl) ⟨2417390, by rfl⟩ : syracuseStep 3223187 = 4834781) B4834781
theorem B2150075 : Blo 1431535 2150075 := bstep (se 1 (by rfl) ⟨1612556, by rfl⟩ : syracuseStep 2150075 = 3225113) B3225113
theorem B3223241 : Blo 1431535 3223241 := bstep (se 2 (by rfl) ⟨1208715, by rfl⟩ : syracuseStep 3223241 = 2417431) B2417431
theorem B2150135 : Blo 1431535 2150135 := bstep (se 1 (by rfl) ⟨1612601, by rfl⟩ : syracuseStep 2150135 = 3225203) B3225203
theorem B1838863 : Blo 1431535 1838863 := bstep (se 1 (by rfl) ⟨1379147, by rfl⟩ : syracuseStep 1838863 = 2758295) B2758295
theorem B2150159 : Blo 1431535 2150159 := bstep (se 1 (by rfl) ⟨1612619, by rfl⟩ : syracuseStep 2150159 = 3225239) B3225239
theorem B2150201 : Blo 1431535 2150201 := bstep (se 2 (by rfl) ⟨806325, by rfl⟩ : syracuseStep 2150201 = 1612651) B1612651
theorem B6532979 : Blo 1431535 6532979 := bstep (se 1 (by rfl) ⟨4899734, by rfl⟩ : syracuseStep 6532979 = 9799469) B9799469
theorem B1937287 : Blo 1431535 1937287 := bstep (se 1 (by rfl) ⟨1452965, by rfl⟩ : syracuseStep 1937287 = 2905931) B2905931
theorem B2150279 : Blo 1431535 2150279 := bstep (se 1 (by rfl) ⟨1612709, by rfl⟩ : syracuseStep 2150279 = 3225419) B3225419
theorem B3624851 : Blo 1431535 3624851 := bstep (se 1 (by rfl) ⟨2718638, by rfl⟩ : syracuseStep 3624851 = 5437277) B5437277
theorem B5165117 : Blo 1431535 5165117 := bstep (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) B1936919
theorem B2904211 : Blo 1431535 2904211 := bstep (se 1 (by rfl) ⟨2178158, by rfl⟩ : syracuseStep 2904211 = 4356317) B4356317
theorem B14151853 : Blo 1431535 14151853 := bstep (se 3 (by rfl) ⟨2653472, by rfl⟩ : syracuseStep 14151853 = 5306945) B5306945
theorem B3625145 : Blo 1431535 3625145 := bstep (se 2 (by rfl) ⟨1359429, by rfl⟩ : syracuseStep 3625145 = 2718859) B2718859
theorem B3100873 : Blo 1431535 3100873 := bstep (se 2 (by rfl) ⟨1162827, by rfl⟩ : syracuseStep 3100873 = 2325655) B2325655
theorem B9802043 : Blo 1431535 9802043 := bstep (se 1 (by rfl) ⟨7351532, by rfl⟩ : syracuseStep 9802043 = 14703065) B14703065
theorem B15692167 : Blo 1431535 15692167 := bstep (se 1 (by rfl) ⟨11769125, by rfl⟩ : syracuseStep 15692167 = 23538251) B23538251
theorem B3223943 : Blo 1431535 3223943 := bstep (se 1 (by rfl) ⟨2417957, by rfl⟩ : syracuseStep 3223943 = 4835915) B4835915
theorem B17437133 : Blo 1431535 17437133 := bstep (se 3 (by rfl) ⟨3269462, by rfl⟩ : syracuseStep 17437133 = 6538925) B6538925
theorem B3871243 : Blo 1431535 3871243 := bstep (se 1 (by rfl) ⟨2903432, by rfl⟩ : syracuseStep 3871243 = 5806865) B5806865
theorem B3674639 : Blo 1431535 3674639 := bstep (se 1 (by rfl) ⟨2755979, by rfl⟩ : syracuseStep 3674639 = 5511959) B5511959
theorem B3224123 : Blo 1431535 3224123 := bstep (se 1 (by rfl) ⟨2418092, by rfl⟩ : syracuseStep 3224123 = 4836185) B4836185
theorem B5165635 : Blo 1431535 5165635 := bstep (se 1 (by rfl) ⟨3874226, by rfl⟩ : syracuseStep 5165635 = 7748453) B7748453
theorem B3224249 : Blo 1431535 3224249 := bstep (se 2 (by rfl) ⟨1209093, by rfl⟩ : syracuseStep 3224249 = 2418187) B2418187
theorem B13759307 : Blo 1431535 13759307 := bstep (se 1 (by rfl) ⟨10319480, by rfl⟩ : syracuseStep 13759307 = 20638961) B20638961
theorem B3625843 : Blo 1431535 3625843 := bstep (se 1 (by rfl) ⟨2719382, by rfl⟩ : syracuseStep 3625843 = 5438765) B5438765
theorem B3625985 : Blo 1431535 3625985 := bstep (se 2 (by rfl) ⟨1359744, by rfl⟩ : syracuseStep 3625985 = 2719489) B2719489
theorem B3224591 : Blo 1431535 3224591 := bstep (se 1 (by rfl) ⟨2418443, by rfl⟩ : syracuseStep 3224591 = 4836887) B4836887
theorem B3224609 : Blo 1431535 3224609 := bstep (se 2 (by rfl) ⟨1209228, by rfl⟩ : syracuseStep 3224609 = 2418457) B2418457
theorem B5436503 : Blo 1431535 5436503 := bstep (se 1 (by rfl) ⟨4077377, by rfl⟩ : syracuseStep 5436503 = 8154755) B8154755
theorem B4076659 : Blo 1431535 4076659 := bstep (se 1 (by rfl) ⟨3057494, by rfl⟩ : syracuseStep 4076659 = 6114989) B6114989
theorem B1610887 : Blo 1431535 1610887 := bstep (se 1 (by rfl) ⟨1208165, by rfl⟩ : syracuseStep 1610887 = 2416331) B2416331
theorem B10876193 : Blo 1431535 10876193 := bstep (se 2 (by rfl) ⟨4078572, by rfl⟩ : syracuseStep 10876193 = 8157145) B8157145
theorem B5805371 : Blo 1431535 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B1611067 : Blo 1431535 1611067 := bstep (se 1 (by rfl) ⟨1208300, by rfl⟩ : syracuseStep 1611067 = 2416601) B2416601
theorem B4076887 : Blo 1431535 4076887 := bstep (se 1 (by rfl) ⟨3057665, by rfl⟩ : syracuseStep 4076887 = 6115331) B6115331
theorem B8271193 : Blo 1431535 8271193 := bstep (se 2 (by rfl) ⟨3101697, by rfl⟩ : syracuseStep 8271193 = 6203395) B6203395
theorem B6886745 : Blo 1431535 6886745 := bstep (se 2 (by rfl) ⟨2582529, by rfl⟩ : syracuseStep 6886745 = 5165059) B5165059
theorem B3224951 : Blo 1431535 3224951 := bstep (se 1 (by rfl) ⟨2418713, by rfl⟩ : syracuseStep 3224951 = 4837427) B4837427
theorem B3626441 : Blo 1431535 3626441 := bstep (se 2 (by rfl) ⟨1359915, by rfl⟩ : syracuseStep 3626441 = 2719831) B2719831
theorem B3225131 : Blo 1431535 3225131 := bstep (se 1 (by rfl) ⟨2418848, by rfl⟩ : syracuseStep 3225131 = 4837697) B4837697
theorem B5436989 : Blo 1431535 5436989 := bstep (se 3 (by rfl) ⟨1019435, by rfl⟩ : syracuseStep 5436989 = 2038871) B2038871
theorem B1611535 : Blo 1431535 1611535 := bstep (se 1 (by rfl) ⟨1208651, by rfl⟩ : syracuseStep 1611535 = 2417303) B2417303
theorem B3626795 : Blo 1431535 3626795 := bstep (se 1 (by rfl) ⟨2720096, by rfl⟩ : syracuseStep 3626795 = 5440193) B5440193
theorem B3872627 : Blo 1431535 3872627 := bstep (se 1 (by rfl) ⟨2904470, by rfl⟩ : syracuseStep 3872627 = 5808941) B5808941
theorem B1431559 : Blo 1431535 1431559 := bstep (se 1 (by rfl) ⟨1073669, by rfl⟩ : syracuseStep 1431559 = 2147339) B2147339
theorem B1431567 : Blo 1431535 1431567 := bstep (se 1 (by rfl) ⟨1073675, by rfl⟩ : syracuseStep 1431567 = 2147351) B2147351
theorem B1431611 : Blo 1431535 1431611 := bstep (se 1 (by rfl) ⟨1073708, by rfl⟩ : syracuseStep 1431611 = 2147417) B2147417
theorem B16316477 : Blo 1431535 16316477 := bstep (se 3 (by rfl) ⟨3059339, by rfl⟩ : syracuseStep 16316477 = 6118679) B6118679
theorem B7739459 : Blo 1431535 7739459 := bstep (se 1 (by rfl) ⟨5804594, by rfl⟩ : syracuseStep 7739459 = 11609189) B11609189
theorem B1431687 : Blo 1431535 1431687 := bstep (se 1 (by rfl) ⟨1073765, by rfl⟩ : syracuseStep 1431687 = 2147531) B2147531
theorem B1431695 : Blo 1431535 1431695 := bstep (se 1 (by rfl) ⟨1073771, by rfl⟩ : syracuseStep 1431695 = 2147543) B2147543
theorem B1431739 : Blo 1431535 1431739 := bstep (se 1 (by rfl) ⟨1073804, by rfl⟩ : syracuseStep 1431739 = 2147609) B2147609
theorem B4831433 : Blo 1431535 4831433 := bstep (se 2 (by rfl) ⟨1811787, by rfl⟩ : syracuseStep 4831433 = 3623575) B3623575
theorem B10877165 : Blo 1431535 10877165 := bstep (se 3 (by rfl) ⟨2039468, by rfl⟩ : syracuseStep 10877165 = 4078937) B4078937
theorem B1431815 : Blo 1431535 1431815 := bstep (se 1 (by rfl) ⟨1073861, by rfl⟩ : syracuseStep 1431815 = 2147723) B2147723
theorem B1612039 : Blo 1431535 1612039 := bstep (se 1 (by rfl) ⟨1209029, by rfl⟩ : syracuseStep 1612039 = 2418059) B2418059
theorem B1431823 : Blo 1431535 1431823 := bstep (se 1 (by rfl) ⟨1073867, by rfl⟩ : syracuseStep 1431823 = 2147735) B2147735
theorem B1431867 : Blo 1431535 1431867 := bstep (se 1 (by rfl) ⟨1073900, by rfl⟩ : syracuseStep 1431867 = 2147801) B2147801
theorem B17422685 : Blo 1431535 17422685 := bstep (se 3 (by rfl) ⟨3266753, by rfl⟩ : syracuseStep 17422685 = 6533507) B6533507
theorem B6199667 : Blo 1431535 6199667 := bstep (se 1 (by rfl) ⟨4649750, by rfl⟩ : syracuseStep 6199667 = 9299501) B9299501
theorem B1431943 : Blo 1431535 1431943 := bstep (se 1 (by rfl) ⟨1073957, by rfl⟩ : syracuseStep 1431943 = 2147915) B2147915
theorem B1530247 : Blo 1431535 1530247 := bstep (se 1 (by rfl) ⟨1147685, by rfl⟩ : syracuseStep 1530247 = 2295371) B2295371
theorem B1431951 : Blo 1431535 1431951 := bstep (se 1 (by rfl) ⟨1073963, by rfl⟩ : syracuseStep 1431951 = 2147927) B2147927
theorem B7256465 : Blo 1431535 7256465 := bstep (se 2 (by rfl) ⟨2721174, by rfl⟩ : syracuseStep 7256465 = 5442349) B5442349
theorem B2718137 : Blo 1431535 2718137 := bstep (se 2 (by rfl) ⟨1019301, by rfl⟩ : syracuseStep 2718137 = 2038603) B2038603
theorem B1431995 : Blo 1431535 1431995 := bstep (se 1 (by rfl) ⟨1073996, by rfl⟩ : syracuseStep 1431995 = 2147993) B2147993
theorem B1612219 : Blo 1431535 1612219 := bstep (se 1 (by rfl) ⟨1209164, by rfl⟩ : syracuseStep 1612219 = 2418329) B2418329
theorem B10459601 : Blo 1431535 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B2038279 : Blo 1431535 2038279 := bstep (se 1 (by rfl) ⟨1528709, by rfl⟩ : syracuseStep 2038279 = 3057419) B3057419
theorem B1432071 : Blo 1431535 1432071 := bstep (se 1 (by rfl) ⟨1074053, by rfl⟩ : syracuseStep 1432071 = 2148107) B2148107
theorem B1432079 : Blo 1431535 1432079 := bstep (se 1 (by rfl) ⟨1074059, by rfl⟩ : syracuseStep 1432079 = 2148119) B2148119
theorem B1432123 : Blo 1431535 1432123 := bstep (se 1 (by rfl) ⟨1074092, by rfl⟩ : syracuseStep 1432123 = 2148185) B2148185
theorem B1432199 : Blo 1431535 1432199 := bstep (se 1 (by rfl) ⟨1074149, by rfl⟩ : syracuseStep 1432199 = 2148299) B2148299
theorem B1432207 : Blo 1431535 1432207 := bstep (se 1 (by rfl) ⟨1074155, by rfl⟩ : syracuseStep 1432207 = 2148311) B2148311
theorem B16546481 : Blo 1431535 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B1432251 : Blo 1431535 1432251 := bstep (se 1 (by rfl) ⟨1074188, by rfl⟩ : syracuseStep 1432251 = 2148377) B2148377
theorem B8706797 : Blo 1431535 8706797 := bstep (se 3 (by rfl) ⟨1632524, by rfl⟩ : syracuseStep 8706797 = 3265049) B3265049
theorem B1432327 : Blo 1431535 1432327 := bstep (se 1 (by rfl) ⟨1074245, by rfl⟩ : syracuseStep 1432327 = 2148491) B2148491
theorem B3627787 : Blo 1431535 3627787 := bstep (se 1 (by rfl) ⟨2720840, by rfl⟩ : syracuseStep 3627787 = 5441681) B5441681
theorem B1432335 : Blo 1431535 1432335 := bstep (se 1 (by rfl) ⟨1074251, by rfl⟩ : syracuseStep 1432335 = 2148503) B2148503
theorem B1432379 : Blo 1431535 1432379 := bstep (se 1 (by rfl) ⟨1074284, by rfl⟩ : syracuseStep 1432379 = 2148569) B2148569
theorem B6290291 : Blo 1431535 6290291 := bstep (se 1 (by rfl) ⟨4717718, by rfl⟩ : syracuseStep 6290291 = 9435437) B9435437
theorem B4832135 : Blo 1431535 4832135 := bstep (se 1 (by rfl) ⟨3624101, by rfl⟩ : syracuseStep 4832135 = 7248203) B7248203
theorem B4078471 : Blo 1431535 4078471 := bstep (se 1 (by rfl) ⟨3058853, by rfl⟩ : syracuseStep 4078471 = 6117707) B6117707
theorem B1432455 : Blo 1431535 1432455 := bstep (se 1 (by rfl) ⟨1074341, by rfl⟩ : syracuseStep 1432455 = 2148683) B2148683
theorem B1432463 : Blo 1431535 1432463 := bstep (se 1 (by rfl) ⟨1074347, by rfl⟩ : syracuseStep 1432463 = 2148695) B2148695
theorem B1612687 : Blo 1431535 1612687 := bstep (se 1 (by rfl) ⟨1209515, by rfl⟩ : syracuseStep 1612687 = 2419031) B2419031
theorem B3627929 : Blo 1431535 3627929 := bstep (se 2 (by rfl) ⟨1360473, by rfl⟩ : syracuseStep 3627929 = 2720947) B2720947
theorem B1432507 : Blo 1431535 1432507 := bstep (se 1 (by rfl) ⟨1074380, by rfl⟩ : syracuseStep 1432507 = 2148761) B2148761
theorem B1432583 : Blo 1431535 1432583 := bstep (se 1 (by rfl) ⟨1074437, by rfl⟩ : syracuseStep 1432583 = 2148875) B2148875
theorem B1432591 : Blo 1431535 1432591 := bstep (se 1 (by rfl) ⟨1074443, by rfl⟩ : syracuseStep 1432591 = 2148887) B2148887
theorem B1432635 : Blo 1431535 1432635 := bstep (se 1 (by rfl) ⟨1074476, by rfl⟩ : syracuseStep 1432635 = 2148953) B2148953
theorem B3628091 : Blo 1431535 3628091 := bstep (se 1 (by rfl) ⟨2721068, by rfl⟩ : syracuseStep 3628091 = 5442137) B5442137
theorem B1432711 : Blo 1431535 1432711 := bstep (se 1 (by rfl) ⟨1074533, by rfl⟩ : syracuseStep 1432711 = 2149067) B2149067
theorem B1432719 : Blo 1431535 1432719 := bstep (se 1 (by rfl) ⟨1074539, by rfl⟩ : syracuseStep 1432719 = 2149079) B2149079
theorem B4078745 : Blo 1431535 4078745 := bstep (se 2 (by rfl) ⟨1529529, by rfl⟩ : syracuseStep 4078745 = 3059059) B3059059
theorem B1432763 : Blo 1431535 1432763 := bstep (se 1 (by rfl) ⟨1074572, by rfl⟩ : syracuseStep 1432763 = 2149145) B2149145
theorem B4832513 : Blo 1431535 4832513 := bstep (se 2 (by rfl) ⟨1812192, by rfl⟩ : syracuseStep 4832513 = 3624385) B3624385
theorem B1432839 : Blo 1431535 1432839 := bstep (se 1 (by rfl) ⟨1074629, by rfl⟩ : syracuseStep 1432839 = 2149259) B2149259
theorem B5438735 : Blo 1431535 5438735 := bstep (se 1 (by rfl) ⟨4079051, by rfl⟩ : syracuseStep 5438735 = 8158103) B8158103
theorem B1432847 : Blo 1431535 1432847 := bstep (se 1 (by rfl) ⟨1074635, by rfl⟩ : syracuseStep 1432847 = 2149271) B2149271
theorem B3980573 : Blo 1431535 3980573 := bstep (se 3 (by rfl) ⟨746357, by rfl⟩ : syracuseStep 3980573 = 1492715) B1492715
theorem B2579755 : Blo 1431535 2579755 := bstep (se 1 (by rfl) ⟨1934816, by rfl⟩ : syracuseStep 2579755 = 3869633) B3869633
theorem B1432891 : Blo 1431535 1432891 := bstep (se 1 (by rfl) ⟨1074668, by rfl⟩ : syracuseStep 1432891 = 2149337) B2149337
theorem B2178377 : Blo 1431535 2178377 := bstep (se 2 (by rfl) ⟨816891, by rfl⟩ : syracuseStep 2178377 = 1633783) B1633783
theorem B2416007 : Blo 1431535 2416007 := bstep (se 1 (by rfl) ⟨1812005, by rfl⟩ : syracuseStep 2416007 = 3624011) B3624011
theorem B6200711 : Blo 1431535 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B1432967 : Blo 1431535 1432967 := bstep (se 1 (by rfl) ⟨1074725, by rfl⟩ : syracuseStep 1432967 = 2149451) B2149451
theorem B1432975 : Blo 1431535 1432975 := bstep (se 1 (by rfl) ⟨1074731, by rfl⟩ : syracuseStep 1432975 = 2149463) B2149463
theorem B3628435 : Blo 1431535 3628435 := bstep (se 1 (by rfl) ⟨2721326, by rfl⟩ : syracuseStep 3628435 = 5442653) B5442653
theorem B7249337 : Blo 1431535 7249337 := bstep (se 2 (by rfl) ⟨2718501, by rfl⟩ : syracuseStep 7249337 = 5437003) B5437003
theorem B1433019 : Blo 1431535 1433019 := bstep (se 1 (by rfl) ⟨1074764, by rfl⟩ : syracuseStep 1433019 = 2149529) B2149529
theorem B1433095 : Blo 1431535 1433095 := bstep (se 1 (by rfl) ⟨1074821, by rfl⟩ : syracuseStep 1433095 = 2149643) B2149643
theorem B1433103 : Blo 1431535 1433103 := bstep (se 1 (by rfl) ⟨1074827, by rfl⟩ : syracuseStep 1433103 = 2149655) B2149655
theorem B3628577 : Blo 1431535 3628577 := bstep (se 2 (by rfl) ⟨1360716, by rfl⟩ : syracuseStep 3628577 = 2721433) B2721433
theorem B1433147 : Blo 1431535 1433147 := bstep (se 1 (by rfl) ⟨1074860, by rfl⟩ : syracuseStep 1433147 = 2149721) B2149721
theorem B1433223 : Blo 1431535 1433223 := bstep (se 1 (by rfl) ⟨1074917, by rfl⟩ : syracuseStep 1433223 = 2149835) B2149835
theorem B1433231 : Blo 1431535 1433231 := bstep (se 1 (by rfl) ⟨1074923, by rfl⟩ : syracuseStep 1433231 = 2149847) B2149847
theorem B1433275 : Blo 1431535 1433275 := bstep (se 1 (by rfl) ⟨1074956, by rfl⟩ : syracuseStep 1433275 = 2149913) B2149913
theorem B2096903 : Blo 1431535 2096903 := bstep (se 1 (by rfl) ⟨1572677, by rfl⟩ : syracuseStep 2096903 = 3145355) B3145355
theorem B1433351 : Blo 1431535 1433351 := bstep (se 1 (by rfl) ⟨1075013, by rfl⟩ : syracuseStep 1433351 = 2150027) B2150027
theorem B1433359 : Blo 1431535 1433359 := bstep (se 1 (by rfl) ⟨1075019, by rfl⟩ : syracuseStep 1433359 = 2150039) B2150039
theorem B4079393 : Blo 1431535 4079393 := bstep (se 2 (by rfl) ⟨1529772, by rfl⟩ : syracuseStep 4079393 = 3059545) B3059545
theorem B1433403 : Blo 1431535 1433403 := bstep (se 1 (by rfl) ⟨1075052, by rfl⟩ : syracuseStep 1433403 = 2150105) B2150105
theorem B1433479 : Blo 1431535 1433479 := bstep (se 1 (by rfl) ⟨1075109, by rfl⟩ : syracuseStep 1433479 = 2150219) B2150219
theorem B1433487 : Blo 1431535 1433487 := bstep (se 1 (by rfl) ⟨1075115, by rfl⟩ : syracuseStep 1433487 = 2150231) B2150231
theorem B8159129 : Blo 1431535 8159129 := bstep (se 2 (by rfl) ⟨3059673, by rfl⟩ : syracuseStep 8159129 = 6119347) B6119347
theorem B1720235 : Blo 1431535 1720235 := bstep (se 1 (by rfl) ⟨1290176, by rfl⟩ : syracuseStep 1720235 = 2580353) B2580353
theorem B2039737 : Blo 1431535 2039737 := bstep (se 2 (by rfl) ⟨764901, by rfl⟩ : syracuseStep 2039737 = 1529803) B1529803
theorem B1433531 : Blo 1431535 1433531 := bstep (se 1 (by rfl) ⟨1075148, by rfl⟩ : syracuseStep 1433531 = 2150297) B2150297
theorem B44130365 : Blo 1431535 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B2416763 : Blo 1431535 2416763 := bstep (se 1 (by rfl) ⟨1812572, by rfl⟩ : syracuseStep 2416763 = 3625145) B3625145
theorem B13762723 : Blo 1431535 13762723 := bstep (se 1 (by rfl) ⟨10322042, by rfl⟩ : syracuseStep 13762723 = 20644085) B20644085
theorem B11624755 : Blo 1431535 11624755 := bstep (se 1 (by rfl) ⟨8718566, by rfl⟩ : syracuseStep 11624755 = 17437133) B17437133
theorem B2449759 : Blo 1431535 2449759 := bstep (se 1 (by rfl) ⟨1837319, by rfl⟩ : syracuseStep 2449759 = 3674639) B3674639
theorem B4833755 : Blo 1431535 4833755 := bstep (se 1 (by rfl) ⟨3625316, by rfl⟩ : syracuseStep 4833755 = 7250633) B7250633
theorem B20922889 : Blo 1431535 20922889 := bstep (se 2 (by rfl) ⟨7846083, by rfl⟩ : syracuseStep 20922889 = 15692167) B15692167
theorem B2417161 : Blo 1431535 2417161 := bstep (se 2 (by rfl) ⟨906435, by rfl⟩ : syracuseStep 2417161 = 1812871) B1812871
theorem B6119945 : Blo 1431535 6119945 := bstep (se 2 (by rfl) ⟨2294979, by rfl⟩ : syracuseStep 6119945 = 4589959) B4589959
theorem B2040329 : Blo 1431535 2040329 := bstep (se 2 (by rfl) ⟨765123, by rfl⟩ : syracuseStep 2040329 = 1530247) B1530247
theorem B8159879 : Blo 1431535 8159879 := bstep (se 1 (by rfl) ⟨6119909, by rfl⟩ : syracuseStep 8159879 = 12239819) B12239819
theorem B2417323 : Blo 1431535 2417323 := bstep (se 1 (by rfl) ⟨1812992, by rfl⟩ : syracuseStep 2417323 = 3625985) B3625985
theorem B5161657 : Blo 1431535 5161657 := bstep (se 2 (by rfl) ⟨1935621, by rfl⟩ : syracuseStep 5161657 = 3871243) B3871243
theorem B15483755 : Blo 1431535 15483755 := bstep (se 1 (by rfl) ⟨11612816, by rfl⟩ : syracuseStep 15483755 = 23225633) B23225633
theorem B7250795 : Blo 1431535 7250795 := bstep (se 1 (by rfl) ⟨5438096, by rfl⟩ : syracuseStep 7250795 = 10876193) B10876193
theorem B2417627 : Blo 1431535 2417627 := bstep (se 1 (by rfl) ⟨1813220, by rfl⟩ : syracuseStep 2417627 = 3626441) B3626441
theorem B4359187 : Blo 1431535 4359187 := bstep (se 1 (by rfl) ⟨3269390, by rfl⟩ : syracuseStep 4359187 = 6538781) B6538781
theorem B8160335 : Blo 1431535 8160335 := bstep (se 1 (by rfl) ⟨6120251, by rfl⟩ : syracuseStep 8160335 = 12240503) B12240503
theorem B4834457 : Blo 1431535 4834457 := bstep (se 2 (by rfl) ⟨1812921, by rfl⟩ : syracuseStep 4834457 = 3625843) B3625843
theorem B2417863 : Blo 1431535 2417863 := bstep (se 1 (by rfl) ⟨1813397, by rfl⟩ : syracuseStep 2417863 = 3626795) B3626795
theorem B3441911 : Blo 1431535 3441911 := bstep (se 1 (by rfl) ⟨2581433, by rfl⟩ : syracuseStep 3441911 = 5162867) B5162867
theorem B2581751 : Blo 1431535 2581751 := bstep (se 1 (by rfl) ⟨1936313, by rfl⟩ : syracuseStep 2581751 = 3872627) B3872627
theorem B2418025 : Blo 1431535 2418025 := bstep (se 2 (by rfl) ⟨906759, by rfl⟩ : syracuseStep 2418025 = 1813519) B1813519
theorem B2147759 : Blo 1431535 2147759 := bstep (se 1 (by rfl) ⟨1610819, by rfl⟩ : syracuseStep 2147759 = 3221639) B3221639
theorem B3220955 : Blo 1431535 3220955 := bstep (se 1 (by rfl) ⟨2415716, by rfl⟩ : syracuseStep 3220955 = 4831433) B4831433
theorem B7251443 : Blo 1431535 7251443 := bstep (se 1 (by rfl) ⟨5438582, by rfl⟩ : syracuseStep 7251443 = 10877165) B10877165
theorem B2147849 : Blo 1431535 2147849 := bstep (se 2 (by rfl) ⟨805443, by rfl⟩ : syracuseStep 2147849 = 1610887) B1610887
theorem B2721289 : Blo 1431535 2721289 := bstep (se 2 (by rfl) ⟨1020483, by rfl⟩ : syracuseStep 2721289 = 2040967) B2040967
theorem B2147879 : Blo 1431535 2147879 := bstep (se 1 (by rfl) ⟨1610909, by rfl⟩ : syracuseStep 2147879 = 3221819) B3221819
theorem B2147963 : Blo 1431535 2147963 := bstep (se 1 (by rfl) ⟨1610972, by rfl⟩ : syracuseStep 2147963 = 3221945) B3221945
theorem B6973067 : Blo 1431535 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B2148089 : Blo 1431535 2148089 := bstep (se 2 (by rfl) ⟨805533, by rfl⟩ : syracuseStep 2148089 = 1611067) B1611067
theorem B11028257 : Blo 1431535 11028257 := bstep (se 2 (by rfl) ⟨4135596, by rfl⟩ : syracuseStep 11028257 = 8271193) B8271193
theorem B2148191 : Blo 1431535 2148191 := bstep (se 1 (by rfl) ⟨1611143, by rfl⟩ : syracuseStep 2148191 = 3222287) B3222287
theorem B2451305 : Blo 1431535 2451305 := bstep (se 2 (by rfl) ⟨919239, by rfl⟩ : syracuseStep 2451305 = 1838479) B1838479
theorem B2148203 : Blo 1431535 2148203 := bstep (se 1 (by rfl) ⟨1611152, by rfl⟩ : syracuseStep 2148203 = 3222305) B3222305
theorem B3221423 : Blo 1431535 3221423 := bstep (se 1 (by rfl) ⟨2416067, by rfl⟩ : syracuseStep 3221423 = 4832135) B4832135
theorem B2418619 : Blo 1431535 2418619 := bstep (se 1 (by rfl) ⟨1813964, by rfl⟩ : syracuseStep 2418619 = 3627929) B3627929
theorem B2066395 : Blo 1431535 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B10881053 : Blo 1431535 10881053 := bstep (se 3 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 10881053 = 4080395) B4080395
theorem B2418727 : Blo 1431535 2418727 := bstep (se 1 (by rfl) ⟨1814045, by rfl⟩ : syracuseStep 2418727 = 3628091) B3628091
theorem B8161337 : Blo 1431535 8161337 := bstep (se 2 (by rfl) ⟨3060501, by rfl⟩ : syracuseStep 8161337 = 6121003) B6121003
theorem B2148431 : Blo 1431535 2148431 := bstep (se 1 (by rfl) ⟨1611323, by rfl⟩ : syracuseStep 2148431 = 3222647) B3222647
theorem B5441651 : Blo 1431535 5441651 := bstep (se 1 (by rfl) ⟨4081238, by rfl⟩ : syracuseStep 5441651 = 8162477) B8162477
theorem B66119813 : Blo 1431535 66119813 := bstep (se 4 (by rfl) ⟨6198732, by rfl⟩ : syracuseStep 66119813 = 12397465) B12397465
theorem B3221675 : Blo 1431535 3221675 := bstep (se 1 (by rfl) ⟨2416256, by rfl⟩ : syracuseStep 3221675 = 4832513) B4832513
theorem B2148551 : Blo 1431535 2148551 := bstep (se 1 (by rfl) ⟨1611413, by rfl⟩ : syracuseStep 2148551 = 3222827) B3222827
theorem B1452251 : Blo 1431535 1452251 := bstep (se 1 (by rfl) ⟨1089188, by rfl⟩ : syracuseStep 1452251 = 2178377) B2178377
theorem B10324235 : Blo 1431535 10324235 := bstep (se 1 (by rfl) ⟨7743176, by rfl⟩ : syracuseStep 10324235 = 15486353) B15486353
theorem B4835645 : Blo 1431535 4835645 := bstep (se 3 (by rfl) ⟨906683, by rfl⟩ : syracuseStep 4835645 = 1813367) B1813367
theorem B18368855 : Blo 1431535 18368855 := bstep (se 1 (by rfl) ⟨13776641, by rfl⟩ : syracuseStep 18368855 = 27553283) B27553283
theorem B2148713 : Blo 1431535 2148713 := bstep (se 2 (by rfl) ⟨805767, by rfl⟩ : syracuseStep 2148713 = 1611535) B1611535
theorem B2451817 : Blo 1431535 2451817 := bstep (se 2 (by rfl) ⟨919431, by rfl⟩ : syracuseStep 2451817 = 1838863) B1838863
theorem B2419051 : Blo 1431535 2419051 := bstep (se 1 (by rfl) ⟨1814288, by rfl⟩ : syracuseStep 2419051 = 3628577) B3628577
theorem B2148791 : Blo 1431535 2148791 := bstep (se 1 (by rfl) ⟨1611593, by rfl⟩ : syracuseStep 2148791 = 3223187) B3223187
theorem B2148827 : Blo 1431535 2148827 := bstep (se 1 (by rfl) ⟨1611620, by rfl⟩ : syracuseStep 2148827 = 3223241) B3223241
theorem B2583049 : Blo 1431535 2583049 := bstep (se 2 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 2583049 = 1937287) B1937287
theorem B3222215 : Blo 1431535 3222215 := bstep (se 1 (by rfl) ⟨2416661, by rfl⟩ : syracuseStep 3222215 = 4833323) B4833323
theorem B3443411 : Blo 1431535 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B7252739 : Blo 1431535 7252739 := bstep (se 1 (by rfl) ⟨5439554, by rfl⟩ : syracuseStep 7252739 = 10879109) B10879109
theorem B46476179 : Blo 1431535 46476179 := bstep (se 1 (by rfl) ⟨34857134, by rfl⟩ : syracuseStep 46476179 = 69714269) B69714269
theorem B1813423 : Blo 1431535 1813423 := bstep (se 1 (by rfl) ⟨1360067, by rfl⟩ : syracuseStep 1813423 = 2720135) B2720135
theorem B2149295 : Blo 1431535 2149295 := bstep (se 1 (by rfl) ⟨1611971, by rfl⟩ : syracuseStep 2149295 = 3223943) B3223943
theorem B2149385 : Blo 1431535 2149385 := bstep (se 2 (by rfl) ⟨806019, by rfl⟩ : syracuseStep 2149385 = 1612039) B1612039
theorem B2149415 : Blo 1431535 2149415 := bstep (se 1 (by rfl) ⟨1612061, by rfl⟩ : syracuseStep 2149415 = 3224123) B3224123
theorem B2149499 : Blo 1431535 2149499 := bstep (se 1 (by rfl) ⟨1612124, by rfl⟩ : syracuseStep 2149499 = 3224249) B3224249
theorem B4836509 : Blo 1431535 4836509 := bstep (se 3 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 4836509 = 1813691) B1813691
theorem B2149625 : Blo 1431535 2149625 := bstep (se 2 (by rfl) ⟨806109, by rfl⟩ : syracuseStep 2149625 = 1612219) B1612219
theorem B2149727 : Blo 1431535 2149727 := bstep (se 1 (by rfl) ⟨1612295, by rfl⟩ : syracuseStep 2149727 = 3224591) B3224591
theorem B2149739 : Blo 1431535 2149739 := bstep (se 1 (by rfl) ⟨1612304, by rfl⟩ : syracuseStep 2149739 = 3224609) B3224609
theorem B3624335 : Blo 1431535 3624335 := bstep (se 1 (by rfl) ⟨2718251, by rfl⟩ : syracuseStep 3624335 = 5436503) B5436503
theorem B3223079 : Blo 1431535 3223079 := bstep (se 1 (by rfl) ⟨2417309, by rfl⟩ : syracuseStep 3223079 = 4834619) B4834619
theorem B4591163 : Blo 1431535 4591163 := bstep (se 1 (by rfl) ⟨3443372, by rfl⟩ : syracuseStep 4591163 = 6886745) B6886745
theorem B75476549 : Blo 1431535 75476549 := bstep (se 4 (by rfl) ⟨7075926, by rfl⟩ : syracuseStep 75476549 = 14151853) B14151853
theorem B2149967 : Blo 1431535 2149967 := bstep (se 1 (by rfl) ⟨1612475, by rfl⟩ : syracuseStep 2149967 = 3224951) B3224951
theorem B4837049 : Blo 1431535 4837049 := bstep (se 2 (by rfl) ⟨1813893, by rfl⟩ : syracuseStep 4837049 = 3627787) B3627787
theorem B6885053 : Blo 1431535 6885053 := bstep (se 3 (by rfl) ⟨1290947, by rfl⟩ : syracuseStep 6885053 = 2581895) B2581895
theorem B2150087 : Blo 1431535 2150087 := bstep (se 1 (by rfl) ⟨1612565, by rfl⟩ : syracuseStep 2150087 = 3225131) B3225131
theorem B3624659 : Blo 1431535 3624659 := bstep (se 1 (by rfl) ⟨2718494, by rfl⟩ : syracuseStep 3624659 = 5436989) B5436989
theorem B5164829 : Blo 1431535 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B2150249 : Blo 1431535 2150249 := bstep (se 2 (by rfl) ⟨806343, by rfl⟩ : syracuseStep 2150249 = 1612687) B1612687
theorem B3223403 : Blo 1431535 3223403 := bstep (se 1 (by rfl) ⟨2417552, by rfl⟩ : syracuseStep 3223403 = 4835105) B4835105
theorem B3223457 : Blo 1431535 3223457 := bstep (se 2 (by rfl) ⟨1208796, by rfl⟩ : syracuseStep 3223457 = 2417593) B2417593
theorem B9801817 : Blo 1431535 9801817 := bstep (se 2 (by rfl) ⟨3675681, by rfl⟩ : syracuseStep 9801817 = 7351363) B7351363
theorem B5435545 : Blo 1431535 5435545 := bstep (se 2 (by rfl) ⟨2038329, by rfl⟩ : syracuseStep 5435545 = 4076659) B4076659
theorem B4133111 : Blo 1431535 4133111 := bstep (se 1 (by rfl) ⟨3099833, by rfl⟩ : syracuseStep 4133111 = 6199667) B6199667
theorem B3223799 : Blo 1431535 3223799 := bstep (se 1 (by rfl) ⟨2417849, by rfl⟩ : syracuseStep 3223799 = 4835699) B4835699
theorem B4837643 : Blo 1431535 4837643 := bstep (se 1 (by rfl) ⟨3628232, by rfl⟩ : syracuseStep 4837643 = 7256465) B7256465
theorem B7254359 : Blo 1431535 7254359 := bstep (se 1 (by rfl) ⟨5440769, by rfl⟩ : syracuseStep 7254359 = 10881539) B10881539
theorem B5435849 : Blo 1431535 5435849 := bstep (se 2 (by rfl) ⟨2038443, by rfl⟩ : syracuseStep 5435849 = 4076887) B4076887
theorem B11030987 : Blo 1431535 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B5804531 : Blo 1431535 5804531 := bstep (se 1 (by rfl) ⟨4353398, by rfl⟩ : syracuseStep 5804531 = 8706797) B8706797
theorem B4837913 : Blo 1431535 4837913 := bstep (se 2 (by rfl) ⟨1814217, by rfl⟩ : syracuseStep 4837913 = 3628435) B3628435
theorem B3060263 : Blo 1431535 3060263 := bstep (se 1 (by rfl) ⟨2295197, by rfl⟩ : syracuseStep 3060263 = 4590395) B4590395
theorem B5591741 : Blo 1431535 5591741 := bstep (se 3 (by rfl) ⟨1048451, by rfl⟩ : syracuseStep 5591741 = 2096903) B2096903
theorem B4354759 : Blo 1431535 4354759 := bstep (se 1 (by rfl) ⟨3266069, by rfl⟩ : syracuseStep 4354759 = 6532139) B6532139
theorem B3224393 : Blo 1431535 3224393 := bstep (se 2 (by rfl) ⟨1209147, by rfl⟩ : syracuseStep 3224393 = 2418295) B2418295
theorem B3625823 : Blo 1431535 3625823 := bstep (se 1 (by rfl) ⟨2719367, by rfl⟩ : syracuseStep 3625823 = 5438735) B5438735
theorem B1610671 : Blo 1431535 1610671 := bstep (se 1 (by rfl) ⟨1208003, by rfl⟩ : syracuseStep 1610671 = 2416007) B2416007
theorem B5436335 : Blo 1431535 5436335 := bstep (se 1 (by rfl) ⟨4077251, by rfl⟩ : syracuseStep 5436335 = 8154503) B8154503
theorem B4133807 : Blo 1431535 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B17421277 : Blo 1431535 17421277 := bstep (se 3 (by rfl) ⟨3266489, by rfl⟩ : syracuseStep 17421277 = 6532979) B6532979
theorem B15496211 : Blo 1431535 15496211 := bstep (se 1 (by rfl) ⟨11622158, by rfl⟩ : syracuseStep 15496211 = 23244317) B23244317
theorem B32257091 : Blo 1431535 32257091 := bstep (se 1 (by rfl) ⟨24192818, by rfl⟩ : syracuseStep 32257091 = 48385637) B48385637
theorem B1611103 : Blo 1431535 1611103 := bstep (se 1 (by rfl) ⟨1208327, by rfl⟩ : syracuseStep 1611103 = 2416655) B2416655
theorem B3872281 : Blo 1431535 3872281 := bstep (se 2 (by rfl) ⟨1452105, by rfl⟩ : syracuseStep 3872281 = 2904211) B2904211
theorem B6116903 : Blo 1431535 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B6534695 : Blo 1431535 6534695 := bstep (se 1 (by rfl) ⟨4901021, by rfl⟩ : syracuseStep 6534695 = 9802043) B9802043
theorem B4134497 : Blo 1431535 4134497 := bstep (se 2 (by rfl) ⟨1550436, by rfl⟩ : syracuseStep 4134497 = 3100873) B3100873
theorem B3225185 : Blo 1431535 3225185 := bstep (se 2 (by rfl) ⟨1209444, by rfl⟩ : syracuseStep 3225185 = 2418889) B2418889
theorem B1611463 : Blo 1431535 1611463 := bstep (se 1 (by rfl) ⟨1208597, by rfl⟩ : syracuseStep 1611463 = 2417195) B2417195
theorem B3266399 : Blo 1431535 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B9172871 : Blo 1431535 9172871 := bstep (se 1 (by rfl) ⟨6879653, by rfl⟩ : syracuseStep 9172871 = 13759307) B13759307
theorem B3626927 : Blo 1431535 3626927 := bstep (se 1 (by rfl) ⟨2720195, by rfl⟩ : syracuseStep 3626927 = 5440391) B5440391
theorem B7247879 : Blo 1431535 7247879 := bstep (se 1 (by rfl) ⟨5435909, by rfl⟩ : syracuseStep 7247879 = 10871819) B10871819
theorem B2717705 : Blo 1431535 2717705 := bstep (se 2 (by rfl) ⟨1019139, by rfl⟩ : syracuseStep 2717705 = 2038279) B2038279
theorem B1431591 : Blo 1431535 1431591 := bstep (se 1 (by rfl) ⟨1073693, by rfl⟩ : syracuseStep 1431591 = 2147387) B2147387
theorem B1431631 : Blo 1431535 1431631 := bstep (se 1 (by rfl) ⟨1073723, by rfl⟩ : syracuseStep 1431631 = 2147447) B2147447
theorem B6887513 : Blo 1431535 6887513 := bstep (se 2 (by rfl) ⟨2582817, by rfl⟩ : syracuseStep 6887513 = 5165635) B5165635
theorem B1431647 : Blo 1431535 1431647 := bstep (se 1 (by rfl) ⟨1073735, by rfl⟩ : syracuseStep 1431647 = 2147471) B2147471
theorem B1431675 : Blo 1431535 1431675 := bstep (se 1 (by rfl) ⟨1073756, by rfl⟩ : syracuseStep 1431675 = 2147513) B2147513
theorem B15480989 : Blo 1431535 15480989 := bstep (se 3 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 15480989 = 5805371) B5805371
theorem B1431727 : Blo 1431535 1431727 := bstep (se 1 (by rfl) ⟨1073795, by rfl⟩ : syracuseStep 1431727 = 2147591) B2147591
theorem B1431751 : Blo 1431535 1431751 := bstep (se 1 (by rfl) ⟨1073813, by rfl⟩ : syracuseStep 1431751 = 2147627) B2147627
theorem B1431771 : Blo 1431535 1431771 := bstep (se 1 (by rfl) ⟨1073828, by rfl⟩ : syracuseStep 1431771 = 2147657) B2147657
theorem B1431847 : Blo 1431535 1431847 := bstep (se 1 (by rfl) ⟨1073885, by rfl⟩ : syracuseStep 1431847 = 2147771) B2147771
theorem B10885427 : Blo 1431535 10885427 := bstep (se 1 (by rfl) ⟨8164070, by rfl⟩ : syracuseStep 10885427 = 16328141) B16328141
theorem B1431887 : Blo 1431535 1431887 := bstep (se 1 (by rfl) ⟨1073915, by rfl⟩ : syracuseStep 1431887 = 2147831) B2147831
theorem B1431903 : Blo 1431535 1431903 := bstep (se 1 (by rfl) ⟨1073927, by rfl⟩ : syracuseStep 1431903 = 2147855) B2147855
theorem B11032937 : Blo 1431535 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B1431931 : Blo 1431535 1431931 := bstep (se 1 (by rfl) ⟨1073948, by rfl⟩ : syracuseStep 1431931 = 2147897) B2147897
theorem B23222659 : Blo 1431535 23222659 := bstep (se 1 (by rfl) ⟨17416994, by rfl⟩ : syracuseStep 23222659 = 34833989) B34833989
theorem B1431983 : Blo 1431535 1431983 := bstep (se 1 (by rfl) ⟨1073987, by rfl⟩ : syracuseStep 1431983 = 2147975) B2147975
theorem B1432007 : Blo 1431535 1432007 := bstep (se 1 (by rfl) ⟨1074005, by rfl⟩ : syracuseStep 1432007 = 2148011) B2148011
theorem B1432027 : Blo 1431535 1432027 := bstep (se 1 (by rfl) ⟨1074020, by rfl⟩ : syracuseStep 1432027 = 2148041) B2148041
theorem B8608237 : Blo 1431535 8608237 := bstep (se 3 (by rfl) ⟨1614044, by rfl⟩ : syracuseStep 8608237 = 3228089) B3228089
theorem B7248365 : Blo 1431535 7248365 := bstep (se 3 (by rfl) ⟨1359068, by rfl⟩ : syracuseStep 7248365 = 2718137) B2718137
theorem B5437961 : Blo 1431535 5437961 := bstep (se 2 (by rfl) ⟨2039235, by rfl⟩ : syracuseStep 5437961 = 4078471) B4078471
theorem B1432103 : Blo 1431535 1432103 := bstep (se 1 (by rfl) ⟨1074077, by rfl⟩ : syracuseStep 1432103 = 2148155) B2148155
theorem B1612327 : Blo 1431535 1612327 := bstep (se 1 (by rfl) ⟨1209245, by rfl⟩ : syracuseStep 1612327 = 2418491) B2418491
theorem B13769261 : Blo 1431535 13769261 := bstep (se 3 (by rfl) ⟨2581736, by rfl⟩ : syracuseStep 13769261 = 5163473) B5163473
theorem B1432143 : Blo 1431535 1432143 := bstep (se 1 (by rfl) ⟨1074107, by rfl⟩ : syracuseStep 1432143 = 2148215) B2148215
theorem B1432159 : Blo 1431535 1432159 := bstep (se 1 (by rfl) ⟨1074119, by rfl⟩ : syracuseStep 1432159 = 2148239) B2148239
theorem B1432187 : Blo 1431535 1432187 := bstep (se 1 (by rfl) ⟨1074140, by rfl⟩ : syracuseStep 1432187 = 2148281) B2148281
theorem B1432239 : Blo 1431535 1432239 := bstep (se 1 (by rfl) ⟨1074179, by rfl⟩ : syracuseStep 1432239 = 2148359) B2148359
theorem B1432263 : Blo 1431535 1432263 := bstep (se 1 (by rfl) ⟨1074197, by rfl⟩ : syracuseStep 1432263 = 2148395) B2148395
theorem B10877651 : Blo 1431535 10877651 := bstep (se 1 (by rfl) ⟨8158238, by rfl⟩ : syracuseStep 10877651 = 16316477) B16316477
theorem B5159639 : Blo 1431535 5159639 := bstep (se 1 (by rfl) ⟨3869729, by rfl⟩ : syracuseStep 5159639 = 7739459) B7739459
theorem B1432283 : Blo 1431535 1432283 := bstep (se 1 (by rfl) ⟨1074212, by rfl⟩ : syracuseStep 1432283 = 2148425) B2148425
theorem B1432359 : Blo 1431535 1432359 := bstep (se 1 (by rfl) ⟨1074269, by rfl⟩ : syracuseStep 1432359 = 2148539) B2148539
theorem B1432399 : Blo 1431535 1432399 := bstep (se 1 (by rfl) ⟨1074299, by rfl⟩ : syracuseStep 1432399 = 2148599) B2148599
theorem B1432415 : Blo 1431535 1432415 := bstep (se 1 (by rfl) ⟨1074311, by rfl⟩ : syracuseStep 1432415 = 2148623) B2148623
theorem B1432443 : Blo 1431535 1432443 := bstep (se 1 (by rfl) ⟨1074332, by rfl⟩ : syracuseStep 1432443 = 2148665) B2148665
theorem B11615123 : Blo 1431535 11615123 := bstep (se 1 (by rfl) ⟨8711342, by rfl⟩ : syracuseStep 11615123 = 17422685) B17422685
theorem B1432495 : Blo 1431535 1432495 := bstep (se 1 (by rfl) ⟨1074371, by rfl⟩ : syracuseStep 1432495 = 2148743) B2148743
theorem B1432519 : Blo 1431535 1432519 := bstep (se 1 (by rfl) ⟨1074389, by rfl⟩ : syracuseStep 1432519 = 2148779) B2148779
theorem B1432539 : Blo 1431535 1432539 := bstep (se 1 (by rfl) ⟨1074404, by rfl⟩ : syracuseStep 1432539 = 2148809) B2148809
theorem B1432615 : Blo 1431535 1432615 := bstep (se 1 (by rfl) ⟨1074461, by rfl⟩ : syracuseStep 1432615 = 2148923) B2148923
theorem B3439673 : Blo 1431535 3439673 := bstep (se 2 (by rfl) ⟨1289877, by rfl⟩ : syracuseStep 3439673 = 2579755) B2579755
theorem B1432655 : Blo 1431535 1432655 := bstep (se 1 (by rfl) ⟨1074491, by rfl⟩ : syracuseStep 1432655 = 2148983) B2148983
theorem B3628111 : Blo 1431535 3628111 := bstep (se 1 (by rfl) ⟨2721083, by rfl⟩ : syracuseStep 3628111 = 5442167) B5442167
theorem B1432671 : Blo 1431535 1432671 := bstep (se 1 (by rfl) ⟨1074503, by rfl⟩ : syracuseStep 1432671 = 2149007) B2149007
theorem B1432699 : Blo 1431535 1432699 := bstep (se 1 (by rfl) ⟨1074524, by rfl⟩ : syracuseStep 1432699 = 2149049) B2149049
theorem B1432751 : Blo 1431535 1432751 := bstep (se 1 (by rfl) ⟨1074563, by rfl⟩ : syracuseStep 1432751 = 2149127) B2149127
theorem B1432775 : Blo 1431535 1432775 := bstep (se 1 (by rfl) ⟨1074581, by rfl⟩ : syracuseStep 1432775 = 2149163) B2149163
theorem B1432795 : Blo 1431535 1432795 := bstep (se 1 (by rfl) ⟨1074596, by rfl⟩ : syracuseStep 1432795 = 2149193) B2149193
theorem B5807351 : Blo 1431535 5807351 := bstep (se 1 (by rfl) ⟨4355513, by rfl⟩ : syracuseStep 5807351 = 8711027) B8711027
theorem B2415865 : Blo 1431535 2415865 := bstep (se 2 (by rfl) ⟨905949, by rfl⟩ : syracuseStep 2415865 = 1811899) B1811899
theorem B4193527 : Blo 1431535 4193527 := bstep (se 1 (by rfl) ⟨3145145, by rfl⟩ : syracuseStep 4193527 = 6290291) B6290291
theorem B7249175 : Blo 1431535 7249175 := bstep (se 1 (by rfl) ⟨5436881, by rfl⟩ : syracuseStep 7249175 = 10873763) B10873763
theorem B1432871 : Blo 1431535 1432871 := bstep (se 1 (by rfl) ⟨1074653, by rfl⟩ : syracuseStep 1432871 = 2149307) B2149307
theorem B1432911 : Blo 1431535 1432911 := bstep (se 1 (by rfl) ⟨1074683, by rfl⟩ : syracuseStep 1432911 = 2149367) B2149367
theorem B5807447 : Blo 1431535 5807447 := bstep (se 1 (by rfl) ⟨4355585, by rfl⟩ : syracuseStep 5807447 = 8711171) B8711171
theorem B1432927 : Blo 1431535 1432927 := bstep (se 1 (by rfl) ⟨1074695, by rfl⟩ : syracuseStep 1432927 = 2149391) B2149391
theorem B1432955 : Blo 1431535 1432955 := bstep (se 1 (by rfl) ⟨1074716, by rfl⟩ : syracuseStep 1432955 = 2149433) B2149433
theorem B1433007 : Blo 1431535 1433007 := bstep (se 1 (by rfl) ⟨1074755, by rfl⟩ : syracuseStep 1433007 = 2149511) B2149511
theorem B2719163 : Blo 1431535 2719163 := bstep (se 1 (by rfl) ⟨2039372, by rfl⟩ : syracuseStep 2719163 = 4078745) B4078745
theorem B1433031 : Blo 1431535 1433031 := bstep (se 1 (by rfl) ⟨1074773, by rfl⟩ : syracuseStep 1433031 = 2149547) B2149547
theorem B1433051 : Blo 1431535 1433051 := bstep (se 1 (by rfl) ⟨1074788, by rfl⟩ : syracuseStep 1433051 = 2149577) B2149577
theorem B4136435 : Blo 1431535 4136435 := bstep (se 1 (by rfl) ⟨3102326, by rfl⟩ : syracuseStep 4136435 = 6204653) B6204653
theorem B2416135 : Blo 1431535 2416135 := bstep (se 1 (by rfl) ⟨1812101, by rfl⟩ : syracuseStep 2416135 = 3624203) B3624203
theorem B2653715 : Blo 1431535 2653715 := bstep (se 1 (by rfl) ⟨1990286, by rfl⟩ : syracuseStep 2653715 = 3980573) B3980573
theorem B2580007 : Blo 1431535 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B1433127 : Blo 1431535 1433127 := bstep (se 1 (by rfl) ⟨1074845, by rfl⟩ : syracuseStep 1433127 = 2149691) B2149691
theorem B1433167 : Blo 1431535 1433167 := bstep (se 1 (by rfl) ⟨1074875, by rfl⟩ : syracuseStep 1433167 = 2149751) B2149751
theorem B1433183 : Blo 1431535 1433183 := bstep (se 1 (by rfl) ⟨1074887, by rfl⟩ : syracuseStep 1433183 = 2149775) B2149775
theorem B20700791 : Blo 1431535 20700791 := bstep (se 1 (by rfl) ⟨15525593, by rfl⟩ : syracuseStep 20700791 = 31051187) B31051187
theorem B4832891 : Blo 1431535 4832891 := bstep (se 1 (by rfl) ⟨3624668, by rfl⟩ : syracuseStep 4832891 = 7249337) B7249337
theorem B1433211 : Blo 1431535 1433211 := bstep (se 1 (by rfl) ⟨1074908, by rfl⟩ : syracuseStep 1433211 = 2149817) B2149817
theorem B1433263 : Blo 1431535 1433263 := bstep (se 1 (by rfl) ⟨1074947, by rfl⟩ : syracuseStep 1433263 = 2149895) B2149895
theorem B1433287 : Blo 1431535 1433287 := bstep (se 1 (by rfl) ⟨1074965, by rfl⟩ : syracuseStep 1433287 = 2149931) B2149931
theorem B1433307 : Blo 1431535 1433307 := bstep (se 1 (by rfl) ⟨1074980, by rfl⟩ : syracuseStep 1433307 = 2149961) B2149961
theorem B4587293 : Blo 1431535 4587293 := bstep (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) B1720235
theorem B4833053 : Blo 1431535 4833053 := bstep (se 3 (by rfl) ⟨906197, by rfl⟩ : syracuseStep 4833053 = 1812395) B1812395
theorem B1433383 : Blo 1431535 1433383 := bstep (se 1 (by rfl) ⟨1075037, by rfl⟩ : syracuseStep 1433383 = 2150075) B2150075
theorem B1433423 : Blo 1431535 1433423 := bstep (se 1 (by rfl) ⟨1075067, by rfl⟩ : syracuseStep 1433423 = 2150135) B2150135
theorem B1433439 : Blo 1431535 1433439 := bstep (se 1 (by rfl) ⟨1075079, by rfl⟩ : syracuseStep 1433439 = 2150159) B2150159
theorem B2719595 : Blo 1431535 2719595 := bstep (se 1 (by rfl) ⟨2039696, by rfl⟩ : syracuseStep 2719595 = 4079393) B4079393
theorem B1433467 : Blo 1431535 1433467 := bstep (se 1 (by rfl) ⟨1075100, by rfl⟩ : syracuseStep 1433467 = 2150201) B2150201
theorem B2719649 : Blo 1431535 2719649 := bstep (se 2 (by rfl) ⟨1019868, by rfl⟩ : syracuseStep 2719649 = 2039737) B2039737
theorem B1433519 : Blo 1431535 1433519 := bstep (se 1 (by rfl) ⟨1075139, by rfl⟩ : syracuseStep 1433519 = 2150279) B2150279
theorem B2416567 : Blo 1431535 2416567 := bstep (se 1 (by rfl) ⟨1812425, by rfl⟩ : syracuseStep 2416567 = 3624851) B3624851
theorem B5439419 : Blo 1431535 5439419 := bstep (se 1 (by rfl) ⟨4079564, by rfl⟩ : syracuseStep 5439419 = 8159129) B8159129
theorem B18350297 : Blo 1431535 18350297 := bstep (se 2 (by rfl) ⟨6881361, by rfl⟩ : syracuseStep 18350297 = 13762723) B13762723
theorem B4079963 : Blo 1431535 4079963 := bstep (se 1 (by rfl) ⟨3059972, by rfl⟩ : syracuseStep 4079963 = 6119945) B6119945
theorem B2040175 : Blo 1431535 2040175 := bstep (se 1 (by rfl) ⟨1530131, by rfl⟩ : syracuseStep 2040175 = 3060263) B3060263
theorem B15499673 : Blo 1431535 15499673 := bstep (se 2 (by rfl) ⟨5812377, by rfl⟩ : syracuseStep 15499673 = 11624755) B11624755
theorem B5439919 : Blo 1431535 5439919 := bstep (se 1 (by rfl) ⟨4079939, by rfl⟩ : syracuseStep 5439919 = 8159879) B8159879
theorem B3269089 : Blo 1431535 3269089 := bstep (se 2 (by rfl) ⟨1225908, by rfl⟩ : syracuseStep 3269089 = 2451817) B2451817
theorem B2417215 : Blo 1431535 2417215 := bstep (se 1 (by rfl) ⟨1812911, by rfl⟩ : syracuseStep 2417215 = 3625823) B3625823
theorem B4833863 : Blo 1431535 4833863 := bstep (se 1 (by rfl) ⟨3625397, by rfl⟩ : syracuseStep 4833863 = 7250795) B7250795
theorem B21504727 : Blo 1431535 21504727 := bstep (se 1 (by rfl) ⟨16128545, by rfl⟩ : syracuseStep 21504727 = 32257091) B32257091
theorem B5440223 : Blo 1431535 5440223 := bstep (se 1 (by rfl) ⟨4080167, by rfl⟩ : syracuseStep 5440223 = 8160335) B8160335
theorem B6882209 : Blo 1431535 6882209 := bstep (se 2 (by rfl) ⟨2580828, by rfl⟩ : syracuseStep 6882209 = 5161657) B5161657
theorem B2147303 : Blo 1431535 2147303 := bstep (se 1 (by rfl) ⟨1610477, by rfl⟩ : syracuseStep 2147303 = 3220955) B3220955
theorem B4834295 : Blo 1431535 4834295 := bstep (se 1 (by rfl) ⟨3625721, by rfl⟩ : syracuseStep 4834295 = 7251443) B7251443
theorem B2147561 : Blo 1431535 2147561 := bstep (se 2 (by rfl) ⟨805335, by rfl⟩ : syracuseStep 2147561 = 1610671) B1610671
theorem B2417897 : Blo 1431535 2417897 := bstep (se 2 (by rfl) ⟨906711, by rfl⟩ : syracuseStep 2417897 = 1813423) B1813423
theorem B2147615 : Blo 1431535 2147615 := bstep (se 1 (by rfl) ⟨1610711, by rfl⟩ : syracuseStep 2147615 = 3221423) B3221423
theorem B2417951 : Blo 1431535 2417951 := bstep (se 1 (by rfl) ⟨1813463, by rfl⟩ : syracuseStep 2417951 = 3626927) B3626927
theorem B1811803 : Blo 1431535 1811803 := bstep (se 1 (by rfl) ⟨1358852, by rfl⟩ : syracuseStep 1811803 = 2717705) B2717705
theorem B5440877 : Blo 1431535 5440877 := bstep (se 3 (by rfl) ⟨1020164, by rfl⟩ : syracuseStep 5440877 = 2040329) B2040329
theorem B5440891 : Blo 1431535 5440891 := bstep (se 1 (by rfl) ⟨4080668, by rfl⟩ : syracuseStep 5440891 = 8161337) B8161337
theorem B2147783 : Blo 1431535 2147783 := bstep (se 1 (by rfl) ⟨1610837, by rfl⟩ : syracuseStep 2147783 = 3221675) B3221675
theorem B6882823 : Blo 1431535 6882823 := bstep (se 1 (by rfl) ⟨5162117, by rfl⟩ : syracuseStep 6882823 = 10324235) B10324235
theorem B3221153 : Blo 1431535 3221153 := bstep (se 2 (by rfl) ⟨1207932, by rfl⟩ : syracuseStep 3221153 = 2415865) B2415865
theorem B2148137 : Blo 1431535 2148137 := bstep (se 2 (by rfl) ⟨805551, by rfl⟩ : syracuseStep 2148137 = 1611103) B1611103
theorem B2148143 : Blo 1431535 2148143 := bstep (se 1 (by rfl) ⟨1611107, by rfl⟩ : syracuseStep 2148143 = 3222215) B3222215
theorem B7251767 : Blo 1431535 7251767 := bstep (se 1 (by rfl) ⟨5438825, by rfl⟩ : syracuseStep 7251767 = 10877651) B10877651
theorem B14911309 : Blo 1431535 14911309 := bstep (se 3 (by rfl) ⟨2795870, by rfl⟩ : syracuseStep 14911309 = 5591741) B5591741
theorem B4835159 : Blo 1431535 4835159 := bstep (se 1 (by rfl) ⟨3626369, by rfl⟩ : syracuseStep 4835159 = 7252739) B7252739
theorem B30984119 : Blo 1431535 30984119 := bstep (se 1 (by rfl) ⟨23238089, by rfl⟩ : syracuseStep 30984119 = 46476179) B46476179
theorem B3221513 : Blo 1431535 3221513 := bstep (se 2 (by rfl) ⟨1208067, by rfl⟩ : syracuseStep 3221513 = 2416135) B2416135
theorem B5163041 : Blo 1431535 5163041 := bstep (se 2 (by rfl) ⟨1936140, by rfl⟩ : syracuseStep 5163041 = 3872281) B3872281
theorem B12232781 : Blo 1431535 12232781 := bstep (se 3 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 12232781 = 4587293) B4587293
theorem B2148617 : Blo 1431535 2148617 := bstep (se 2 (by rfl) ⟨805731, by rfl⟩ : syracuseStep 2148617 = 1611463) B1611463
theorem B41290013 : Blo 1431535 41290013 := bstep (se 3 (by rfl) ⟨7741877, by rfl⟩ : syracuseStep 41290013 = 15483755) B15483755
theorem B7252253 : Blo 1431535 7252253 := bstep (se 3 (by rfl) ⟨1359797, by rfl⟩ : syracuseStep 7252253 = 2719595) B2719595
theorem B1812775 : Blo 1431535 1812775 := bstep (se 1 (by rfl) ⟨1359581, by rfl⟩ : syracuseStep 1812775 = 2719163) B2719163
theorem B2148719 : Blo 1431535 2148719 := bstep (se 1 (by rfl) ⟨1611539, by rfl⟩ : syracuseStep 2148719 = 3223079) B3223079
theorem B50317699 : Blo 1431535 50317699 := bstep (se 1 (by rfl) ⟨37738274, by rfl⟩ : syracuseStep 50317699 = 75476549) B75476549
theorem B3221927 : Blo 1431535 3221927 := bstep (se 1 (by rfl) ⟨2416445, by rfl⟩ : syracuseStep 3221927 = 4832891) B4832891
theorem B4590035 : Blo 1431535 4590035 := bstep (se 1 (by rfl) ⟨3442526, by rfl⟩ : syracuseStep 4590035 = 6885053) B6885053
theorem B3222035 : Blo 1431535 3222035 := bstep (se 1 (by rfl) ⟨2416526, by rfl⟩ : syracuseStep 3222035 = 4833053) B4833053
theorem B3443219 : Blo 1431535 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B45910597 : Blo 1431535 45910597 := bstep (se 4 (by rfl) ⟨4304118, by rfl⟩ : syracuseStep 45910597 = 8608237) B8608237
theorem B2148935 : Blo 1431535 2148935 := bstep (se 1 (by rfl) ⟨1611701, by rfl⟩ : syracuseStep 2148935 = 3223403) B3223403
theorem B3222089 : Blo 1431535 3222089 := bstep (se 2 (by rfl) ⟨1208283, by rfl⟩ : syracuseStep 3222089 = 2416567) B2416567
theorem B1813099 : Blo 1431535 1813099 := bstep (se 1 (by rfl) ⟨1359824, by rfl⟩ : syracuseStep 1813099 = 2719649) B2719649
theorem B2148971 : Blo 1431535 2148971 := bstep (se 1 (by rfl) ⟨1611728, by rfl⟩ : syracuseStep 2148971 = 3223457) B3223457
theorem B2755193 : Blo 1431535 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B29420243 : Blo 1431535 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B41323229 : Blo 1431535 41323229 := bstep (se 3 (by rfl) ⟨7748105, by rfl⟩ : syracuseStep 41323229 = 15496211) B15496211
theorem B2149199 : Blo 1431535 2149199 := bstep (se 1 (by rfl) ⟨1611899, by rfl⟩ : syracuseStep 2149199 = 3223799) B3223799
theorem B4836239 : Blo 1431535 4836239 := bstep (se 1 (by rfl) ⟨3627179, by rfl⟩ : syracuseStep 4836239 = 7254359) B7254359
theorem B3623899 : Blo 1431535 3623899 := bstep (se 1 (by rfl) ⟨2717924, by rfl⟩ : syracuseStep 3623899 = 5435849) B5435849
theorem B3222503 : Blo 1431535 3222503 := bstep (se 1 (by rfl) ⟨2416877, by rfl⟩ : syracuseStep 3222503 = 4833755) B4833755
theorem B3869687 : Blo 1431535 3869687 := bstep (se 1 (by rfl) ⟨2902265, by rfl⟩ : syracuseStep 3869687 = 5804531) B5804531
theorem B52276357 : Blo 1431535 52276357 := bstep (se 4 (by rfl) ⟨4900908, by rfl⟩ : syracuseStep 52276357 = 9801817) B9801817
theorem B2149595 : Blo 1431535 2149595 := bstep (se 1 (by rfl) ⟨1612196, by rfl⟩ : syracuseStep 2149595 = 3224393) B3224393
theorem B3624223 : Blo 1431535 3624223 := bstep (se 1 (by rfl) ⟨2718167, by rfl⟩ : syracuseStep 3624223 = 5436335) B5436335
theorem B2755871 : Blo 1431535 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B9178429 : Blo 1431535 9178429 := bstep (se 3 (by rfl) ⟨1720955, by rfl⟩ : syracuseStep 9178429 = 3441911) B3441911
theorem B6884669 : Blo 1431535 6884669 := bstep (se 3 (by rfl) ⟨1290875, by rfl⟩ : syracuseStep 6884669 = 2581751) B2581751
theorem B27897185 : Blo 1431535 27897185 := bstep (se 2 (by rfl) ⟨10461444, by rfl⟩ : syracuseStep 27897185 = 20922889) B20922889
theorem B3222881 : Blo 1431535 3222881 := bstep (se 2 (by rfl) ⟨1208580, by rfl⟩ : syracuseStep 3222881 = 2417161) B2417161
theorem B3444065 : Blo 1431535 3444065 := bstep (se 2 (by rfl) ⟨1291524, by rfl⟩ : syracuseStep 3444065 = 2583049) B2583049
theorem B2149769 : Blo 1431535 2149769 := bstep (se 2 (by rfl) ⟨806163, by rfl⟩ : syracuseStep 2149769 = 1612327) B1612327
theorem B3222971 : Blo 1431535 3222971 := bstep (se 1 (by rfl) ⟨2417228, by rfl⟩ : syracuseStep 3222971 = 4834457) B4834457
theorem B3223097 : Blo 1431535 3223097 := bstep (se 2 (by rfl) ⟨1208661, by rfl⟩ : syracuseStep 3223097 = 2417323) B2417323
theorem B2150123 : Blo 1431535 2150123 := bstep (se 1 (by rfl) ⟨1612592, by rfl⟩ : syracuseStep 2150123 = 3225185) B3225185
theorem B7352171 : Blo 1431535 7352171 := bstep (se 1 (by rfl) ⟨5514128, by rfl⟩ : syracuseStep 7352171 = 11028257) B11028257
theorem B1634203 : Blo 1431535 1634203 := bstep (se 1 (by rfl) ⟨1225652, by rfl⟩ : syracuseStep 1634203 = 2451305) B2451305
theorem B6115247 : Blo 1431535 6115247 := bstep (se 1 (by rfl) ⟨4586435, by rfl⟩ : syracuseStep 6115247 = 9172871) B9172871
theorem B23228369 : Blo 1431535 23228369 := bstep (se 2 (by rfl) ⟨8710638, by rfl⟩ : syracuseStep 23228369 = 17421277) B17421277
theorem B7254035 : Blo 1431535 7254035 := bstep (se 1 (by rfl) ⟨5440526, by rfl⟩ : syracuseStep 7254035 = 10881053) B10881053
theorem B5812249 : Blo 1431535 5812249 := bstep (se 2 (by rfl) ⟨2179593, by rfl⟩ : syracuseStep 5812249 = 4359187) B4359187
theorem B4591675 : Blo 1431535 4591675 := bstep (se 1 (by rfl) ⟨3443756, by rfl⟩ : syracuseStep 4591675 = 6887513) B6887513
theorem B4837481 : Blo 1431535 4837481 := bstep (se 2 (by rfl) ⟨1814055, by rfl⟩ : syracuseStep 4837481 = 3628111) B3628111
theorem B3223763 : Blo 1431535 3223763 := bstep (se 1 (by rfl) ⟨2417822, by rfl⟩ : syracuseStep 3223763 = 4835645) B4835645
theorem B3223817 : Blo 1431535 3223817 := bstep (se 2 (by rfl) ⟨1208931, by rfl⟩ : syracuseStep 3223817 = 2417863) B2417863
theorem B5591369 : Blo 1431535 5591369 := bstep (se 2 (by rfl) ⟨2096763, by rfl⟩ : syracuseStep 5591369 = 4193527) B4193527
theorem B3625307 : Blo 1431535 3625307 := bstep (se 1 (by rfl) ⟨2718980, by rfl⟩ : syracuseStep 3625307 = 5437961) B5437961
theorem B9179507 : Blo 1431535 9179507 := bstep (se 1 (by rfl) ⟨6884630, by rfl⟩ : syracuseStep 9179507 = 13769261) B13769261
theorem B3224033 : Blo 1431535 3224033 := bstep (se 2 (by rfl) ⟨1209012, by rfl⟩ : syracuseStep 3224033 = 2418025) B2418025
theorem B3224339 : Blo 1431535 3224339 := bstep (se 1 (by rfl) ⟨2418254, by rfl⟩ : syracuseStep 3224339 = 4836509) B4836509
theorem B3871567 : Blo 1431535 3871567 := bstep (se 1 (by rfl) ⟨2903675, by rfl⟩ : syracuseStep 3871567 = 5807351) B5807351
theorem B3871631 : Blo 1431535 3871631 := bstep (se 1 (by rfl) ⟨2903723, by rfl⟩ : syracuseStep 3871631 = 5807447) B5807447
theorem B3060775 : Blo 1431535 3060775 := bstep (se 1 (by rfl) ⟨2295581, by rfl⟩ : syracuseStep 3060775 = 4591163) B4591163
theorem B13800527 : Blo 1431535 13800527 := bstep (se 1 (by rfl) ⟨10350395, by rfl⟩ : syracuseStep 13800527 = 20700791) B20700791
theorem B3224699 : Blo 1431535 3224699 := bstep (se 1 (by rfl) ⟨2418524, by rfl⟩ : syracuseStep 3224699 = 4837049) B4837049
theorem B44086517 : Blo 1431535 44086517 := bstep (se 5 (by rfl) ⟨2066555, by rfl⟩ : syracuseStep 44086517 = 4133111) B4133111
theorem B3224825 : Blo 1431535 3224825 := bstep (se 2 (by rfl) ⟨1209309, by rfl⟩ : syracuseStep 3224825 = 2418619) B2418619
theorem B3626279 : Blo 1431535 3626279 := bstep (se 1 (by rfl) ⟨2719709, by rfl⟩ : syracuseStep 3626279 = 5439419) B5439419
theorem B3224969 : Blo 1431535 3224969 := bstep (se 2 (by rfl) ⟨1209363, by rfl⟩ : syracuseStep 3224969 = 2418727) B2418727
theorem B1611175 : Blo 1431535 1611175 := bstep (se 1 (by rfl) ⟨1208381, by rfl⟩ : syracuseStep 1611175 = 2416763) B2416763
theorem B3225095 : Blo 1431535 3225095 := bstep (se 1 (by rfl) ⟨2418821, by rfl⟩ : syracuseStep 3225095 = 4837643) B4837643
theorem B7247393 : Blo 1431535 7247393 := bstep (se 2 (by rfl) ⟨2717772, by rfl⟩ : syracuseStep 7247393 = 5435545) B5435545
theorem B7353991 : Blo 1431535 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B3225275 : Blo 1431535 3225275 := bstep (se 1 (by rfl) ⟨2418956, by rfl⟩ : syracuseStep 3225275 = 4837913) B4837913
theorem B3266345 : Blo 1431535 3266345 := bstep (se 2 (by rfl) ⟨1224879, by rfl⟩ : syracuseStep 3266345 = 2449759) B2449759
theorem B3225401 : Blo 1431535 3225401 := bstep (se 2 (by rfl) ⟨1209525, by rfl⟩ : syracuseStep 3225401 = 2419051) B2419051
theorem B30963545 : Blo 1431535 30963545 := bstep (se 2 (by rfl) ⟨11611329, by rfl⟩ : syracuseStep 30963545 = 23222659) B23222659
theorem B3872669 : Blo 1431535 3872669 := bstep (se 3 (by rfl) ⟨726125, by rfl⟩ : syracuseStep 3872669 = 1452251) B1452251
theorem B1611751 : Blo 1431535 1611751 := bstep (se 1 (by rfl) ⟨1208813, by rfl⟩ : syracuseStep 1611751 = 2417627) B2417627
theorem B5806345 : Blo 1431535 5806345 := bstep (se 2 (by rfl) ⟨2177379, by rfl⟩ : syracuseStep 5806345 = 4354759) B4354759
theorem B1431839 : Blo 1431535 1431839 := bstep (se 1 (by rfl) ⟨1073879, by rfl⟩ : syracuseStep 1431839 = 2147759) B2147759
theorem B1431899 : Blo 1431535 1431899 := bstep (se 1 (by rfl) ⟨1073924, by rfl⟩ : syracuseStep 1431899 = 2147849) B2147849
theorem B1431919 : Blo 1431535 1431919 := bstep (se 1 (by rfl) ⟨1073939, by rfl⟩ : syracuseStep 1431919 = 2147879) B2147879
theorem B4077935 : Blo 1431535 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B4356463 : Blo 1431535 4356463 := bstep (se 1 (by rfl) ⟨3267347, by rfl⟩ : syracuseStep 4356463 = 6534695) B6534695
theorem B1431975 : Blo 1431535 1431975 := bstep (se 1 (by rfl) ⟨1073981, by rfl⟩ : syracuseStep 1431975 = 2147963) B2147963
theorem B1432059 : Blo 1431535 1432059 := bstep (se 1 (by rfl) ⟨1074044, by rfl⟩ : syracuseStep 1432059 = 2148089) B2148089
theorem B1432127 : Blo 1431535 1432127 := bstep (se 1 (by rfl) ⟨1074095, by rfl⟩ : syracuseStep 1432127 = 2148191) B2148191
theorem B2177599 : Blo 1431535 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B1432135 : Blo 1431535 1432135 := bstep (se 1 (by rfl) ⟨1074101, by rfl⟩ : syracuseStep 1432135 = 2148203) B2148203
theorem B4831919 : Blo 1431535 4831919 := bstep (se 1 (by rfl) ⟨3623939, by rfl⟩ : syracuseStep 4831919 = 7247879) B7247879
theorem B1432287 : Blo 1431535 1432287 := bstep (se 1 (by rfl) ⟨1074215, by rfl⟩ : syracuseStep 1432287 = 2148431) B2148431
theorem B3627767 : Blo 1431535 3627767 := bstep (se 1 (by rfl) ⟨2720825, by rfl⟩ : syracuseStep 3627767 = 5441651) B5441651
theorem B44079875 : Blo 1431535 44079875 := bstep (se 1 (by rfl) ⟨33059906, by rfl⟩ : syracuseStep 44079875 = 66119813) B66119813
theorem B10320659 : Blo 1431535 10320659 := bstep (se 1 (by rfl) ⟨7740494, by rfl⟩ : syracuseStep 10320659 = 15480989) B15480989
theorem B1432367 : Blo 1431535 1432367 := bstep (se 1 (by rfl) ⟨1074275, by rfl⟩ : syracuseStep 1432367 = 2148551) B2148551
theorem B7256951 : Blo 1431535 7256951 := bstep (se 1 (by rfl) ⟨5442713, by rfl⟩ : syracuseStep 7256951 = 10885427) B10885427
theorem B12245903 : Blo 1431535 12245903 := bstep (se 1 (by rfl) ⟨9184427, by rfl⟩ : syracuseStep 12245903 = 18368855) B18368855
theorem B1432475 : Blo 1431535 1432475 := bstep (se 1 (by rfl) ⟨1074356, by rfl⟩ : syracuseStep 1432475 = 2148713) B2148713
theorem B7355291 : Blo 1431535 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B11025325 : Blo 1431535 11025325 := bstep (se 3 (by rfl) ⟨2067248, by rfl⟩ : syracuseStep 11025325 = 4134497) B4134497
theorem B1432527 : Blo 1431535 1432527 := bstep (se 1 (by rfl) ⟨1074395, by rfl⟩ : syracuseStep 1432527 = 2148791) B2148791
theorem B1432551 : Blo 1431535 1432551 := bstep (se 1 (by rfl) ⟨1074413, by rfl⟩ : syracuseStep 1432551 = 2148827) B2148827
theorem B4832243 : Blo 1431535 4832243 := bstep (se 1 (by rfl) ⟨3624182, by rfl⟩ : syracuseStep 4832243 = 7248365) B7248365
theorem B18594845 : Blo 1431535 18594845 := bstep (se 3 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 18594845 = 6973067) B6973067
theorem B3439759 : Blo 1431535 3439759 := bstep (se 1 (by rfl) ⟨2579819, by rfl⟩ : syracuseStep 3439759 = 5159639) B5159639
theorem B9182429 : Blo 1431535 9182429 := bstep (se 3 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 9182429 = 3443411) B3443411
theorem B1432863 : Blo 1431535 1432863 := bstep (se 1 (by rfl) ⟨1074647, by rfl⟩ : syracuseStep 1432863 = 2149295) B2149295
theorem B1432923 : Blo 1431535 1432923 := bstep (se 1 (by rfl) ⟨1074692, by rfl⟩ : syracuseStep 1432923 = 2149385) B2149385
theorem B3628385 : Blo 1431535 3628385 := bstep (se 2 (by rfl) ⟨1360644, by rfl⟩ : syracuseStep 3628385 = 2721289) B2721289
theorem B1432943 : Blo 1431535 1432943 := bstep (se 1 (by rfl) ⟨1074707, by rfl⟩ : syracuseStep 1432943 = 2149415) B2149415
theorem B2293115 : Blo 1431535 2293115 := bstep (se 1 (by rfl) ⟨1719836, by rfl⟩ : syracuseStep 2293115 = 3439673) B3439673
theorem B3440009 : Blo 1431535 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B1432999 : Blo 1431535 1432999 := bstep (se 1 (by rfl) ⟨1074749, by rfl⟩ : syracuseStep 1432999 = 2149499) B2149499
theorem B176487893 : Blo 1431535 176487893 := bstep (se 7 (by rfl) ⟨2068217, by rfl⟩ : syracuseStep 176487893 = 4136435) B4136435
theorem B1433083 : Blo 1431535 1433083 := bstep (se 1 (by rfl) ⟨1074812, by rfl⟩ : syracuseStep 1433083 = 2149625) B2149625
theorem B4832783 : Blo 1431535 4832783 := bstep (se 1 (by rfl) ⟨3624587, by rfl⟩ : syracuseStep 4832783 = 7249175) B7249175
theorem B1433151 : Blo 1431535 1433151 := bstep (se 1 (by rfl) ⟨1074863, by rfl⟩ : syracuseStep 1433151 = 2149727) B2149727
theorem B1433159 : Blo 1431535 1433159 := bstep (se 1 (by rfl) ⟨1074869, by rfl⟩ : syracuseStep 1433159 = 2149739) B2149739
theorem B2416223 : Blo 1431535 2416223 := bstep (se 1 (by rfl) ⟨1812167, by rfl⟩ : syracuseStep 2416223 = 3624335) B3624335
theorem B1769143 : Blo 1431535 1769143 := bstep (se 1 (by rfl) ⟨1326857, by rfl⟩ : syracuseStep 1769143 = 2653715) B2653715
theorem B30973661 : Blo 1431535 30973661 := bstep (se 3 (by rfl) ⟨5807561, by rfl⟩ : syracuseStep 30973661 = 11615123) B11615123
theorem B1433311 : Blo 1431535 1433311 := bstep (se 1 (by rfl) ⟨1074983, by rfl⟩ : syracuseStep 1433311 = 2149967) B2149967
theorem B1433391 : Blo 1431535 1433391 := bstep (se 1 (by rfl) ⟨1075043, by rfl⟩ : syracuseStep 1433391 = 2150087) B2150087
theorem B2416439 : Blo 1431535 2416439 := bstep (se 1 (by rfl) ⟨1812329, by rfl⟩ : syracuseStep 2416439 = 3624659) B3624659
theorem B1433499 : Blo 1431535 1433499 := bstep (se 1 (by rfl) ⟨1075124, by rfl⟩ : syracuseStep 1433499 = 2150249) B2150249
theorem B7749665 : Blo 1431535 7749665 := bstep (se 2 (by rfl) ⟨2906124, by rfl⟩ : syracuseStep 7749665 = 5812249) B5812249
theorem B2416871 : Blo 1431535 2416871 := bstep (se 1 (by rfl) ⟨1812653, by rfl⟩ : syracuseStep 2416871 = 3625307) B3625307
theorem B2719975 : Blo 1431535 2719975 := bstep (se 1 (by rfl) ⟨2039981, by rfl⟩ : syracuseStep 2719975 = 4079963) B4079963
theorem B6119671 : Blo 1431535 6119671 := bstep (se 1 (by rfl) ⟨4589753, by rfl⟩ : syracuseStep 6119671 = 9179507) B9179507
theorem B7741793 : Blo 1431535 7741793 := bstep (se 2 (by rfl) ⟨2903172, by rfl⟩ : syracuseStep 7741793 = 5806345) B5806345
theorem B2417033 : Blo 1431535 2417033 := bstep (se 2 (by rfl) ⟨906387, by rfl⟩ : syracuseStep 2417033 = 1812775) B1812775
theorem B5808617 : Blo 1431535 5808617 := bstep (se 2 (by rfl) ⟨2178231, by rfl⟩ : syracuseStep 5808617 = 4356463) B4356463
theorem B2720233 : Blo 1431535 2720233 := bstep (se 2 (by rfl) ⟨1020087, by rfl⟩ : syracuseStep 2720233 = 2040175) B2040175
theorem B4588139 : Blo 1431535 4588139 := bstep (se 1 (by rfl) ⟨3441104, by rfl⟩ : syracuseStep 4588139 = 6882209) B6882209
theorem B9200351 : Blo 1431535 9200351 := bstep (se 1 (by rfl) ⟨6900263, by rfl⟩ : syracuseStep 9200351 = 13800527) B13800527
theorem B2417465 : Blo 1431535 2417465 := bstep (se 2 (by rfl) ⟨906549, by rfl⟩ : syracuseStep 2417465 = 1813099) B1813099
theorem B14910317 : Blo 1431535 14910317 := bstep (se 3 (by rfl) ⟨2795684, by rfl⟩ : syracuseStep 14910317 = 5591369) B5591369
theorem B2417519 : Blo 1431535 2417519 := bstep (se 1 (by rfl) ⟨1813139, by rfl⟩ : syracuseStep 2417519 = 3626279) B3626279
theorem B28672969 : Blo 1431535 28672969 := bstep (se 2 (by rfl) ⟨10752363, by rfl⟩ : syracuseStep 28672969 = 21504727) B21504727
theorem B2147435 : Blo 1431535 2147435 := bstep (se 1 (by rfl) ⟨1610576, by rfl⟩ : syracuseStep 2147435 = 3221153) B3221153
theorem B4834511 : Blo 1431535 4834511 := bstep (se 1 (by rfl) ⟨3625883, by rfl⟩ : syracuseStep 4834511 = 7251767) B7251767
theorem B2147675 : Blo 1431535 2147675 := bstep (se 1 (by rfl) ⟨1610756, by rfl⟩ : syracuseStep 2147675 = 3221513) B3221513
theorem B3442027 : Blo 1431535 3442027 := bstep (se 1 (by rfl) ⟨2581520, by rfl⟩ : syracuseStep 3442027 = 5163041) B5163041
theorem B4081033 : Blo 1431535 4081033 := bstep (se 2 (by rfl) ⟨1530387, by rfl⟩ : syracuseStep 4081033 = 3060775) B3060775
theorem B27526675 : Blo 1431535 27526675 := bstep (se 1 (by rfl) ⟨20645006, by rfl⟩ : syracuseStep 27526675 = 41290013) B41290013
theorem B4834835 : Blo 1431535 4834835 := bstep (se 1 (by rfl) ⟨3626126, by rfl⟩ : syracuseStep 4834835 = 7252253) B7252253
theorem B2147951 : Blo 1431535 2147951 := bstep (se 1 (by rfl) ⟨1610963, by rfl⟩ : syracuseStep 2147951 = 3221927) B3221927
theorem B2148023 : Blo 1431535 2148023 := bstep (se 1 (by rfl) ⟨1611017, by rfl⟩ : syracuseStep 2148023 = 3222035) B3222035
theorem B2295479 : Blo 1431535 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B2148059 : Blo 1431535 2148059 := bstep (se 1 (by rfl) ⟨1611044, by rfl⟩ : syracuseStep 2148059 = 3222089) B3222089
theorem B3221279 : Blo 1431535 3221279 := bstep (se 1 (by rfl) ⟨2415959, by rfl⟩ : syracuseStep 3221279 = 4831919) B4831919
theorem B19613495 : Blo 1431535 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B2418511 : Blo 1431535 2418511 := bstep (se 1 (by rfl) ⟨1813883, by rfl⟩ : syracuseStep 2418511 = 3627767) B3627767
theorem B29386583 : Blo 1431535 29386583 := bstep (se 1 (by rfl) ⟨22039937, by rfl⟩ : syracuseStep 29386583 = 44079875) B44079875
theorem B2148233 : Blo 1431535 2148233 := bstep (se 2 (by rfl) ⟨805587, by rfl⟩ : syracuseStep 2148233 = 1611175) B1611175
theorem B2148335 : Blo 1431535 2148335 := bstep (se 1 (by rfl) ⟨1611251, by rfl⟩ : syracuseStep 2148335 = 3222503) B3222503
theorem B3221495 : Blo 1431535 3221495 := bstep (se 1 (by rfl) ⟨2416121, by rfl⟩ : syracuseStep 3221495 = 4832243) B4832243
theorem B9177097 : Blo 1431535 9177097 := bstep (se 2 (by rfl) ⟨3441411, by rfl⟩ : syracuseStep 9177097 = 6882823) B6882823
theorem B12396563 : Blo 1431535 12396563 := bstep (se 1 (by rfl) ⟨9297422, by rfl⟩ : syracuseStep 12396563 = 18594845) B18594845
theorem B8710253 : Blo 1431535 8710253 := bstep (se 3 (by rfl) ⟨1633172, by rfl⟩ : syracuseStep 8710253 = 3266345) B3266345
theorem B6121619 : Blo 1431535 6121619 := bstep (se 1 (by rfl) ⟨4591214, by rfl⟩ : syracuseStep 6121619 = 9182429) B9182429
theorem B1837247 : Blo 1431535 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B4589779 : Blo 1431535 4589779 := bstep (se 1 (by rfl) ⟨3442334, by rfl⟩ : syracuseStep 4589779 = 6884669) B6884669
theorem B18598123 : Blo 1431535 18598123 := bstep (se 1 (by rfl) ⟨13948592, by rfl⟩ : syracuseStep 18598123 = 27897185) B27897185
theorem B2148587 : Blo 1431535 2148587 := bstep (se 1 (by rfl) ⟨1611440, by rfl⟩ : syracuseStep 2148587 = 3222881) B3222881
theorem B2296043 : Blo 1431535 2296043 := bstep (se 1 (by rfl) ⟨1722032, by rfl⟩ : syracuseStep 2296043 = 3444065) B3444065
theorem B2418923 : Blo 1431535 2418923 := bstep (se 1 (by rfl) ⟨1814192, by rfl⟩ : syracuseStep 2418923 = 3628385) B3628385
theorem B2148647 : Blo 1431535 2148647 := bstep (se 1 (by rfl) ⟨1611485, by rfl⟩ : syracuseStep 2148647 = 3222971) B3222971
theorem B3221855 : Blo 1431535 3221855 := bstep (se 1 (by rfl) ⟨2416391, by rfl⟩ : syracuseStep 3221855 = 4832783) B4832783
theorem B2148731 : Blo 1431535 2148731 := bstep (se 1 (by rfl) ⟨1611548, by rfl⟩ : syracuseStep 2148731 = 3223097) B3223097
theorem B10324349 : Blo 1431535 10324349 := bstep (se 3 (by rfl) ⟨1935815, by rfl⟩ : syracuseStep 10324349 = 3871631) B3871631
theorem B19614109 : Blo 1431535 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B17435141 : Blo 1431535 17435141 := bstep (se 4 (by rfl) ⟨1634544, by rfl⟩ : syracuseStep 17435141 = 3269089) B3269089
theorem B4901447 : Blo 1431535 4901447 := bstep (se 1 (by rfl) ⟨3676085, by rfl⟩ : syracuseStep 4901447 = 7352171) B7352171
theorem B2149001 : Blo 1431535 2149001 := bstep (se 2 (by rfl) ⟨805875, by rfl⟩ : syracuseStep 2149001 = 1611751) B1611751
theorem B15485579 : Blo 1431535 15485579 := bstep (se 1 (by rfl) ⟨11614184, by rfl⟩ : syracuseStep 15485579 = 23228369) B23228369
theorem B4836023 : Blo 1431535 4836023 := bstep (se 1 (by rfl) ⟨3627017, by rfl⟩ : syracuseStep 4836023 = 7254035) B7254035
theorem B6122233 : Blo 1431535 6122233 := bstep (se 2 (by rfl) ⟨2295837, by rfl⟩ : syracuseStep 6122233 = 4591675) B4591675
theorem B2149175 : Blo 1431535 2149175 := bstep (se 1 (by rfl) ⟨1611881, by rfl⟩ : syracuseStep 2149175 = 3223763) B3223763
theorem B12233531 : Blo 1431535 12233531 := bstep (se 1 (by rfl) ⟨9175148, by rfl⟩ : syracuseStep 12233531 = 18350297) B18350297
theorem B2149211 : Blo 1431535 2149211 := bstep (se 1 (by rfl) ⟨1611908, by rfl⟩ : syracuseStep 2149211 = 3223817) B3223817
theorem B10333115 : Blo 1431535 10333115 := bstep (se 1 (by rfl) ⟨7749836, by rfl⟩ : syracuseStep 10333115 = 15499673) B15499673
theorem B2149355 : Blo 1431535 2149355 := bstep (se 1 (by rfl) ⟨1612016, by rfl⟩ : syracuseStep 2149355 = 3224033) B3224033
theorem B3222575 : Blo 1431535 3222575 := bstep (se 1 (by rfl) ⟨2416931, by rfl⟩ : syracuseStep 3222575 = 4833863) B4833863
theorem B2149559 : Blo 1431535 2149559 := bstep (se 1 (by rfl) ⟨1612169, by rfl⟩ : syracuseStep 2149559 = 3224339) B3224339
theorem B7253225 : Blo 1431535 7253225 := bstep (se 2 (by rfl) ⟨2719959, by rfl⟩ : syracuseStep 7253225 = 5439919) B5439919
theorem B3222863 : Blo 1431535 3222863 := bstep (se 1 (by rfl) ⟨2417147, by rfl⟩ : syracuseStep 3222863 = 4834295) B4834295
theorem B2149799 : Blo 1431535 2149799 := bstep (se 1 (by rfl) ⟨1612349, by rfl⟩ : syracuseStep 2149799 = 3224699) B3224699
theorem B2903465 : Blo 1431535 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B3222953 : Blo 1431535 3222953 := bstep (se 2 (by rfl) ⟨1208607, by rfl⟩ : syracuseStep 3222953 = 2417215) B2417215
theorem B61214129 : Blo 1431535 61214129 := bstep (se 2 (by rfl) ⟨22955298, by rfl⟩ : syracuseStep 61214129 = 45910597) B45910597
theorem B2149883 : Blo 1431535 2149883 := bstep (se 1 (by rfl) ⟨1612412, by rfl⟩ : syracuseStep 2149883 = 3224825) B3224825
theorem B2149979 : Blo 1431535 2149979 := bstep (se 1 (by rfl) ⟨1612484, by rfl⟩ : syracuseStep 2149979 = 3224969) B3224969
theorem B6114973 : Blo 1431535 6114973 := bstep (se 3 (by rfl) ⟨1146557, by rfl⟩ : syracuseStep 6114973 = 2293115) B2293115
theorem B2150063 : Blo 1431535 2150063 := bstep (se 1 (by rfl) ⟨1612547, by rfl⟩ : syracuseStep 2150063 = 3225095) B3225095
theorem B2150183 : Blo 1431535 2150183 := bstep (se 1 (by rfl) ⟨1612637, by rfl⟩ : syracuseStep 2150183 = 3225275) B3225275
theorem B2150267 : Blo 1431535 2150267 := bstep (se 1 (by rfl) ⟨1612700, by rfl⟩ : syracuseStep 2150267 = 3225401) B3225401
theorem B3223439 : Blo 1431535 3223439 := bstep (se 1 (by rfl) ⟨2417579, by rfl⟩ : syracuseStep 3223439 = 4835159) B4835159
theorem B20656079 : Blo 1431535 20656079 := bstep (se 1 (by rfl) ⟨15492059, by rfl⟩ : syracuseStep 20656079 = 30984119) B30984119
theorem B8155187 : Blo 1431535 8155187 := bstep (se 1 (by rfl) ⟨6116390, by rfl⟩ : syracuseStep 8155187 = 12232781) B12232781
theorem B69701809 : Blo 1431535 69701809 := bstep (se 2 (by rfl) ⟨26138178, by rfl⟩ : syracuseStep 69701809 = 52276357) B52276357
theorem B3060023 : Blo 1431535 3060023 := bstep (se 1 (by rfl) ⟨2295017, by rfl⟩ : syracuseStep 3060023 = 4590035) B4590035
theorem B20648357 : Blo 1431535 20648357 := bstep (se 4 (by rfl) ⟨1935783, by rfl⟩ : syracuseStep 20648357 = 3871567) B3871567
theorem B7254521 : Blo 1431535 7254521 := bstep (se 2 (by rfl) ⟨2720445, by rfl⟩ : syracuseStep 7254521 = 5440891) B5440891
theorem B4837967 : Blo 1431535 4837967 := bstep (se 1 (by rfl) ⟨3628475, by rfl⟩ : syracuseStep 4837967 = 7256951) B7256951
theorem B3224159 : Blo 1431535 3224159 := bstep (se 1 (by rfl) ⟨2418119, by rfl⟩ : syracuseStep 3224159 = 4836239) B4836239
theorem B8163935 : Blo 1431535 8163935 := bstep (se 1 (by rfl) ⟨6122951, by rfl⟩ : syracuseStep 8163935 = 12245903) B12245903
theorem B117658595 : Blo 1431535 117658595 := bstep (se 1 (by rfl) ⟨88243946, by rfl⟩ : syracuseStep 117658595 = 176487893) B176487893
theorem B1610815 : Blo 1431535 1610815 := bstep (se 1 (by rfl) ⟨1208111, by rfl⟩ : syracuseStep 1610815 = 2416223) B2416223
theorem B10327117 : Blo 1431535 10327117 := bstep (se 3 (by rfl) ⟨1936334, by rfl⟩ : syracuseStep 10327117 = 3872669) B3872669
theorem B20649107 : Blo 1431535 20649107 := bstep (se 1 (by rfl) ⟨15486830, by rfl⟩ : syracuseStep 20649107 = 30973661) B30973661
theorem B1610959 : Blo 1431535 1610959 := bstep (se 1 (by rfl) ⟨1208219, by rfl⟩ : syracuseStep 1610959 = 2416439) B2416439
theorem B4076831 : Blo 1431535 4076831 := bstep (se 1 (by rfl) ⟨3057623, by rfl⟩ : syracuseStep 4076831 = 6115247) B6115247
theorem B3224987 : Blo 1431535 3224987 := bstep (se 1 (by rfl) ⟨2418740, by rfl⟩ : syracuseStep 3224987 = 4837481) B4837481
theorem B3626815 : Blo 1431535 3626815 := bstep (se 1 (by rfl) ⟨2720111, by rfl⟩ : syracuseStep 3626815 = 5440223) B5440223
theorem B67090265 : Blo 1431535 67090265 := bstep (se 2 (by rfl) ⟨25158849, by rfl⟩ : syracuseStep 67090265 = 50317699) B50317699
theorem B1431535 : Blo 1431535 1431535 := bstep (se 1 (by rfl) ⟨1073651, by rfl⟩ : syracuseStep 1431535 = 2147303) B2147303
theorem B1431707 : Blo 1431535 1431707 := bstep (se 1 (by rfl) ⟨1073780, by rfl⟩ : syracuseStep 1431707 = 2147561) B2147561
theorem B1611931 : Blo 1431535 1611931 := bstep (se 1 (by rfl) ⟨1208948, by rfl⟩ : syracuseStep 1611931 = 2417897) B2417897
theorem B29391011 : Blo 1431535 29391011 := bstep (se 1 (by rfl) ⟨22043258, by rfl⟩ : syracuseStep 29391011 = 44086517) B44086517
theorem B1431743 : Blo 1431535 1431743 := bstep (se 1 (by rfl) ⟨1073807, by rfl⟩ : syracuseStep 1431743 = 2147615) B2147615
theorem B1611967 : Blo 1431535 1611967 := bstep (se 1 (by rfl) ⟨1208975, by rfl⟩ : syracuseStep 1611967 = 2417951) B2417951
theorem B3627251 : Blo 1431535 3627251 := bstep (se 1 (by rfl) ⟨2720438, by rfl⟩ : syracuseStep 3627251 = 5440877) B5440877
theorem B1431855 : Blo 1431535 1431855 := bstep (se 1 (by rfl) ⟨1073891, by rfl⟩ : syracuseStep 1431855 = 2147783) B2147783
theorem B4831595 : Blo 1431535 4831595 := bstep (se 1 (by rfl) ⟨3623696, by rfl⟩ : syracuseStep 4831595 = 7247393) B7247393
theorem B9173357 : Blo 1431535 9173357 := bstep (se 3 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 9173357 = 3440009) B3440009
theorem B1432091 : Blo 1431535 1432091 := bstep (se 1 (by rfl) ⟨1074068, by rfl⟩ : syracuseStep 1432091 = 2148137) B2148137
theorem B1432095 : Blo 1431535 1432095 := bstep (se 1 (by rfl) ⟨1074071, by rfl⟩ : syracuseStep 1432095 = 2148143) B2148143
theorem B20642363 : Blo 1431535 20642363 := bstep (se 1 (by rfl) ⟨15481772, by rfl⟩ : syracuseStep 20642363 = 30963545) B30963545
theorem B4831865 : Blo 1431535 4831865 := bstep (se 2 (by rfl) ⟨1811949, by rfl⟩ : syracuseStep 4831865 = 3623899) B3623899
theorem B1432411 : Blo 1431535 1432411 := bstep (se 1 (by rfl) ⟨1074308, by rfl⟩ : syracuseStep 1432411 = 2148617) B2148617
theorem B4586345 : Blo 1431535 4586345 := bstep (se 2 (by rfl) ⟨1719879, by rfl⟩ : syracuseStep 4586345 = 3439759) B3439759
theorem B2718623 : Blo 1431535 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B1432479 : Blo 1431535 1432479 := bstep (se 1 (by rfl) ⟨1074359, by rfl⟩ : syracuseStep 1432479 = 2148719) B2148719
theorem B7347181 : Blo 1431535 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B4832297 : Blo 1431535 4832297 := bstep (se 2 (by rfl) ⟨1812111, by rfl⟩ : syracuseStep 4832297 = 3624223) B3624223
theorem B1432623 : Blo 1431535 1432623 := bstep (se 1 (by rfl) ⟨1074467, by rfl⟩ : syracuseStep 1432623 = 2148935) B2148935
theorem B1432647 : Blo 1431535 1432647 := bstep (se 1 (by rfl) ⟨1074485, by rfl⟩ : syracuseStep 1432647 = 2148971) B2148971
theorem B12237905 : Blo 1431535 12237905 := bstep (se 2 (by rfl) ⟨4589214, by rfl⟩ : syracuseStep 12237905 = 9178429) B9178429
theorem B2415737 : Blo 1431535 2415737 := bstep (se 2 (by rfl) ⟨905901, by rfl⟩ : syracuseStep 2415737 = 1811803) B1811803
theorem B27548819 : Blo 1431535 27548819 := bstep (se 1 (by rfl) ⟨20661614, by rfl⟩ : syracuseStep 27548819 = 41323229) B41323229
theorem B6880439 : Blo 1431535 6880439 := bstep (se 1 (by rfl) ⟨5160329, by rfl⟩ : syracuseStep 6880439 = 10320659) B10320659
theorem B1432799 : Blo 1431535 1432799 := bstep (se 1 (by rfl) ⟨1074599, by rfl⟩ : syracuseStep 1432799 = 2149199) B2149199
theorem B2579791 : Blo 1431535 2579791 := bstep (se 1 (by rfl) ⟨1934843, by rfl⟩ : syracuseStep 2579791 = 3869687) B3869687
theorem B1433063 : Blo 1431535 1433063 := bstep (se 1 (by rfl) ⟨1074797, by rfl⟩ : syracuseStep 1433063 = 2149595) B2149595
theorem B9805321 : Blo 1431535 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B58801733 : Blo 1431535 58801733 := bstep (se 4 (by rfl) ⟨5512662, by rfl⟩ : syracuseStep 58801733 = 11025325) B11025325
theorem B2358857 : Blo 1431535 2358857 := bstep (se 2 (by rfl) ⟨884571, by rfl⟩ : syracuseStep 2358857 = 1769143) B1769143
theorem B1433179 : Blo 1431535 1433179 := bstep (se 1 (by rfl) ⟨1074884, by rfl⟩ : syracuseStep 1433179 = 2149769) B2149769
theorem B19881745 : Blo 1431535 19881745 := bstep (se 2 (by rfl) ⟨7455654, by rfl⟩ : syracuseStep 19881745 = 14911309) B14911309
theorem B1433415 : Blo 1431535 1433415 := bstep (se 1 (by rfl) ⟨1075061, by rfl⟩ : syracuseStep 1433415 = 2150123) B2150123
theorem B2178937 : Blo 1431535 2178937 := bstep (se 2 (by rfl) ⟨817101, by rfl⟩ : syracuseStep 2178937 = 1634203) B1634203
theorem B5161195 : Blo 1431535 5161195 := bstep (se 1 (by rfl) ⟨3870896, by rfl⟩ : syracuseStep 5161195 = 7741793) B7741793
theorem B6119705 : Blo 1431535 6119705 := bstep (se 2 (by rfl) ⟨2294889, by rfl⟩ : syracuseStep 6119705 = 4589779) B4589779
theorem B24797497 : Blo 1431535 24797497 := bstep (se 2 (by rfl) ⟨9299061, by rfl⟩ : syracuseStep 24797497 = 18598123) B18598123
theorem B8159561 : Blo 1431535 8159561 := bstep (se 2 (by rfl) ⟨3059835, by rfl⟩ : syracuseStep 8159561 = 6119671) B6119671
theorem B4899325 : Blo 1431535 4899325 := bstep (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) B1837247
theorem B78439063 : Blo 1431535 78439063 := bstep (se 1 (by rfl) ⟨58829297, by rfl⟩ : syracuseStep 78439063 = 117658595) B117658595
theorem B8160061 : Blo 1431535 8160061 := bstep (se 3 (by rfl) ⟨1530011, by rfl⟩ : syracuseStep 8160061 = 3060023) B3060023
theorem B2147519 : Blo 1431535 2147519 := bstep (se 1 (by rfl) ⟨1610639, by rfl⟩ : syracuseStep 2147519 = 3221279) B3221279
theorem B13075663 : Blo 1431535 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B2147663 : Blo 1431535 2147663 := bstep (se 1 (by rfl) ⟨1610747, by rfl⟩ : syracuseStep 2147663 = 3221495) B3221495
theorem B2147753 : Blo 1431535 2147753 := bstep (se 2 (by rfl) ⟨805407, by rfl⟩ : syracuseStep 2147753 = 1610815) B1610815
theorem B4081079 : Blo 1431535 4081079 := bstep (se 1 (by rfl) ⟨3060809, by rfl⟩ : syracuseStep 4081079 = 6121619) B6121619
theorem B2418167 : Blo 1431535 2418167 := bstep (se 1 (by rfl) ⟨1813625, by rfl⟩ : syracuseStep 2418167 = 3627251) B3627251
theorem B2147903 : Blo 1431535 2147903 := bstep (se 1 (by rfl) ⟨1610927, by rfl⟩ : syracuseStep 2147903 = 3221855) B3221855
theorem B3221063 : Blo 1431535 3221063 := bstep (se 1 (by rfl) ⟨2415797, by rfl⟩ : syracuseStep 3221063 = 4831595) B4831595
theorem B6882899 : Blo 1431535 6882899 := bstep (se 1 (by rfl) ⟨5162174, by rfl⟩ : syracuseStep 6882899 = 10324349) B10324349
theorem B2147945 : Blo 1431535 2147945 := bstep (se 2 (by rfl) ⟨805479, by rfl⟩ : syracuseStep 2147945 = 1610959) B1610959
theorem B3221243 : Blo 1431535 3221243 := bstep (se 1 (by rfl) ⟨2415932, by rfl⟩ : syracuseStep 3221243 = 4831865) B4831865
theorem B10323719 : Blo 1431535 10323719 := bstep (se 1 (by rfl) ⟨7742789, by rfl⟩ : syracuseStep 10323719 = 15485579) B15485579
theorem B4589369 : Blo 1431535 4589369 := bstep (se 2 (by rfl) ⟨1721013, by rfl⟩ : syracuseStep 4589369 = 3442027) B3442027
theorem B6121277 : Blo 1431535 6121277 := bstep (se 3 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 6121277 = 2295479) B2295479
theorem B5441377 : Blo 1431535 5441377 := bstep (se 2 (by rfl) ⟨2040516, by rfl⟩ : syracuseStep 5441377 = 4081033) B4081033
theorem B3057563 : Blo 1431535 3057563 := bstep (se 1 (by rfl) ⟨2293172, by rfl⟩ : syracuseStep 3057563 = 4586345) B4586345
theorem B36702233 : Blo 1431535 36702233 := bstep (se 2 (by rfl) ⟨13763337, by rfl⟩ : syracuseStep 36702233 = 27526675) B27526675
theorem B3221531 : Blo 1431535 3221531 := bstep (se 1 (by rfl) ⟨2416148, by rfl⟩ : syracuseStep 3221531 = 4832297) B4832297
theorem B2148383 : Blo 1431535 2148383 := bstep (se 1 (by rfl) ⟨1611287, by rfl⟩ : syracuseStep 2148383 = 3222575) B3222575
theorem B4835483 : Blo 1431535 4835483 := bstep (se 1 (by rfl) ⟨3626612, by rfl⟩ : syracuseStep 4835483 = 7253225) B7253225
theorem B8153297 : Blo 1431535 8153297 := bstep (se 2 (by rfl) ⟨3057486, by rfl⟩ : syracuseStep 8153297 = 6114973) B6114973
theorem B2148575 : Blo 1431535 2148575 := bstep (se 1 (by rfl) ⟨1611431, by rfl⟩ : syracuseStep 2148575 = 3222863) B3222863
theorem B1935643 : Blo 1431535 1935643 := bstep (se 1 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 1935643 = 2903465) B2903465
theorem B2148635 : Blo 1431535 2148635 := bstep (se 1 (by rfl) ⟨1611476, by rfl⟩ : syracuseStep 2148635 = 3222953) B3222953
theorem B39201155 : Blo 1431535 39201155 := bstep (se 1 (by rfl) ⟨29400866, by rfl⟩ : syracuseStep 39201155 = 58801733) B58801733
theorem B4835753 : Blo 1431535 4835753 := bstep (se 2 (by rfl) ⟨1813407, by rfl⟩ : syracuseStep 4835753 = 3626815) B3626815
theorem B2148959 : Blo 1431535 2148959 := bstep (se 1 (by rfl) ⟨1611719, by rfl⟩ : syracuseStep 2148959 = 3223439) B3223439
theorem B2149241 : Blo 1431535 2149241 := bstep (se 2 (by rfl) ⟨805965, by rfl⟩ : syracuseStep 2149241 = 1611931) B1611931
theorem B2149289 : Blo 1431535 2149289 := bstep (se 2 (by rfl) ⟨805983, by rfl⟩ : syracuseStep 2149289 = 1611967) B1611967
theorem B13765571 : Blo 1431535 13765571 := bstep (se 1 (by rfl) ⟨10324178, by rfl⟩ : syracuseStep 13765571 = 20648357) B20648357
theorem B4836347 : Blo 1431535 4836347 := bstep (se 1 (by rfl) ⟨3627260, by rfl⟩ : syracuseStep 4836347 = 7254521) B7254521
theorem B424143893 : Blo 1431535 424143893 := bstep (se 6 (by rfl) ⟨9940872, by rfl⟩ : syracuseStep 424143893 = 19881745) B19881745
theorem B2149439 : Blo 1431535 2149439 := bstep (se 1 (by rfl) ⟨1612079, by rfl⟩ : syracuseStep 2149439 = 3224159) B3224159
theorem B5442623 : Blo 1431535 5442623 := bstep (se 1 (by rfl) ⟨4081967, by rfl⟩ : syracuseStep 5442623 = 8163935) B8163935
theorem B3058759 : Blo 1431535 3058759 := bstep (se 1 (by rfl) ⟨2294069, by rfl⟩ : syracuseStep 3058759 = 4588139) B4588139
theorem B26152145 : Blo 1431535 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B9940211 : Blo 1431535 9940211 := bstep (se 1 (by rfl) ⟨7455158, by rfl⟩ : syracuseStep 9940211 = 14910317) B14910317
theorem B13766071 : Blo 1431535 13766071 := bstep (se 1 (by rfl) ⟨10324553, by rfl⟩ : syracuseStep 13766071 = 20649107) B20649107
theorem B3223007 : Blo 1431535 3223007 := bstep (se 1 (by rfl) ⟨2417255, by rfl⟩ : syracuseStep 3223007 = 4834511) B4834511
theorem B2149991 : Blo 1431535 2149991 := bstep (se 1 (by rfl) ⟨1612493, by rfl⟩ : syracuseStep 2149991 = 3224987) B3224987
theorem B8162977 : Blo 1431535 8162977 := bstep (se 2 (by rfl) ⟨3061116, by rfl⟩ : syracuseStep 8162977 = 6122233) B6122233
theorem B3223223 : Blo 1431535 3223223 := bstep (se 1 (by rfl) ⟨2417417, by rfl⟩ : syracuseStep 3223223 = 4834835) B4834835
theorem B19591055 : Blo 1431535 19591055 := bstep (se 1 (by rfl) ⟨14693291, by rfl⟩ : syracuseStep 19591055 = 29386583) B29386583
theorem B6115571 : Blo 1431535 6115571 := bstep (se 1 (by rfl) ⟨4586678, by rfl⟩ : syracuseStep 6115571 = 9173357) B9173357
theorem B3224015 : Blo 1431535 3224015 := bstep (se 1 (by rfl) ⟨2418011, by rfl⟩ : syracuseStep 3224015 = 4836023) B4836023
theorem B8155687 : Blo 1431535 8155687 := bstep (se 1 (by rfl) ⟨6116765, by rfl⟩ : syracuseStep 8155687 = 12233531) B12233531
theorem B1610491 : Blo 1431535 1610491 := bstep (se 1 (by rfl) ⟨1207868, by rfl⟩ : syracuseStep 1610491 = 2415737) B2415737
theorem B40809419 : Blo 1431535 40809419 := bstep (se 1 (by rfl) ⟨30607064, by rfl⟩ : syracuseStep 40809419 = 61214129) B61214129
theorem B3224681 : Blo 1431535 3224681 := bstep (se 2 (by rfl) ⟨1209255, by rfl⟩ : syracuseStep 3224681 = 2418511) B2418511
theorem B2905249 : Blo 1431535 2905249 := bstep (se 2 (by rfl) ⟨1089468, by rfl⟩ : syracuseStep 2905249 = 2178937) B2178937
theorem B12236129 : Blo 1431535 12236129 := bstep (se 2 (by rfl) ⟨4588548, by rfl⟩ : syracuseStep 12236129 = 9177097) B9177097
theorem B5166443 : Blo 1431535 5166443 := bstep (se 1 (by rfl) ⟨3874832, by rfl⟩ : syracuseStep 5166443 = 7749665) B7749665
theorem B5436791 : Blo 1431535 5436791 := bstep (se 1 (by rfl) ⟨4077593, by rfl⟩ : syracuseStep 5436791 = 8155187) B8155187
theorem B1611247 : Blo 1431535 1611247 := bstep (se 1 (by rfl) ⟨1208435, by rfl⟩ : syracuseStep 1611247 = 2416871) B2416871
theorem B92935745 : Blo 1431535 92935745 := bstep (se 2 (by rfl) ⟨34850904, by rfl⟩ : syracuseStep 92935745 = 69701809) B69701809
theorem B1611355 : Blo 1431535 1611355 := bstep (se 1 (by rfl) ⟨1208516, by rfl⟩ : syracuseStep 1611355 = 2417033) B2417033
theorem B3626633 : Blo 1431535 3626633 := bstep (se 2 (by rfl) ⟨1359987, by rfl⟩ : syracuseStep 3626633 = 2719975) B2719975
theorem B3872411 : Blo 1431535 3872411 := bstep (se 1 (by rfl) ⟨2904308, by rfl⟩ : syracuseStep 3872411 = 5808617) B5808617
theorem B3225311 : Blo 1431535 3225311 := bstep (se 1 (by rfl) ⟨2418983, by rfl⟩ : syracuseStep 3225311 = 4837967) B4837967
theorem B6133567 : Blo 1431535 6133567 := bstep (se 1 (by rfl) ⟨4600175, by rfl⟩ : syracuseStep 6133567 = 9200351) B9200351
theorem B1611643 : Blo 1431535 1611643 := bstep (se 1 (by rfl) ⟨1208732, by rfl⟩ : syracuseStep 1611643 = 2417465) B2417465
theorem B1611679 : Blo 1431535 1611679 := bstep (se 1 (by rfl) ⟨1208759, by rfl⟩ : syracuseStep 1611679 = 2417519) B2417519
theorem B3626977 : Blo 1431535 3626977 := bstep (se 2 (by rfl) ⟨1360116, by rfl⟩ : syracuseStep 3626977 = 2720233) B2720233
theorem B1431623 : Blo 1431535 1431623 := bstep (se 1 (by rfl) ⟨1073717, by rfl⟩ : syracuseStep 1431623 = 2147435) B2147435
theorem B2717887 : Blo 1431535 2717887 := bstep (se 1 (by rfl) ⟨2038415, by rfl⟩ : syracuseStep 2717887 = 4076831) B4076831
theorem B1431783 : Blo 1431535 1431783 := bstep (se 1 (by rfl) ⟨1073837, by rfl⟩ : syracuseStep 1431783 = 2147675) B2147675
theorem B1431967 : Blo 1431535 1431967 := bstep (se 1 (by rfl) ⟨1073975, by rfl⟩ : syracuseStep 1431967 = 2147951) B2147951
theorem B1432015 : Blo 1431535 1432015 := bstep (se 1 (by rfl) ⟨1074011, by rfl⟩ : syracuseStep 1432015 = 2148023) B2148023
theorem B1432039 : Blo 1431535 1432039 := bstep (se 1 (by rfl) ⟨1074029, by rfl⟩ : syracuseStep 1432039 = 2148059) B2148059
theorem B44726843 : Blo 1431535 44726843 := bstep (se 1 (by rfl) ⟨33545132, by rfl⟩ : syracuseStep 44726843 = 67090265) B67090265
theorem B1432155 : Blo 1431535 1432155 := bstep (se 1 (by rfl) ⟨1074116, by rfl⟩ : syracuseStep 1432155 = 2148233) B2148233
theorem B38230625 : Blo 1431535 38230625 := bstep (se 2 (by rfl) ⟨14336484, by rfl⟩ : syracuseStep 38230625 = 28672969) B28672969
theorem B9796241 : Blo 1431535 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B1432223 : Blo 1431535 1432223 := bstep (se 1 (by rfl) ⟨1074167, by rfl⟩ : syracuseStep 1432223 = 2148335) B2148335
theorem B8264375 : Blo 1431535 8264375 := bstep (se 1 (by rfl) ⟨6198281, by rfl⟩ : syracuseStep 8264375 = 12396563) B12396563
theorem B5806835 : Blo 1431535 5806835 := bstep (se 1 (by rfl) ⟨4355126, by rfl⟩ : syracuseStep 5806835 = 8710253) B8710253
theorem B13769489 : Blo 1431535 13769489 := bstep (se 2 (by rfl) ⟨5163558, by rfl⟩ : syracuseStep 13769489 = 10327117) B10327117
theorem B19594007 : Blo 1431535 19594007 := bstep (se 1 (by rfl) ⟨14695505, by rfl⟩ : syracuseStep 19594007 = 29391011) B29391011
theorem B1432391 : Blo 1431535 1432391 := bstep (se 1 (by rfl) ⟨1074293, by rfl⟩ : syracuseStep 1432391 = 2148587) B2148587
theorem B1530695 : Blo 1431535 1530695 := bstep (se 1 (by rfl) ⟨1148021, by rfl⟩ : syracuseStep 1530695 = 2296043) B2296043
theorem B1612615 : Blo 1431535 1612615 := bstep (se 1 (by rfl) ⟨1209461, by rfl⟩ : syracuseStep 1612615 = 2418923) B2418923
theorem B1432431 : Blo 1431535 1432431 := bstep (se 1 (by rfl) ⟨1074323, by rfl⟩ : syracuseStep 1432431 = 2148647) B2148647
theorem B1432487 : Blo 1431535 1432487 := bstep (se 1 (by rfl) ⟨1074365, by rfl⟩ : syracuseStep 1432487 = 2148731) B2148731
theorem B11623427 : Blo 1431535 11623427 := bstep (se 1 (by rfl) ⟨8717570, by rfl⟩ : syracuseStep 11623427 = 17435141) B17435141
theorem B13761575 : Blo 1431535 13761575 := bstep (se 1 (by rfl) ⟨10321181, by rfl⟩ : syracuseStep 13761575 = 20642363) B20642363
theorem B3267631 : Blo 1431535 3267631 := bstep (se 1 (by rfl) ⟨2450723, by rfl⟩ : syracuseStep 3267631 = 4901447) B4901447
theorem B1432667 : Blo 1431535 1432667 := bstep (se 1 (by rfl) ⟨1074500, by rfl⟩ : syracuseStep 1432667 = 2149001) B2149001
theorem B3439721 : Blo 1431535 3439721 := bstep (se 2 (by rfl) ⟨1289895, by rfl⟩ : syracuseStep 3439721 = 2579791) B2579791
theorem B1432783 : Blo 1431535 1432783 := bstep (se 1 (by rfl) ⟨1074587, by rfl⟩ : syracuseStep 1432783 = 2149175) B2149175
theorem B1432807 : Blo 1431535 1432807 := bstep (se 1 (by rfl) ⟨1074605, by rfl⟩ : syracuseStep 1432807 = 2149211) B2149211
theorem B6888743 : Blo 1431535 6888743 := bstep (se 1 (by rfl) ⟨5166557, by rfl⟩ : syracuseStep 6888743 = 10333115) B10333115
theorem B1432903 : Blo 1431535 1432903 := bstep (se 1 (by rfl) ⟨1074677, by rfl⟩ : syracuseStep 1432903 = 2149355) B2149355
theorem B13073761 : Blo 1431535 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B8158603 : Blo 1431535 8158603 := bstep (se 1 (by rfl) ⟨6118952, by rfl⟩ : syracuseStep 8158603 = 12237905) B12237905
theorem B18365879 : Blo 1431535 18365879 := bstep (se 1 (by rfl) ⟨13774409, by rfl⟩ : syracuseStep 18365879 = 27548819) B27548819
theorem B4586959 : Blo 1431535 4586959 := bstep (se 1 (by rfl) ⟨3440219, by rfl⟩ : syracuseStep 4586959 = 6880439) B6880439
theorem B1433039 : Blo 1431535 1433039 := bstep (se 1 (by rfl) ⟨1074779, by rfl⟩ : syracuseStep 1433039 = 2149559) B2149559
theorem B1433199 : Blo 1431535 1433199 := bstep (se 1 (by rfl) ⟨1074899, by rfl⟩ : syracuseStep 1433199 = 2149799) B2149799
theorem B1433255 : Blo 1431535 1433255 := bstep (se 1 (by rfl) ⟨1074941, by rfl⟩ : syracuseStep 1433255 = 2149883) B2149883
theorem B1572571 : Blo 1431535 1572571 := bstep (se 1 (by rfl) ⟨1179428, by rfl⟩ : syracuseStep 1572571 = 2358857) B2358857
theorem B1433319 : Blo 1431535 1433319 := bstep (se 1 (by rfl) ⟨1074989, by rfl⟩ : syracuseStep 1433319 = 2149979) B2149979
theorem B7249661 : Blo 1431535 7249661 := bstep (se 3 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 7249661 = 2718623) B2718623
theorem B1433375 : Blo 1431535 1433375 := bstep (se 1 (by rfl) ⟨1075031, by rfl⟩ : syracuseStep 1433375 = 2150063) B2150063
theorem B1433455 : Blo 1431535 1433455 := bstep (se 1 (by rfl) ⟨1075091, by rfl⟩ : syracuseStep 1433455 = 2150183) B2150183
theorem B1433511 : Blo 1431535 1433511 := bstep (se 1 (by rfl) ⟨1075133, by rfl⟩ : syracuseStep 1433511 = 2150267) B2150267
theorem B13770719 : Blo 1431535 13770719 := bstep (se 1 (by rfl) ⟨10328039, by rfl⟩ : syracuseStep 13770719 = 20656079) B20656079
theorem B4079803 : Blo 1431535 4079803 := bstep (se 1 (by rfl) ⟨3059852, by rfl⟩ : syracuseStep 4079803 = 6119705) B6119705
theorem B5439707 : Blo 1431535 5439707 := bstep (se 1 (by rfl) ⟨4079780, by rfl⟩ : syracuseStep 5439707 = 8159561) B8159561
theorem B6881593 : Blo 1431535 6881593 := bstep (se 2 (by rfl) ⟨2580597, by rfl⟩ : syracuseStep 6881593 = 5161195) B5161195
theorem B2580857 : Blo 1431535 2580857 := bstep (se 2 (by rfl) ⟨967821, by rfl⟩ : syracuseStep 2580857 = 1935643) B1935643
theorem B33063329 : Blo 1431535 33063329 := bstep (se 2 (by rfl) ⟨12398748, by rfl⟩ : syracuseStep 33063329 = 24797497) B24797497
theorem B27206279 : Blo 1431535 27206279 := bstep (se 1 (by rfl) ⟨20404709, by rfl⟩ : syracuseStep 27206279 = 40809419) B40809419
theorem B2720719 : Blo 1431535 2720719 := bstep (se 1 (by rfl) ⟨2040539, by rfl⟩ : syracuseStep 2720719 = 4081079) B4081079
theorem B2147321 : Blo 1431535 2147321 := bstep (se 2 (by rfl) ⟨805245, by rfl⟩ : syracuseStep 2147321 = 1610491) B1610491
theorem B61957163 : Blo 1431535 61957163 := bstep (se 1 (by rfl) ⟨46467872, by rfl⟩ : syracuseStep 61957163 = 92935745) B92935745
theorem B2147375 : Blo 1431535 2147375 := bstep (se 1 (by rfl) ⟨1610531, by rfl⟩ : syracuseStep 2147375 = 3221063) B3221063
theorem B10880081 : Blo 1431535 10880081 := bstep (se 2 (by rfl) ⟨4080030, by rfl⟩ : syracuseStep 10880081 = 8160061) B8160061
theorem B2417755 : Blo 1431535 2417755 := bstep (se 1 (by rfl) ⟨1813316, by rfl⟩ : syracuseStep 2417755 = 3626633) B3626633
theorem B2581607 : Blo 1431535 2581607 := bstep (se 1 (by rfl) ⟨1936205, by rfl⟩ : syracuseStep 2581607 = 3872411) B3872411
theorem B2147495 : Blo 1431535 2147495 := bstep (se 1 (by rfl) ⟨1610621, by rfl⟩ : syracuseStep 2147495 = 3221243) B3221243
theorem B6882479 : Blo 1431535 6882479 := bstep (se 1 (by rfl) ⟨5161859, by rfl⟩ : syracuseStep 6882479 = 10323719) B10323719
theorem B4080851 : Blo 1431535 4080851 := bstep (se 1 (by rfl) ⟨3060638, by rfl⟩ : syracuseStep 4080851 = 6121277) B6121277
theorem B2147687 : Blo 1431535 2147687 := bstep (se 1 (by rfl) ⟨1610765, by rfl⟩ : syracuseStep 2147687 = 3221531) B3221531
theorem B26134103 : Blo 1431535 26134103 := bstep (se 1 (by rfl) ⟨19600577, by rfl⟩ : syracuseStep 26134103 = 39201155) B39201155
theorem B17434217 : Blo 1431535 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B25487083 : Blo 1431535 25487083 := bstep (se 1 (by rfl) ⟨19115312, by rfl⟩ : syracuseStep 25487083 = 38230625) B38230625
theorem B6530827 : Blo 1431535 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B9177047 : Blo 1431535 9177047 := bstep (se 1 (by rfl) ⟨6882785, by rfl⟩ : syracuseStep 9177047 = 13765571) B13765571
theorem B2148329 : Blo 1431535 2148329 := bstep (se 2 (by rfl) ⟨805623, by rfl⟩ : syracuseStep 2148329 = 1611247) B1611247
theorem B2148473 : Blo 1431535 2148473 := bstep (se 2 (by rfl) ⟨805677, by rfl⟩ : syracuseStep 2148473 = 1611355) B1611355
theorem B17434763 : Blo 1431535 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B4081853 : Blo 1431535 4081853 := bstep (se 3 (by rfl) ⟨765347, by rfl⟩ : syracuseStep 4081853 = 1530695) B1530695
theorem B2148671 : Blo 1431535 2148671 := bstep (se 1 (by rfl) ⟨1611503, by rfl⟩ : syracuseStep 2148671 = 3223007) B3223007
theorem B24463781 : Blo 1431535 24463781 := bstep (se 4 (by rfl) ⟨2293479, by rfl⟩ : syracuseStep 24463781 = 4586959) B4586959
theorem B8178089 : Blo 1431535 8178089 := bstep (se 2 (by rfl) ⟨3066783, by rfl⟩ : syracuseStep 8178089 = 6133567) B6133567
theorem B2148815 : Blo 1431535 2148815 := bstep (se 1 (by rfl) ⟨1611611, by rfl⟩ : syracuseStep 2148815 = 3223223) B3223223
theorem B2148857 : Blo 1431535 2148857 := bstep (se 2 (by rfl) ⟨805821, by rfl⟩ : syracuseStep 2148857 = 1611643) B1611643
theorem B2148905 : Blo 1431535 2148905 := bstep (se 2 (by rfl) ⟨805839, by rfl⟩ : syracuseStep 2148905 = 1611679) B1611679
theorem B13060703 : Blo 1431535 13060703 := bstep (se 1 (by rfl) ⟨9795527, by rfl⟩ : syracuseStep 13060703 = 19591055) B19591055
theorem B4835969 : Blo 1431535 4835969 := bstep (se 2 (by rfl) ⟨1813488, by rfl⟩ : syracuseStep 4835969 = 3626977) B3626977
theorem B3623849 : Blo 1431535 3623849 := bstep (se 2 (by rfl) ⟨1358943, by rfl⟩ : syracuseStep 3623849 = 2717887) B2717887
theorem B2149343 : Blo 1431535 2149343 := bstep (se 1 (by rfl) ⟨1612007, by rfl⟩ : syracuseStep 2149343 = 3224015) B3224015
theorem B6532433 : Blo 1431535 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B10874249 : Blo 1431535 10874249 := bstep (se 2 (by rfl) ⟨4077843, by rfl⟩ : syracuseStep 10874249 = 8155687) B8155687
theorem B2149787 : Blo 1431535 2149787 := bstep (se 1 (by rfl) ⟨1612340, by rfl⟩ : syracuseStep 2149787 = 3224681) B3224681
theorem B3444295 : Blo 1431535 3444295 := bstep (se 1 (by rfl) ⟨2583221, by rfl⟩ : syracuseStep 3444295 = 5166443) B5166443
theorem B3624527 : Blo 1431535 3624527 := bstep (se 1 (by rfl) ⟨2718395, by rfl⟩ : syracuseStep 3624527 = 5436791) B5436791
theorem B2150153 : Blo 1431535 2150153 := bstep (se 2 (by rfl) ⟨806307, by rfl⟩ : syracuseStep 2150153 = 1612615) B1612615
theorem B2150207 : Blo 1431535 2150207 := bstep (se 1 (by rfl) ⟨1612655, by rfl⟩ : syracuseStep 2150207 = 3225311) B3225311
theorem B3059579 : Blo 1431535 3059579 := bstep (se 1 (by rfl) ⟨2294684, by rfl⟩ : syracuseStep 3059579 = 4589369) B4589369
theorem B3223655 : Blo 1431535 3223655 := bstep (se 1 (by rfl) ⟨2417741, by rfl⟩ : syracuseStep 3223655 = 4835483) B4835483
theorem B5435531 : Blo 1431535 5435531 := bstep (se 1 (by rfl) ⟨4076648, by rfl⟩ : syracuseStep 5435531 = 8153297) B8153297
theorem B18354397 : Blo 1431535 18354397 := bstep (se 3 (by rfl) ⟨3441449, by rfl⟩ : syracuseStep 18354397 = 6882899) B6882899
theorem B3223835 : Blo 1431535 3223835 := bstep (se 1 (by rfl) ⟨2417876, by rfl⟩ : syracuseStep 3223835 = 4835753) B4835753
theorem B5509583 : Blo 1431535 5509583 := bstep (se 1 (by rfl) ⟨4132187, by rfl⟩ : syracuseStep 5509583 = 8264375) B8264375
theorem B3871223 : Blo 1431535 3871223 := bstep (se 1 (by rfl) ⟨2903417, by rfl⟩ : syracuseStep 3871223 = 5806835) B5806835
theorem B9179659 : Blo 1431535 9179659 := bstep (se 1 (by rfl) ⟨6884744, by rfl⟩ : syracuseStep 9179659 = 13769489) B13769489
theorem B13062671 : Blo 1431535 13062671 := bstep (se 1 (by rfl) ⟨9797003, by rfl⟩ : syracuseStep 13062671 = 19594007) B19594007
theorem B18354761 : Blo 1431535 18354761 := bstep (se 2 (by rfl) ⟨6883035, by rfl⟩ : syracuseStep 18354761 = 13766071) B13766071
theorem B3224231 : Blo 1431535 3224231 := bstep (se 1 (by rfl) ⟨2418173, by rfl⟩ : syracuseStep 3224231 = 4836347) B4836347
theorem B4592495 : Blo 1431535 4592495 := bstep (se 1 (by rfl) ⟨3444371, by rfl⟩ : syracuseStep 4592495 = 6888743) B6888743
theorem B10883969 : Blo 1431535 10883969 := bstep (se 2 (by rfl) ⟨4081488, by rfl⟩ : syracuseStep 10883969 = 8162977) B8162977
theorem B12243919 : Blo 1431535 12243919 := bstep (se 1 (by rfl) ⟨9182939, by rfl⟩ : syracuseStep 12243919 = 18365879) B18365879
theorem B7255169 : Blo 1431535 7255169 := bstep (se 2 (by rfl) ⟨2720688, by rfl⟩ : syracuseStep 7255169 = 5441377) B5441377
theorem B9180479 : Blo 1431535 9180479 := bstep (se 1 (by rfl) ⟨6885359, by rfl⟩ : syracuseStep 9180479 = 13770719) B13770719
theorem B4077047 : Blo 1431535 4077047 := bstep (se 1 (by rfl) ⟨3057785, by rfl⟩ : syracuseStep 4077047 = 6115571) B6115571
theorem B1431679 : Blo 1431535 1431679 := bstep (se 1 (by rfl) ⟨1073759, by rfl⟩ : syracuseStep 1431679 = 2147519) B2147519
theorem B104585417 : Blo 1431535 104585417 := bstep (se 2 (by rfl) ⟨39219531, by rfl⟩ : syracuseStep 104585417 = 78439063) B78439063
theorem B1431775 : Blo 1431535 1431775 := bstep (se 1 (by rfl) ⟨1073831, by rfl⟩ : syracuseStep 1431775 = 2147663) B2147663
theorem B8157419 : Blo 1431535 8157419 := bstep (se 1 (by rfl) ⟨6118064, by rfl⟩ : syracuseStep 8157419 = 12236129) B12236129
theorem B1431835 : Blo 1431535 1431835 := bstep (se 1 (by rfl) ⟨1073876, by rfl⟩ : syracuseStep 1431835 = 2147753) B2147753
theorem B1612111 : Blo 1431535 1612111 := bstep (se 1 (by rfl) ⟨1209083, by rfl⟩ : syracuseStep 1612111 = 2418167) B2418167
theorem B1431935 : Blo 1431535 1431935 := bstep (se 1 (by rfl) ⟨1073951, by rfl⟩ : syracuseStep 1431935 = 2147903) B2147903
theorem B1431963 : Blo 1431535 1431963 := bstep (se 1 (by rfl) ⟨1073972, by rfl⟩ : syracuseStep 1431963 = 2147945) B2147945
theorem B2038375 : Blo 1431535 2038375 := bstep (se 1 (by rfl) ⟨1528781, by rfl⟩ : syracuseStep 2038375 = 3057563) B3057563
theorem B24468155 : Blo 1431535 24468155 := bstep (se 1 (by rfl) ⟨18351116, by rfl⟩ : syracuseStep 24468155 = 36702233) B36702233
theorem B1432255 : Blo 1431535 1432255 := bstep (se 1 (by rfl) ⟨1074191, by rfl⟩ : syracuseStep 1432255 = 2148383) B2148383
theorem B4356841 : Blo 1431535 4356841 := bstep (se 2 (by rfl) ⟨1633815, by rfl⟩ : syracuseStep 4356841 = 3267631) B3267631
theorem B4078345 : Blo 1431535 4078345 := bstep (se 2 (by rfl) ⟨1529379, by rfl⟩ : syracuseStep 4078345 = 3058759) B3058759
theorem B1432383 : Blo 1431535 1432383 := bstep (se 1 (by rfl) ⟨1074287, by rfl⟩ : syracuseStep 1432383 = 2148575) B2148575
theorem B1432423 : Blo 1431535 1432423 := bstep (se 1 (by rfl) ⟨1074317, by rfl⟩ : syracuseStep 1432423 = 2148635) B2148635
theorem B3873665 : Blo 1431535 3873665 := bstep (se 2 (by rfl) ⟨1452624, by rfl⟩ : syracuseStep 3873665 = 2905249) B2905249
theorem B29817895 : Blo 1431535 29817895 := bstep (se 1 (by rfl) ⟨22363421, by rfl⟩ : syracuseStep 29817895 = 44726843) B44726843
theorem B1432639 : Blo 1431535 1432639 := bstep (se 1 (by rfl) ⟨1074479, by rfl⟩ : syracuseStep 1432639 = 2148959) B2148959
theorem B17431681 : Blo 1431535 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B10878137 : Blo 1431535 10878137 := bstep (se 2 (by rfl) ⟨4079301, by rfl⟩ : syracuseStep 10878137 = 8158603) B8158603
theorem B1432827 : Blo 1431535 1432827 := bstep (se 1 (by rfl) ⟨1074620, by rfl⟩ : syracuseStep 1432827 = 2149241) B2149241
theorem B1432859 : Blo 1431535 1432859 := bstep (se 1 (by rfl) ⟨1074644, by rfl⟩ : syracuseStep 1432859 = 2149289) B2149289
theorem B7748951 : Blo 1431535 7748951 := bstep (se 1 (by rfl) ⟨5811713, by rfl⟩ : syracuseStep 7748951 = 11623427) B11623427
theorem B282762595 : Blo 1431535 282762595 := bstep (se 1 (by rfl) ⟨212071946, by rfl⟩ : syracuseStep 282762595 = 424143893) B424143893
theorem B9174383 : Blo 1431535 9174383 := bstep (se 1 (by rfl) ⟨6880787, by rfl⟩ : syracuseStep 9174383 = 13761575) B13761575
theorem B1432959 : Blo 1431535 1432959 := bstep (se 1 (by rfl) ⟨1074719, by rfl⟩ : syracuseStep 1432959 = 2149439) B2149439
theorem B3628415 : Blo 1431535 3628415 := bstep (se 1 (by rfl) ⟨2721311, by rfl⟩ : syracuseStep 3628415 = 5442623) B5442623
theorem B2293147 : Blo 1431535 2293147 := bstep (se 1 (by rfl) ⟨1719860, by rfl⟩ : syracuseStep 2293147 = 3439721) B3439721
theorem B6626807 : Blo 1431535 6626807 := bstep (se 1 (by rfl) ⟨4970105, by rfl⟩ : syracuseStep 6626807 = 9940211) B9940211
theorem B2096761 : Blo 1431535 2096761 := bstep (se 2 (by rfl) ⟨786285, by rfl⟩ : syracuseStep 2096761 = 1572571) B1572571
theorem B1433327 : Blo 1431535 1433327 := bstep (se 1 (by rfl) ⟨1074995, by rfl⟩ : syracuseStep 1433327 = 2149991) B2149991
theorem B4833107 : Blo 1431535 4833107 := bstep (se 1 (by rfl) ⟨3624830, by rfl⟩ : syracuseStep 4833107 = 7249661) B7249661
theorem B5439737 : Blo 1431535 5439737 := bstep (se 2 (by rfl) ⟨2039901, by rfl⟩ : syracuseStep 5439737 = 4079803) B4079803
theorem B1720571 : Blo 1431535 1720571 := bstep (se 1 (by rfl) ⟨1290428, by rfl⟩ : syracuseStep 1720571 = 2580857) B2580857
theorem B2580815 : Blo 1431535 2580815 := bstep (se 1 (by rfl) ⟨1935611, by rfl⟩ : syracuseStep 2580815 = 3871223) B3871223
theorem B8708447 : Blo 1431535 8708447 := bstep (se 1 (by rfl) ⟨6531335, by rfl⟩ : syracuseStep 8708447 = 13062671) B13062671
theorem B9175457 : Blo 1431535 9175457 := bstep (se 2 (by rfl) ⟨3440796, by rfl⟩ : syracuseStep 9175457 = 6881593) B6881593
theorem B18137519 : Blo 1431535 18137519 := bstep (se 1 (by rfl) ⟨13603139, by rfl⟩ : syracuseStep 18137519 = 27206279) B27206279
theorem B10871333 : Blo 1431535 10871333 := bstep (se 4 (by rfl) ⟨1019187, by rfl⟩ : syracuseStep 10871333 = 2038375) B2038375
theorem B12239545 : Blo 1431535 12239545 := bstep (se 2 (by rfl) ⟨4589829, by rfl⟩ : syracuseStep 12239545 = 9179659) B9179659
theorem B41304775 : Blo 1431535 41304775 := bstep (se 1 (by rfl) ⟨30978581, by rfl⟩ : syracuseStep 41304775 = 61957163) B61957163
theorem B1721071 : Blo 1431535 1721071 := bstep (se 1 (by rfl) ⟨1290803, by rfl⟩ : syracuseStep 1721071 = 2581607) B2581607
theorem B4588319 : Blo 1431535 4588319 := bstep (se 1 (by rfl) ⟨3441239, by rfl⟩ : syracuseStep 4588319 = 6882479) B6882479
theorem B2720567 : Blo 1431535 2720567 := bstep (se 1 (by rfl) ⟨2040425, by rfl⟩ : syracuseStep 2720567 = 4080851) B4080851
theorem B5809121 : Blo 1431535 5809121 := bstep (se 2 (by rfl) ⟨2178420, by rfl⟩ : syracuseStep 5809121 = 4356841) B4356841
theorem B21808237 : Blo 1431535 21808237 := bstep (se 3 (by rfl) ⟨4089044, by rfl⟩ : syracuseStep 21808237 = 8178089) B8178089
theorem B39757193 : Blo 1431535 39757193 := bstep (se 2 (by rfl) ⟨14908947, by rfl⟩ : syracuseStep 39757193 = 29817895) B29817895
theorem B69723611 : Blo 1431535 69723611 := bstep (se 1 (by rfl) ⟨52292708, by rfl⟩ : syracuseStep 69723611 = 104585417) B104585417
theorem B23242241 : Blo 1431535 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B46491245 : Blo 1431535 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B16312103 : Blo 1431535 16312103 := bstep (se 1 (by rfl) ⟨12234077, by rfl⟩ : syracuseStep 16312103 = 24468155) B24468155
theorem B1508067173 : Blo 1431535 1508067173 := bstep (se 4 (by rfl) ⟨141381297, by rfl⟩ : syracuseStep 1508067173 = 282762595) B282762595
theorem B3057529 : Blo 1431535 3057529 := bstep (se 2 (by rfl) ⟨1146573, by rfl⟩ : syracuseStep 3057529 = 2293147) B2293147
theorem B2582443 : Blo 1431535 2582443 := bstep (se 1 (by rfl) ⟨1936832, by rfl⟩ : syracuseStep 2582443 = 3873665) B3873665
theorem B7252091 : Blo 1431535 7252091 := bstep (se 1 (by rfl) ⟨5439068, by rfl⟩ : syracuseStep 7252091 = 10878137) B10878137
theorem B2795681 : Blo 1431535 2795681 := bstep (se 2 (by rfl) ⟨1048380, by rfl⟩ : syracuseStep 2795681 = 2096761) B2096761
theorem B2418943 : Blo 1431535 2418943 := bstep (se 1 (by rfl) ⟨1814207, by rfl⟩ : syracuseStep 2418943 = 3628415) B3628415
theorem B33982777 : Blo 1431535 33982777 := bstep (se 2 (by rfl) ⟨12743541, by rfl⟩ : syracuseStep 33982777 = 25487083) B25487083
theorem B4417871 : Blo 1431535 4417871 := bstep (se 1 (by rfl) ⟨3313403, by rfl⟩ : syracuseStep 4417871 = 6626807) B6626807
theorem B3222071 : Blo 1431535 3222071 := bstep (se 1 (by rfl) ⟨2416553, by rfl⟩ : syracuseStep 3222071 = 4833107) B4833107
theorem B2149103 : Blo 1431535 2149103 := bstep (se 1 (by rfl) ⟨1611827, by rfl⟩ : syracuseStep 2149103 = 3223655) B3223655
theorem B3623687 : Blo 1431535 3623687 := bstep (se 1 (by rfl) ⟨2717765, by rfl⟩ : syracuseStep 3623687 = 5435531) B5435531
theorem B2149223 : Blo 1431535 2149223 := bstep (se 1 (by rfl) ⟨1611917, by rfl⟩ : syracuseStep 2149223 = 3223835) B3223835
theorem B24472529 : Blo 1431535 24472529 := bstep (se 2 (by rfl) ⟨9177198, by rfl⟩ : syracuseStep 24472529 = 18354397) B18354397
theorem B3673055 : Blo 1431535 3673055 := bstep (se 1 (by rfl) ⟨2754791, by rfl⟩ : syracuseStep 3673055 = 5509583) B5509583
theorem B2149481 : Blo 1431535 2149481 := bstep (se 2 (by rfl) ⟨806055, by rfl⟩ : syracuseStep 2149481 = 1612111) B1612111
theorem B2149487 : Blo 1431535 2149487 := bstep (se 1 (by rfl) ⟨1612115, by rfl⟩ : syracuseStep 2149487 = 3224231) B3224231
theorem B7253387 : Blo 1431535 7253387 := bstep (se 1 (by rfl) ⟨5440040, by rfl⟩ : syracuseStep 7253387 = 10880081) B10880081
theorem B4836779 : Blo 1431535 4836779 := bstep (se 1 (by rfl) ⟨3627584, by rfl⟩ : syracuseStep 4836779 = 7255169) B7255169
theorem B24481277 : Blo 1431535 24481277 := bstep (se 3 (by rfl) ⟨4590239, by rfl⟩ : syracuseStep 24481277 = 9180479) B9180479
theorem B20663869 : Blo 1431535 20663869 := bstep (se 3 (by rfl) ⟨3874475, by rfl⟩ : syracuseStep 20663869 = 7748951) B7748951
theorem B3223673 : Blo 1431535 3223673 := bstep (se 2 (by rfl) ⟨1208877, by rfl⟩ : syracuseStep 3223673 = 2417755) B2417755
theorem B3223979 : Blo 1431535 3223979 := bstep (se 1 (by rfl) ⟨2417984, by rfl⟩ : syracuseStep 3223979 = 4835969) B4835969
theorem B4592393 : Blo 1431535 4592393 := bstep (se 2 (by rfl) ⟨1722147, by rfl⟩ : syracuseStep 4592393 = 3444295) B3444295
theorem B4354955 : Blo 1431535 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B6116255 : Blo 1431535 6116255 := bstep (se 1 (by rfl) ⟨4587191, by rfl⟩ : syracuseStep 6116255 = 9174383) B9174383
theorem B3626471 : Blo 1431535 3626471 := bstep (se 1 (by rfl) ⟨2719853, by rfl⟩ : syracuseStep 3626471 = 5439707) B5439707
theorem B22042219 : Blo 1431535 22042219 := bstep (se 1 (by rfl) ⟨16531664, by rfl⟩ : syracuseStep 22042219 = 33063329) B33063329
theorem B12236507 : Blo 1431535 12236507 := bstep (se 1 (by rfl) ⟨9177380, by rfl⟩ : syracuseStep 12236507 = 18354761) B18354761
theorem B10884941 : Blo 1431535 10884941 := bstep (se 3 (by rfl) ⟨2040926, by rfl⟩ : syracuseStep 10884941 = 4081853) B4081853
theorem B7255979 : Blo 1431535 7255979 := bstep (se 1 (by rfl) ⟨5441984, by rfl⟩ : syracuseStep 7255979 = 10883969) B10883969
theorem B1431547 : Blo 1431535 1431547 := bstep (se 1 (by rfl) ⟨1073660, by rfl⟩ : syracuseStep 1431547 = 2147321) B2147321
theorem B1431583 : Blo 1431535 1431583 := bstep (se 1 (by rfl) ⟨1073687, by rfl⟩ : syracuseStep 1431583 = 2147375) B2147375
theorem B1431663 : Blo 1431535 1431663 := bstep (se 1 (by rfl) ⟨1073747, by rfl⟩ : syracuseStep 1431663 = 2147495) B2147495
theorem B1431791 : Blo 1431535 1431791 := bstep (se 1 (by rfl) ⟨1073843, by rfl⟩ : syracuseStep 1431791 = 2147687) B2147687
theorem B2718031 : Blo 1431535 2718031 := bstep (se 1 (by rfl) ⟨2038523, by rfl⟩ : syracuseStep 2718031 = 4077047) B4077047
theorem B5437793 : Blo 1431535 5437793 := bstep (se 2 (by rfl) ⟨2039172, by rfl⟩ : syracuseStep 5437793 = 4078345) B4078345
theorem B17422735 : Blo 1431535 17422735 := bstep (se 1 (by rfl) ⟨13067051, by rfl⟩ : syracuseStep 17422735 = 26134103) B26134103
theorem B3627625 : Blo 1431535 3627625 := bstep (se 2 (by rfl) ⟨1360359, by rfl⟩ : syracuseStep 3627625 = 2720719) B2720719
theorem B16325225 : Blo 1431535 16325225 := bstep (se 2 (by rfl) ⟨6121959, by rfl⟩ : syracuseStep 16325225 = 12243919) B12243919
theorem B6118031 : Blo 1431535 6118031 := bstep (se 1 (by rfl) ⟨4588523, by rfl⟩ : syracuseStep 6118031 = 9177047) B9177047
theorem B1432219 : Blo 1431535 1432219 := bstep (se 1 (by rfl) ⟨1074164, by rfl⟩ : syracuseStep 1432219 = 2148329) B2148329
theorem B1432315 : Blo 1431535 1432315 := bstep (se 1 (by rfl) ⟨1074236, by rfl⟩ : syracuseStep 1432315 = 2148473) B2148473
theorem B11623175 : Blo 1431535 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B5438279 : Blo 1431535 5438279 := bstep (se 1 (by rfl) ⟨4078709, by rfl⟩ : syracuseStep 5438279 = 8157419) B8157419
theorem B1432447 : Blo 1431535 1432447 := bstep (se 1 (by rfl) ⟨1074335, by rfl⟩ : syracuseStep 1432447 = 2148671) B2148671
theorem B16309187 : Blo 1431535 16309187 := bstep (se 1 (by rfl) ⟨12231890, by rfl⟩ : syracuseStep 16309187 = 24463781) B24463781
theorem B1432543 : Blo 1431535 1432543 := bstep (se 1 (by rfl) ⟨1074407, by rfl⟩ : syracuseStep 1432543 = 2148815) B2148815
theorem B1432571 : Blo 1431535 1432571 := bstep (se 1 (by rfl) ⟨1074428, by rfl⟩ : syracuseStep 1432571 = 2148857) B2148857
theorem B1432603 : Blo 1431535 1432603 := bstep (se 1 (by rfl) ⟨1074452, by rfl⟩ : syracuseStep 1432603 = 2148905) B2148905
theorem B8707135 : Blo 1431535 8707135 := bstep (se 1 (by rfl) ⟨6530351, by rfl⟩ : syracuseStep 8707135 = 13060703) B13060703
theorem B2415899 : Blo 1431535 2415899 := bstep (se 1 (by rfl) ⟨1811924, by rfl⟩ : syracuseStep 2415899 = 3623849) B3623849
theorem B1432895 : Blo 1431535 1432895 := bstep (se 1 (by rfl) ⟨1074671, by rfl⟩ : syracuseStep 1432895 = 2149343) B2149343
theorem B7249499 : Blo 1431535 7249499 := bstep (se 1 (by rfl) ⟨5437124, by rfl⟩ : syracuseStep 7249499 = 10874249) B10874249
theorem B1433191 : Blo 1431535 1433191 := bstep (se 1 (by rfl) ⟨1074893, by rfl⟩ : syracuseStep 1433191 = 2149787) B2149787
theorem B12246653 : Blo 1431535 12246653 := bstep (se 3 (by rfl) ⟨2296247, by rfl⟩ : syracuseStep 12246653 = 4592495) B4592495
theorem B8158877 : Blo 1431535 8158877 := bstep (se 3 (by rfl) ⟨1529789, by rfl⟩ : syracuseStep 8158877 = 3059579) B3059579
theorem B8707769 : Blo 1431535 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B2416351 : Blo 1431535 2416351 := bstep (se 1 (by rfl) ⟨1812263, by rfl⟩ : syracuseStep 2416351 = 3624527) B3624527
theorem B1433435 : Blo 1431535 1433435 := bstep (se 1 (by rfl) ⟨1075076, by rfl⟩ : syracuseStep 1433435 = 2150153) B2150153
theorem B1433471 : Blo 1431535 1433471 := bstep (se 1 (by rfl) ⟨1075103, by rfl⟩ : syracuseStep 1433471 = 2150207) B2150207
theorem B1720543 : Blo 1431535 1720543 := bstep (se 1 (by rfl) ⟨1290407, by rfl⟩ : syracuseStep 1720543 = 2580815) B2580815
theorem B12091679 : Blo 1431535 12091679 := bstep (se 1 (by rfl) ⟨9068759, by rfl⟩ : syracuseStep 12091679 = 18137519) B18137519
theorem B45310369 : Blo 1431535 45310369 := bstep (se 2 (by rfl) ⟨16991388, by rfl⟩ : syracuseStep 45310369 = 33982777) B33982777
theorem B7455149 : Blo 1431535 7455149 := bstep (se 3 (by rfl) ⟨1397840, by rfl⟩ : syracuseStep 7455149 = 2795681) B2795681
theorem B16319393 : Blo 1431535 16319393 := bstep (se 2 (by rfl) ⟨6119772, by rfl⟩ : syracuseStep 16319393 = 12239545) B12239545
theorem B46482407 : Blo 1431535 46482407 := bstep (se 1 (by rfl) ⟨34861805, by rfl⟩ : syracuseStep 46482407 = 69723611) B69723611
theorem B2417647 : Blo 1431535 2417647 := bstep (se 1 (by rfl) ⟨1813235, by rfl⟩ : syracuseStep 2417647 = 3626471) B3626471
theorem B4834727 : Blo 1431535 4834727 := bstep (se 1 (by rfl) ⟨3626045, by rfl⟩ : syracuseStep 4834727 = 7252091) B7252091
theorem B11609513 : Blo 1431535 11609513 := bstep (se 2 (by rfl) ⟨4353567, by rfl⟩ : syracuseStep 11609513 = 8707135) B8707135
theorem B2148047 : Blo 1431535 2148047 := bstep (se 1 (by rfl) ⟨1611035, by rfl⟩ : syracuseStep 2148047 = 3222071) B3222071
theorem B10872791 : Blo 1431535 10872791 := bstep (se 1 (by rfl) ⟨8154593, by rfl⟩ : syracuseStep 10872791 = 16309187) B16309187
theorem B27551825 : Blo 1431535 27551825 := bstep (se 2 (by rfl) ⟨10331934, by rfl⟩ : syracuseStep 27551825 = 20663869) B20663869
theorem B4835591 : Blo 1431535 4835591 := bstep (se 1 (by rfl) ⟨3626693, by rfl⟩ : syracuseStep 4835591 = 7253387) B7253387
theorem B3221801 : Blo 1431535 3221801 := bstep (se 2 (by rfl) ⟨1208175, by rfl⟩ : syracuseStep 3221801 = 2416351) B2416351
theorem B16320851 : Blo 1431535 16320851 := bstep (se 1 (by rfl) ⟨12240638, by rfl⟩ : syracuseStep 16320851 = 24481277) B24481277
theorem B3443257 : Blo 1431535 3443257 := bstep (se 2 (by rfl) ⟨1291221, by rfl⟩ : syracuseStep 3443257 = 2582443) B2582443
theorem B18352757 : Blo 1431535 18352757 := bstep (se 5 (by rfl) ⟨860285, by rfl⟩ : syracuseStep 18352757 = 1720571) B1720571
theorem B2149115 : Blo 1431535 2149115 := bstep (se 1 (by rfl) ⟨1611836, by rfl⟩ : syracuseStep 2149115 = 3223673) B3223673
theorem B2149319 : Blo 1431535 2149319 := bstep (se 1 (by rfl) ⟨1611989, by rfl⟩ : syracuseStep 2149319 = 3223979) B3223979
theorem B3624041 : Blo 1431535 3624041 := bstep (se 2 (by rfl) ⟨1359015, by rfl⟩ : syracuseStep 3624041 = 2718031) B2718031
theorem B3058879 : Blo 1431535 3058879 := bstep (se 1 (by rfl) ⟨2294159, by rfl⟩ : syracuseStep 3058879 = 4588319) B4588319
theorem B2903303 : Blo 1431535 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B4836833 : Blo 1431535 4836833 := bstep (se 2 (by rfl) ⟨1813812, by rfl⟩ : syracuseStep 4836833 = 3627625) B3627625
theorem B47123957 : Blo 1431535 47123957 := bstep (se 5 (by rfl) ⟨2208935, by rfl⟩ : syracuseStep 47123957 = 4417871) B4417871
theorem B26504795 : Blo 1431535 26504795 := bstep (se 1 (by rfl) ⟨19878596, by rfl⟩ : syracuseStep 26504795 = 39757193) B39757193
theorem B15494827 : Blo 1431535 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B30994163 : Blo 1431535 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B10874735 : Blo 1431535 10874735 := bstep (se 1 (by rfl) ⟨8156051, by rfl⟩ : syracuseStep 10874735 = 16312103) B16312103
theorem B9179045 : Blo 1431535 9179045 := bstep (se 4 (by rfl) ⟨860535, by rfl⟩ : syracuseStep 9179045 = 1721071) B1721071
theorem B4837319 : Blo 1431535 4837319 := bstep (se 1 (by rfl) ⟨3627989, by rfl⟩ : syracuseStep 4837319 = 7255979) B7255979
theorem B29077649 : Blo 1431535 29077649 := bstep (se 2 (by rfl) ⟨10904118, by rfl⟩ : syracuseStep 29077649 = 21808237) B21808237
theorem B3625195 : Blo 1431535 3625195 := bstep (se 1 (by rfl) ⟨2718896, by rfl⟩ : syracuseStep 3625195 = 5437793) B5437793
theorem B10883483 : Blo 1431535 10883483 := bstep (se 1 (by rfl) ⟨8162612, by rfl⟩ : syracuseStep 10883483 = 16325225) B16325225
theorem B3625519 : Blo 1431535 3625519 := bstep (se 1 (by rfl) ⟨2719139, by rfl⟩ : syracuseStep 3625519 = 5438279) B5438279
theorem B16315019 : Blo 1431535 16315019 := bstep (se 1 (by rfl) ⟨12236264, by rfl⟩ : syracuseStep 16315019 = 24472529) B24472529
theorem B29389625 : Blo 1431535 29389625 := bstep (se 2 (by rfl) ⟨11021109, by rfl⟩ : syracuseStep 29389625 = 22042219) B22042219
theorem B7254845 : Blo 1431535 7254845 := bstep (se 3 (by rfl) ⟨1360283, by rfl⟩ : syracuseStep 7254845 = 2720567) B2720567
theorem B1610599 : Blo 1431535 1610599 := bstep (se 1 (by rfl) ⟨1207949, by rfl⟩ : syracuseStep 1610599 = 2415899) B2415899
theorem B3224519 : Blo 1431535 3224519 := bstep (se 1 (by rfl) ⟨2418389, by rfl⟩ : syracuseStep 3224519 = 4836779) B4836779
theorem B8164435 : Blo 1431535 8164435 := bstep (se 1 (by rfl) ⟨6123326, by rfl⟩ : syracuseStep 8164435 = 12246653) B12246653
theorem B5805179 : Blo 1431535 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B4076705 : Blo 1431535 4076705 := bstep (se 2 (by rfl) ⟨1528764, by rfl⟩ : syracuseStep 4076705 = 3057529) B3057529
theorem B3626491 : Blo 1431535 3626491 := bstep (se 1 (by rfl) ⟨2719868, by rfl⟩ : syracuseStep 3626491 = 5439737) B5439737
theorem B5805631 : Blo 1431535 5805631 := bstep (se 1 (by rfl) ⟨4354223, by rfl⟩ : syracuseStep 5805631 = 8708447) B8708447
theorem B6116971 : Blo 1431535 6116971 := bstep (se 1 (by rfl) ⟨4587728, by rfl⟩ : syracuseStep 6116971 = 9175457) B9175457
theorem B3225257 : Blo 1431535 3225257 := bstep (se 2 (by rfl) ⟨1209471, by rfl⟩ : syracuseStep 3225257 = 2418943) B2418943
theorem B7247555 : Blo 1431535 7247555 := bstep (se 1 (by rfl) ⟨5435666, by rfl⟩ : syracuseStep 7247555 = 10871333) B10871333
theorem B3061595 : Blo 1431535 3061595 := bstep (se 1 (by rfl) ⟨2296196, by rfl⟩ : syracuseStep 3061595 = 4592393) B4592393
theorem B23230313 : Blo 1431535 23230313 := bstep (se 2 (by rfl) ⟨8711367, by rfl⟩ : syracuseStep 23230313 = 17422735) B17422735
theorem B4077503 : Blo 1431535 4077503 := bstep (se 1 (by rfl) ⟨3058127, by rfl⟩ : syracuseStep 4077503 = 6116255) B6116255
theorem B3872747 : Blo 1431535 3872747 := bstep (se 1 (by rfl) ⟨2904560, by rfl⟩ : syracuseStep 3872747 = 5809121) B5809121
theorem B55073033 : Blo 1431535 55073033 := bstep (se 2 (by rfl) ⟨20652387, by rfl⟩ : syracuseStep 55073033 = 41304775) B41304775
theorem B8157671 : Blo 1431535 8157671 := bstep (se 1 (by rfl) ⟨6118253, by rfl⟩ : syracuseStep 8157671 = 12236507) B12236507
theorem B7256627 : Blo 1431535 7256627 := bstep (se 1 (by rfl) ⟨5442470, by rfl⟩ : syracuseStep 7256627 = 10884941) B10884941
theorem B1005378115 : Blo 1431535 1005378115 := bstep (se 1 (by rfl) ⟨754033586, by rfl⟩ : syracuseStep 1005378115 = 1508067173) B1508067173
theorem B4078687 : Blo 1431535 4078687 := bstep (se 1 (by rfl) ⟨3059015, by rfl⟩ : syracuseStep 4078687 = 6118031) B6118031
theorem B1432735 : Blo 1431535 1432735 := bstep (se 1 (by rfl) ⟨1074551, by rfl⟩ : syracuseStep 1432735 = 2149103) B2149103
theorem B2415791 : Blo 1431535 2415791 := bstep (se 1 (by rfl) ⟨1811843, by rfl⟩ : syracuseStep 2415791 = 3623687) B3623687
theorem B7748783 : Blo 1431535 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B1432815 : Blo 1431535 1432815 := bstep (se 1 (by rfl) ⟨1074611, by rfl⟩ : syracuseStep 1432815 = 2149223) B2149223
theorem B2448703 : Blo 1431535 2448703 := bstep (se 1 (by rfl) ⟨1836527, by rfl⟩ : syracuseStep 2448703 = 3673055) B3673055
theorem B1432987 : Blo 1431535 1432987 := bstep (se 1 (by rfl) ⟨1074740, by rfl⟩ : syracuseStep 1432987 = 2149481) B2149481
theorem B1432991 : Blo 1431535 1432991 := bstep (se 1 (by rfl) ⟨1074743, by rfl⟩ : syracuseStep 1432991 = 2149487) B2149487
theorem B4832999 : Blo 1431535 4832999 := bstep (se 1 (by rfl) ⟨3624749, by rfl⟩ : syracuseStep 4832999 = 7249499) B7249499
theorem B5439251 : Blo 1431535 5439251 := bstep (se 1 (by rfl) ⟨4079438, by rfl⟩ : syracuseStep 5439251 = 8158877) B8158877
theorem B8061119 : Blo 1431535 8061119 := bstep (se 1 (by rfl) ⟨6045839, by rfl⟩ : syracuseStep 8061119 = 12091679) B12091679
theorem B2294057 : Blo 1431535 2294057 := bstep (se 2 (by rfl) ⟨860271, by rfl⟩ : syracuseStep 2294057 = 1720543) B1720543
theorem B4833593 : Blo 1431535 4833593 := bstep (se 2 (by rfl) ⟨1812597, by rfl⟩ : syracuseStep 4833593 = 3625195) B3625195
theorem B10879595 : Blo 1431535 10879595 := bstep (se 1 (by rfl) ⟨8159696, by rfl⟩ : syracuseStep 10879595 = 16319393) B16319393
theorem B7742141 : Blo 1431535 7742141 := bstep (se 3 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 7742141 = 2903303) B2903303
theorem B4834025 : Blo 1431535 4834025 := bstep (se 2 (by rfl) ⟨1812759, by rfl⟩ : syracuseStep 4834025 = 3625519) B3625519
theorem B2147465 : Blo 1431535 2147465 := bstep (se 2 (by rfl) ⟨805299, by rfl⟩ : syracuseStep 2147465 = 1610599) B1610599
theorem B2581831 : Blo 1431535 2581831 := bstep (se 1 (by rfl) ⟨1936373, by rfl⟩ : syracuseStep 2581831 = 3872747) B3872747
theorem B18367883 : Blo 1431535 18367883 := bstep (se 1 (by rfl) ⟨13775912, by rfl⟩ : syracuseStep 18367883 = 27551825) B27551825
theorem B2147867 : Blo 1431535 2147867 := bstep (se 1 (by rfl) ⟨1610900, by rfl⟩ : syracuseStep 2147867 = 3221801) B3221801
theorem B10880567 : Blo 1431535 10880567 := bstep (se 1 (by rfl) ⟨8160425, by rfl⟩ : syracuseStep 10880567 = 16320851) B16320851
theorem B4835321 : Blo 1431535 4835321 := bstep (se 2 (by rfl) ⟨1813245, by rfl⟩ : syracuseStep 4835321 = 3626491) B3626491
theorem B3221999 : Blo 1431535 3221999 := bstep (se 1 (by rfl) ⟨2416499, by rfl⟩ : syracuseStep 3221999 = 4832999) B4832999
theorem B20662775 : Blo 1431535 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B19385099 : Blo 1431535 19385099 := bstep (se 1 (by rfl) ⟨14538824, by rfl⟩ : syracuseStep 19385099 = 29077649) B29077649
theorem B4836563 : Blo 1431535 4836563 := bstep (se 1 (by rfl) ⟨3627422, by rfl⟩ : syracuseStep 4836563 = 7254845) B7254845
theorem B2149679 : Blo 1431535 2149679 := bstep (se 1 (by rfl) ⟨1612259, by rfl⟩ : syracuseStep 2149679 = 3224519) B3224519
theorem B4591009 : Blo 1431535 4591009 := bstep (se 2 (by rfl) ⟨1721628, by rfl⟩ : syracuseStep 4591009 = 3443257) B3443257
theorem B3870119 : Blo 1431535 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B3223151 : Blo 1431535 3223151 := bstep (se 1 (by rfl) ⟨2417363, by rfl⟩ : syracuseStep 3223151 = 4834727) B4834727
theorem B2150171 : Blo 1431535 2150171 := bstep (se 1 (by rfl) ⟨1612628, by rfl⟩ : syracuseStep 2150171 = 3225257) B3225257
theorem B15486875 : Blo 1431535 15486875 := bstep (se 1 (by rfl) ⟨11615156, by rfl⟩ : syracuseStep 15486875 = 23230313) B23230313
theorem B3223529 : Blo 1431535 3223529 := bstep (se 2 (by rfl) ⟨1208823, by rfl⟩ : syracuseStep 3223529 = 2417647) B2417647
theorem B3223727 : Blo 1431535 3223727 := bstep (se 1 (by rfl) ⟨2417795, by rfl⟩ : syracuseStep 3223727 = 4835591) B4835591
theorem B4837751 : Blo 1431535 4837751 := bstep (se 1 (by rfl) ⟨3628313, by rfl⟩ : syracuseStep 4837751 = 7256627) B7256627
theorem B12235171 : Blo 1431535 12235171 := bstep (se 1 (by rfl) ⟨9176378, by rfl⟩ : syracuseStep 12235171 = 18352757) B18352757
theorem B3264937 : Blo 1431535 3264937 := bstep (se 2 (by rfl) ⟨1224351, by rfl⟩ : syracuseStep 3264937 = 2448703) B2448703
theorem B1610527 : Blo 1431535 1610527 := bstep (se 1 (by rfl) ⟨1207895, by rfl⟩ : syracuseStep 1610527 = 2415791) B2415791
theorem B5165855 : Blo 1431535 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B8155961 : Blo 1431535 8155961 := bstep (se 2 (by rfl) ⟨3058485, by rfl⟩ : syracuseStep 8155961 = 6116971) B6116971
theorem B8164253 : Blo 1431535 8164253 := bstep (se 3 (by rfl) ⟨1530797, by rfl⟩ : syracuseStep 8164253 = 3061595) B3061595
theorem B3224555 : Blo 1431535 3224555 := bstep (se 1 (by rfl) ⟨2418416, by rfl⟩ : syracuseStep 3224555 = 4836833) B4836833
theorem B3626167 : Blo 1431535 3626167 := bstep (se 1 (by rfl) ⟨2719625, by rfl⟩ : syracuseStep 3626167 = 5439251) B5439251
theorem B3224879 : Blo 1431535 3224879 := bstep (se 1 (by rfl) ⟨2418659, by rfl⟩ : syracuseStep 3224879 = 4837319) B4837319
theorem B7255655 : Blo 1431535 7255655 := bstep (se 1 (by rfl) ⟨5441741, by rfl⟩ : syracuseStep 7255655 = 10883483) B10883483
theorem B4970099 : Blo 1431535 4970099 := bstep (se 1 (by rfl) ⟨3727574, by rfl⟩ : syracuseStep 4970099 = 7455149) B7455149
theorem B10876679 : Blo 1431535 10876679 := bstep (se 1 (by rfl) ⟨8157509, by rfl⟩ : syracuseStep 10876679 = 16315019) B16315019
theorem B19593083 : Blo 1431535 19593083 := bstep (se 1 (by rfl) ⟨14694812, by rfl⟩ : syracuseStep 19593083 = 29389625) B29389625
theorem B60413825 : Blo 1431535 60413825 := bstep (se 2 (by rfl) ⟨22655184, by rfl⟩ : syracuseStep 60413825 = 45310369) B45310369
theorem B30988271 : Blo 1431535 30988271 := bstep (se 1 (by rfl) ⟨23241203, by rfl⟩ : syracuseStep 30988271 = 46482407) B46482407
theorem B1340504153 : Blo 1431535 1340504153 := bstep (se 2 (by rfl) ⟨502689057, by rfl⟩ : syracuseStep 1340504153 = 1005378115) B1005378115
theorem B2717803 : Blo 1431535 2717803 := bstep (se 1 (by rfl) ⟨2038352, by rfl⟩ : syracuseStep 2717803 = 4076705) B4076705
theorem B7739675 : Blo 1431535 7739675 := bstep (se 1 (by rfl) ⟨5804756, by rfl⟩ : syracuseStep 7739675 = 11609513) B11609513
theorem B4831703 : Blo 1431535 4831703 := bstep (se 1 (by rfl) ⟨3623777, by rfl⟩ : syracuseStep 4831703 = 7247555) B7247555
theorem B1432031 : Blo 1431535 1432031 := bstep (se 1 (by rfl) ⟨1074023, by rfl⟩ : syracuseStep 1432031 = 2148047) B2148047
theorem B2718335 : Blo 1431535 2718335 := bstep (se 1 (by rfl) ⟨2038751, by rfl⟩ : syracuseStep 2718335 = 4077503) B4077503
theorem B7248527 : Blo 1431535 7248527 := bstep (se 1 (by rfl) ⟨5436395, by rfl⟩ : syracuseStep 7248527 = 10872791) B10872791
theorem B10885913 : Blo 1431535 10885913 := bstep (se 2 (by rfl) ⟨4082217, by rfl⟩ : syracuseStep 10885913 = 8164435) B8164435
theorem B5438249 : Blo 1431535 5438249 := bstep (se 2 (by rfl) ⟨2039343, by rfl⟩ : syracuseStep 5438249 = 4078687) B4078687
theorem B36715355 : Blo 1431535 36715355 := bstep (se 1 (by rfl) ⟨27536516, by rfl⟩ : syracuseStep 36715355 = 55073033) B55073033
theorem B4078505 : Blo 1431535 4078505 := bstep (se 2 (by rfl) ⟨1529439, by rfl⟩ : syracuseStep 4078505 = 3058879) B3058879
theorem B5438447 : Blo 1431535 5438447 := bstep (se 1 (by rfl) ⟨4078835, by rfl⟩ : syracuseStep 5438447 = 8157671) B8157671
theorem B1432743 : Blo 1431535 1432743 := bstep (se 1 (by rfl) ⟨1074557, by rfl⟩ : syracuseStep 1432743 = 2149115) B2149115
theorem B1432879 : Blo 1431535 1432879 := bstep (se 1 (by rfl) ⟨1074659, by rfl⟩ : syracuseStep 1432879 = 2149319) B2149319
theorem B2416027 : Blo 1431535 2416027 := bstep (se 1 (by rfl) ⟨1812020, by rfl⟩ : syracuseStep 2416027 = 3624041) B3624041
theorem B7740841 : Blo 1431535 7740841 := bstep (se 2 (by rfl) ⟨2902815, by rfl⟩ : syracuseStep 7740841 = 5805631) B5805631
theorem B20659769 : Blo 1431535 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B31415971 : Blo 1431535 31415971 := bstep (se 1 (by rfl) ⟨23561978, by rfl⟩ : syracuseStep 31415971 = 47123957) B47123957
theorem B17669863 : Blo 1431535 17669863 := bstep (se 1 (by rfl) ⟨13252397, by rfl⟩ : syracuseStep 17669863 = 26504795) B26504795
theorem B7249823 : Blo 1431535 7249823 := bstep (se 1 (by rfl) ⟨5437367, by rfl⟩ : syracuseStep 7249823 = 10874735) B10874735
theorem B6119363 : Blo 1431535 6119363 := bstep (se 1 (by rfl) ⟨4589522, by rfl⟩ : syracuseStep 6119363 = 9179045) B9179045
theorem B5374079 : Blo 1431535 5374079 := bstep (se 1 (by rfl) ⟨4030559, by rfl⟩ : syracuseStep 5374079 = 8061119) B8061119
theorem B5161427 : Blo 1431535 5161427 := bstep (se 1 (by rfl) ⟨3871070, by rfl⟩ : syracuseStep 5161427 = 7742141) B7742141
theorem B2147369 : Blo 1431535 2147369 := bstep (se 2 (by rfl) ⟨805263, by rfl⟩ : syracuseStep 2147369 = 1610527) B1610527
theorem B7251119 : Blo 1431535 7251119 := bstep (se 1 (by rfl) ⟨5438339, by rfl⟩ : syracuseStep 7251119 = 10876679) B10876679
theorem B4834889 : Blo 1431535 4834889 := bstep (se 2 (by rfl) ⟨1813083, by rfl⟩ : syracuseStep 4834889 = 3626167) B3626167
theorem B3221135 : Blo 1431535 3221135 := bstep (se 1 (by rfl) ⟨2415851, by rfl⟩ : syracuseStep 3221135 = 4831703) B4831703
theorem B2147999 : Blo 1431535 2147999 := bstep (se 1 (by rfl) ⟨1610999, by rfl⟩ : syracuseStep 2147999 = 3221999) B3221999
theorem B1812223 : Blo 1431535 1812223 := bstep (se 1 (by rfl) ⟨1359167, by rfl⟩ : syracuseStep 1812223 = 2718335) B2718335
theorem B3442441 : Blo 1431535 3442441 := bstep (se 2 (by rfl) ⟨1290915, by rfl⟩ : syracuseStep 3442441 = 2581831) B2581831
theorem B3221369 : Blo 1431535 3221369 := bstep (se 2 (by rfl) ⟨1208013, by rfl⟩ : syracuseStep 3221369 = 2416027) B2416027
theorem B6121345 : Blo 1431535 6121345 := bstep (se 2 (by rfl) ⟨2295504, by rfl⟩ : syracuseStep 6121345 = 4591009) B4591009
theorem B41887961 : Blo 1431535 41887961 := bstep (se 2 (by rfl) ⟨15707985, by rfl⟩ : syracuseStep 41887961 = 31415971) B31415971
theorem B13773179 : Blo 1431535 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B2148767 : Blo 1431535 2148767 := bstep (se 1 (by rfl) ⟨1611575, by rfl⟩ : syracuseStep 2148767 = 3223151) B3223151
theorem B10324583 : Blo 1431535 10324583 := bstep (se 1 (by rfl) ⟨7743437, by rfl⟩ : syracuseStep 10324583 = 15486875) B15486875
theorem B2149019 : Blo 1431535 2149019 := bstep (se 1 (by rfl) ⟨1611764, by rfl⟩ : syracuseStep 2149019 = 3223529) B3223529
theorem B2149151 : Blo 1431535 2149151 := bstep (se 1 (by rfl) ⟨1611863, by rfl⟩ : syracuseStep 2149151 = 3223727) B3223727
theorem B3623737 : Blo 1431535 3623737 := bstep (se 2 (by rfl) ⟨1358901, by rfl⟩ : syracuseStep 3623737 = 2717803) B2717803
theorem B3222395 : Blo 1431535 3222395 := bstep (se 1 (by rfl) ⟨2416796, by rfl⟩ : syracuseStep 3222395 = 4833593) B4833593
theorem B7253063 : Blo 1431535 7253063 := bstep (se 1 (by rfl) ⟨5439797, by rfl⟩ : syracuseStep 7253063 = 10879595) B10879595
theorem B3222683 : Blo 1431535 3222683 := bstep (se 1 (by rfl) ⟨2417012, by rfl⟩ : syracuseStep 3222683 = 4834025) B4834025
theorem B3443903 : Blo 1431535 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B16313561 : Blo 1431535 16313561 := bstep (se 2 (by rfl) ⟨6117585, by rfl⟩ : syracuseStep 16313561 = 12235171) B12235171
theorem B5442835 : Blo 1431535 5442835 := bstep (se 1 (by rfl) ⟨4082126, by rfl⟩ : syracuseStep 5442835 = 8164253) B8164253
theorem B2149703 : Blo 1431535 2149703 := bstep (se 1 (by rfl) ⟨1612277, by rfl⟩ : syracuseStep 2149703 = 3224555) B3224555
theorem B2149919 : Blo 1431535 2149919 := bstep (se 1 (by rfl) ⟨1612439, by rfl⟩ : syracuseStep 2149919 = 3224879) B3224879
theorem B7253711 : Blo 1431535 7253711 := bstep (se 1 (by rfl) ⟨5440283, by rfl⟩ : syracuseStep 7253711 = 10880567) B10880567
theorem B4837103 : Blo 1431535 4837103 := bstep (se 1 (by rfl) ⟨3627827, by rfl⟩ : syracuseStep 4837103 = 7255655) B7255655
theorem B3313399 : Blo 1431535 3313399 := bstep (se 1 (by rfl) ⟨2485049, by rfl⟩ : syracuseStep 3313399 = 4970099) B4970099
theorem B13062055 : Blo 1431535 13062055 := bstep (se 1 (by rfl) ⟨9796541, by rfl⟩ : syracuseStep 13062055 = 19593083) B19593083
theorem B40275883 : Blo 1431535 40275883 := bstep (se 1 (by rfl) ⟨30206912, by rfl⟩ : syracuseStep 40275883 = 60413825) B60413825
theorem B3223547 : Blo 1431535 3223547 := bstep (se 1 (by rfl) ⟨2417660, by rfl⟩ : syracuseStep 3223547 = 4835321) B4835321
theorem B893669435 : Blo 1431535 893669435 := bstep (se 1 (by rfl) ⟨670252076, by rfl⟩ : syracuseStep 893669435 = 1340504153) B1340504153
theorem B13775183 : Blo 1431535 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B12923399 : Blo 1431535 12923399 := bstep (se 1 (by rfl) ⟨9692549, by rfl⟩ : syracuseStep 12923399 = 19385099) B19385099
theorem B3625499 : Blo 1431535 3625499 := bstep (se 1 (by rfl) ⟨2719124, by rfl⟩ : syracuseStep 3625499 = 5438249) B5438249
theorem B3625631 : Blo 1431535 3625631 := bstep (se 1 (by rfl) ⟨2719223, by rfl⟩ : syracuseStep 3625631 = 5438447) B5438447
theorem B3224375 : Blo 1431535 3224375 := bstep (se 1 (by rfl) ⟨2418281, by rfl⟩ : syracuseStep 3224375 = 4836563) B4836563
theorem B17412997 : Blo 1431535 17412997 := bstep (se 4 (by rfl) ⟨1632468, by rfl⟩ : syracuseStep 17412997 = 3264937) B3264937
theorem B1529371 : Blo 1431535 1529371 := bstep (se 1 (by rfl) ⟨1147028, by rfl⟩ : syracuseStep 1529371 = 2294057) B2294057
theorem B3225167 : Blo 1431535 3225167 := bstep (se 1 (by rfl) ⟨2418875, by rfl⟩ : syracuseStep 3225167 = 4837751) B4837751
theorem B5437307 : Blo 1431535 5437307 := bstep (se 1 (by rfl) ⟨4077980, by rfl⟩ : syracuseStep 5437307 = 8155961) B8155961
theorem B1431643 : Blo 1431535 1431643 := bstep (se 1 (by rfl) ⟨1073732, by rfl⟩ : syracuseStep 1431643 = 2147465) B2147465
theorem B12245255 : Blo 1431535 12245255 := bstep (se 1 (by rfl) ⟨9183941, by rfl⟩ : syracuseStep 12245255 = 18367883) B18367883
theorem B1431911 : Blo 1431535 1431911 := bstep (se 1 (by rfl) ⟨1073933, by rfl⟩ : syracuseStep 1431911 = 2147867) B2147867
theorem B10320317 : Blo 1431535 10320317 := bstep (se 3 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 10320317 = 3870119) B3870119
theorem B20658847 : Blo 1431535 20658847 := bstep (se 1 (by rfl) ⟨15494135, by rfl⟩ : syracuseStep 20658847 = 30988271) B30988271
theorem B5159783 : Blo 1431535 5159783 := bstep (se 1 (by rfl) ⟨3869837, by rfl⟩ : syracuseStep 5159783 = 7739675) B7739675
theorem B4832351 : Blo 1431535 4832351 := bstep (se 1 (by rfl) ⟨3624263, by rfl⟩ : syracuseStep 4832351 = 7248527) B7248527
theorem B7257275 : Blo 1431535 7257275 := bstep (se 1 (by rfl) ⟨5442956, by rfl⟩ : syracuseStep 7257275 = 10885913) B10885913
theorem B10321121 : Blo 1431535 10321121 := bstep (se 2 (by rfl) ⟨3870420, by rfl⟩ : syracuseStep 10321121 = 7740841) B7740841
theorem B24476903 : Blo 1431535 24476903 := bstep (se 1 (by rfl) ⟨18357677, by rfl⟩ : syracuseStep 24476903 = 36715355) B36715355
theorem B2719003 : Blo 1431535 2719003 := bstep (se 1 (by rfl) ⟨2039252, by rfl⟩ : syracuseStep 2719003 = 4078505) B4078505
theorem B1433119 : Blo 1431535 1433119 := bstep (se 1 (by rfl) ⟨1074839, by rfl⟩ : syracuseStep 1433119 = 2149679) B2149679
theorem B23559817 : Blo 1431535 23559817 := bstep (se 2 (by rfl) ⟨8834931, by rfl⟩ : syracuseStep 23559817 = 17669863) B17669863
theorem B1433447 : Blo 1431535 1433447 := bstep (se 1 (by rfl) ⟨1075085, by rfl⟩ : syracuseStep 1433447 = 2150171) B2150171
theorem B4833215 : Blo 1431535 4833215 := bstep (se 1 (by rfl) ⟨3624911, by rfl⟩ : syracuseStep 4833215 = 7249823) B7249823
theorem B4079575 : Blo 1431535 4079575 := bstep (se 1 (by rfl) ⟨3059681, by rfl⟩ : syracuseStep 4079575 = 6119363) B6119363
theorem B595779623 : Blo 1431535 595779623 := bstep (se 1 (by rfl) ⟨446834717, by rfl⟩ : syracuseStep 595779623 = 893669435) B893669435
theorem B9183455 : Blo 1431535 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B3440951 : Blo 1431535 3440951 := bstep (se 1 (by rfl) ⟨2580713, by rfl⟩ : syracuseStep 3440951 = 5161427) B5161427
theorem B2416999 : Blo 1431535 2416999 := bstep (se 1 (by rfl) ⟨1812749, by rfl⟩ : syracuseStep 2416999 = 3625499) B3625499
theorem B2417087 : Blo 1431535 2417087 := bstep (se 1 (by rfl) ⟨1812815, by rfl⟩ : syracuseStep 2417087 = 3625631) B3625631
theorem B4834079 : Blo 1431535 4834079 := bstep (se 1 (by rfl) ⟨3625559, by rfl⟩ : syracuseStep 4834079 = 7251119) B7251119
theorem B2147423 : Blo 1431535 2147423 := bstep (se 1 (by rfl) ⟨1610567, by rfl⟩ : syracuseStep 2147423 = 3221135) B3221135
theorem B23217329 : Blo 1431535 23217329 := bstep (se 2 (by rfl) ⟨8706498, by rfl⟩ : syracuseStep 23217329 = 17412997) B17412997
theorem B2147579 : Blo 1431535 2147579 := bstep (se 1 (by rfl) ⟨1610684, by rfl⟩ : syracuseStep 2147579 = 3221369) B3221369
theorem B6883055 : Blo 1431535 6883055 := bstep (se 1 (by rfl) ⟨5162291, by rfl⟩ : syracuseStep 6883055 = 10324583) B10324583
theorem B2148263 : Blo 1431535 2148263 := bstep (se 1 (by rfl) ⟨1611197, by rfl⟩ : syracuseStep 2148263 = 3222395) B3222395
theorem B4835375 : Blo 1431535 4835375 := bstep (se 1 (by rfl) ⟨3626531, by rfl⟩ : syracuseStep 4835375 = 7253063) B7253063
theorem B3221567 : Blo 1431535 3221567 := bstep (se 1 (by rfl) ⟨2416175, by rfl⟩ : syracuseStep 3221567 = 4832351) B4832351
theorem B2148455 : Blo 1431535 2148455 := bstep (se 1 (by rfl) ⟨1611341, by rfl⟩ : syracuseStep 2148455 = 3222683) B3222683
theorem B2295935 : Blo 1431535 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B4417865 : Blo 1431535 4417865 := bstep (se 2 (by rfl) ⟨1656699, by rfl⟩ : syracuseStep 4417865 = 3313399) B3313399
theorem B4589921 : Blo 1431535 4589921 := bstep (se 2 (by rfl) ⟨1721220, by rfl⟩ : syracuseStep 4589921 = 3442441) B3442441
theorem B4835807 : Blo 1431535 4835807 := bstep (se 1 (by rfl) ⟨3626855, by rfl⟩ : syracuseStep 4835807 = 7253711) B7253711
theorem B8161793 : Blo 1431535 8161793 := bstep (se 2 (by rfl) ⟨3060672, by rfl⟩ : syracuseStep 8161793 = 6121345) B6121345
theorem B53701177 : Blo 1431535 53701177 := bstep (se 2 (by rfl) ⟨20137941, by rfl⟩ : syracuseStep 53701177 = 40275883) B40275883
theorem B3222143 : Blo 1431535 3222143 := bstep (se 1 (by rfl) ⟨2416607, by rfl⟩ : syracuseStep 3222143 = 4833215) B4833215
theorem B2149031 : Blo 1431535 2149031 := bstep (se 1 (by rfl) ⟨1611773, by rfl⟩ : syracuseStep 2149031 = 3223547) B3223547
theorem B3582719 : Blo 1431535 3582719 := bstep (se 1 (by rfl) ⟨2687039, by rfl⟩ : syracuseStep 3582719 = 5374079) B5374079
theorem B2149583 : Blo 1431535 2149583 := bstep (se 1 (by rfl) ⟨1612187, by rfl⟩ : syracuseStep 2149583 = 3224375) B3224375
theorem B27545129 : Blo 1431535 27545129 := bstep (se 2 (by rfl) ⟨10329423, by rfl⟩ : syracuseStep 27545129 = 20658847) B20658847
theorem B36728477 : Blo 1431535 36728477 := bstep (se 3 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 36728477 = 13773179) B13773179
theorem B3223259 : Blo 1431535 3223259 := bstep (se 1 (by rfl) ⟨2417444, by rfl⟩ : syracuseStep 3223259 = 4834889) B4834889
theorem B2150111 : Blo 1431535 2150111 := bstep (se 1 (by rfl) ⟨1612583, by rfl⟩ : syracuseStep 2150111 = 3225167) B3225167
theorem B3624871 : Blo 1431535 3624871 := bstep (se 1 (by rfl) ⟨2718653, by rfl⟩ : syracuseStep 3624871 = 5437307) B5437307
theorem B8163503 : Blo 1431535 8163503 := bstep (se 1 (by rfl) ⟨6122627, by rfl⟩ : syracuseStep 8163503 = 12245255) B12245255
theorem B3625337 : Blo 1431535 3625337 := bstep (se 2 (by rfl) ⟨1359501, by rfl⟩ : syracuseStep 3625337 = 2719003) B2719003
theorem B4838183 : Blo 1431535 4838183 := bstep (se 1 (by rfl) ⟨3628637, by rfl⟩ : syracuseStep 4838183 = 7257275) B7257275
theorem B10875707 : Blo 1431535 10875707 := bstep (se 1 (by rfl) ⟨8156780, by rfl⟩ : syracuseStep 10875707 = 16313561) B16313561
theorem B31413089 : Blo 1431535 31413089 := bstep (se 2 (by rfl) ⟨11779908, by rfl⟩ : syracuseStep 31413089 = 23559817) B23559817
theorem B3224735 : Blo 1431535 3224735 := bstep (se 1 (by rfl) ⟨2418551, by rfl⟩ : syracuseStep 3224735 = 4837103) B4837103
theorem B8156645 : Blo 1431535 8156645 := bstep (se 4 (by rfl) ⟨764685, by rfl⟩ : syracuseStep 8156645 = 1529371) B1529371
theorem B8615599 : Blo 1431535 8615599 := bstep (se 1 (by rfl) ⟨6461699, by rfl⟩ : syracuseStep 8615599 = 12923399) B12923399
theorem B1431579 : Blo 1431535 1431579 := bstep (se 1 (by rfl) ⟨1073684, by rfl⟩ : syracuseStep 1431579 = 2147369) B2147369
theorem B4831649 : Blo 1431535 4831649 := bstep (se 2 (by rfl) ⟨1811868, by rfl⟩ : syracuseStep 4831649 = 3623737) B3623737
theorem B1431999 : Blo 1431535 1431999 := bstep (se 1 (by rfl) ⟨1073999, by rfl⟩ : syracuseStep 1431999 = 2147999) B2147999
theorem B27925307 : Blo 1431535 27925307 := bstep (se 1 (by rfl) ⟨20943980, by rfl⟩ : syracuseStep 27925307 = 41887961) B41887961
theorem B1432511 : Blo 1431535 1432511 := bstep (se 1 (by rfl) ⟨1074383, by rfl⟩ : syracuseStep 1432511 = 2148767) B2148767
theorem B6880211 : Blo 1431535 6880211 := bstep (se 1 (by rfl) ⟨5160158, by rfl⟩ : syracuseStep 6880211 = 10320317) B10320317
theorem B7257113 : Blo 1431535 7257113 := bstep (se 2 (by rfl) ⟨2721417, by rfl⟩ : syracuseStep 7257113 = 5442835) B5442835
theorem B1432679 : Blo 1431535 1432679 := bstep (se 1 (by rfl) ⟨1074509, by rfl⟩ : syracuseStep 1432679 = 2149019) B2149019
theorem B1432767 : Blo 1431535 1432767 := bstep (se 1 (by rfl) ⟨1074575, by rfl⟩ : syracuseStep 1432767 = 2149151) B2149151
theorem B3439855 : Blo 1431535 3439855 := bstep (se 1 (by rfl) ⟨2579891, by rfl⟩ : syracuseStep 3439855 = 5159783) B5159783
theorem B6880747 : Blo 1431535 6880747 := bstep (se 1 (by rfl) ⟨5160560, by rfl⟩ : syracuseStep 6880747 = 10321121) B10321121
theorem B16317935 : Blo 1431535 16317935 := bstep (se 1 (by rfl) ⟨12238451, by rfl⟩ : syracuseStep 16317935 = 24476903) B24476903
theorem B1433135 : Blo 1431535 1433135 := bstep (se 1 (by rfl) ⟨1074851, by rfl⟩ : syracuseStep 1433135 = 2149703) B2149703
theorem B2416297 : Blo 1431535 2416297 := bstep (se 2 (by rfl) ⟨906111, by rfl⟩ : syracuseStep 2416297 = 1812223) B1812223
theorem B1433279 : Blo 1431535 1433279 := bstep (se 1 (by rfl) ⟨1074959, by rfl⟩ : syracuseStep 1433279 = 2149919) B2149919
theorem B17416073 : Blo 1431535 17416073 := bstep (se 2 (by rfl) ⟨6531027, by rfl⟩ : syracuseStep 17416073 = 13062055) B13062055
theorem B5439433 : Blo 1431535 5439433 := bstep (se 2 (by rfl) ⟨2039787, by rfl⟩ : syracuseStep 5439433 = 4079575) B4079575
theorem B2293967 : Blo 1431535 2293967 := bstep (se 1 (by rfl) ⟨1720475, by rfl⟩ : syracuseStep 2293967 = 3440951) B3440951
theorem B2416891 : Blo 1431535 2416891 := bstep (se 1 (by rfl) ⟨1812668, by rfl⟩ : syracuseStep 2416891 = 3625337) B3625337
theorem B7250471 : Blo 1431535 7250471 := bstep (se 1 (by rfl) ⟨5437853, by rfl⟩ : syracuseStep 7250471 = 10875707) B10875707
theorem B45949861 : Blo 1431535 45949861 := bstep (se 4 (by rfl) ⟨4307799, by rfl⟩ : syracuseStep 45949861 = 8615599) B8615599
theorem B4588703 : Blo 1431535 4588703 := bstep (se 1 (by rfl) ⟨3441527, by rfl⟩ : syracuseStep 4588703 = 6883055) B6883055
theorem B2147711 : Blo 1431535 2147711 := bstep (se 1 (by rfl) ⟨1610783, by rfl⟩ : syracuseStep 2147711 = 3221567) B3221567
theorem B3221099 : Blo 1431535 3221099 := bstep (se 1 (by rfl) ⟨2415824, by rfl⟩ : syracuseStep 3221099 = 4831649) B4831649
theorem B5441195 : Blo 1431535 5441195 := bstep (se 1 (by rfl) ⟨4080896, by rfl⟩ : syracuseStep 5441195 = 8161793) B8161793
theorem B2148095 : Blo 1431535 2148095 := bstep (se 1 (by rfl) ⟨1611071, by rfl⟩ : syracuseStep 2148095 = 3222143) B3222143
theorem B3221729 : Blo 1431535 3221729 := bstep (se 2 (by rfl) ⟨1208148, by rfl⟩ : syracuseStep 3221729 = 2416297) B2416297
theorem B2148839 : Blo 1431535 2148839 := bstep (se 1 (by rfl) ⟨1611629, by rfl⟩ : syracuseStep 2148839 = 3223259) B3223259
theorem B11610715 : Blo 1431535 11610715 := bstep (se 1 (by rfl) ⟨8708036, by rfl⟩ : syracuseStep 11610715 = 17416073) B17416073
theorem B7252577 : Blo 1431535 7252577 := bstep (se 2 (by rfl) ⟨2719716, by rfl⟩ : syracuseStep 7252577 = 5439433) B5439433
theorem B5442335 : Blo 1431535 5442335 := bstep (se 1 (by rfl) ⟨4081751, by rfl⟩ : syracuseStep 5442335 = 8163503) B8163503
theorem B6122303 : Blo 1431535 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B3222665 : Blo 1431535 3222665 := bstep (se 2 (by rfl) ⟨1208499, by rfl⟩ : syracuseStep 3222665 = 2416999) B2416999
theorem B3222719 : Blo 1431535 3222719 := bstep (se 1 (by rfl) ⟨2417039, by rfl⟩ : syracuseStep 3222719 = 4834079) B4834079
theorem B20942059 : Blo 1431535 20942059 := bstep (se 1 (by rfl) ⟨15706544, by rfl⟩ : syracuseStep 20942059 = 31413089) B31413089
theorem B71601569 : Blo 1431535 71601569 := bstep (se 2 (by rfl) ⟨26850588, by rfl⟩ : syracuseStep 71601569 = 53701177) B53701177
theorem B2149823 : Blo 1431535 2149823 := bstep (se 1 (by rfl) ⟨1612367, by rfl⟩ : syracuseStep 2149823 = 3224735) B3224735
theorem B15478219 : Blo 1431535 15478219 := bstep (se 1 (by rfl) ⟨11608664, by rfl⟩ : syracuseStep 15478219 = 23217329) B23217329
theorem B3223583 : Blo 1431535 3223583 := bstep (se 1 (by rfl) ⟨2417687, by rfl⟩ : syracuseStep 3223583 = 4835375) B4835375
theorem B2945243 : Blo 1431535 2945243 := bstep (se 1 (by rfl) ⟨2208932, by rfl⟩ : syracuseStep 2945243 = 4417865) B4417865
theorem B3059947 : Blo 1431535 3059947 := bstep (se 1 (by rfl) ⟨2294960, by rfl⟩ : syracuseStep 3059947 = 4589921) B4589921
theorem B3223871 : Blo 1431535 3223871 := bstep (se 1 (by rfl) ⟨2417903, by rfl⟩ : syracuseStep 3223871 = 4835807) B4835807
theorem B2388479 : Blo 1431535 2388479 := bstep (se 1 (by rfl) ⟨1791359, by rfl⟩ : syracuseStep 2388479 = 3582719) B3582719
theorem B18616871 : Blo 1431535 18616871 := bstep (se 1 (by rfl) ⟨13962653, by rfl⟩ : syracuseStep 18616871 = 27925307) B27925307
theorem B4838075 : Blo 1431535 4838075 := bstep (se 1 (by rfl) ⟨3628556, by rfl⟩ : syracuseStep 4838075 = 7257113) B7257113
theorem B18363419 : Blo 1431535 18363419 := bstep (se 1 (by rfl) ⟨13772564, by rfl⟩ : syracuseStep 18363419 = 27545129) B27545129
theorem B397186415 : Blo 1431535 397186415 := bstep (se 1 (by rfl) ⟨297889811, by rfl⟩ : syracuseStep 397186415 = 595779623) B595779623
theorem B1611391 : Blo 1431535 1611391 := bstep (se 1 (by rfl) ⟨1208543, by rfl⟩ : syracuseStep 1611391 = 2417087) B2417087
theorem B3225455 : Blo 1431535 3225455 := bstep (se 1 (by rfl) ⟨2419091, by rfl⟩ : syracuseStep 3225455 = 4838183) B4838183
theorem B1431615 : Blo 1431535 1431615 := bstep (se 1 (by rfl) ⟨1073711, by rfl⟩ : syracuseStep 1431615 = 2147423) B2147423
theorem B1431719 : Blo 1431535 1431719 := bstep (se 1 (by rfl) ⟨1073789, by rfl⟩ : syracuseStep 1431719 = 2147579) B2147579
theorem B5437763 : Blo 1431535 5437763 := bstep (se 1 (by rfl) ⟨4078322, by rfl⟩ : syracuseStep 5437763 = 8156645) B8156645
theorem B1432175 : Blo 1431535 1432175 := bstep (se 1 (by rfl) ⟨1074131, by rfl⟩ : syracuseStep 1432175 = 2148263) B2148263
theorem B1432303 : Blo 1431535 1432303 := bstep (se 1 (by rfl) ⟨1074227, by rfl⟩ : syracuseStep 1432303 = 2148455) B2148455
theorem B1530623 : Blo 1431535 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B4586473 : Blo 1431535 4586473 := bstep (se 2 (by rfl) ⟨1719927, by rfl⟩ : syracuseStep 4586473 = 3439855) B3439855
theorem B1432687 : Blo 1431535 1432687 := bstep (se 1 (by rfl) ⟨1074515, by rfl⟩ : syracuseStep 1432687 = 2149031) B2149031
theorem B4586807 : Blo 1431535 4586807 := bstep (se 1 (by rfl) ⟨3440105, by rfl⟩ : syracuseStep 4586807 = 6880211) B6880211
theorem B9174329 : Blo 1431535 9174329 := bstep (se 2 (by rfl) ⟨3440373, by rfl⟩ : syracuseStep 9174329 = 6880747) B6880747
theorem B1433055 : Blo 1431535 1433055 := bstep (se 1 (by rfl) ⟨1074791, by rfl⟩ : syracuseStep 1433055 = 2149583) B2149583
theorem B10878623 : Blo 1431535 10878623 := bstep (se 1 (by rfl) ⟨8158967, by rfl⟩ : syracuseStep 10878623 = 16317935) B16317935
theorem B24485651 : Blo 1431535 24485651 := bstep (se 1 (by rfl) ⟨18364238, by rfl⟩ : syracuseStep 24485651 = 36728477) B36728477
theorem B1433407 : Blo 1431535 1433407 := bstep (se 1 (by rfl) ⟨1075055, by rfl⟩ : syracuseStep 1433407 = 2150111) B2150111
theorem B4833161 : Blo 1431535 4833161 := bstep (se 2 (by rfl) ⟨1812435, by rfl⟩ : syracuseStep 4833161 = 3624871) B3624871
theorem B4079929 : Blo 1431535 4079929 := bstep (se 2 (by rfl) ⟨1529973, by rfl⟩ : syracuseStep 4079929 = 3059947) B3059947
theorem B4833647 : Blo 1431535 4833647 := bstep (se 1 (by rfl) ⟨3625235, by rfl⟩ : syracuseStep 4833647 = 7250471) B7250471
theorem B12411247 : Blo 1431535 12411247 := bstep (se 1 (by rfl) ⟨9308435, by rfl⟩ : syracuseStep 12411247 = 18616871) B18616871
theorem B264790943 : Blo 1431535 264790943 := bstep (se 1 (by rfl) ⟨198593207, by rfl⟩ : syracuseStep 264790943 = 397186415) B397186415
theorem B2147399 : Blo 1431535 2147399 := bstep (se 1 (by rfl) ⟨1610549, by rfl⟩ : syracuseStep 2147399 = 3221099) B3221099
theorem B2147819 : Blo 1431535 2147819 := bstep (se 1 (by rfl) ⟨1610864, by rfl⟩ : syracuseStep 2147819 = 3221729) B3221729
theorem B4835051 : Blo 1431535 4835051 := bstep (se 1 (by rfl) ⟨3626288, by rfl⟩ : syracuseStep 4835051 = 7252577) B7252577
theorem B4081535 : Blo 1431535 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B4081661 : Blo 1431535 4081661 := bstep (se 3 (by rfl) ⟨765311, by rfl⟩ : syracuseStep 4081661 = 1530623) B1530623
theorem B2148443 : Blo 1431535 2148443 := bstep (se 1 (by rfl) ⟨1611332, by rfl⟩ : syracuseStep 2148443 = 3222665) B3222665
theorem B2148479 : Blo 1431535 2148479 := bstep (se 1 (by rfl) ⟨1611359, by rfl⟩ : syracuseStep 2148479 = 3222719) B3222719
theorem B2148521 : Blo 1431535 2148521 := bstep (se 2 (by rfl) ⟨805695, by rfl⟩ : syracuseStep 2148521 = 1611391) B1611391
theorem B245065925 : Blo 1431535 245065925 := bstep (se 4 (by rfl) ⟨22974930, by rfl⟩ : syracuseStep 245065925 = 45949861) B45949861
theorem B3057871 : Blo 1431535 3057871 := bstep (se 1 (by rfl) ⟨2293403, by rfl⟩ : syracuseStep 3057871 = 4586807) B4586807
theorem B7252415 : Blo 1431535 7252415 := bstep (se 1 (by rfl) ⟨5439311, by rfl⟩ : syracuseStep 7252415 = 10878623) B10878623
theorem B3222107 : Blo 1431535 3222107 := bstep (se 1 (by rfl) ⟨2416580, by rfl⟩ : syracuseStep 3222107 = 4833161) B4833161
theorem B2149055 : Blo 1431535 2149055 := bstep (se 1 (by rfl) ⟨1611791, by rfl⟩ : syracuseStep 2149055 = 3223583) B3223583
theorem B2149247 : Blo 1431535 2149247 := bstep (se 1 (by rfl) ⟨1611935, by rfl⟩ : syracuseStep 2149247 = 3223871) B3223871
theorem B3222521 : Blo 1431535 3222521 := bstep (se 2 (by rfl) ⟨1208445, by rfl⟩ : syracuseStep 3222521 = 2416891) B2416891
theorem B12242279 : Blo 1431535 12242279 := bstep (se 1 (by rfl) ⟨9181709, by rfl⟩ : syracuseStep 12242279 = 18363419) B18363419
theorem B3059135 : Blo 1431535 3059135 := bstep (se 1 (by rfl) ⟨2294351, by rfl⟩ : syracuseStep 3059135 = 4588703) B4588703
theorem B2150303 : Blo 1431535 2150303 := bstep (se 1 (by rfl) ⟨1612727, by rfl⟩ : syracuseStep 2150303 = 3225455) B3225455
theorem B6115297 : Blo 1431535 6115297 := bstep (se 2 (by rfl) ⟨2293236, by rfl⟩ : syracuseStep 6115297 = 4586473) B4586473
theorem B6369277 : Blo 1431535 6369277 := bstep (se 3 (by rfl) ⟨1194239, by rfl⟩ : syracuseStep 6369277 = 2388479) B2388479
theorem B3625175 : Blo 1431535 3625175 := bstep (se 1 (by rfl) ⟨2718881, by rfl⟩ : syracuseStep 3625175 = 5437763) B5437763
theorem B27922745 : Blo 1431535 27922745 := bstep (se 2 (by rfl) ⟨10471029, by rfl⟩ : syracuseStep 27922745 = 20942059) B20942059
theorem B6116219 : Blo 1431535 6116219 := bstep (se 1 (by rfl) ⟨4587164, by rfl⟩ : syracuseStep 6116219 = 9174329) B9174329
theorem B16323767 : Blo 1431535 16323767 := bstep (se 1 (by rfl) ⟨12242825, by rfl⟩ : syracuseStep 16323767 = 24485651) B24485651
theorem B1963495 : Blo 1431535 1963495 := bstep (se 1 (by rfl) ⟨1472621, by rfl⟩ : syracuseStep 1963495 = 2945243) B2945243
theorem B3225383 : Blo 1431535 3225383 := bstep (se 1 (by rfl) ⟨2419037, by rfl⟩ : syracuseStep 3225383 = 4838075) B4838075
theorem B6117245 : Blo 1431535 6117245 := bstep (se 3 (by rfl) ⟨1146983, by rfl⟩ : syracuseStep 6117245 = 2293967) B2293967
theorem B15480953 : Blo 1431535 15480953 := bstep (se 2 (by rfl) ⟨5805357, by rfl⟩ : syracuseStep 15480953 = 11610715) B11610715
theorem B1431807 : Blo 1431535 1431807 := bstep (se 1 (by rfl) ⟨1073855, by rfl⟩ : syracuseStep 1431807 = 2147711) B2147711
theorem B3627463 : Blo 1431535 3627463 := bstep (se 1 (by rfl) ⟨2720597, by rfl⟩ : syracuseStep 3627463 = 5441195) B5441195
theorem B1432063 : Blo 1431535 1432063 := bstep (se 1 (by rfl) ⟨1074047, by rfl⟩ : syracuseStep 1432063 = 2148095) B2148095
theorem B1432559 : Blo 1431535 1432559 := bstep (se 1 (by rfl) ⟨1074419, by rfl⟩ : syracuseStep 1432559 = 2148839) B2148839
theorem B3628223 : Blo 1431535 3628223 := bstep (se 1 (by rfl) ⟨2721167, by rfl⟩ : syracuseStep 3628223 = 5442335) B5442335
theorem B47734379 : Blo 1431535 47734379 := bstep (se 1 (by rfl) ⟨35800784, by rfl⟩ : syracuseStep 47734379 = 71601569) B71601569
theorem B1433215 : Blo 1431535 1433215 := bstep (se 1 (by rfl) ⟨1074911, by rfl⟩ : syracuseStep 1433215 = 2149823) B2149823
theorem B82550501 : Blo 1431535 82550501 := bstep (se 4 (by rfl) ⟨7739109, by rfl⟩ : syracuseStep 82550501 = 15478219) B15478219
theorem B2416783 : Blo 1431535 2416783 := bstep (se 1 (by rfl) ⟨1812587, by rfl⟩ : syracuseStep 2416783 = 3625175) B3625175
theorem B5439905 : Blo 1431535 5439905 := bstep (se 2 (by rfl) ⟨2039964, by rfl⟩ : syracuseStep 5439905 = 4079929) B4079929
theorem B16548329 : Blo 1431535 16548329 := bstep (se 2 (by rfl) ⟨6205623, by rfl⟩ : syracuseStep 16548329 = 12411247) B12411247
theorem B2721023 : Blo 1431535 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B2721107 : Blo 1431535 2721107 := bstep (se 1 (by rfl) ⟨2040830, by rfl⟩ : syracuseStep 2721107 = 4081661) B4081661
theorem B4834943 : Blo 1431535 4834943 := bstep (se 1 (by rfl) ⟨3626207, by rfl⟩ : syracuseStep 4834943 = 7252415) B7252415
theorem B2148071 : Blo 1431535 2148071 := bstep (se 1 (by rfl) ⟨1611053, by rfl⟩ : syracuseStep 2148071 = 3222107) B3222107
theorem B2148347 : Blo 1431535 2148347 := bstep (se 1 (by rfl) ⟨1611260, by rfl⟩ : syracuseStep 2148347 = 3222521) B3222521
theorem B2418815 : Blo 1431535 2418815 := bstep (se 1 (by rfl) ⟨1814111, by rfl⟩ : syracuseStep 2418815 = 3628223) B3628223
theorem B8161519 : Blo 1431535 8161519 := bstep (se 1 (by rfl) ⟨6121139, by rfl⟩ : syracuseStep 8161519 = 12242279) B12242279
theorem B8153729 : Blo 1431535 8153729 := bstep (se 2 (by rfl) ⟨3057648, by rfl⟩ : syracuseStep 8153729 = 6115297) B6115297
theorem B3222431 : Blo 1431535 3222431 := bstep (se 1 (by rfl) ⟨2416823, by rfl⟩ : syracuseStep 3222431 = 4833647) B4833647
theorem B4836617 : Blo 1431535 4836617 := bstep (se 2 (by rfl) ⟨1813731, by rfl⟩ : syracuseStep 4836617 = 3627463) B3627463
theorem B10882511 : Blo 1431535 10882511 := bstep (se 1 (by rfl) ⟨8161883, by rfl⟩ : syracuseStep 10882511 = 16323767) B16323767
theorem B74460653 : Blo 1431535 74460653 := bstep (se 3 (by rfl) ⟨13961372, by rfl⟩ : syracuseStep 74460653 = 27922745) B27922745
theorem B3223367 : Blo 1431535 3223367 := bstep (se 1 (by rfl) ⟨2417525, by rfl⟩ : syracuseStep 3223367 = 4835051) B4835051
theorem B2150255 : Blo 1431535 2150255 := bstep (se 1 (by rfl) ⟨1612691, by rfl⟩ : syracuseStep 2150255 = 3225383) B3225383
theorem B163377283 : Blo 1431535 163377283 := bstep (se 1 (by rfl) ⟨122532962, by rfl⟩ : syracuseStep 163377283 = 245065925) B245065925
theorem B2617993 : Blo 1431535 2617993 := bstep (se 2 (by rfl) ⟨981747, by rfl⟩ : syracuseStep 2617993 = 1963495) B1963495
theorem B31822919 : Blo 1431535 31822919 := bstep (se 1 (by rfl) ⟨23867189, by rfl⟩ : syracuseStep 31822919 = 47734379) B47734379
theorem B8492369 : Blo 1431535 8492369 := bstep (se 2 (by rfl) ⟨3184638, by rfl⟩ : syracuseStep 8492369 = 6369277) B6369277
theorem B4077161 : Blo 1431535 4077161 := bstep (se 2 (by rfl) ⟨1528935, by rfl⟩ : syracuseStep 4077161 = 3057871) B3057871
theorem B4077479 : Blo 1431535 4077479 := bstep (se 1 (by rfl) ⟨3058109, by rfl⟩ : syracuseStep 4077479 = 6116219) B6116219
theorem B176527295 : Blo 1431535 176527295 := bstep (se 1 (by rfl) ⟨132395471, by rfl⟩ : syracuseStep 176527295 = 264790943) B264790943
theorem B1431599 : Blo 1431535 1431599 := bstep (se 1 (by rfl) ⟨1073699, by rfl⟩ : syracuseStep 1431599 = 2147399) B2147399
theorem B1431879 : Blo 1431535 1431879 := bstep (se 1 (by rfl) ⟨1073909, by rfl⟩ : syracuseStep 1431879 = 2147819) B2147819
theorem B4078163 : Blo 1431535 4078163 := bstep (se 1 (by rfl) ⟨3058622, by rfl⟩ : syracuseStep 4078163 = 6117245) B6117245
theorem B1432295 : Blo 1431535 1432295 := bstep (se 1 (by rfl) ⟨1074221, by rfl⟩ : syracuseStep 1432295 = 2148443) B2148443
theorem B10320635 : Blo 1431535 10320635 := bstep (se 1 (by rfl) ⟨7740476, by rfl⟩ : syracuseStep 10320635 = 15480953) B15480953
theorem B1432319 : Blo 1431535 1432319 := bstep (se 1 (by rfl) ⟨1074239, by rfl⟩ : syracuseStep 1432319 = 2148479) B2148479
theorem B1432347 : Blo 1431535 1432347 := bstep (se 1 (by rfl) ⟨1074260, by rfl⟩ : syracuseStep 1432347 = 2148521) B2148521
theorem B1432703 : Blo 1431535 1432703 := bstep (se 1 (by rfl) ⟨1074527, by rfl⟩ : syracuseStep 1432703 = 2149055) B2149055
theorem B1432831 : Blo 1431535 1432831 := bstep (se 1 (by rfl) ⟨1074623, by rfl⟩ : syracuseStep 1432831 = 2149247) B2149247
theorem B2039423 : Blo 1431535 2039423 := bstep (se 1 (by rfl) ⟨1529567, by rfl⟩ : syracuseStep 2039423 = 3059135) B3059135
theorem B55033667 : Blo 1431535 55033667 := bstep (se 1 (by rfl) ⟨41275250, by rfl⟩ : syracuseStep 55033667 = 82550501) B82550501
theorem B1433535 : Blo 1431535 1433535 := bstep (se 1 (by rfl) ⟨1075151, by rfl⟩ : syracuseStep 1433535 = 2150303) B2150303
theorem B3490657 : Blo 1431535 3490657 := bstep (se 2 (by rfl) ⟨1308996, by rfl⟩ : syracuseStep 3490657 = 2617993) B2617993
theorem B2148287 : Blo 1431535 2148287 := bstep (se 1 (by rfl) ⟨1611215, by rfl⟩ : syracuseStep 2148287 = 3222431) B3222431
theorem B10873277 : Blo 1431535 10873277 := bstep (se 3 (by rfl) ⟨2038739, by rfl⟩ : syracuseStep 10873277 = 4077479) B4077479
theorem B2148911 : Blo 1431535 2148911 := bstep (se 1 (by rfl) ⟨1611683, by rfl⟩ : syracuseStep 2148911 = 3223367) B3223367
theorem B217836377 : Blo 1431535 217836377 := bstep (se 2 (by rfl) ⟨81688641, by rfl⟩ : syracuseStep 217836377 = 163377283) B163377283
theorem B3222377 : Blo 1431535 3222377 := bstep (se 2 (by rfl) ⟨1208391, by rfl⟩ : syracuseStep 3222377 = 2416783) B2416783
theorem B10882025 : Blo 1431535 10882025 := bstep (se 2 (by rfl) ⟨4080759, by rfl⟩ : syracuseStep 10882025 = 8161519) B8161519
theorem B1814015 : Blo 1431535 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B22646317 : Blo 1431535 22646317 := bstep (se 3 (by rfl) ⟨4246184, by rfl⟩ : syracuseStep 22646317 = 8492369) B8492369
theorem B1814071 : Blo 1431535 1814071 := bstep (se 1 (by rfl) ⟨1360553, by rfl⟩ : syracuseStep 1814071 = 2721107) B2721107
theorem B3223295 : Blo 1431535 3223295 := bstep (se 1 (by rfl) ⟨2417471, by rfl⟩ : syracuseStep 3223295 = 4834943) B4834943
theorem B5435819 : Blo 1431535 5435819 := bstep (se 1 (by rfl) ⟨4076864, by rfl⟩ : syracuseStep 5435819 = 8153729) B8153729
theorem B3224411 : Blo 1431535 3224411 := bstep (se 1 (by rfl) ⟨2418308, by rfl⟩ : syracuseStep 3224411 = 4836617) B4836617
theorem B7255007 : Blo 1431535 7255007 := bstep (se 1 (by rfl) ⟨5441255, by rfl⟩ : syracuseStep 7255007 = 10882511) B10882511
theorem B49640435 : Blo 1431535 49640435 := bstep (se 1 (by rfl) ⟨37230326, by rfl⟩ : syracuseStep 49640435 = 74460653) B74460653
theorem B36689111 : Blo 1431535 36689111 := bstep (se 1 (by rfl) ⟨27516833, by rfl⟩ : syracuseStep 36689111 = 55033667) B55033667
theorem B3626603 : Blo 1431535 3626603 := bstep (se 1 (by rfl) ⟨2719952, by rfl⟩ : syracuseStep 3626603 = 5439905) B5439905
theorem B11032219 : Blo 1431535 11032219 := bstep (se 1 (by rfl) ⟨8274164, by rfl⟩ : syracuseStep 11032219 = 16548329) B16548329
theorem B21215279 : Blo 1431535 21215279 := bstep (se 1 (by rfl) ⟨15911459, by rfl⟩ : syracuseStep 21215279 = 31822919) B31822919
theorem B2718107 : Blo 1431535 2718107 := bstep (se 1 (by rfl) ⟨2038580, by rfl⟩ : syracuseStep 2718107 = 4077161) B4077161
theorem B1432047 : Blo 1431535 1432047 := bstep (se 1 (by rfl) ⟨1074035, by rfl⟩ : syracuseStep 1432047 = 2148071) B2148071
theorem B117684863 : Blo 1431535 117684863 := bstep (se 1 (by rfl) ⟨88263647, by rfl⟩ : syracuseStep 117684863 = 176527295) B176527295
theorem B1432231 : Blo 1431535 1432231 := bstep (se 1 (by rfl) ⟨1074173, by rfl⟩ : syracuseStep 1432231 = 2148347) B2148347
theorem B1612543 : Blo 1431535 1612543 := bstep (se 1 (by rfl) ⟨1209407, by rfl⟩ : syracuseStep 1612543 = 2418815) B2418815
theorem B5438461 : Blo 1431535 5438461 := bstep (se 3 (by rfl) ⟨1019711, by rfl⟩ : syracuseStep 5438461 = 2039423) B2039423
theorem B2718775 : Blo 1431535 2718775 := bstep (se 1 (by rfl) ⟨2039081, by rfl⟩ : syracuseStep 2718775 = 4078163) B4078163
theorem B6880423 : Blo 1431535 6880423 := bstep (se 1 (by rfl) ⟨5160317, by rfl⟩ : syracuseStep 6880423 = 10320635) B10320635
theorem B1433503 : Blo 1431535 1433503 := bstep (se 1 (by rfl) ⟨1075127, by rfl⟩ : syracuseStep 1433503 = 2150255) B2150255
theorem B2417735 : Blo 1431535 2417735 := bstep (se 1 (by rfl) ⟨1813301, by rfl⟩ : syracuseStep 2417735 = 3626603) B3626603
theorem B7251281 : Blo 1431535 7251281 := bstep (se 2 (by rfl) ⟨2719230, by rfl⟩ : syracuseStep 7251281 = 5438461) B5438461
theorem B1812071 : Blo 1431535 1812071 := bstep (se 1 (by rfl) ⟨1359053, by rfl⟩ : syracuseStep 1812071 = 2718107) B2718107
theorem B78456575 : Blo 1431535 78456575 := bstep (se 1 (by rfl) ⟨58842431, by rfl⟩ : syracuseStep 78456575 = 117684863) B117684863
theorem B2148251 : Blo 1431535 2148251 := bstep (se 1 (by rfl) ⟨1611188, by rfl⟩ : syracuseStep 2148251 = 3222377) B3222377
theorem B2418761 : Blo 1431535 2418761 := bstep (se 2 (by rfl) ⟨907035, by rfl⟩ : syracuseStep 2418761 = 1814071) B1814071
theorem B2148863 : Blo 1431535 2148863 := bstep (se 1 (by rfl) ⟨1611647, by rfl⟩ : syracuseStep 2148863 = 3223295) B3223295
theorem B3623879 : Blo 1431535 3623879 := bstep (se 1 (by rfl) ⟨2717909, by rfl⟩ : syracuseStep 3623879 = 5435819) B5435819
theorem B2149607 : Blo 1431535 2149607 := bstep (se 1 (by rfl) ⟨1612205, by rfl⟩ : syracuseStep 2149607 = 3224411) B3224411
theorem B4836671 : Blo 1431535 4836671 := bstep (se 1 (by rfl) ⟨3627503, by rfl⟩ : syracuseStep 4836671 = 7255007) B7255007
theorem B58838501 : Blo 1431535 58838501 := bstep (se 4 (by rfl) ⟨5516109, by rfl⟩ : syracuseStep 58838501 = 11032219) B11032219
theorem B2150057 : Blo 1431535 2150057 := bstep (se 2 (by rfl) ⟨806271, by rfl⟩ : syracuseStep 2150057 = 1612543) B1612543
theorem B4837373 : Blo 1431535 4837373 := bstep (se 3 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 4837373 = 1814015) B1814015
theorem B14143519 : Blo 1431535 14143519 := bstep (se 1 (by rfl) ⟨10607639, by rfl⟩ : syracuseStep 14143519 = 21215279) B21215279
theorem B3625033 : Blo 1431535 3625033 := bstep (se 2 (by rfl) ⟨1359387, by rfl⟩ : syracuseStep 3625033 = 2718775) B2718775
theorem B18616837 : Blo 1431535 18616837 := bstep (se 4 (by rfl) ⟨1745328, by rfl⟩ : syracuseStep 18616837 = 3490657) B3490657
theorem B145224251 : Blo 1431535 145224251 := bstep (se 1 (by rfl) ⟨108918188, by rfl⟩ : syracuseStep 145224251 = 217836377) B217836377
theorem B7254683 : Blo 1431535 7254683 := bstep (se 1 (by rfl) ⟨5441012, by rfl⟩ : syracuseStep 7254683 = 10882025) B10882025
theorem B33093623 : Blo 1431535 33093623 := bstep (se 1 (by rfl) ⟨24820217, by rfl⟩ : syracuseStep 33093623 = 49640435) B49640435
theorem B24459407 : Blo 1431535 24459407 := bstep (se 1 (by rfl) ⟨18344555, by rfl⟩ : syracuseStep 24459407 = 36689111) B36689111
theorem B1432191 : Blo 1431535 1432191 := bstep (se 1 (by rfl) ⟨1074143, by rfl⟩ : syracuseStep 1432191 = 2148287) B2148287
theorem B9173897 : Blo 1431535 9173897 := bstep (se 2 (by rfl) ⟨3440211, by rfl⟩ : syracuseStep 9173897 = 6880423) B6880423
theorem B7248851 : Blo 1431535 7248851 := bstep (se 1 (by rfl) ⟨5436638, by rfl⟩ : syracuseStep 7248851 = 10873277) B10873277
theorem B1432607 : Blo 1431535 1432607 := bstep (se 1 (by rfl) ⟨1074455, by rfl⟩ : syracuseStep 1432607 = 2148911) B2148911
theorem B30195089 : Blo 1431535 30195089 := bstep (se 2 (by rfl) ⟨11323158, by rfl⟩ : syracuseStep 30195089 = 22646317) B22646317
theorem B18858025 : Blo 1431535 18858025 := bstep (se 2 (by rfl) ⟨7071759, by rfl⟩ : syracuseStep 18858025 = 14143519) B14143519
theorem B4833377 : Blo 1431535 4833377 := bstep (se 2 (by rfl) ⟨1812516, by rfl⟩ : syracuseStep 4833377 = 3625033) B3625033
theorem B24822449 : Blo 1431535 24822449 := bstep (se 2 (by rfl) ⟨9308418, by rfl⟩ : syracuseStep 24822449 = 18616837) B18616837
theorem B4834187 : Blo 1431535 4834187 := bstep (se 1 (by rfl) ⟨3625640, by rfl⟩ : syracuseStep 4834187 = 7251281) B7251281
theorem B22062415 : Blo 1431535 22062415 := bstep (se 1 (by rfl) ⟨16546811, by rfl⟩ : syracuseStep 22062415 = 33093623) B33093623
theorem B20130059 : Blo 1431535 20130059 := bstep (se 1 (by rfl) ⟨15097544, by rfl⟩ : syracuseStep 20130059 = 30195089) B30195089
theorem B39225667 : Blo 1431535 39225667 := bstep (se 1 (by rfl) ⟨29419250, by rfl⟩ : syracuseStep 39225667 = 58838501) B58838501
theorem B96816167 : Blo 1431535 96816167 := bstep (se 1 (by rfl) ⟨72612125, by rfl⟩ : syracuseStep 96816167 = 145224251) B145224251
theorem B4836455 : Blo 1431535 4836455 := bstep (se 1 (by rfl) ⟨3627341, by rfl⟩ : syracuseStep 4836455 = 7254683) B7254683
theorem B16306271 : Blo 1431535 16306271 := bstep (se 1 (by rfl) ⟨12229703, by rfl⟩ : syracuseStep 16306271 = 24459407) B24459407
theorem B6115931 : Blo 1431535 6115931 := bstep (se 1 (by rfl) ⟨4586948, by rfl⟩ : syracuseStep 6115931 = 9173897) B9173897
theorem B3224447 : Blo 1431535 3224447 := bstep (se 1 (by rfl) ⟨2418335, by rfl⟩ : syracuseStep 3224447 = 4836671) B4836671
theorem B3224915 : Blo 1431535 3224915 := bstep (se 1 (by rfl) ⟨2418686, by rfl⟩ : syracuseStep 3224915 = 4837373) B4837373
theorem B1611823 : Blo 1431535 1611823 := bstep (se 1 (by rfl) ⟨1208867, by rfl⟩ : syracuseStep 1611823 = 2417735) B2417735
theorem B52304383 : Blo 1431535 52304383 := bstep (se 1 (by rfl) ⟨39228287, by rfl⟩ : syracuseStep 52304383 = 78456575) B78456575
theorem B1432167 : Blo 1431535 1432167 := bstep (se 1 (by rfl) ⟨1074125, by rfl⟩ : syracuseStep 1432167 = 2148251) B2148251
theorem B1612507 : Blo 1431535 1612507 := bstep (se 1 (by rfl) ⟨1209380, by rfl⟩ : syracuseStep 1612507 = 2418761) B2418761
theorem B4832189 : Blo 1431535 4832189 := bstep (se 3 (by rfl) ⟨906035, by rfl⟩ : syracuseStep 4832189 = 1812071) B1812071
theorem B1432575 : Blo 1431535 1432575 := bstep (se 1 (by rfl) ⟨1074431, by rfl⟩ : syracuseStep 1432575 = 2148863) B2148863
theorem B2415919 : Blo 1431535 2415919 := bstep (se 1 (by rfl) ⟨1811939, by rfl⟩ : syracuseStep 2415919 = 3623879) B3623879
theorem B4832567 : Blo 1431535 4832567 := bstep (se 1 (by rfl) ⟨3624425, by rfl⟩ : syracuseStep 4832567 = 7248851) B7248851
theorem B1433071 : Blo 1431535 1433071 := bstep (se 1 (by rfl) ⟨1074803, by rfl⟩ : syracuseStep 1433071 = 2149607) B2149607
theorem B1433371 : Blo 1431535 1433371 := bstep (se 1 (by rfl) ⟨1075028, by rfl⟩ : syracuseStep 1433371 = 2150057) B2150057
theorem B10870847 : Blo 1431535 10870847 := bstep (se 1 (by rfl) ⟨8153135, by rfl⟩ : syracuseStep 10870847 = 16306271) B16306271
theorem B16548299 : Blo 1431535 16548299 := bstep (se 1 (by rfl) ⟨12411224, by rfl⟩ : syracuseStep 16548299 = 24822449) B24822449
theorem B69739177 : Blo 1431535 69739177 := bstep (se 2 (by rfl) ⟨26152191, by rfl⟩ : syracuseStep 69739177 = 52304383) B52304383
theorem B13420039 : Blo 1431535 13420039 := bstep (se 1 (by rfl) ⟨10065029, by rfl⟩ : syracuseStep 13420039 = 20130059) B20130059
theorem B3221225 : Blo 1431535 3221225 := bstep (se 2 (by rfl) ⟨1207959, by rfl⟩ : syracuseStep 3221225 = 2415919) B2415919
theorem B3221459 : Blo 1431535 3221459 := bstep (se 1 (by rfl) ⟨2416094, by rfl⟩ : syracuseStep 3221459 = 4832189) B4832189
theorem B3221711 : Blo 1431535 3221711 := bstep (se 1 (by rfl) ⟨2416283, by rfl⟩ : syracuseStep 3221711 = 4832567) B4832567
theorem B2149097 : Blo 1431535 2149097 := bstep (se 2 (by rfl) ⟨805911, by rfl⟩ : syracuseStep 2149097 = 1611823) B1611823
theorem B3222251 : Blo 1431535 3222251 := bstep (se 1 (by rfl) ⟨2416688, by rfl⟩ : syracuseStep 3222251 = 4833377) B4833377
theorem B100576133 : Blo 1431535 100576133 := bstep (se 4 (by rfl) ⟨9429012, by rfl⟩ : syracuseStep 100576133 = 18858025) B18858025
theorem B52300889 : Blo 1431535 52300889 := bstep (se 2 (by rfl) ⟨19612833, by rfl⟩ : syracuseStep 52300889 = 39225667) B39225667
theorem B2149631 : Blo 1431535 2149631 := bstep (se 1 (by rfl) ⟨1612223, by rfl⟩ : syracuseStep 2149631 = 3224447) B3224447
theorem B3222791 : Blo 1431535 3222791 := bstep (se 1 (by rfl) ⟨2417093, by rfl⟩ : syracuseStep 3222791 = 4834187) B4834187
theorem B2149943 : Blo 1431535 2149943 := bstep (se 1 (by rfl) ⟨1612457, by rfl⟩ : syracuseStep 2149943 = 3224915) B3224915
theorem B2150009 : Blo 1431535 2150009 := bstep (se 2 (by rfl) ⟨806253, by rfl⟩ : syracuseStep 2150009 = 1612507) B1612507
theorem B3224303 : Blo 1431535 3224303 := bstep (se 1 (by rfl) ⟨2418227, by rfl⟩ : syracuseStep 3224303 = 4836455) B4836455
theorem B4077287 : Blo 1431535 4077287 := bstep (se 1 (by rfl) ⟨3057965, by rfl⟩ : syracuseStep 4077287 = 6115931) B6115931
theorem B29416553 : Blo 1431535 29416553 := bstep (se 2 (by rfl) ⟨11031207, by rfl⟩ : syracuseStep 29416553 = 22062415) B22062415
theorem B64544111 : Blo 1431535 64544111 := bstep (se 1 (by rfl) ⟨48408083, by rfl⟩ : syracuseStep 64544111 = 96816167) B96816167
theorem B2147483 : Blo 1431535 2147483 := bstep (se 1 (by rfl) ⟨1610612, by rfl⟩ : syracuseStep 2147483 = 3221225) B3221225
theorem B2147639 : Blo 1431535 2147639 := bstep (se 1 (by rfl) ⟨1610729, by rfl⟩ : syracuseStep 2147639 = 3221459) B3221459
theorem B2147807 : Blo 1431535 2147807 := bstep (se 1 (by rfl) ⟨1610855, by rfl⟩ : syracuseStep 2147807 = 3221711) B3221711
theorem B2148167 : Blo 1431535 2148167 := bstep (se 1 (by rfl) ⟨1611125, by rfl⟩ : syracuseStep 2148167 = 3222251) B3222251
theorem B17893385 : Blo 1431535 17893385 := bstep (se 2 (by rfl) ⟨6710019, by rfl⟩ : syracuseStep 17893385 = 13420039) B13420039
theorem B34867259 : Blo 1431535 34867259 := bstep (se 1 (by rfl) ⟨26150444, by rfl⟩ : syracuseStep 34867259 = 52300889) B52300889
theorem B2148527 : Blo 1431535 2148527 := bstep (se 1 (by rfl) ⟨1611395, by rfl⟩ : syracuseStep 2148527 = 3222791) B3222791
theorem B2149535 : Blo 1431535 2149535 := bstep (se 1 (by rfl) ⟨1612151, by rfl⟩ : syracuseStep 2149535 = 3224303) B3224303
theorem B43029407 : Blo 1431535 43029407 := bstep (se 1 (by rfl) ⟨32272055, by rfl⟩ : syracuseStep 43029407 = 64544111) B64544111
theorem B7247231 : Blo 1431535 7247231 := bstep (se 1 (by rfl) ⟨5435423, by rfl⟩ : syracuseStep 7247231 = 10870847) B10870847
theorem B11032199 : Blo 1431535 11032199 := bstep (se 1 (by rfl) ⟨8274149, by rfl⟩ : syracuseStep 11032199 = 16548299) B16548299
theorem B92985569 : Blo 1431535 92985569 := bstep (se 2 (by rfl) ⟨34869588, by rfl⟩ : syracuseStep 92985569 = 69739177) B69739177
theorem B2718191 : Blo 1431535 2718191 := bstep (se 1 (by rfl) ⟨2038643, by rfl⟩ : syracuseStep 2718191 = 4077287) B4077287
theorem B1432731 : Blo 1431535 1432731 := bstep (se 1 (by rfl) ⟨1074548, by rfl⟩ : syracuseStep 1432731 = 2149097) B2149097
theorem B67050755 : Blo 1431535 67050755 := bstep (se 1 (by rfl) ⟨50288066, by rfl⟩ : syracuseStep 67050755 = 100576133) B100576133
theorem B19611035 : Blo 1431535 19611035 := bstep (se 1 (by rfl) ⟨14708276, by rfl⟩ : syracuseStep 19611035 = 29416553) B29416553
theorem B1433087 : Blo 1431535 1433087 := bstep (se 1 (by rfl) ⟨1074815, by rfl⟩ : syracuseStep 1433087 = 2149631) B2149631
theorem B1433295 : Blo 1431535 1433295 := bstep (se 1 (by rfl) ⟨1074971, by rfl⟩ : syracuseStep 1433295 = 2149943) B2149943
theorem B1433339 : Blo 1431535 1433339 := bstep (se 1 (by rfl) ⟨1075004, by rfl⟩ : syracuseStep 1433339 = 2150009) B2150009
theorem B11928923 : Blo 1431535 11928923 := bstep (se 1 (by rfl) ⟨8946692, by rfl⟩ : syracuseStep 11928923 = 17893385) B17893385
theorem B61990379 : Blo 1431535 61990379 := bstep (se 1 (by rfl) ⟨46492784, by rfl⟩ : syracuseStep 61990379 = 92985569) B92985569
theorem B1812127 : Blo 1431535 1812127 := bstep (se 1 (by rfl) ⟨1359095, by rfl⟩ : syracuseStep 1812127 = 2718191) B2718191
theorem B23244839 : Blo 1431535 23244839 := bstep (se 1 (by rfl) ⟨17433629, by rfl⟩ : syracuseStep 23244839 = 34867259) B34867259
theorem B44700503 : Blo 1431535 44700503 := bstep (se 1 (by rfl) ⟨33525377, by rfl⟩ : syracuseStep 44700503 = 67050755) B67050755
theorem B28686271 : Blo 1431535 28686271 := bstep (se 1 (by rfl) ⟨21514703, by rfl⟩ : syracuseStep 28686271 = 43029407) B43029407
theorem B1431655 : Blo 1431535 1431655 := bstep (se 1 (by rfl) ⟨1073741, by rfl⟩ : syracuseStep 1431655 = 2147483) B2147483
theorem B1431759 : Blo 1431535 1431759 := bstep (se 1 (by rfl) ⟨1073819, by rfl⟩ : syracuseStep 1431759 = 2147639) B2147639
theorem B4831487 : Blo 1431535 4831487 := bstep (se 1 (by rfl) ⟨3623615, by rfl⟩ : syracuseStep 4831487 = 7247231) B7247231
theorem B1431871 : Blo 1431535 1431871 := bstep (se 1 (by rfl) ⟨1073903, by rfl⟩ : syracuseStep 1431871 = 2147807) B2147807
theorem B7354799 : Blo 1431535 7354799 := bstep (se 1 (by rfl) ⟨5516099, by rfl⟩ : syracuseStep 7354799 = 11032199) B11032199
theorem B1432111 : Blo 1431535 1432111 := bstep (se 1 (by rfl) ⟨1074083, by rfl⟩ : syracuseStep 1432111 = 2148167) B2148167
theorem B1432351 : Blo 1431535 1432351 := bstep (se 1 (by rfl) ⟨1074263, by rfl⟩ : syracuseStep 1432351 = 2148527) B2148527
theorem B1433023 : Blo 1431535 1433023 := bstep (se 1 (by rfl) ⟨1074767, by rfl⟩ : syracuseStep 1433023 = 2149535) B2149535
theorem B13074023 : Blo 1431535 13074023 := bstep (se 1 (by rfl) ⟨9805517, by rfl⟩ : syracuseStep 13074023 = 19611035) B19611035
theorem B3220991 : Blo 1431535 3220991 := bstep (se 1 (by rfl) ⟨2415743, by rfl⟩ : syracuseStep 3220991 = 4831487) B4831487
theorem B4903199 : Blo 1431535 4903199 := bstep (se 1 (by rfl) ⟨3677399, by rfl⟩ : syracuseStep 4903199 = 7354799) B7354799
theorem B15496559 : Blo 1431535 15496559 := bstep (se 1 (by rfl) ⟨11622419, by rfl⟩ : syracuseStep 15496559 = 23244839) B23244839
theorem B7952615 : Blo 1431535 7952615 := bstep (se 1 (by rfl) ⟨5964461, by rfl⟩ : syracuseStep 7952615 = 11928923) B11928923
theorem B41326919 : Blo 1431535 41326919 := bstep (se 1 (by rfl) ⟨30995189, by rfl⟩ : syracuseStep 41326919 = 61990379) B61990379
theorem B2416169 : Blo 1431535 2416169 := bstep (se 2 (by rfl) ⟨906063, by rfl⟩ : syracuseStep 2416169 = 1812127) B1812127
theorem B119201341 : Blo 1431535 119201341 := bstep (se 3 (by rfl) ⟨22350251, by rfl⟩ : syracuseStep 119201341 = 44700503) B44700503
theorem B8716015 : Blo 1431535 8716015 := bstep (se 1 (by rfl) ⟨6537011, by rfl⟩ : syracuseStep 8716015 = 13074023) B13074023
theorem B38248361 : Blo 1431535 38248361 := bstep (se 2 (by rfl) ⟨14343135, by rfl⟩ : syracuseStep 38248361 = 28686271) B28686271
theorem B3268799 : Blo 1431535 3268799 := bstep (se 1 (by rfl) ⟨2451599, by rfl⟩ : syracuseStep 3268799 = 4903199) B4903199
theorem B10331039 : Blo 1431535 10331039 := bstep (se 1 (by rfl) ⟨7748279, by rfl⟩ : syracuseStep 10331039 = 15496559) B15496559
theorem B2147327 : Blo 1431535 2147327 := bstep (se 1 (by rfl) ⟨1610495, by rfl⟩ : syracuseStep 2147327 = 3220991) B3220991
theorem B5301743 : Blo 1431535 5301743 := bstep (se 1 (by rfl) ⟨3976307, by rfl⟩ : syracuseStep 5301743 = 7952615) B7952615
theorem B27551279 : Blo 1431535 27551279 := bstep (se 1 (by rfl) ⟨20663459, by rfl⟩ : syracuseStep 27551279 = 41326919) B41326919
theorem B158935121 : Blo 1431535 158935121 := bstep (se 2 (by rfl) ⟨59600670, by rfl⟩ : syracuseStep 158935121 = 119201341) B119201341
theorem B11621353 : Blo 1431535 11621353 := bstep (se 2 (by rfl) ⟨4358007, by rfl⟩ : syracuseStep 11621353 = 8716015) B8716015
theorem B1610779 : Blo 1431535 1610779 := bstep (se 1 (by rfl) ⟨1208084, by rfl⟩ : syracuseStep 1610779 = 2416169) B2416169
theorem B25498907 : Blo 1431535 25498907 := bstep (se 1 (by rfl) ⟨19124180, by rfl⟩ : syracuseStep 25498907 = 38248361) B38248361
theorem B2179199 : Blo 1431535 2179199 := bstep (se 1 (by rfl) ⟨1634399, by rfl⟩ : syracuseStep 2179199 = 3268799) B3268799
theorem B16999271 : Blo 1431535 16999271 := bstep (se 1 (by rfl) ⟨12749453, by rfl⟩ : syracuseStep 16999271 = 25498907) B25498907
theorem B18367519 : Blo 1431535 18367519 := bstep (se 1 (by rfl) ⟨13775639, by rfl⟩ : syracuseStep 18367519 = 27551279) B27551279
theorem B2147705 : Blo 1431535 2147705 := bstep (se 2 (by rfl) ⟨805389, by rfl⟩ : syracuseStep 2147705 = 1610779) B1610779
theorem B105956747 : Blo 1431535 105956747 := bstep (se 1 (by rfl) ⟨79467560, by rfl⟩ : syracuseStep 105956747 = 158935121) B158935121
theorem B56551925 : Blo 1431535 56551925 := bstep (se 5 (by rfl) ⟨2650871, by rfl⟩ : syracuseStep 56551925 = 5301743) B5301743
theorem B15495137 : Blo 1431535 15495137 := bstep (se 2 (by rfl) ⟨5810676, by rfl⟩ : syracuseStep 15495137 = 11621353) B11621353
theorem B6887359 : Blo 1431535 6887359 := bstep (se 1 (by rfl) ⟨5165519, by rfl⟩ : syracuseStep 6887359 = 10331039) B10331039
theorem B1431551 : Blo 1431535 1431551 := bstep (se 1 (by rfl) ⟨1073663, by rfl⟩ : syracuseStep 1431551 = 2147327) B2147327
theorem B37701283 : Blo 1431535 37701283 := bstep (se 1 (by rfl) ⟨28275962, by rfl⟩ : syracuseStep 37701283 = 56551925) B56551925
theorem B1452799 : Blo 1431535 1452799 := bstep (se 1 (by rfl) ⟨1089599, by rfl⟩ : syracuseStep 1452799 = 2179199) B2179199
theorem B11332847 : Blo 1431535 11332847 := bstep (se 1 (by rfl) ⟨8499635, by rfl⟩ : syracuseStep 11332847 = 16999271) B16999271
theorem B24490025 : Blo 1431535 24490025 := bstep (se 2 (by rfl) ⟨9183759, by rfl⟩ : syracuseStep 24490025 = 18367519) B18367519
theorem B1431803 : Blo 1431535 1431803 := bstep (se 1 (by rfl) ⟨1073852, by rfl⟩ : syracuseStep 1431803 = 2147705) B2147705
theorem B70637831 : Blo 1431535 70637831 := bstep (se 1 (by rfl) ⟨52978373, by rfl⟩ : syracuseStep 70637831 = 105956747) B105956747
theorem B9183145 : Blo 1431535 9183145 := bstep (se 2 (by rfl) ⟨3443679, by rfl⟩ : syracuseStep 9183145 = 6887359) B6887359
theorem B10330091 : Blo 1431535 10330091 := bstep (se 1 (by rfl) ⟨7747568, by rfl⟩ : syracuseStep 10330091 = 15495137) B15495137
theorem B16326683 : Blo 1431535 16326683 := bstep (se 1 (by rfl) ⟨12245012, by rfl⟩ : syracuseStep 16326683 = 24490025) B24490025
theorem B7555231 : Blo 1431535 7555231 := bstep (se 1 (by rfl) ⟨5666423, by rfl⟩ : syracuseStep 7555231 = 11332847) B11332847
theorem B50268377 : Blo 1431535 50268377 := bstep (se 2 (by rfl) ⟨18850641, by rfl⟩ : syracuseStep 50268377 = 37701283) B37701283
theorem B47091887 : Blo 1431535 47091887 := bstep (se 1 (by rfl) ⟨35318915, by rfl⟩ : syracuseStep 47091887 = 70637831) B70637831
theorem B12244193 : Blo 1431535 12244193 := bstep (se 2 (by rfl) ⟨4591572, by rfl⟩ : syracuseStep 12244193 = 9183145) B9183145
theorem B6886727 : Blo 1431535 6886727 := bstep (se 1 (by rfl) ⟨5165045, by rfl⟩ : syracuseStep 6886727 = 10330091) B10330091
theorem B7748261 : Blo 1431535 7748261 := bstep (se 4 (by rfl) ⟨726399, by rfl⟩ : syracuseStep 7748261 = 1452799) B1452799
theorem B31394591 : Blo 1431535 31394591 := bstep (se 1 (by rfl) ⟨23545943, by rfl⟩ : syracuseStep 31394591 = 47091887) B47091887
theorem B8162795 : Blo 1431535 8162795 := bstep (se 1 (by rfl) ⟨6122096, by rfl⟩ : syracuseStep 8162795 = 12244193) B12244193
theorem B4591151 : Blo 1431535 4591151 := bstep (se 1 (by rfl) ⟨3443363, by rfl⟩ : syracuseStep 4591151 = 6886727) B6886727
theorem B5165507 : Blo 1431535 5165507 := bstep (se 1 (by rfl) ⟨3874130, by rfl⟩ : syracuseStep 5165507 = 7748261) B7748261
theorem B10884455 : Blo 1431535 10884455 := bstep (se 1 (by rfl) ⟨8163341, by rfl⟩ : syracuseStep 10884455 = 16326683) B16326683
theorem B10073641 : Blo 1431535 10073641 := bstep (se 2 (by rfl) ⟨3777615, by rfl⟩ : syracuseStep 10073641 = 7555231) B7555231
theorem B33512251 : Blo 1431535 33512251 := bstep (se 1 (by rfl) ⟨25134188, by rfl⟩ : syracuseStep 33512251 = 50268377) B50268377
theorem B5441863 : Blo 1431535 5441863 := bstep (se 1 (by rfl) ⟨4081397, by rfl⟩ : syracuseStep 5441863 = 8162795) B8162795
theorem B3443671 : Blo 1431535 3443671 := bstep (se 1 (by rfl) ⟨2582753, by rfl⟩ : syracuseStep 3443671 = 5165507) B5165507
theorem B44683001 : Blo 1431535 44683001 := bstep (se 2 (by rfl) ⟨16756125, by rfl⟩ : syracuseStep 44683001 = 33512251) B33512251
theorem B13431521 : Blo 1431535 13431521 := bstep (se 2 (by rfl) ⟨5036820, by rfl⟩ : syracuseStep 13431521 = 10073641) B10073641
theorem B3060767 : Blo 1431535 3060767 := bstep (se 1 (by rfl) ⟨2295575, by rfl⟩ : syracuseStep 3060767 = 4591151) B4591151
theorem B7256303 : Blo 1431535 7256303 := bstep (se 1 (by rfl) ⟨5442227, by rfl⟩ : syracuseStep 7256303 = 10884455) B10884455
theorem B20929727 : Blo 1431535 20929727 := bstep (se 1 (by rfl) ⟨15697295, by rfl⟩ : syracuseStep 20929727 = 31394591) B31394591
theorem B35817389 : Blo 1431535 35817389 := bstep (se 3 (by rfl) ⟨6715760, by rfl⟩ : syracuseStep 35817389 = 13431521) B13431521
theorem B13953151 : Blo 1431535 13953151 := bstep (se 1 (by rfl) ⟨10464863, by rfl⟩ : syracuseStep 13953151 = 20929727) B20929727
theorem B29788667 : Blo 1431535 29788667 := bstep (se 1 (by rfl) ⟨22341500, by rfl⟩ : syracuseStep 29788667 = 44683001) B44683001
theorem B8162045 : Blo 1431535 8162045 := bstep (se 3 (by rfl) ⟨1530383, by rfl⟩ : syracuseStep 8162045 = 3060767) B3060767
theorem B4591561 : Blo 1431535 4591561 := bstep (se 2 (by rfl) ⟨1721835, by rfl⟩ : syracuseStep 4591561 = 3443671) B3443671
theorem B4837535 : Blo 1431535 4837535 := bstep (se 1 (by rfl) ⟨3628151, by rfl⟩ : syracuseStep 4837535 = 7256303) B7256303
theorem B7255817 : Blo 1431535 7255817 := bstep (se 2 (by rfl) ⟨2720931, by rfl⟩ : syracuseStep 7255817 = 5441863) B5441863
theorem B18604201 : Blo 1431535 18604201 := bstep (se 2 (by rfl) ⟨6976575, by rfl⟩ : syracuseStep 18604201 = 13953151) B13953151
theorem B19859111 : Blo 1431535 19859111 := bstep (se 1 (by rfl) ⟨14894333, by rfl⟩ : syracuseStep 19859111 = 29788667) B29788667
theorem B5441363 : Blo 1431535 5441363 := bstep (se 1 (by rfl) ⟨4081022, by rfl⟩ : syracuseStep 5441363 = 8162045) B8162045
theorem B6122081 : Blo 1431535 6122081 := bstep (se 2 (by rfl) ⟨2295780, by rfl⟩ : syracuseStep 6122081 = 4591561) B4591561
theorem B4837211 : Blo 1431535 4837211 := bstep (se 1 (by rfl) ⟨3627908, by rfl⟩ : syracuseStep 4837211 = 7255817) B7255817
theorem B3225023 : Blo 1431535 3225023 := bstep (se 1 (by rfl) ⟨2418767, by rfl⟩ : syracuseStep 3225023 = 4837535) B4837535
theorem B23878259 : Blo 1431535 23878259 := bstep (se 1 (by rfl) ⟨17908694, by rfl⟩ : syracuseStep 23878259 = 35817389) B35817389
theorem B24805601 : Blo 1431535 24805601 := bstep (se 2 (by rfl) ⟨9302100, by rfl⟩ : syracuseStep 24805601 = 18604201) B18604201
theorem B13239407 : Blo 1431535 13239407 := bstep (se 1 (by rfl) ⟨9929555, by rfl⟩ : syracuseStep 13239407 = 19859111) B19859111
theorem B4081387 : Blo 1431535 4081387 := bstep (se 1 (by rfl) ⟨3061040, by rfl⟩ : syracuseStep 4081387 = 6122081) B6122081
theorem B15918839 : Blo 1431535 15918839 := bstep (se 1 (by rfl) ⟨11939129, by rfl⟩ : syracuseStep 15918839 = 23878259) B23878259
theorem B2150015 : Blo 1431535 2150015 := bstep (se 1 (by rfl) ⟨1612511, by rfl⟩ : syracuseStep 2150015 = 3225023) B3225023
theorem B3224807 : Blo 1431535 3224807 := bstep (se 1 (by rfl) ⟨2418605, by rfl⟩ : syracuseStep 3224807 = 4837211) B4837211
theorem B3627575 : Blo 1431535 3627575 := bstep (se 1 (by rfl) ⟨2720681, by rfl⟩ : syracuseStep 3627575 = 5441363) B5441363
theorem B2418383 : Blo 1431535 2418383 := bstep (se 1 (by rfl) ⟨1813787, by rfl⟩ : syracuseStep 2418383 = 3627575) B3627575
theorem B5441849 : Blo 1431535 5441849 := bstep (se 2 (by rfl) ⟨2040693, by rfl⟩ : syracuseStep 5441849 = 4081387) B4081387
theorem B2149871 : Blo 1431535 2149871 := bstep (se 1 (by rfl) ⟨1612403, by rfl⟩ : syracuseStep 2149871 = 3224807) B3224807
theorem B10612559 : Blo 1431535 10612559 := bstep (se 1 (by rfl) ⟨7959419, by rfl⟩ : syracuseStep 10612559 = 15918839) B15918839
theorem B16537067 : Blo 1431535 16537067 := bstep (se 1 (by rfl) ⟨12402800, by rfl⟩ : syracuseStep 16537067 = 24805601) B24805601
theorem B35305085 : Blo 1431535 35305085 := bstep (se 3 (by rfl) ⟨6619703, by rfl⟩ : syracuseStep 35305085 = 13239407) B13239407
theorem B1433343 : Blo 1431535 1433343 := bstep (se 1 (by rfl) ⟨1075007, by rfl⟩ : syracuseStep 1433343 = 2150015) B2150015
theorem B94146893 : Blo 1431535 94146893 := bstep (se 3 (by rfl) ⟨17652542, by rfl⟩ : syracuseStep 94146893 = 35305085) B35305085
theorem B7075039 : Blo 1431535 7075039 := bstep (se 1 (by rfl) ⟨5306279, by rfl⟩ : syracuseStep 7075039 = 10612559) B10612559
theorem B11024711 : Blo 1431535 11024711 := bstep (se 1 (by rfl) ⟨8268533, by rfl⟩ : syracuseStep 11024711 = 16537067) B16537067
theorem B1612255 : Blo 1431535 1612255 := bstep (se 1 (by rfl) ⟨1209191, by rfl⟩ : syracuseStep 1612255 = 2418383) B2418383
theorem B3627899 : Blo 1431535 3627899 := bstep (se 1 (by rfl) ⟨2720924, by rfl⟩ : syracuseStep 3627899 = 5441849) B5441849
theorem B1433247 : Blo 1431535 1433247 := bstep (se 1 (by rfl) ⟨1074935, by rfl⟩ : syracuseStep 1433247 = 2149871) B2149871
theorem B7349807 : Blo 1431535 7349807 := bstep (se 1 (by rfl) ⟨5512355, by rfl⟩ : syracuseStep 7349807 = 11024711) B11024711
theorem B2418599 : Blo 1431535 2418599 := bstep (se 1 (by rfl) ⟨1813949, by rfl⟩ : syracuseStep 2418599 = 3627899) B3627899
theorem B2149673 : Blo 1431535 2149673 := bstep (se 2 (by rfl) ⟨806127, by rfl⟩ : syracuseStep 2149673 = 1612255) B1612255
theorem B9433385 : Blo 1431535 9433385 := bstep (se 2 (by rfl) ⟨3537519, by rfl⟩ : syracuseStep 9433385 = 7075039) B7075039
theorem B62764595 : Blo 1431535 62764595 := bstep (se 1 (by rfl) ⟨47073446, by rfl⟩ : syracuseStep 62764595 = 94146893) B94146893
theorem B4899871 : Blo 1431535 4899871 := bstep (se 1 (by rfl) ⟨3674903, by rfl⟩ : syracuseStep 4899871 = 7349807) B7349807
theorem B6288923 : Blo 1431535 6288923 := bstep (se 1 (by rfl) ⟨4716692, by rfl⟩ : syracuseStep 6288923 = 9433385) B9433385
theorem B41843063 : Blo 1431535 41843063 := bstep (se 1 (by rfl) ⟨31382297, by rfl⟩ : syracuseStep 41843063 = 62764595) B62764595
theorem B1612399 : Blo 1431535 1612399 := bstep (se 1 (by rfl) ⟨1209299, by rfl⟩ : syracuseStep 1612399 = 2418599) B2418599
theorem B1433115 : Blo 1431535 1433115 := bstep (se 1 (by rfl) ⟨1074836, by rfl⟩ : syracuseStep 1433115 = 2149673) B2149673
theorem B26132645 : Blo 1431535 26132645 := bstep (se 4 (by rfl) ⟨2449935, by rfl⟩ : syracuseStep 26132645 = 4899871) B4899871
theorem B16770461 : Blo 1431535 16770461 := bstep (se 3 (by rfl) ⟨3144461, by rfl⟩ : syracuseStep 16770461 = 6288923) B6288923
theorem B27895375 : Blo 1431535 27895375 := bstep (se 1 (by rfl) ⟨20921531, by rfl⟩ : syracuseStep 27895375 = 41843063) B41843063
theorem B2149865 : Blo 1431535 2149865 := bstep (se 2 (by rfl) ⟨806199, by rfl⟩ : syracuseStep 2149865 = 1612399) B1612399
theorem B44721229 : Blo 1431535 44721229 := bstep (se 3 (by rfl) ⟨8385230, by rfl⟩ : syracuseStep 44721229 = 16770461) B16770461
theorem B37193833 : Blo 1431535 37193833 := bstep (se 2 (by rfl) ⟨13947687, by rfl⟩ : syracuseStep 37193833 = 27895375) B27895375
theorem B17421763 : Blo 1431535 17421763 := bstep (se 1 (by rfl) ⟨13066322, by rfl⟩ : syracuseStep 17421763 = 26132645) B26132645
theorem B1433243 : Blo 1431535 1433243 := bstep (se 1 (by rfl) ⟨1074932, by rfl⟩ : syracuseStep 1433243 = 2149865) B2149865
theorem B23229017 : Blo 1431535 23229017 := bstep (se 2 (by rfl) ⟨8710881, by rfl⟩ : syracuseStep 23229017 = 17421763) B17421763
theorem B49591777 : Blo 1431535 49591777 := bstep (se 2 (by rfl) ⟨18596916, by rfl⟩ : syracuseStep 49591777 = 37193833) B37193833
theorem B59628305 : Blo 1431535 59628305 := bstep (se 2 (by rfl) ⟨22360614, by rfl⟩ : syracuseStep 59628305 = 44721229) B44721229
theorem B15486011 : Blo 1431535 15486011 := bstep (se 1 (by rfl) ⟨11614508, by rfl⟩ : syracuseStep 15486011 = 23229017) B23229017
theorem B39752203 : Blo 1431535 39752203 := bstep (se 1 (by rfl) ⟨29814152, by rfl⟩ : syracuseStep 39752203 = 59628305) B59628305
theorem B66122369 : Blo 1431535 66122369 := bstep (se 2 (by rfl) ⟨24795888, by rfl⟩ : syracuseStep 66122369 = 49591777) B49591777
theorem B44081579 : Blo 1431535 44081579 := bstep (se 1 (by rfl) ⟨33061184, by rfl⟩ : syracuseStep 44081579 = 66122369) B66122369
theorem B53002937 : Blo 1431535 53002937 := bstep (se 2 (by rfl) ⟨19876101, by rfl⟩ : syracuseStep 53002937 = 39752203) B39752203
theorem B10324007 : Blo 1431535 10324007 := bstep (se 1 (by rfl) ⟨7743005, by rfl⟩ : syracuseStep 10324007 = 15486011) B15486011
theorem B6882671 : Blo 1431535 6882671 := bstep (se 1 (by rfl) ⟨5162003, by rfl⟩ : syracuseStep 6882671 = 10324007) B10324007
theorem B29387719 : Blo 1431535 29387719 := bstep (se 1 (by rfl) ⟨22040789, by rfl⟩ : syracuseStep 29387719 = 44081579) B44081579
theorem B35335291 : Blo 1431535 35335291 := bstep (se 1 (by rfl) ⟨26501468, by rfl⟩ : syracuseStep 35335291 = 53002937) B53002937
theorem B4588447 : Blo 1431535 4588447 := bstep (se 1 (by rfl) ⟨3441335, by rfl⟩ : syracuseStep 4588447 = 6882671) B6882671
theorem B39183625 : Blo 1431535 39183625 := bstep (se 2 (by rfl) ⟨14693859, by rfl⟩ : syracuseStep 39183625 = 29387719) B29387719
theorem B47113721 : Blo 1431535 47113721 := bstep (se 2 (by rfl) ⟨17667645, by rfl⟩ : syracuseStep 47113721 = 35335291) B35335291
theorem B31409147 : Blo 1431535 31409147 := bstep (se 1 (by rfl) ⟨23556860, by rfl⟩ : syracuseStep 31409147 = 47113721) B47113721
theorem B52244833 : Blo 1431535 52244833 := bstep (se 2 (by rfl) ⟨19591812, by rfl⟩ : syracuseStep 52244833 = 39183625) B39183625
theorem B6117929 : Blo 1431535 6117929 := bstep (se 2 (by rfl) ⟨2294223, by rfl⟩ : syracuseStep 6117929 = 4588447) B4588447
theorem B20939431 : Blo 1431535 20939431 := bstep (se 1 (by rfl) ⟨15704573, by rfl⟩ : syracuseStep 20939431 = 31409147) B31409147
theorem B69659777 : Blo 1431535 69659777 := bstep (se 2 (by rfl) ⟨26122416, by rfl⟩ : syracuseStep 69659777 = 52244833) B52244833
theorem B4078619 : Blo 1431535 4078619 := bstep (se 1 (by rfl) ⟨3058964, by rfl⟩ : syracuseStep 4078619 = 6117929) B6117929
theorem B27919241 : Blo 1431535 27919241 := bstep (se 2 (by rfl) ⟨10469715, by rfl⟩ : syracuseStep 27919241 = 20939431) B20939431
theorem B2719079 : Blo 1431535 2719079 := bstep (se 1 (by rfl) ⟨2039309, by rfl⟩ : syracuseStep 2719079 = 4078619) B4078619
theorem B46439851 : Blo 1431535 46439851 := bstep (se 1 (by rfl) ⟨34829888, by rfl⟩ : syracuseStep 46439851 = 69659777) B69659777
theorem B18612827 : Blo 1431535 18612827 := bstep (se 1 (by rfl) ⟨13959620, by rfl⟩ : syracuseStep 18612827 = 27919241) B27919241
theorem B1812719 : Blo 1431535 1812719 := bstep (se 1 (by rfl) ⟨1359539, by rfl⟩ : syracuseStep 1812719 = 2719079) B2719079
theorem B61919801 : Blo 1431535 61919801 := bstep (se 2 (by rfl) ⟨23219925, by rfl⟩ : syracuseStep 61919801 = 46439851) B46439851
theorem B41279867 : Blo 1431535 41279867 := bstep (se 1 (by rfl) ⟨30959900, by rfl⟩ : syracuseStep 41279867 = 61919801) B61919801
theorem B4833917 : Blo 1431535 4833917 := bstep (se 3 (by rfl) ⟨906359, by rfl⟩ : syracuseStep 4833917 = 1812719) B1812719
theorem B12408551 : Blo 1431535 12408551 := bstep (se 1 (by rfl) ⟨9306413, by rfl⟩ : syracuseStep 12408551 = 18612827) B18612827
theorem B27519911 : Blo 1431535 27519911 := bstep (se 1 (by rfl) ⟨20639933, by rfl⟩ : syracuseStep 27519911 = 41279867) B41279867
theorem B3222611 : Blo 1431535 3222611 := bstep (se 1 (by rfl) ⟨2416958, by rfl⟩ : syracuseStep 3222611 = 4833917) B4833917
theorem B8272367 : Blo 1431535 8272367 := bstep (se 1 (by rfl) ⟨6204275, by rfl⟩ : syracuseStep 8272367 = 12408551) B12408551
theorem B5514911 : Blo 1431535 5514911 := bstep (se 1 (by rfl) ⟨4136183, by rfl⟩ : syracuseStep 5514911 = 8272367) B8272367
theorem B2148407 : Blo 1431535 2148407 := bstep (se 1 (by rfl) ⟨1611305, by rfl⟩ : syracuseStep 2148407 = 3222611) B3222611
theorem B18346607 : Blo 1431535 18346607 := bstep (se 1 (by rfl) ⟨13759955, by rfl⟩ : syracuseStep 18346607 = 27519911) B27519911
theorem B12231071 : Blo 1431535 12231071 := bstep (se 1 (by rfl) ⟨9173303, by rfl⟩ : syracuseStep 12231071 = 18346607) B18346607
theorem B3676607 : Blo 1431535 3676607 := bstep (se 1 (by rfl) ⟨2757455, by rfl⟩ : syracuseStep 3676607 = 5514911) B5514911
theorem B1432271 : Blo 1431535 1432271 := bstep (se 1 (by rfl) ⟨1074203, by rfl⟩ : syracuseStep 1432271 = 2148407) B2148407
theorem B2451071 : Blo 1431535 2451071 := bstep (se 1 (by rfl) ⟨1838303, by rfl⟩ : syracuseStep 2451071 = 3676607) B3676607
theorem B8154047 : Blo 1431535 8154047 := bstep (se 1 (by rfl) ⟨6115535, by rfl⟩ : syracuseStep 8154047 = 12231071) B12231071
theorem B5436031 : Blo 1431535 5436031 := bstep (se 1 (by rfl) ⟨4077023, by rfl⟩ : syracuseStep 5436031 = 8154047) B8154047
theorem B6536189 : Blo 1431535 6536189 := bstep (se 3 (by rfl) ⟨1225535, by rfl⟩ : syracuseStep 6536189 = 2451071) B2451071
theorem B7248041 : Blo 1431535 7248041 := bstep (se 2 (by rfl) ⟨2718015, by rfl⟩ : syracuseStep 7248041 = 5436031) B5436031
theorem B4357459 : Blo 1431535 4357459 := bstep (se 1 (by rfl) ⟨3268094, by rfl⟩ : syracuseStep 4357459 = 6536189) B6536189
theorem B4832027 : Blo 1431535 4832027 := bstep (se 1 (by rfl) ⟨3624020, by rfl⟩ : syracuseStep 4832027 = 7248041) B7248041
theorem B23239781 : Blo 1431535 23239781 := bstep (se 4 (by rfl) ⟨2178729, by rfl⟩ : syracuseStep 23239781 = 4357459) B4357459
theorem B3221351 : Blo 1431535 3221351 := bstep (se 1 (by rfl) ⟨2416013, by rfl⟩ : syracuseStep 3221351 = 4832027) B4832027
theorem B15493187 : Blo 1431535 15493187 := bstep (se 1 (by rfl) ⟨11619890, by rfl⟩ : syracuseStep 15493187 = 23239781) B23239781
theorem B2147567 : Blo 1431535 2147567 := bstep (se 1 (by rfl) ⟨1610675, by rfl⟩ : syracuseStep 2147567 = 3221351) B3221351
theorem B10328791 : Blo 1431535 10328791 := bstep (se 1 (by rfl) ⟨7746593, by rfl⟩ : syracuseStep 10328791 = 15493187) B15493187
theorem B13771721 : Blo 1431535 13771721 := bstep (se 2 (by rfl) ⟨5164395, by rfl⟩ : syracuseStep 13771721 = 10328791) B10328791
theorem B1431711 : Blo 1431535 1431711 := bstep (se 1 (by rfl) ⟨1073783, by rfl⟩ : syracuseStep 1431711 = 2147567) B2147567
theorem B9181147 : Blo 1431535 9181147 := bstep (se 1 (by rfl) ⟨6885860, by rfl⟩ : syracuseStep 9181147 = 13771721) B13771721
theorem B12241529 : Blo 1431535 12241529 := bstep (se 2 (by rfl) ⟨4590573, by rfl⟩ : syracuseStep 12241529 = 9181147) B9181147
theorem B8161019 : Blo 1431535 8161019 := bstep (se 1 (by rfl) ⟨6120764, by rfl⟩ : syracuseStep 8161019 = 12241529) B12241529
theorem B5440679 : Blo 1431535 5440679 := bstep (se 1 (by rfl) ⟨4080509, by rfl⟩ : syracuseStep 5440679 = 8161019) B8161019
theorem B3627119 : Blo 1431535 3627119 := bstep (se 1 (by rfl) ⟨2720339, by rfl⟩ : syracuseStep 3627119 = 5440679) B5440679
theorem B2418079 : Blo 1431535 2418079 := bstep (se 1 (by rfl) ⟨1813559, by rfl⟩ : syracuseStep 2418079 = 3627119) B3627119
theorem B3224105 : Blo 1431535 3224105 := bstep (se 2 (by rfl) ⟨1209039, by rfl⟩ : syracuseStep 3224105 = 2418079) B2418079
theorem B2149403 : Blo 1431535 2149403 := bstep (se 1 (by rfl) ⟨1612052, by rfl⟩ : syracuseStep 2149403 = 3224105) B3224105
theorem B1432935 : Blo 1431535 1432935 := bstep (se 1 (by rfl) ⟨1074701, by rfl⟩ : syracuseStep 1432935 = 2149403) B2149403

theorem C0 (j : ℕ) (h1 : 357883 ≤ j) (h2 : j ≤ 358383) : Blo 1431535 (4 * j + 3) := by
  interval_cases j
  · exact B1431535
  · exact B1431539
  · exact B1431543
  · exact B1431547
  · exact B1431551
  · exact B1431555
  · exact B1431559
  · exact B1431563
  · exact B1431567
  · exact B1431571
  · exact B1431575
  · exact B1431579
  · exact B1431583
  · exact B1431587
  · exact B1431591
  · exact B1431595
  · exact B1431599
  · exact B1431603
  · exact B1431607
  · exact B1431611
  · exact B1431615
  · exact B1431619
  · exact B1431623
  · exact B1431627
  · exact B1431631
  · exact B1431635
  · exact B1431639
  · exact B1431643
  · exact B1431647
  · exact B1431651
  · exact B1431655
  · exact B1431659
  · exact B1431663
  · exact B1431667
  · exact B1431671
  · exact B1431675
  · exact B1431679
  · exact B1431683
  · exact B1431687
  · exact B1431691
  · exact B1431695
  · exact B1431699
  · exact B1431703
  · exact B1431707
  · exact B1431711
  · exact B1431715
  · exact B1431719
  · exact B1431723
  · exact B1431727
  · exact B1431731
  · exact B1431735
  · exact B1431739
  · exact B1431743
  · exact B1431747
  · exact B1431751
  · exact B1431755
  · exact B1431759
  · exact B1431763
  · exact B1431767
  · exact B1431771
  · exact B1431775
  · exact B1431779
  · exact B1431783
  · exact B1431787
  · exact B1431791
  · exact B1431795
  · exact B1431799
  · exact B1431803
  · exact B1431807
  · exact B1431811
  · exact B1431815
  · exact B1431819
  · exact B1431823
  · exact B1431827
  · exact B1431831
  · exact B1431835
  · exact B1431839
  · exact B1431843
  · exact B1431847
  · exact B1431851
  · exact B1431855
  · exact B1431859
  · exact B1431863
  · exact B1431867
  · exact B1431871
  · exact B1431875
  · exact B1431879
  · exact B1431883
  · exact B1431887
  · exact B1431891
  · exact B1431895
  · exact B1431899
  · exact B1431903
  · exact B1431907
  · exact B1431911
  · exact B1431915
  · exact B1431919
  · exact B1431923
  · exact B1431927
  · exact B1431931
  · exact B1431935
  · exact B1431939
  · exact B1431943
  · exact B1431947
  · exact B1431951
  · exact B1431955
  · exact B1431959
  · exact B1431963
  · exact B1431967
  · exact B1431971
  · exact B1431975
  · exact B1431979
  · exact B1431983
  · exact B1431987
  · exact B1431991
  · exact B1431995
  · exact B1431999
  · exact B1432003
  · exact B1432007
  · exact B1432011
  · exact B1432015
  · exact B1432019
  · exact B1432023
  · exact B1432027
  · exact B1432031
  · exact B1432035
  · exact B1432039
  · exact B1432043
  · exact B1432047
  · exact B1432051
  · exact B1432055
  · exact B1432059
  · exact B1432063
  · exact B1432067
  · exact B1432071
  · exact B1432075
  · exact B1432079
  · exact B1432083
  · exact B1432087
  · exact B1432091
  · exact B1432095
  · exact B1432099
  · exact B1432103
  · exact B1432107
  · exact B1432111
  · exact B1432115
  · exact B1432119
  · exact B1432123
  · exact B1432127
  · exact B1432131
  · exact B1432135
  · exact B1432139
  · exact B1432143
  · exact B1432147
  · exact B1432151
  · exact B1432155
  · exact B1432159
  · exact B1432163
  · exact B1432167
  · exact B1432171
  · exact B1432175
  · exact B1432179
  · exact B1432183
  · exact B1432187
  · exact B1432191
  · exact B1432195
  · exact B1432199
  · exact B1432203
  · exact B1432207
  · exact B1432211
  · exact B1432215
  · exact B1432219
  · exact B1432223
  · exact B1432227
  · exact B1432231
  · exact B1432235
  · exact B1432239
  · exact B1432243
  · exact B1432247
  · exact B1432251
  · exact B1432255
  · exact B1432259
  · exact B1432263
  · exact B1432267
  · exact B1432271
  · exact B1432275
  · exact B1432279
  · exact B1432283
  · exact B1432287
  · exact B1432291
  · exact B1432295
  · exact B1432299
  · exact B1432303
  · exact B1432307
  · exact B1432311
  · exact B1432315
  · exact B1432319
  · exact B1432323
  · exact B1432327
  · exact B1432331
  · exact B1432335
  · exact B1432339
  · exact B1432343
  · exact B1432347
  · exact B1432351
  · exact B1432355
  · exact B1432359
  · exact B1432363
  · exact B1432367
  · exact B1432371
  · exact B1432375
  · exact B1432379
  · exact B1432383
  · exact B1432387
  · exact B1432391
  · exact B1432395
  · exact B1432399
  · exact B1432403
  · exact B1432407
  · exact B1432411
  · exact B1432415
  · exact B1432419
  · exact B1432423
  · exact B1432427
  · exact B1432431
  · exact B1432435
  · exact B1432439
  · exact B1432443
  · exact B1432447
  · exact B1432451
  · exact B1432455
  · exact B1432459
  · exact B1432463
  · exact B1432467
  · exact B1432471
  · exact B1432475
  · exact B1432479
  · exact B1432483
  · exact B1432487
  · exact B1432491
  · exact B1432495
  · exact B1432499
  · exact B1432503
  · exact B1432507
  · exact B1432511
  · exact B1432515
  · exact B1432519
  · exact B1432523
  · exact B1432527
  · exact B1432531
  · exact B1432535
  · exact B1432539
  · exact B1432543
  · exact B1432547
  · exact B1432551
  · exact B1432555
  · exact B1432559
  · exact B1432563
  · exact B1432567
  · exact B1432571
  · exact B1432575
  · exact B1432579
  · exact B1432583
  · exact B1432587
  · exact B1432591
  · exact B1432595
  · exact B1432599
  · exact B1432603
  · exact B1432607
  · exact B1432611
  · exact B1432615
  · exact B1432619
  · exact B1432623
  · exact B1432627
  · exact B1432631
  · exact B1432635
  · exact B1432639
  · exact B1432643
  · exact B1432647
  · exact B1432651
  · exact B1432655
  · exact B1432659
  · exact B1432663
  · exact B1432667
  · exact B1432671
  · exact B1432675
  · exact B1432679
  · exact B1432683
  · exact B1432687
  · exact B1432691
  · exact B1432695
  · exact B1432699
  · exact B1432703
  · exact B1432707
  · exact B1432711
  · exact B1432715
  · exact B1432719
  · exact B1432723
  · exact B1432727
  · exact B1432731
  · exact B1432735
  · exact B1432739
  · exact B1432743
  · exact B1432747
  · exact B1432751
  · exact B1432755
  · exact B1432759
  · exact B1432763
  · exact B1432767
  · exact B1432771
  · exact B1432775
  · exact B1432779
  · exact B1432783
  · exact B1432787
  · exact B1432791
  · exact B1432795
  · exact B1432799
  · exact B1432803
  · exact B1432807
  · exact B1432811
  · exact B1432815
  · exact B1432819
  · exact B1432823
  · exact B1432827
  · exact B1432831
  · exact B1432835
  · exact B1432839
  · exact B1432843
  · exact B1432847
  · exact B1432851
  · exact B1432855
  · exact B1432859
  · exact B1432863
  · exact B1432867
  · exact B1432871
  · exact B1432875
  · exact B1432879
  · exact B1432883
  · exact B1432887
  · exact B1432891
  · exact B1432895
  · exact B1432899
  · exact B1432903
  · exact B1432907
  · exact B1432911
  · exact B1432915
  · exact B1432919
  · exact B1432923
  · exact B1432927
  · exact B1432931
  · exact B1432935
  · exact B1432939
  · exact B1432943
  · exact B1432947
  · exact B1432951
  · exact B1432955
  · exact B1432959
  · exact B1432963
  · exact B1432967
  · exact B1432971
  · exact B1432975
  · exact B1432979
  · exact B1432983
  · exact B1432987
  · exact B1432991
  · exact B1432995
  · exact B1432999
  · exact B1433003
  · exact B1433007
  · exact B1433011
  · exact B1433015
  · exact B1433019
  · exact B1433023
  · exact B1433027
  · exact B1433031
  · exact B1433035
  · exact B1433039
  · exact B1433043
  · exact B1433047
  · exact B1433051
  · exact B1433055
  · exact B1433059
  · exact B1433063
  · exact B1433067
  · exact B1433071
  · exact B1433075
  · exact B1433079
  · exact B1433083
  · exact B1433087
  · exact B1433091
  · exact B1433095
  · exact B1433099
  · exact B1433103
  · exact B1433107
  · exact B1433111
  · exact B1433115
  · exact B1433119
  · exact B1433123
  · exact B1433127
  · exact B1433131
  · exact B1433135
  · exact B1433139
  · exact B1433143
  · exact B1433147
  · exact B1433151
  · exact B1433155
  · exact B1433159
  · exact B1433163
  · exact B1433167
  · exact B1433171
  · exact B1433175
  · exact B1433179
  · exact B1433183
  · exact B1433187
  · exact B1433191
  · exact B1433195
  · exact B1433199
  · exact B1433203
  · exact B1433207
  · exact B1433211
  · exact B1433215
  · exact B1433219
  · exact B1433223
  · exact B1433227
  · exact B1433231
  · exact B1433235
  · exact B1433239
  · exact B1433243
  · exact B1433247
  · exact B1433251
  · exact B1433255
  · exact B1433259
  · exact B1433263
  · exact B1433267
  · exact B1433271
  · exact B1433275
  · exact B1433279
  · exact B1433283
  · exact B1433287
  · exact B1433291
  · exact B1433295
  · exact B1433299
  · exact B1433303
  · exact B1433307
  · exact B1433311
  · exact B1433315
  · exact B1433319
  · exact B1433323
  · exact B1433327
  · exact B1433331
  · exact B1433335
  · exact B1433339
  · exact B1433343
  · exact B1433347
  · exact B1433351
  · exact B1433355
  · exact B1433359
  · exact B1433363
  · exact B1433367
  · exact B1433371
  · exact B1433375
  · exact B1433379
  · exact B1433383
  · exact B1433387
  · exact B1433391
  · exact B1433395
  · exact B1433399
  · exact B1433403
  · exact B1433407
  · exact B1433411
  · exact B1433415
  · exact B1433419
  · exact B1433423
  · exact B1433427
  · exact B1433431
  · exact B1433435
  · exact B1433439
  · exact B1433443
  · exact B1433447
  · exact B1433451
  · exact B1433455
  · exact B1433459
  · exact B1433463
  · exact B1433467
  · exact B1433471
  · exact B1433475
  · exact B1433479
  · exact B1433483
  · exact B1433487
  · exact B1433491
  · exact B1433495
  · exact B1433499
  · exact B1433503
  · exact B1433507
  · exact B1433511
  · exact B1433515
  · exact B1433519
  · exact B1433523
  · exact B1433527
  · exact B1433531
  · exact B1433535

theorem solution (m : ℕ) (hlo : 1431535 ≤ m) (hhi : m ≤ 1433535) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 357883 ≤ j := by omega
    have hj2 : j ≤ 358383 := by omega
    have hb : Blo 1431535 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
