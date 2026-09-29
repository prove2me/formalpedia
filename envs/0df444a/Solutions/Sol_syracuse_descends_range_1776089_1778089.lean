-- Prove2me | solution 1 for syracuse_descends_range_1776089_1778089
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:43:19.161273+00:00
-- url     : https://prove2.me/submissions/b6f5663e-24bc-43ee-a7d8-fd643bcc56a9

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


theorem B3997709 : Blo 1776089 3997709 := bbase (se 3 (by rfl) ⟨749570, by rfl⟩ : syracuseStep 3997709 = 1499141) (by norm_num)
theorem B3604501 : Blo 1776089 3604501 := bbase (se 6 (by rfl) ⟨84480, by rfl⟩ : syracuseStep 3604501 = 168961) (by norm_num)
theorem B1998877 : Blo 1776089 1998877 := bbase (se 3 (by rfl) ⟨374789, by rfl⟩ : syracuseStep 1998877 = 749579) (by norm_num)
theorem B2998309 : Blo 1776089 2998309 := bbase (se 4 (by rfl) ⟨281091, by rfl⟩ : syracuseStep 2998309 = 562183) (by norm_num)
theorem B1998913 : Blo 1776089 1998913 := bbase (se 2 (by rfl) ⟨749592, by rfl⟩ : syracuseStep 1998913 = 1499185) (by norm_num)
theorem B3997781 : Blo 1776089 3997781 := bbase (se 8 (by rfl) ⟨23424, by rfl⟩ : syracuseStep 3997781 = 46849) (by norm_num)
theorem B6406229 : Blo 1776089 6406229 := bbase (se 8 (by rfl) ⟨37536, by rfl⟩ : syracuseStep 6406229 = 75073) (by norm_num)
theorem B5996645 : Blo 1776089 5996645 := bbase (se 4 (by rfl) ⟨562185, by rfl⟩ : syracuseStep 5996645 = 1124371) (by norm_num)
theorem B1998949 : Blo 1776089 1998949 := bbase (se 4 (by rfl) ⟨187401, by rfl⟩ : syracuseStep 1998949 = 374803) (by norm_num)
theorem B2998397 : Blo 1776089 2998397 := bbase (se 3 (by rfl) ⟨562199, by rfl⟩ : syracuseStep 2998397 = 1124399) (by norm_num)
theorem B1998985 : Blo 1776089 1998985 := bbase (se 2 (by rfl) ⟨749619, by rfl⟩ : syracuseStep 1998985 = 1499239) (by norm_num)
theorem B4497565 : Blo 1776089 4497565 := bbase (se 3 (by rfl) ⟨843293, by rfl⟩ : syracuseStep 4497565 = 1686587) (by norm_num)
theorem B3997853 : Blo 1776089 3997853 := bbase (se 3 (by rfl) ⟨749597, by rfl⟩ : syracuseStep 3997853 = 1499195) (by norm_num)
theorem B1999021 : Blo 1776089 1999021 := bbase (se 3 (by rfl) ⟨374816, by rfl⟩ : syracuseStep 1999021 = 749633) (by norm_num)
theorem B5062837 : Blo 1776089 5062837 := bbase (se 5 (by rfl) ⟨237320, by rfl⟩ : syracuseStep 5062837 = 474641) (by norm_num)
theorem B2162873 : Blo 1776089 2162873 := bbase (se 2 (by rfl) ⟨811077, by rfl⟩ : syracuseStep 2162873 = 1622155) (by norm_num)
theorem B1851589 : Blo 1776089 1851589 := bbase (se 4 (by rfl) ⟨173586, by rfl⟩ : syracuseStep 1851589 = 347173) (by norm_num)
theorem B1999057 : Blo 1776089 1999057 := bbase (se 2 (by rfl) ⟨749646, by rfl⟩ : syracuseStep 1999057 = 1499293) (by norm_num)
theorem B3997925 : Blo 1776089 3997925 := bbase (se 4 (by rfl) ⟨374805, by rfl⟩ : syracuseStep 3997925 = 749611) (by norm_num)
theorem B1999093 : Blo 1776089 1999093 := bbase (se 5 (by rfl) ⟨93707, by rfl⟩ : syracuseStep 1999093 = 187415) (by norm_num)
theorem B2998525 : Blo 1776089 2998525 := bbase (se 3 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 2998525 = 1124447) (by norm_num)
theorem B4497677 : Blo 1776089 4497677 := bbase (se 3 (by rfl) ⟨843314, by rfl⟩ : syracuseStep 4497677 = 1686629) (by norm_num)
theorem B1999129 : Blo 1776089 1999129 := bbase (se 2 (by rfl) ⟨749673, by rfl⟩ : syracuseStep 1999129 = 1499347) (by norm_num)
theorem B3997997 : Blo 1776089 3997997 := bbase (se 3 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 3997997 = 1499249) (by norm_num)
theorem B3203381 : Blo 1776089 3203381 := bbase (se 5 (by rfl) ⟨150158, by rfl⟩ : syracuseStep 3203381 = 300317) (by norm_num)
theorem B1999165 : Blo 1776089 1999165 := bbase (se 3 (by rfl) ⟨374843, by rfl⟩ : syracuseStep 1999165 = 749687) (by norm_num)
theorem B2998613 : Blo 1776089 2998613 := bbase (se 10 (by rfl) ⟨4392, by rfl⟩ : syracuseStep 2998613 = 8785) (by norm_num)
theorem B3375445 : Blo 1776089 3375445 := bbase (se 10 (by rfl) ⟨4944, by rfl⟩ : syracuseStep 3375445 = 9889) (by norm_num)
theorem B1999201 : Blo 1776089 1999201 := bbase (se 2 (by rfl) ⟨749700, by rfl⟩ : syracuseStep 1999201 = 1499401) (by norm_num)
theorem B3998069 : Blo 1776089 3998069 := bbase (se 5 (by rfl) ⟨187409, by rfl⟩ : syracuseStep 3998069 = 374819) (by norm_num)
theorem B1999237 : Blo 1776089 1999237 := bbase (se 4 (by rfl) ⟨187428, by rfl⟩ : syracuseStep 1999237 = 374857) (by norm_num)
theorem B3793301 : Blo 1776089 3793301 := bbase (se 6 (by rfl) ⟨88905, by rfl⟩ : syracuseStep 3793301 = 177811) (by norm_num)
theorem B1999273 : Blo 1776089 1999273 := bbase (se 2 (by rfl) ⟨749727, by rfl⟩ : syracuseStep 1999273 = 1499455) (by norm_num)
theorem B3998141 : Blo 1776089 3998141 := bbase (se 3 (by rfl) ⟨749651, by rfl⟩ : syracuseStep 3998141 = 1499303) (by norm_num)
theorem B6668741 : Blo 1776089 6668741 := bbase (se 4 (by rfl) ⟨625194, by rfl⟩ : syracuseStep 6668741 = 1250389) (by norm_num)
theorem B3203525 : Blo 1776089 3203525 := bbase (se 4 (by rfl) ⟨300330, by rfl⟩ : syracuseStep 3203525 = 600661) (by norm_num)
theorem B6750661 : Blo 1776089 6750661 := bbase (se 4 (by rfl) ⟨632874, by rfl⟩ : syracuseStep 6750661 = 1265749) (by norm_num)
theorem B4497869 : Blo 1776089 4497869 := bbase (se 3 (by rfl) ⟨843350, by rfl⟩ : syracuseStep 4497869 = 1686701) (by norm_num)
theorem B1999309 : Blo 1776089 1999309 := bbase (se 3 (by rfl) ⟨374870, by rfl⟩ : syracuseStep 1999309 = 749741) (by norm_num)
theorem B2998741 : Blo 1776089 2998741 := bbase (se 7 (by rfl) ⟨35141, by rfl⟩ : syracuseStep 2998741 = 70283) (by norm_num)
theorem B3375589 : Blo 1776089 3375589 := bbase (se 4 (by rfl) ⟨316461, by rfl⟩ : syracuseStep 3375589 = 632923) (by norm_num)
theorem B1999345 : Blo 1776089 1999345 := bbase (se 2 (by rfl) ⟨749754, by rfl⟩ : syracuseStep 1999345 = 1499509) (by norm_num)
theorem B3998213 : Blo 1776089 3998213 := bbase (se 4 (by rfl) ⟨374832, by rfl⟩ : syracuseStep 3998213 = 749665) (by norm_num)
theorem B3203597 : Blo 1776089 3203597 := bbase (se 3 (by rfl) ⟨600674, by rfl⟩ : syracuseStep 3203597 = 1201349) (by norm_num)
theorem B5997077 : Blo 1776089 5997077 := bbase (se 6 (by rfl) ⟨140556, by rfl⟩ : syracuseStep 5997077 = 281113) (by norm_num)
theorem B1999381 : Blo 1776089 1999381 := bbase (se 6 (by rfl) ⟨46860, by rfl⟩ : syracuseStep 1999381 = 93721) (by norm_num)
theorem B2400805 : Blo 1776089 2400805 := bbase (se 4 (by rfl) ⟨225075, by rfl⟩ : syracuseStep 2400805 = 450151) (by norm_num)
theorem B2998829 : Blo 1776089 2998829 := bbase (se 3 (by rfl) ⟨562280, by rfl⟩ : syracuseStep 2998829 = 1124561) (by norm_num)
theorem B4268597 : Blo 1776089 4268597 := bbase (se 5 (by rfl) ⟨200090, by rfl⟩ : syracuseStep 4268597 = 400181) (by norm_num)
theorem B1999417 : Blo 1776089 1999417 := bbase (se 2 (by rfl) ⟨749781, by rfl⟩ : syracuseStep 1999417 = 1499563) (by norm_num)
theorem B3998285 : Blo 1776089 3998285 := bbase (se 3 (by rfl) ⟨749678, by rfl⟩ : syracuseStep 3998285 = 1499357) (by norm_num)
theorem B1999453 : Blo 1776089 1999453 := bbase (se 3 (by rfl) ⟨374897, by rfl⟩ : syracuseStep 1999453 = 749795) (by norm_num)
theorem B8102501 : Blo 1776089 8102501 := bbase (se 4 (by rfl) ⟨759609, by rfl⟩ : syracuseStep 8102501 = 1519219) (by norm_num)
theorem B1999489 : Blo 1776089 1999489 := bbase (se 2 (by rfl) ⟨749808, by rfl⟩ : syracuseStep 1999489 = 1499617) (by norm_num)
theorem B3793549 : Blo 1776089 3793549 := bbase (se 3 (by rfl) ⟨711290, by rfl⟩ : syracuseStep 3793549 = 1422581) (by norm_num)
theorem B3998357 : Blo 1776089 3998357 := bbase (se 6 (by rfl) ⟨93711, by rfl⟩ : syracuseStep 3998357 = 187423) (by norm_num)
theorem B1999525 : Blo 1776089 1999525 := bbase (se 4 (by rfl) ⟨187455, by rfl⟩ : syracuseStep 1999525 = 374911) (by norm_num)
theorem B2998957 : Blo 1776089 2998957 := bbase (se 3 (by rfl) ⟨562304, by rfl⟩ : syracuseStep 2998957 = 1124609) (by norm_num)
theorem B1999561 : Blo 1776089 1999561 := bbase (se 2 (by rfl) ⟨749835, by rfl⟩ : syracuseStep 1999561 = 1499671) (by norm_num)
theorem B3998429 : Blo 1776089 3998429 := bbase (se 3 (by rfl) ⟨749705, by rfl⟩ : syracuseStep 3998429 = 1499411) (by norm_num)
theorem B3203813 : Blo 1776089 3203813 := bbase (se 4 (by rfl) ⟨300357, by rfl⟩ : syracuseStep 3203813 = 600715) (by norm_num)
theorem B1999597 : Blo 1776089 1999597 := bbase (se 3 (by rfl) ⟨374924, by rfl⟩ : syracuseStep 1999597 = 749849) (by norm_num)
theorem B6750965 : Blo 1776089 6750965 := bbase (se 5 (by rfl) ⟨316451, by rfl⟩ : syracuseStep 6750965 = 632903) (by norm_num)
theorem B2999045 : Blo 1776089 2999045 := bbase (se 4 (by rfl) ⟨281160, by rfl⟩ : syracuseStep 2999045 = 562321) (by norm_num)
theorem B1999633 : Blo 1776089 1999633 := bbase (se 2 (by rfl) ⟨749862, by rfl⟩ : syracuseStep 1999633 = 1499725) (by norm_num)
theorem B6406933 : Blo 1776089 6406933 := bbase (se 6 (by rfl) ⟨150162, by rfl⟩ : syracuseStep 6406933 = 300325) (by norm_num)
theorem B4498213 : Blo 1776089 4498213 := bbase (se 4 (by rfl) ⟨421707, by rfl⟩ : syracuseStep 4498213 = 843415) (by norm_num)
theorem B3998501 : Blo 1776089 3998501 := bbase (se 4 (by rfl) ⟨374859, by rfl⟩ : syracuseStep 3998501 = 749719) (by norm_num)
theorem B1999669 : Blo 1776089 1999669 := bbase (se 5 (by rfl) ⟨93734, by rfl⟩ : syracuseStep 1999669 = 187469) (by norm_num)
theorem B10117973 : Blo 1776089 10117973 := bbase (se 9 (by rfl) ⟨29642, by rfl⟩ : syracuseStep 10117973 = 59285) (by norm_num)
theorem B1999705 : Blo 1776089 1999705 := bbase (se 2 (by rfl) ⟨749889, by rfl⟩ : syracuseStep 1999705 = 1499779) (by norm_num)
theorem B3998573 : Blo 1776089 3998573 := bbase (se 3 (by rfl) ⟨749732, by rfl⟩ : syracuseStep 3998573 = 1499465) (by norm_num)
theorem B12813173 : Blo 1776089 12813173 := bbase (se 5 (by rfl) ⟨600617, by rfl⟩ : syracuseStep 12813173 = 1201235) (by norm_num)
theorem B1999741 : Blo 1776089 1999741 := bbase (se 3 (by rfl) ⟨374951, by rfl⟩ : syracuseStep 1999741 = 749903) (by norm_num)
theorem B2999173 : Blo 1776089 2999173 := bbase (se 4 (by rfl) ⟨281172, by rfl⟩ : syracuseStep 2999173 = 562345) (by norm_num)
theorem B4498325 : Blo 1776089 4498325 := bbase (se 6 (by rfl) ⟨105429, by rfl⟩ : syracuseStep 4498325 = 210859) (by norm_num)
theorem B22782869 : Blo 1776089 22782869 := bbase (se 6 (by rfl) ⟨533973, by rfl⟩ : syracuseStep 22782869 = 1067947) (by norm_num)
theorem B1999777 : Blo 1776089 1999777 := bbase (se 2 (by rfl) ⟨749916, by rfl⟩ : syracuseStep 1999777 = 1499833) (by norm_num)
theorem B3998645 : Blo 1776089 3998645 := bbase (se 5 (by rfl) ⟨187436, by rfl⟩ : syracuseStep 3998645 = 374873) (by norm_num)
theorem B5997509 : Blo 1776089 5997509 := bbase (se 4 (by rfl) ⟨562266, by rfl⟩ : syracuseStep 5997509 = 1124533) (by norm_num)
theorem B1999813 : Blo 1776089 1999813 := bbase (se 4 (by rfl) ⟨187482, by rfl⟩ : syracuseStep 1999813 = 374965) (by norm_num)
theorem B2999261 : Blo 1776089 2999261 := bbase (se 3 (by rfl) ⟨562361, by rfl⟩ : syracuseStep 2999261 = 1124723) (by norm_num)
theorem B1999849 : Blo 1776089 1999849 := bbase (se 2 (by rfl) ⟨749943, by rfl⟩ : syracuseStep 1999849 = 1499887) (by norm_num)
theorem B3998717 : Blo 1776089 3998717 := bbase (se 3 (by rfl) ⟨749759, by rfl⟩ : syracuseStep 3998717 = 1499519) (by norm_num)
theorem B1999885 : Blo 1776089 1999885 := bbase (se 3 (by rfl) ⟨374978, by rfl⟩ : syracuseStep 1999885 = 749957) (by norm_num)
theorem B1999921 : Blo 1776089 1999921 := bbase (se 2 (by rfl) ⟨749970, by rfl⟩ : syracuseStep 1999921 = 1499941) (by norm_num)
theorem B2884661 : Blo 1776089 2884661 := bbase (se 5 (by rfl) ⟨135218, by rfl⟩ : syracuseStep 2884661 = 270437) (by norm_num)
theorem B3998789 : Blo 1776089 3998789 := bbase (se 4 (by rfl) ⟨374886, by rfl⟩ : syracuseStep 3998789 = 749773) (by norm_num)
theorem B4498517 : Blo 1776089 4498517 := bbase (se 8 (by rfl) ⟨26358, by rfl⟩ : syracuseStep 4498517 = 52717) (by norm_num)
theorem B1999957 : Blo 1776089 1999957 := bbase (se 8 (by rfl) ⟨11718, by rfl⟩ : syracuseStep 1999957 = 23437) (by norm_num)
theorem B2999389 : Blo 1776089 2999389 := bbase (se 3 (by rfl) ⟨562385, by rfl⟩ : syracuseStep 2999389 = 1124771) (by norm_num)
theorem B1999993 : Blo 1776089 1999993 := bbase (se 2 (by rfl) ⟨749997, by rfl⟩ : syracuseStep 1999993 = 1499995) (by norm_num)
theorem B3794053 : Blo 1776089 3794053 := bbase (se 4 (by rfl) ⟨355692, by rfl⟩ : syracuseStep 3794053 = 711385) (by norm_num)
theorem B2278541 : Blo 1776089 2278541 := bbase (se 3 (by rfl) ⟨427226, by rfl⟩ : syracuseStep 2278541 = 854453) (by norm_num)
theorem B3998861 : Blo 1776089 3998861 := bbase (se 3 (by rfl) ⟨749786, by rfl⟩ : syracuseStep 3998861 = 1499573) (by norm_num)
theorem B2000029 : Blo 1776089 2000029 := bbase (se 3 (by rfl) ⟨375005, by rfl⟩ : syracuseStep 2000029 = 750011) (by norm_num)
theorem B8996021 : Blo 1776089 8996021 := bbase (se 5 (by rfl) ⟨421688, by rfl⟩ : syracuseStep 8996021 = 843377) (by norm_num)
theorem B2999477 : Blo 1776089 2999477 := bbase (se 5 (by rfl) ⟨140600, by rfl⟩ : syracuseStep 2999477 = 281201) (by norm_num)
theorem B2000065 : Blo 1776089 2000065 := bbase (se 2 (by rfl) ⟨750024, by rfl⟩ : syracuseStep 2000065 = 1500049) (by norm_num)
theorem B3998933 : Blo 1776089 3998933 := bbase (se 7 (by rfl) ⟨46862, by rfl⟩ : syracuseStep 3998933 = 93725) (by norm_num)
theorem B2000101 : Blo 1776089 2000101 := bbase (se 4 (by rfl) ⟨187509, by rfl⟩ : syracuseStep 2000101 = 375019) (by norm_num)
theorem B2000137 : Blo 1776089 2000137 := bbase (se 2 (by rfl) ⟨750051, by rfl⟩ : syracuseStep 2000137 = 1500103) (by norm_num)
theorem B24315157 : Blo 1776089 24315157 := bbase (se 6 (by rfl) ⟨569886, by rfl⟩ : syracuseStep 24315157 = 1139773) (by norm_num)
theorem B3999005 : Blo 1776089 3999005 := bbase (se 3 (by rfl) ⟨749813, by rfl⟩ : syracuseStep 3999005 = 1499627) (by norm_num)
theorem B2000173 : Blo 1776089 2000173 := bbase (se 3 (by rfl) ⟨375032, by rfl⟩ : syracuseStep 2000173 = 750065) (by norm_num)
theorem B2999605 : Blo 1776089 2999605 := bbase (se 5 (by rfl) ⟨140606, by rfl⟩ : syracuseStep 2999605 = 281213) (by norm_num)
theorem B2000209 : Blo 1776089 2000209 := bbase (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) (by norm_num)
theorem B3999077 : Blo 1776089 3999077 := bbase (se 4 (by rfl) ⟨374913, by rfl⟩ : syracuseStep 3999077 = 749827) (by norm_num)
theorem B5997941 : Blo 1776089 5997941 := bbase (se 5 (by rfl) ⟨281153, by rfl⟩ : syracuseStep 5997941 = 562307) (by norm_num)
theorem B2000245 : Blo 1776089 2000245 := bbase (se 5 (by rfl) ⟨93761, by rfl⟩ : syracuseStep 2000245 = 187523) (by norm_num)
theorem B2999693 : Blo 1776089 2999693 := bbase (se 3 (by rfl) ⟨562442, by rfl⟩ : syracuseStep 2999693 = 1124885) (by norm_num)
theorem B2000281 : Blo 1776089 2000281 := bbase (se 2 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 2000281 = 1500211) (by norm_num)
theorem B4498861 : Blo 1776089 4498861 := bbase (se 3 (by rfl) ⟨843536, by rfl⟩ : syracuseStep 4498861 = 1687073) (by norm_num)
theorem B3999149 : Blo 1776089 3999149 := bbase (se 3 (by rfl) ⟨749840, by rfl⟩ : syracuseStep 3999149 = 1499681) (by norm_num)
theorem B2000317 : Blo 1776089 2000317 := bbase (se 3 (by rfl) ⟨375059, by rfl⟩ : syracuseStep 2000317 = 750119) (by norm_num)
theorem B30377429 : Blo 1776089 30377429 := bbase (se 7 (by rfl) ⟨355985, by rfl⟩ : syracuseStep 30377429 = 711971) (by norm_num)
theorem B3999221 : Blo 1776089 3999221 := bbase (se 5 (by rfl) ⟨187463, by rfl⟩ : syracuseStep 3999221 = 374927) (by norm_num)
theorem B2999821 : Blo 1776089 2999821 := bbase (se 3 (by rfl) ⟨562466, by rfl⟩ : syracuseStep 2999821 = 1124933) (by norm_num)
theorem B4498973 : Blo 1776089 4498973 := bbase (se 3 (by rfl) ⟨843557, by rfl⟩ : syracuseStep 4498973 = 1687115) (by norm_num)
theorem B3999293 : Blo 1776089 3999293 := bbase (se 3 (by rfl) ⟨749867, by rfl⟩ : syracuseStep 3999293 = 1499735) (by norm_num)
theorem B2999909 : Blo 1776089 2999909 := bbase (se 4 (by rfl) ⟨281241, by rfl⟩ : syracuseStep 2999909 = 562483) (by norm_num)
theorem B2737781 : Blo 1776089 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B3999365 : Blo 1776089 3999365 := bbase (se 4 (by rfl) ⟨374940, by rfl⟩ : syracuseStep 3999365 = 749881) (by norm_num)
theorem B3999437 : Blo 1776089 3999437 := bbase (se 3 (by rfl) ⟨749894, by rfl⟩ : syracuseStep 3999437 = 1499789) (by norm_num)
theorem B2311885 : Blo 1776089 2311885 := bbase (se 3 (by rfl) ⟨433478, by rfl⟩ : syracuseStep 2311885 = 866957) (by norm_num)
theorem B2664149 : Blo 1776089 2664149 := bbase (se 7 (by rfl) ⟨31220, by rfl⟩ : syracuseStep 2664149 = 62441) (by norm_num)
theorem B4499165 : Blo 1776089 4499165 := bbase (se 3 (by rfl) ⟨843593, by rfl⟩ : syracuseStep 4499165 = 1687187) (by norm_num)
theorem B3000037 : Blo 1776089 3000037 := bbase (se 4 (by rfl) ⟨281253, by rfl⟩ : syracuseStep 3000037 = 562507) (by norm_num)
theorem B2664173 : Blo 1776089 2664173 := bbase (se 3 (by rfl) ⟨499532, by rfl⟩ : syracuseStep 2664173 = 999065) (by norm_num)
theorem B10397429 : Blo 1776089 10397429 := bbase (se 5 (by rfl) ⟨487379, by rfl⟩ : syracuseStep 10397429 = 974759) (by norm_num)
theorem B2664197 : Blo 1776089 2664197 := bbase (se 4 (by rfl) ⟨249768, by rfl⟩ : syracuseStep 2664197 = 499537) (by norm_num)
theorem B3999509 : Blo 1776089 3999509 := bbase (se 6 (by rfl) ⟨93738, by rfl⟩ : syracuseStep 3999509 = 187477) (by norm_num)
theorem B2664221 : Blo 1776089 2664221 := bbase (se 3 (by rfl) ⟨499541, by rfl⟩ : syracuseStep 2664221 = 999083) (by norm_num)
theorem B5998373 : Blo 1776089 5998373 := bbase (se 4 (by rfl) ⟨562347, by rfl⟩ : syracuseStep 5998373 = 1124695) (by norm_num)
theorem B2664245 : Blo 1776089 2664245 := bbase (se 5 (by rfl) ⟨124886, by rfl⟩ : syracuseStep 2664245 = 249773) (by norm_num)
theorem B3000125 : Blo 1776089 3000125 := bbase (se 3 (by rfl) ⟨562523, by rfl⟩ : syracuseStep 3000125 = 1125047) (by norm_num)
theorem B2664269 : Blo 1776089 2664269 := bbase (se 3 (by rfl) ⟨499550, by rfl⟩ : syracuseStep 2664269 = 999101) (by norm_num)
theorem B3999581 : Blo 1776089 3999581 := bbase (se 3 (by rfl) ⟨749921, by rfl⟩ : syracuseStep 3999581 = 1499843) (by norm_num)
theorem B2664293 : Blo 1776089 2664293 := bbase (se 4 (by rfl) ⟨249777, by rfl⟩ : syracuseStep 2664293 = 499555) (by norm_num)
theorem B2664317 : Blo 1776089 2664317 := bbase (se 3 (by rfl) ⟨499559, by rfl⟩ : syracuseStep 2664317 = 999119) (by norm_num)
theorem B2664341 : Blo 1776089 2664341 := bbase (se 6 (by rfl) ⟨62445, by rfl⟩ : syracuseStep 2664341 = 124891) (by norm_num)
theorem B3999653 : Blo 1776089 3999653 := bbase (se 4 (by rfl) ⟨374967, by rfl⟩ : syracuseStep 3999653 = 749935) (by norm_num)
theorem B2664365 : Blo 1776089 2664365 := bbase (se 3 (by rfl) ⟨499568, by rfl⟩ : syracuseStep 2664365 = 999137) (by norm_num)
theorem B9734069 : Blo 1776089 9734069 := bbase (se 5 (by rfl) ⟨456284, by rfl⟩ : syracuseStep 9734069 = 912569) (by norm_num)
theorem B3000253 : Blo 1776089 3000253 := bbase (se 3 (by rfl) ⟨562547, by rfl⟩ : syracuseStep 3000253 = 1125095) (by norm_num)
theorem B2664389 : Blo 1776089 2664389 := bbase (se 4 (by rfl) ⟨249786, by rfl⟩ : syracuseStep 2664389 = 499573) (by norm_num)
theorem B2664413 : Blo 1776089 2664413 := bbase (se 3 (by rfl) ⟨499577, by rfl⟩ : syracuseStep 2664413 = 999155) (by norm_num)
theorem B3999725 : Blo 1776089 3999725 := bbase (se 3 (by rfl) ⟨749948, by rfl⟩ : syracuseStep 3999725 = 1499897) (by norm_num)
theorem B2664437 : Blo 1776089 2664437 := bbase (se 5 (by rfl) ⟨124895, by rfl⟩ : syracuseStep 2664437 = 249791) (by norm_num)
theorem B3794941 : Blo 1776089 3794941 := bbase (se 3 (by rfl) ⟨711551, by rfl⟩ : syracuseStep 3794941 = 1423103) (by norm_num)
theorem B2664461 : Blo 1776089 2664461 := bbase (se 3 (by rfl) ⟨499586, by rfl⟩ : syracuseStep 2664461 = 999173) (by norm_num)
theorem B3000341 : Blo 1776089 3000341 := bbase (se 6 (by rfl) ⟨70320, by rfl⟩ : syracuseStep 3000341 = 140641) (by norm_num)
theorem B2664485 : Blo 1776089 2664485 := bbase (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) (by norm_num)
theorem B4499509 : Blo 1776089 4499509 := bbase (se 5 (by rfl) ⟨210914, by rfl⟩ : syracuseStep 4499509 = 421829) (by norm_num)
theorem B3999797 : Blo 1776089 3999797 := bbase (se 5 (by rfl) ⟨187490, by rfl⟩ : syracuseStep 3999797 = 374981) (by norm_num)
theorem B2664509 : Blo 1776089 2664509 := bbase (se 3 (by rfl) ⟨499595, by rfl⟩ : syracuseStep 2664509 = 999191) (by norm_num)
theorem B2279485 : Blo 1776089 2279485 := bbase (se 3 (by rfl) ⟨427403, by rfl⟩ : syracuseStep 2279485 = 854807) (by norm_num)
theorem B2664533 : Blo 1776089 2664533 := bbase (se 8 (by rfl) ⟨15612, by rfl⟩ : syracuseStep 2664533 = 31225) (by norm_num)
theorem B2664557 : Blo 1776089 2664557 := bbase (se 3 (by rfl) ⟨499604, by rfl⟩ : syracuseStep 2664557 = 999209) (by norm_num)
theorem B3999869 : Blo 1776089 3999869 := bbase (se 3 (by rfl) ⟨749975, by rfl⟩ : syracuseStep 3999869 = 1499951) (by norm_num)
theorem B2664581 : Blo 1776089 2664581 := bbase (se 4 (by rfl) ⟨249804, by rfl⟩ : syracuseStep 2664581 = 499609) (by norm_num)
theorem B3000469 : Blo 1776089 3000469 := bbase (se 6 (by rfl) ⟨70323, by rfl⟩ : syracuseStep 3000469 = 140647) (by norm_num)
theorem B2664605 : Blo 1776089 2664605 := bbase (se 3 (by rfl) ⟨499613, by rfl⟩ : syracuseStep 2664605 = 999227) (by norm_num)
theorem B4499621 : Blo 1776089 4499621 := bbase (se 4 (by rfl) ⟨421839, by rfl⟩ : syracuseStep 4499621 = 843679) (by norm_num)
theorem B2664629 : Blo 1776089 2664629 := bbase (se 5 (by rfl) ⟨124904, by rfl⟩ : syracuseStep 2664629 = 249809) (by norm_num)
theorem B3999941 : Blo 1776089 3999941 := bbase (se 4 (by rfl) ⟨374994, by rfl⟩ : syracuseStep 3999941 = 749989) (by norm_num)
theorem B2664653 : Blo 1776089 2664653 := bbase (se 3 (by rfl) ⟨499622, by rfl⟩ : syracuseStep 2664653 = 999245) (by norm_num)
theorem B5998805 : Blo 1776089 5998805 := bbase (se 7 (by rfl) ⟨70298, by rfl⟩ : syracuseStep 5998805 = 140597) (by norm_num)
theorem B2664677 : Blo 1776089 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B2664701 : Blo 1776089 2664701 := bbase (se 3 (by rfl) ⟨499631, by rfl⟩ : syracuseStep 2664701 = 999263) (by norm_num)
theorem B4000013 : Blo 1776089 4000013 := bbase (se 3 (by rfl) ⟨750002, by rfl⟩ : syracuseStep 4000013 = 1500005) (by norm_num)
theorem B2664725 : Blo 1776089 2664725 := bbase (se 6 (by rfl) ⟨62454, by rfl⟩ : syracuseStep 2664725 = 124909) (by norm_num)
theorem B2279701 : Blo 1776089 2279701 := bbase (se 6 (by rfl) ⟨53430, by rfl⟩ : syracuseStep 2279701 = 106861) (by norm_num)
theorem B4270357 : Blo 1776089 4270357 := bbase (se 6 (by rfl) ⟨100086, by rfl⟩ : syracuseStep 4270357 = 200173) (by norm_num)
theorem B2664749 : Blo 1776089 2664749 := bbase (se 3 (by rfl) ⟨499640, by rfl⟩ : syracuseStep 2664749 = 999281) (by norm_num)
theorem B2664773 : Blo 1776089 2664773 := bbase (se 4 (by rfl) ⟨249822, by rfl⟩ : syracuseStep 2664773 = 499645) (by norm_num)
theorem B4000085 : Blo 1776089 4000085 := bbase (se 10 (by rfl) ⟨5859, by rfl⟩ : syracuseStep 4000085 = 11719) (by norm_num)
theorem B2664797 : Blo 1776089 2664797 := bbase (se 3 (by rfl) ⟨499649, by rfl⟩ : syracuseStep 2664797 = 999299) (by norm_num)
theorem B2279773 : Blo 1776089 2279773 := bbase (se 3 (by rfl) ⟨427457, by rfl⟩ : syracuseStep 2279773 = 854915) (by norm_num)
theorem B4499813 : Blo 1776089 4499813 := bbase (se 4 (by rfl) ⟨421857, by rfl⟩ : syracuseStep 4499813 = 843715) (by norm_num)
theorem B2664821 : Blo 1776089 2664821 := bbase (se 5 (by rfl) ⟨124913, by rfl⟩ : syracuseStep 2664821 = 249827) (by norm_num)
theorem B2886013 : Blo 1776089 2886013 := bbase (se 3 (by rfl) ⟨541127, by rfl⟩ : syracuseStep 2886013 = 1082255) (by norm_num)
theorem B2664845 : Blo 1776089 2664845 := bbase (se 3 (by rfl) ⟨499658, by rfl⟩ : syracuseStep 2664845 = 999317) (by norm_num)
theorem B20253077 : Blo 1776089 20253077 := bbase (se 6 (by rfl) ⟨474681, by rfl⟩ : syracuseStep 20253077 = 949363) (by norm_num)
theorem B4000157 : Blo 1776089 4000157 := bbase (se 3 (by rfl) ⟨750029, by rfl⟩ : syracuseStep 4000157 = 1500059) (by norm_num)
theorem B2664869 : Blo 1776089 2664869 := bbase (se 4 (by rfl) ⟨249831, by rfl⟩ : syracuseStep 2664869 = 499663) (by norm_num)
theorem B2664893 : Blo 1776089 2664893 := bbase (se 3 (by rfl) ⟨499667, by rfl⟩ : syracuseStep 2664893 = 999335) (by norm_num)
theorem B8997317 : Blo 1776089 8997317 := bbase (se 4 (by rfl) ⟨843498, by rfl⟩ : syracuseStep 8997317 = 1686997) (by norm_num)
theorem B2664917 : Blo 1776089 2664917 := bbase (se 7 (by rfl) ⟨31229, by rfl⟩ : syracuseStep 2664917 = 62459) (by norm_num)
theorem B4803029 : Blo 1776089 4803029 := bbase (se 7 (by rfl) ⟨56285, by rfl⟩ : syracuseStep 4803029 = 112571) (by norm_num)
theorem B4000229 : Blo 1776089 4000229 := bbase (se 4 (by rfl) ⟨375021, by rfl⟩ : syracuseStep 4000229 = 750043) (by norm_num)
theorem B2664941 : Blo 1776089 2664941 := bbase (se 3 (by rfl) ⟨499676, by rfl⟩ : syracuseStep 2664941 = 999353) (by norm_num)
theorem B3795437 : Blo 1776089 3795437 := bbase (se 3 (by rfl) ⟨711644, by rfl⟩ : syracuseStep 3795437 = 1423289) (by norm_num)
theorem B2845181 : Blo 1776089 2845181 := bbase (se 3 (by rfl) ⟨533471, by rfl⟩ : syracuseStep 2845181 = 1066943) (by norm_num)
theorem B4270589 : Blo 1776089 4270589 := bbase (se 3 (by rfl) ⟨800735, by rfl⟩ : syracuseStep 4270589 = 1601471) (by norm_num)
theorem B2664965 : Blo 1776089 2664965 := bbase (se 4 (by rfl) ⟨249840, by rfl⟩ : syracuseStep 2664965 = 499681) (by norm_num)
theorem B2664989 : Blo 1776089 2664989 := bbase (se 3 (by rfl) ⟨499685, by rfl⟩ : syracuseStep 2664989 = 999371) (by norm_num)
theorem B4000301 : Blo 1776089 4000301 := bbase (se 3 (by rfl) ⟨750056, by rfl⟩ : syracuseStep 4000301 = 1500113) (by norm_num)
theorem B2665013 : Blo 1776089 2665013 := bbase (se 5 (by rfl) ⟨124922, by rfl⟩ : syracuseStep 2665013 = 249845) (by norm_num)
theorem B2665037 : Blo 1776089 2665037 := bbase (se 3 (by rfl) ⟨499694, by rfl⟩ : syracuseStep 2665037 = 999389) (by norm_num)
theorem B2665061 : Blo 1776089 2665061 := bbase (se 4 (by rfl) ⟨249849, by rfl⟩ : syracuseStep 2665061 = 499699) (by norm_num)
theorem B4000373 : Blo 1776089 4000373 := bbase (se 5 (by rfl) ⟨187517, by rfl⟩ : syracuseStep 4000373 = 375035) (by norm_num)
theorem B2665085 : Blo 1776089 2665085 := bbase (se 3 (by rfl) ⟨499703, by rfl⟩ : syracuseStep 2665085 = 999407) (by norm_num)
theorem B2402941 : Blo 1776089 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B5999237 : Blo 1776089 5999237 := bbase (se 4 (by rfl) ⟨562428, by rfl⟩ : syracuseStep 5999237 = 1124857) (by norm_num)
theorem B2665109 : Blo 1776089 2665109 := bbase (se 6 (by rfl) ⟨62463, by rfl⟩ : syracuseStep 2665109 = 124927) (by norm_num)
theorem B2665133 : Blo 1776089 2665133 := bbase (se 3 (by rfl) ⟨499712, by rfl⟩ : syracuseStep 2665133 = 999425) (by norm_num)
theorem B2402989 : Blo 1776089 2402989 := bbase (se 3 (by rfl) ⟨450560, by rfl⟩ : syracuseStep 2402989 = 901121) (by norm_num)
theorem B4500157 : Blo 1776089 4500157 := bbase (se 3 (by rfl) ⟨843779, by rfl⟩ : syracuseStep 4500157 = 1687559) (by norm_num)
theorem B4000445 : Blo 1776089 4000445 := bbase (se 3 (by rfl) ⟨750083, by rfl⟩ : syracuseStep 4000445 = 1500167) (by norm_num)
theorem B2665157 : Blo 1776089 2665157 := bbase (se 4 (by rfl) ⟨249858, by rfl⟩ : syracuseStep 2665157 = 499717) (by norm_num)
theorem B2665181 : Blo 1776089 2665181 := bbase (se 3 (by rfl) ⟨499721, by rfl⟩ : syracuseStep 2665181 = 999443) (by norm_num)
theorem B2665205 : Blo 1776089 2665205 := bbase (se 5 (by rfl) ⟨124931, by rfl⟩ : syracuseStep 2665205 = 249863) (by norm_num)
theorem B4000517 : Blo 1776089 4000517 := bbase (se 4 (by rfl) ⟨375048, by rfl⟩ : syracuseStep 4000517 = 750097) (by norm_num)
theorem B2665229 : Blo 1776089 2665229 := bbase (se 3 (by rfl) ⟨499730, by rfl⟩ : syracuseStep 2665229 = 999461) (by norm_num)
theorem B2665253 : Blo 1776089 2665253 := bbase (se 4 (by rfl) ⟨249867, by rfl⟩ : syracuseStep 2665253 = 499735) (by norm_num)
theorem B4500269 : Blo 1776089 4500269 := bbase (se 3 (by rfl) ⟨843800, by rfl⟩ : syracuseStep 4500269 = 1687601) (by norm_num)
theorem B2665277 : Blo 1776089 2665277 := bbase (se 3 (by rfl) ⟨499739, by rfl⟩ : syracuseStep 2665277 = 999479) (by norm_num)
theorem B4000589 : Blo 1776089 4000589 := bbase (se 3 (by rfl) ⟨750110, by rfl⟩ : syracuseStep 4000589 = 1500221) (by norm_num)
theorem B2665301 : Blo 1776089 2665301 := bbase (se 9 (by rfl) ⟨7808, by rfl⟩ : syracuseStep 2665301 = 15617) (by norm_num)
theorem B8538965 : Blo 1776089 8538965 := bbase (se 9 (by rfl) ⟨25016, by rfl⟩ : syracuseStep 8538965 = 50033) (by norm_num)
theorem B2665325 : Blo 1776089 2665325 := bbase (se 3 (by rfl) ⟨499748, by rfl⟩ : syracuseStep 2665325 = 999497) (by norm_num)
theorem B2665349 : Blo 1776089 2665349 := bbase (se 4 (by rfl) ⟨249876, by rfl⟩ : syracuseStep 2665349 = 499753) (by norm_num)
theorem B4270981 : Blo 1776089 4270981 := bbase (se 4 (by rfl) ⟨400404, by rfl⟩ : syracuseStep 4270981 = 800809) (by norm_num)
theorem B4000661 : Blo 1776089 4000661 := bbase (se 6 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 4000661 = 187531) (by norm_num)
theorem B2665373 : Blo 1776089 2665373 := bbase (se 3 (by rfl) ⟨499757, by rfl⟩ : syracuseStep 2665373 = 999515) (by norm_num)
theorem B2665397 : Blo 1776089 2665397 := bbase (se 5 (by rfl) ⟨124940, by rfl⟩ : syracuseStep 2665397 = 249881) (by norm_num)
theorem B2665421 : Blo 1776089 2665421 := bbase (se 3 (by rfl) ⟨499766, by rfl⟩ : syracuseStep 2665421 = 999533) (by norm_num)
theorem B2665445 : Blo 1776089 2665445 := bbase (se 4 (by rfl) ⟨249885, by rfl⟩ : syracuseStep 2665445 = 499771) (by norm_num)
theorem B4500461 : Blo 1776089 4500461 := bbase (se 3 (by rfl) ⟨843836, by rfl⟩ : syracuseStep 4500461 = 1687673) (by norm_num)
theorem B2665469 : Blo 1776089 2665469 := bbase (se 3 (by rfl) ⟨499775, by rfl⟩ : syracuseStep 2665469 = 999551) (by norm_num)
theorem B2665493 : Blo 1776089 2665493 := bbase (se 6 (by rfl) ⟨62472, by rfl⟩ : syracuseStep 2665493 = 124945) (by norm_num)
theorem B2665517 : Blo 1776089 2665517 := bbase (se 3 (by rfl) ⟨499784, by rfl⟩ : syracuseStep 2665517 = 999569) (by norm_num)
theorem B5999669 : Blo 1776089 5999669 := bbase (se 5 (by rfl) ⟨281234, by rfl⟩ : syracuseStep 5999669 = 562469) (by norm_num)
theorem B2665541 : Blo 1776089 2665541 := bbase (se 4 (by rfl) ⟨249894, by rfl⟩ : syracuseStep 2665541 = 499789) (by norm_num)
theorem B2665565 : Blo 1776089 2665565 := bbase (se 3 (by rfl) ⟨499793, by rfl⟩ : syracuseStep 2665565 = 999587) (by norm_num)
theorem B7203941 : Blo 1776089 7203941 := bbase (se 4 (by rfl) ⟨675369, by rfl⟩ : syracuseStep 7203941 = 1350739) (by norm_num)
theorem B15174773 : Blo 1776089 15174773 := bbase (se 5 (by rfl) ⟨711317, by rfl⟩ : syracuseStep 15174773 = 1422635) (by norm_num)
theorem B2665589 : Blo 1776089 2665589 := bbase (se 5 (by rfl) ⟨124949, by rfl⟩ : syracuseStep 2665589 = 249899) (by norm_num)
theorem B2845829 : Blo 1776089 2845829 := bbase (se 4 (by rfl) ⟨266796, by rfl⟩ : syracuseStep 2845829 = 533593) (by norm_num)
theorem B7203973 : Blo 1776089 7203973 := bbase (se 4 (by rfl) ⟨675372, by rfl⟩ : syracuseStep 7203973 = 1350745) (by norm_num)
theorem B2665613 : Blo 1776089 2665613 := bbase (se 3 (by rfl) ⟨499802, by rfl⟩ : syracuseStep 2665613 = 999605) (by norm_num)
theorem B8105125 : Blo 1776089 8105125 := bbase (se 4 (by rfl) ⟨759855, by rfl⟩ : syracuseStep 8105125 = 1519711) (by norm_num)
theorem B2665637 : Blo 1776089 2665637 := bbase (se 4 (by rfl) ⟨249903, by rfl⟩ : syracuseStep 2665637 = 499807) (by norm_num)
theorem B2665661 : Blo 1776089 2665661 := bbase (se 3 (by rfl) ⟨499811, by rfl⟩ : syracuseStep 2665661 = 999623) (by norm_num)
theorem B6745301 : Blo 1776089 6745301 := bbase (se 7 (by rfl) ⟨79046, by rfl⟩ : syracuseStep 6745301 = 158093) (by norm_num)
theorem B2665685 : Blo 1776089 2665685 := bbase (se 7 (by rfl) ⟨31238, by rfl⟩ : syracuseStep 2665685 = 62477) (by norm_num)
theorem B2665709 : Blo 1776089 2665709 := bbase (se 3 (by rfl) ⟨499820, by rfl⟩ : syracuseStep 2665709 = 999641) (by norm_num)
theorem B2665733 : Blo 1776089 2665733 := bbase (se 4 (by rfl) ⟨249912, by rfl⟩ : syracuseStep 2665733 = 499825) (by norm_num)
theorem B2665757 : Blo 1776089 2665757 := bbase (se 3 (by rfl) ⟨499829, by rfl⟩ : syracuseStep 2665757 = 999659) (by norm_num)
theorem B2665781 : Blo 1776089 2665781 := bbase (se 5 (by rfl) ⟨124958, by rfl⟩ : syracuseStep 2665781 = 249917) (by norm_num)
theorem B2248013 : Blo 1776089 2248013 := bbase (se 3 (by rfl) ⟨421502, by rfl⟩ : syracuseStep 2248013 = 843005) (by norm_num)
theorem B2665805 : Blo 1776089 2665805 := bbase (se 3 (by rfl) ⟨499838, by rfl⟩ : syracuseStep 2665805 = 999677) (by norm_num)
theorem B5057893 : Blo 1776089 5057893 := bbase (se 4 (by rfl) ⟨474177, by rfl⟩ : syracuseStep 5057893 = 948355) (by norm_num)
theorem B2665829 : Blo 1776089 2665829 := bbase (se 4 (by rfl) ⟨249921, by rfl⟩ : syracuseStep 2665829 = 499843) (by norm_num)
theorem B3796325 : Blo 1776089 3796325 := bbase (se 4 (by rfl) ⟨355905, by rfl⟩ : syracuseStep 3796325 = 711811) (by norm_num)
theorem B2665853 : Blo 1776089 2665853 := bbase (se 3 (by rfl) ⟨499847, by rfl⟩ : syracuseStep 2665853 = 999695) (by norm_num)
theorem B2248069 : Blo 1776089 2248069 := bbase (se 4 (by rfl) ⟨210756, by rfl⟩ : syracuseStep 2248069 = 421513) (by norm_num)
theorem B2665877 : Blo 1776089 2665877 := bbase (se 6 (by rfl) ⟨62481, by rfl⟩ : syracuseStep 2665877 = 124963) (by norm_num)
theorem B4328861 : Blo 1776089 4328861 := bbase (se 3 (by rfl) ⟨811661, by rfl⟩ : syracuseStep 4328861 = 1623323) (by norm_num)
theorem B7589285 : Blo 1776089 7589285 := bbase (se 4 (by rfl) ⟨711495, by rfl⟩ : syracuseStep 7589285 = 1422991) (by norm_num)
theorem B2665901 : Blo 1776089 2665901 := bbase (se 3 (by rfl) ⟨499856, by rfl⟩ : syracuseStep 2665901 = 999713) (by norm_num)
theorem B13495733 : Blo 1776089 13495733 := bbase (se 5 (by rfl) ⟨632612, by rfl⟩ : syracuseStep 13495733 = 1265225) (by norm_num)
theorem B2665925 : Blo 1776089 2665925 := bbase (se 4 (by rfl) ⟨249930, by rfl⟩ : syracuseStep 2665925 = 499861) (by norm_num)
theorem B2665949 : Blo 1776089 2665949 := bbase (se 3 (by rfl) ⟨499865, by rfl⟩ : syracuseStep 2665949 = 999731) (by norm_num)
theorem B3796445 : Blo 1776089 3796445 := bbase (se 3 (by rfl) ⟨711833, by rfl⟩ : syracuseStep 3796445 = 1423667) (by norm_num)
theorem B2248165 : Blo 1776089 2248165 := bbase (se 4 (by rfl) ⟨210765, by rfl⟩ : syracuseStep 2248165 = 421531) (by norm_num)
theorem B6000101 : Blo 1776089 6000101 := bbase (se 4 (by rfl) ⟨562509, by rfl⟩ : syracuseStep 6000101 = 1125019) (by norm_num)
theorem B6745589 : Blo 1776089 6745589 := bbase (se 5 (by rfl) ⟨316199, by rfl⟩ : syracuseStep 6745589 = 632399) (by norm_num)
theorem B2665973 : Blo 1776089 2665973 := bbase (se 5 (by rfl) ⟨124967, by rfl⟩ : syracuseStep 2665973 = 249935) (by norm_num)
theorem B3419653 : Blo 1776089 3419653 := bbase (se 4 (by rfl) ⟨320592, by rfl⟩ : syracuseStep 3419653 = 641185) (by norm_num)
theorem B2665997 : Blo 1776089 2665997 := bbase (se 3 (by rfl) ⟨499874, by rfl⟩ : syracuseStep 2665997 = 999749) (by norm_num)
theorem B2666021 : Blo 1776089 2666021 := bbase (se 4 (by rfl) ⟨249939, by rfl⟩ : syracuseStep 2666021 = 499879) (by norm_num)
theorem B2666045 : Blo 1776089 2666045 := bbase (se 3 (by rfl) ⟨499883, by rfl⟩ : syracuseStep 2666045 = 999767) (by norm_num)
theorem B2666069 : Blo 1776089 2666069 := bbase (se 8 (by rfl) ⟨15621, by rfl⟩ : syracuseStep 2666069 = 31243) (by norm_num)
theorem B124833365 : Blo 1776089 124833365 := bbase (se 8 (by rfl) ⟨731445, by rfl⟩ : syracuseStep 124833365 = 1462891) (by norm_num)
theorem B2666093 : Blo 1776089 2666093 := bbase (se 3 (by rfl) ⟨499892, by rfl⟩ : syracuseStep 2666093 = 999785) (by norm_num)
theorem B2666117 : Blo 1776089 2666117 := bbase (se 4 (by rfl) ⟨249948, by rfl⟩ : syracuseStep 2666117 = 499897) (by norm_num)
theorem B2248337 : Blo 1776089 2248337 := bbase (se 2 (by rfl) ⟨843126, by rfl⟩ : syracuseStep 2248337 = 1686253) (by norm_num)
theorem B2666141 : Blo 1776089 2666141 := bbase (se 3 (by rfl) ⟨499901, by rfl⟩ : syracuseStep 2666141 = 999803) (by norm_num)
theorem B2666165 : Blo 1776089 2666165 := bbase (se 5 (by rfl) ⟨124976, by rfl⟩ : syracuseStep 2666165 = 249953) (by norm_num)
theorem B2248393 : Blo 1776089 2248393 := bbase (se 2 (by rfl) ⟨843147, by rfl⟩ : syracuseStep 2248393 = 1686295) (by norm_num)
theorem B2666189 : Blo 1776089 2666189 := bbase (se 3 (by rfl) ⟨499910, by rfl⟩ : syracuseStep 2666189 = 999821) (by norm_num)
theorem B8998613 : Blo 1776089 8998613 := bbase (se 7 (by rfl) ⟨105452, by rfl⟩ : syracuseStep 8998613 = 210905) (by norm_num)
theorem B2666213 : Blo 1776089 2666213 := bbase (se 4 (by rfl) ⟨249957, by rfl⟩ : syracuseStep 2666213 = 499915) (by norm_num)
theorem B2666237 : Blo 1776089 2666237 := bbase (se 3 (by rfl) ⟨499919, by rfl⟩ : syracuseStep 2666237 = 999839) (by norm_num)
theorem B2666261 : Blo 1776089 2666261 := bbase (se 6 (by rfl) ⟨62490, by rfl⟩ : syracuseStep 2666261 = 124981) (by norm_num)
theorem B2248489 : Blo 1776089 2248489 := bbase (se 2 (by rfl) ⟨843183, by rfl⟩ : syracuseStep 2248489 = 1686367) (by norm_num)
theorem B2666285 : Blo 1776089 2666285 := bbase (se 3 (by rfl) ⟨499928, by rfl⟩ : syracuseStep 2666285 = 999857) (by norm_num)
theorem B6401845 : Blo 1776089 6401845 := bbase (se 5 (by rfl) ⟨300086, by rfl⟩ : syracuseStep 6401845 = 600173) (by norm_num)
theorem B2666309 : Blo 1776089 2666309 := bbase (se 4 (by rfl) ⟨249966, by rfl⟩ : syracuseStep 2666309 = 499933) (by norm_num)
theorem B13487957 : Blo 1776089 13487957 := bbase (se 9 (by rfl) ⟨39515, by rfl⟩ : syracuseStep 13487957 = 79031) (by norm_num)
theorem B2666333 : Blo 1776089 2666333 := bbase (se 3 (by rfl) ⟨499937, by rfl⟩ : syracuseStep 2666333 = 999875) (by norm_num)
theorem B2666357 : Blo 1776089 2666357 := bbase (se 5 (by rfl) ⟨124985, by rfl⟩ : syracuseStep 2666357 = 249971) (by norm_num)
theorem B2666381 : Blo 1776089 2666381 := bbase (se 3 (by rfl) ⟨499946, by rfl⟩ : syracuseStep 2666381 = 999893) (by norm_num)
theorem B6000533 : Blo 1776089 6000533 := bbase (se 6 (by rfl) ⟨140637, by rfl⟩ : syracuseStep 6000533 = 281275) (by norm_num)
theorem B2666405 : Blo 1776089 2666405 := bbase (se 4 (by rfl) ⟨249975, by rfl⟩ : syracuseStep 2666405 = 499951) (by norm_num)
theorem B2666429 : Blo 1776089 2666429 := bbase (se 3 (by rfl) ⟨499955, by rfl⟩ : syracuseStep 2666429 = 999911) (by norm_num)
theorem B4272077 : Blo 1776089 4272077 := bbase (se 3 (by rfl) ⟨801014, by rfl⟩ : syracuseStep 4272077 = 1602029) (by norm_num)
theorem B4558805 : Blo 1776089 4558805 := bbase (se 7 (by rfl) ⟨53423, by rfl⟩ : syracuseStep 4558805 = 106847) (by norm_num)
theorem B2248661 : Blo 1776089 2248661 := bbase (se 7 (by rfl) ⟨26351, by rfl⟩ : syracuseStep 2248661 = 52703) (by norm_num)
theorem B8540117 : Blo 1776089 8540117 := bbase (se 7 (by rfl) ⟨100079, by rfl⟩ : syracuseStep 8540117 = 200159) (by norm_num)
theorem B2666453 : Blo 1776089 2666453 := bbase (se 7 (by rfl) ⟨31247, by rfl⟩ : syracuseStep 2666453 = 62495) (by norm_num)
theorem B2666477 : Blo 1776089 2666477 := bbase (se 3 (by rfl) ⟨499964, by rfl⟩ : syracuseStep 2666477 = 999929) (by norm_num)
theorem B2666501 : Blo 1776089 2666501 := bbase (se 4 (by rfl) ⟨249984, by rfl⟩ : syracuseStep 2666501 = 499969) (by norm_num)
theorem B2248717 : Blo 1776089 2248717 := bbase (se 3 (by rfl) ⟨421634, by rfl⟩ : syracuseStep 2248717 = 843269) (by norm_num)
theorem B4329485 : Blo 1776089 4329485 := bbase (se 3 (by rfl) ⟨811778, by rfl⟩ : syracuseStep 4329485 = 1623557) (by norm_num)
theorem B2666525 : Blo 1776089 2666525 := bbase (se 3 (by rfl) ⟨499973, by rfl⟩ : syracuseStep 2666525 = 999947) (by norm_num)
theorem B2666549 : Blo 1776089 2666549 := bbase (se 5 (by rfl) ⟨124994, by rfl⟩ : syracuseStep 2666549 = 249989) (by norm_num)
theorem B4558909 : Blo 1776089 4558909 := bbase (se 3 (by rfl) ⟨854795, by rfl⟩ : syracuseStep 4558909 = 1709591) (by norm_num)
theorem B2666573 : Blo 1776089 2666573 := bbase (se 3 (by rfl) ⟨499982, by rfl⟩ : syracuseStep 2666573 = 999965) (by norm_num)
theorem B4329557 : Blo 1776089 4329557 := bbase (se 8 (by rfl) ⟨25368, by rfl⟩ : syracuseStep 4329557 = 50737) (by norm_num)
theorem B3797077 : Blo 1776089 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B2846821 : Blo 1776089 2846821 := bbase (se 4 (by rfl) ⟨266889, by rfl⟩ : syracuseStep 2846821 = 533779) (by norm_num)
theorem B2666597 : Blo 1776089 2666597 := bbase (se 4 (by rfl) ⟨249993, by rfl⟩ : syracuseStep 2666597 = 499987) (by norm_num)
theorem B2248813 : Blo 1776089 2248813 := bbase (se 3 (by rfl) ⟨421652, by rfl⟩ : syracuseStep 2248813 = 843305) (by norm_num)
theorem B2666621 : Blo 1776089 2666621 := bbase (se 3 (by rfl) ⟨499991, by rfl⟩ : syracuseStep 2666621 = 999983) (by norm_num)
theorem B2134145 : Blo 1776089 2134145 := bbase (se 2 (by rfl) ⟨800304, by rfl⟩ : syracuseStep 2134145 = 1600609) (by norm_num)
theorem B2666645 : Blo 1776089 2666645 := bbase (se 6 (by rfl) ⟨62499, by rfl⟩ : syracuseStep 2666645 = 124999) (by norm_num)
theorem B2666669 : Blo 1776089 2666669 := bbase (se 3 (by rfl) ⟨500000, by rfl⟩ : syracuseStep 2666669 = 1000001) (by norm_num)
theorem B2134193 : Blo 1776089 2134193 := bbase (se 2 (by rfl) ⟨800322, by rfl⟩ : syracuseStep 2134193 = 1600645) (by norm_num)
theorem B2666693 : Blo 1776089 2666693 := bbase (se 4 (by rfl) ⟨250002, by rfl⟩ : syracuseStep 2666693 = 500005) (by norm_num)
theorem B25972949 : Blo 1776089 25972949 := bbase (se 7 (by rfl) ⟨304370, by rfl⟩ : syracuseStep 25972949 = 608741) (by norm_num)
theorem B25628885 : Blo 1776089 25628885 := bbase (se 7 (by rfl) ⟨300338, by rfl⟩ : syracuseStep 25628885 = 600677) (by norm_num)
theorem B2666717 : Blo 1776089 2666717 := bbase (se 3 (by rfl) ⟨500009, by rfl⟩ : syracuseStep 2666717 = 1000019) (by norm_num)
theorem B2666741 : Blo 1776089 2666741 := bbase (se 5 (by rfl) ⟨125003, by rfl⟩ : syracuseStep 2666741 = 250007) (by norm_num)
theorem B2666765 : Blo 1776089 2666765 := bbase (se 3 (by rfl) ⟨500018, by rfl⟩ : syracuseStep 2666765 = 1000037) (by norm_num)
theorem B22761749 : Blo 1776089 22761749 := bbase (se 6 (by rfl) ⟨533478, by rfl⟩ : syracuseStep 22761749 = 1066957) (by norm_num)
theorem B2248985 : Blo 1776089 2248985 := bbase (se 2 (by rfl) ⟨843369, by rfl⟩ : syracuseStep 2248985 = 1686739) (by norm_num)
theorem B2666789 : Blo 1776089 2666789 := bbase (se 4 (by rfl) ⟨250011, by rfl⟩ : syracuseStep 2666789 = 500023) (by norm_num)
theorem B8106293 : Blo 1776089 8106293 := bbase (se 5 (by rfl) ⟨379982, by rfl⟩ : syracuseStep 8106293 = 759965) (by norm_num)
theorem B2666813 : Blo 1776089 2666813 := bbase (se 3 (by rfl) ⟨500027, by rfl⟩ : syracuseStep 2666813 = 1000055) (by norm_num)
theorem B6000965 : Blo 1776089 6000965 := bbase (se 4 (by rfl) ⟨562590, by rfl⟩ : syracuseStep 6000965 = 1125181) (by norm_num)
theorem B2249041 : Blo 1776089 2249041 := bbase (se 2 (by rfl) ⟨843390, by rfl⟩ : syracuseStep 2249041 = 1686781) (by norm_num)
theorem B2666837 : Blo 1776089 2666837 := bbase (se 10 (by rfl) ⟨3906, by rfl⟩ : syracuseStep 2666837 = 7813) (by norm_num)
theorem B2666861 : Blo 1776089 2666861 := bbase (se 3 (by rfl) ⟨500036, by rfl⟩ : syracuseStep 2666861 = 1000073) (by norm_num)
theorem B2666885 : Blo 1776089 2666885 := bbase (se 4 (by rfl) ⟨250020, by rfl⟩ : syracuseStep 2666885 = 500041) (by norm_num)
theorem B7590293 : Blo 1776089 7590293 := bbase (se 6 (by rfl) ⟨177897, by rfl⟩ : syracuseStep 7590293 = 355795) (by norm_num)
theorem B2666909 : Blo 1776089 2666909 := bbase (se 3 (by rfl) ⟨500045, by rfl⟩ : syracuseStep 2666909 = 1000091) (by norm_num)
theorem B2249137 : Blo 1776089 2249137 := bbase (se 2 (by rfl) ⟨843426, by rfl⟩ : syracuseStep 2249137 = 1686853) (by norm_num)
theorem B2134453 : Blo 1776089 2134453 := bbase (se 5 (by rfl) ⟨100052, by rfl⟩ : syracuseStep 2134453 = 200105) (by norm_num)
theorem B2666933 : Blo 1776089 2666933 := bbase (se 5 (by rfl) ⟨125012, by rfl⟩ : syracuseStep 2666933 = 250025) (by norm_num)
theorem B2666957 : Blo 1776089 2666957 := bbase (se 3 (by rfl) ⟨500054, by rfl⟩ : syracuseStep 2666957 = 1000109) (by norm_num)
theorem B2666981 : Blo 1776089 2666981 := bbase (se 4 (by rfl) ⟨250029, by rfl⟩ : syracuseStep 2666981 = 500059) (by norm_num)
theorem B5403125 : Blo 1776089 5403125 := bbase (se 5 (by rfl) ⟨253271, by rfl⟩ : syracuseStep 5403125 = 506543) (by norm_num)
theorem B2667005 : Blo 1776089 2667005 := bbase (se 3 (by rfl) ⟨500063, by rfl⟩ : syracuseStep 2667005 = 1000127) (by norm_num)
theorem B4051469 : Blo 1776089 4051469 := bbase (se 3 (by rfl) ⟨759650, by rfl⟩ : syracuseStep 4051469 = 1519301) (by norm_num)
theorem B2667029 : Blo 1776089 2667029 := bbase (se 6 (by rfl) ⟨62508, by rfl⟩ : syracuseStep 2667029 = 125017) (by norm_num)
theorem B2847269 : Blo 1776089 2847269 := bbase (se 4 (by rfl) ⟨266931, by rfl⟩ : syracuseStep 2847269 = 533863) (by norm_num)
theorem B2667053 : Blo 1776089 2667053 := bbase (se 3 (by rfl) ⟨500072, by rfl⟩ : syracuseStep 2667053 = 1000145) (by norm_num)
theorem B3600949 : Blo 1776089 3600949 := bbase (se 5 (by rfl) ⟨168794, by rfl⟩ : syracuseStep 3600949 = 337589) (by norm_num)
theorem B2667077 : Blo 1776089 2667077 := bbase (se 4 (by rfl) ⟨250038, by rfl⟩ : syracuseStep 2667077 = 500077) (by norm_num)
theorem B2249309 : Blo 1776089 2249309 := bbase (se 3 (by rfl) ⟨421745, by rfl⟩ : syracuseStep 2249309 = 843491) (by norm_num)
theorem B2667101 : Blo 1776089 2667101 := bbase (se 3 (by rfl) ⟨500081, by rfl⟩ : syracuseStep 2667101 = 1000163) (by norm_num)
theorem B1897069 : Blo 1776089 1897069 := bbase (se 3 (by rfl) ⟨355700, by rfl⟩ : syracuseStep 1897069 = 711401) (by norm_num)
theorem B2667125 : Blo 1776089 2667125 := bbase (se 5 (by rfl) ⟨125021, by rfl⟩ : syracuseStep 2667125 = 250043) (by norm_num)
theorem B6746773 : Blo 1776089 6746773 := bbase (se 6 (by rfl) ⟨158127, by rfl⟩ : syracuseStep 6746773 = 316255) (by norm_num)
theorem B2249365 : Blo 1776089 2249365 := bbase (se 6 (by rfl) ⟨52719, by rfl⟩ : syracuseStep 2249365 = 105439) (by norm_num)
theorem B1897129 : Blo 1776089 1897129 := bbase (se 2 (by rfl) ⟨711423, by rfl⟩ : syracuseStep 1897129 = 1422847) (by norm_num)
theorem B2134717 : Blo 1776089 2134717 := bbase (se 3 (by rfl) ⟨400259, by rfl⟩ : syracuseStep 2134717 = 800519) (by norm_num)
theorem B8540885 : Blo 1776089 8540885 := bbase (se 7 (by rfl) ⟨100088, by rfl⟩ : syracuseStep 8540885 = 200177) (by norm_num)
theorem B2847469 : Blo 1776089 2847469 := bbase (se 3 (by rfl) ⟨533900, by rfl⟩ : syracuseStep 2847469 = 1067801) (by norm_num)
theorem B11383541 : Blo 1776089 11383541 := bbase (se 5 (by rfl) ⟨533603, by rfl⟩ : syracuseStep 11383541 = 1067207) (by norm_num)
theorem B2249461 : Blo 1776089 2249461 := bbase (se 5 (by rfl) ⟨105443, by rfl⟩ : syracuseStep 2249461 = 210887) (by norm_num)
theorem B2134837 : Blo 1776089 2134837 := bbase (se 5 (by rfl) ⟨100070, by rfl⟩ : syracuseStep 2134837 = 200141) (by norm_num)
theorem B5059397 : Blo 1776089 5059397 := bbase (se 4 (by rfl) ⟨474318, by rfl⟩ : syracuseStep 5059397 = 948637) (by norm_num)
theorem B3371861 : Blo 1776089 3371861 := bbase (se 9 (by rfl) ⟨9878, by rfl⟩ : syracuseStep 3371861 = 19757) (by norm_num)
theorem B2249633 : Blo 1776089 2249633 := bbase (se 2 (by rfl) ⟨843612, by rfl⟩ : syracuseStep 2249633 = 1687225) (by norm_num)
theorem B6403013 : Blo 1776089 6403013 := bbase (se 4 (by rfl) ⟨600282, by rfl⟩ : syracuseStep 6403013 = 1200565) (by norm_num)
theorem B6747077 : Blo 1776089 6747077 := bbase (se 4 (by rfl) ⟨632538, by rfl⟩ : syracuseStep 6747077 = 1265077) (by norm_num)
theorem B2249689 : Blo 1776089 2249689 := bbase (se 2 (by rfl) ⟨843633, by rfl⟩ : syracuseStep 2249689 = 1687267) (by norm_num)
theorem B1998841 : Blo 1776089 1998841 := bbase (se 2 (by rfl) ⟨749565, by rfl⟩ : syracuseStep 1998841 = 1499131) (by norm_num)
theorem B4387805 : Blo 1776089 4387805 := bbase (se 3 (by rfl) ⟨822713, by rfl⟩ : syracuseStep 4387805 = 1645427) (by norm_num)
theorem B3372005 : Blo 1776089 3372005 := bbase (se 4 (by rfl) ⟨316125, by rfl⟩ : syracuseStep 3372005 = 632251) (by norm_num)
theorem B1897445 : Blo 1776089 1897445 := bbase (se 4 (by rfl) ⟨177885, by rfl⟩ : syracuseStep 1897445 = 355771) (by norm_num)
theorem B8999909 : Blo 1776089 8999909 := bbase (se 4 (by rfl) ⟨843741, by rfl⟩ : syracuseStep 8999909 = 1687483) (by norm_num)
theorem B2847725 : Blo 1776089 2847725 := bbase (se 3 (by rfl) ⟨533948, by rfl⟩ : syracuseStep 2847725 = 1067897) (by norm_num)
theorem B2249785 : Blo 1776089 2249785 := bbase (se 2 (by rfl) ⟨843669, by rfl⟩ : syracuseStep 2249785 = 1687339) (by norm_num)
theorem B4052045 : Blo 1776089 4052045 := bbase (se 3 (by rfl) ⟨759758, by rfl⟩ : syracuseStep 4052045 = 1519517) (by norm_num)
theorem B2249957 : Blo 1776089 2249957 := bbase (se 4 (by rfl) ⟨210933, by rfl⟩ : syracuseStep 2249957 = 421867) (by norm_num)
theorem B3372293 : Blo 1776089 3372293 := bbase (se 4 (by rfl) ⟨316152, by rfl⟩ : syracuseStep 3372293 = 632305) (by norm_num)
theorem B2250013 : Blo 1776089 2250013 := bbase (se 3 (by rfl) ⟨421877, by rfl⟩ : syracuseStep 2250013 = 843755) (by norm_num)
theorem B2250109 : Blo 1776089 2250109 := bbase (se 3 (by rfl) ⟨421895, by rfl⟩ : syracuseStep 2250109 = 843791) (by norm_num)
theorem B8992133 : Blo 1776089 8992133 := bbase (se 4 (by rfl) ⟨843012, by rfl⟩ : syracuseStep 8992133 = 1686025) (by norm_num)
theorem B3372445 : Blo 1776089 3372445 := bbase (se 3 (by rfl) ⟨632333, by rfl⟩ : syracuseStep 3372445 = 1264667) (by norm_num)
theorem B1897889 : Blo 1776089 1897889 := bbase (se 2 (by rfl) ⟨711708, by rfl⟩ : syracuseStep 1897889 = 1423417) (by norm_num)
theorem B5690837 : Blo 1776089 5690837 := bbase (se 7 (by rfl) ⟨66689, by rfl⟩ : syracuseStep 5690837 = 133379) (by norm_num)
theorem B1897949 : Blo 1776089 1897949 := bbase (se 3 (by rfl) ⟨355865, by rfl⟩ : syracuseStep 1897949 = 711731) (by norm_num)
theorem B2700797 : Blo 1776089 2700797 := bbase (se 3 (by rfl) ⟨506399, by rfl⟩ : syracuseStep 2700797 = 1012799) (by norm_num)
theorem B2250281 : Blo 1776089 2250281 := bbase (se 2 (by rfl) ⟨843855, by rfl⟩ : syracuseStep 2250281 = 1687711) (by norm_num)
theorem B4806229 : Blo 1776089 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B1898077 : Blo 1776089 1898077 := bbase (se 3 (by rfl) ⟨355889, by rfl⟩ : syracuseStep 1898077 = 711779) (by norm_num)
theorem B2250337 : Blo 1776089 2250337 := bbase (se 2 (by rfl) ⟨843876, by rfl⟩ : syracuseStep 2250337 = 1687753) (by norm_num)
theorem B2135693 : Blo 1776089 2135693 := bbase (se 3 (by rfl) ⟨400442, by rfl⟩ : syracuseStep 2135693 = 800885) (by norm_num)
theorem B3372749 : Blo 1776089 3372749 := bbase (se 3 (by rfl) ⟨632390, by rfl⟩ : syracuseStep 3372749 = 1264781) (by norm_num)
theorem B5994485 : Blo 1776089 5994485 := bbase (se 5 (by rfl) ⟨280991, by rfl⟩ : syracuseStep 5994485 = 561983) (by norm_num)
theorem B1898521 : Blo 1776089 1898521 := bbase (se 2 (by rfl) ⟨711945, by rfl⟩ : syracuseStep 1898521 = 1423891) (by norm_num)
theorem B2529397 : Blo 1776089 2529397 := bbase (se 5 (by rfl) ⟨118565, by rfl⟩ : syracuseStep 2529397 = 237131) (by norm_num)
theorem B7592069 : Blo 1776089 7592069 := bbase (se 4 (by rfl) ⟨711756, by rfl⟩ : syracuseStep 7592069 = 1423513) (by norm_num)
theorem B1898641 : Blo 1776089 1898641 := bbase (se 2 (by rfl) ⟨711990, by rfl⟩ : syracuseStep 1898641 = 1423981) (by norm_num)
theorem B46807253 : Blo 1776089 46807253 := bbase (se 7 (by rfl) ⟨548522, by rfl⟩ : syracuseStep 46807253 = 1097045) (by norm_num)
theorem B3651821 : Blo 1776089 3651821 := bbase (se 3 (by rfl) ⟨684716, by rfl⟩ : syracuseStep 3651821 = 1369433) (by norm_num)
theorem B9001205 : Blo 1776089 9001205 := bbase (se 5 (by rfl) ⟨421931, by rfl⟩ : syracuseStep 9001205 = 843863) (by norm_num)
theorem B3602765 : Blo 1776089 3602765 := bbase (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) (by norm_num)
theorem B4495733 : Blo 1776089 4495733 := bbase (se 5 (by rfl) ⟨210737, by rfl⟩ : syracuseStep 4495733 = 421475) (by norm_num)
theorem B5060981 : Blo 1776089 5060981 := bbase (se 5 (by rfl) ⟨237233, by rfl⟩ : syracuseStep 5060981 = 474467) (by norm_num)
theorem B5994917 : Blo 1776089 5994917 := bbase (se 4 (by rfl) ⟨562023, by rfl⟩ : syracuseStep 5994917 = 1124047) (by norm_num)
theorem B3373501 : Blo 1776089 3373501 := bbase (se 3 (by rfl) ⟨632531, by rfl⟩ : syracuseStep 3373501 = 1265063) (by norm_num)
theorem B2529733 : Blo 1776089 2529733 := bbase (se 4 (by rfl) ⟨237162, by rfl⟩ : syracuseStep 2529733 = 474325) (by norm_num)
theorem B3291589 : Blo 1776089 3291589 := bbase (se 4 (by rfl) ⟨308586, by rfl⟩ : syracuseStep 3291589 = 617173) (by norm_num)
theorem B4495925 : Blo 1776089 4495925 := bbase (se 5 (by rfl) ⟨210746, by rfl⟩ : syracuseStep 4495925 = 421493) (by norm_num)
theorem B3373645 : Blo 1776089 3373645 := bbase (se 3 (by rfl) ⟨632558, by rfl⟩ : syracuseStep 3373645 = 1265117) (by norm_num)
theorem B3996269 : Blo 1776089 3996269 := bbase (se 3 (by rfl) ⟨749300, by rfl⟩ : syracuseStep 3996269 = 1498601) (by norm_num)
theorem B8993429 : Blo 1776089 8993429 := bbase (se 6 (by rfl) ⟨210783, by rfl⟩ : syracuseStep 8993429 = 421567) (by norm_num)
theorem B2529949 : Blo 1776089 2529949 := bbase (se 3 (by rfl) ⟨474365, by rfl⟩ : syracuseStep 2529949 = 948731) (by norm_num)
theorem B3996341 : Blo 1776089 3996341 := bbase (se 5 (by rfl) ⟨187328, by rfl⟩ : syracuseStep 3996341 = 374657) (by norm_num)
theorem B10115765 : Blo 1776089 10115765 := bbase (se 5 (by rfl) ⟨474176, by rfl⟩ : syracuseStep 10115765 = 948353) (by norm_num)
theorem B3373805 : Blo 1776089 3373805 := bbase (se 3 (by rfl) ⟨632588, by rfl⟩ : syracuseStep 3373805 = 1265177) (by norm_num)
theorem B3996413 : Blo 1776089 3996413 := bbase (se 3 (by rfl) ⟨749327, by rfl⟩ : syracuseStep 3996413 = 1498655) (by norm_num)
theorem B6077189 : Blo 1776089 6077189 := bbase (se 4 (by rfl) ⟨569736, by rfl⟩ : syracuseStep 6077189 = 1139473) (by norm_num)
theorem B3996485 : Blo 1776089 3996485 := bbase (se 4 (by rfl) ⟨374670, by rfl⟩ : syracuseStep 3996485 = 749341) (by norm_num)
theorem B5995349 : Blo 1776089 5995349 := bbase (se 9 (by rfl) ⟨17564, by rfl⟩ : syracuseStep 5995349 = 35129) (by norm_num)
theorem B3373949 : Blo 1776089 3373949 := bbase (se 3 (by rfl) ⟨632615, by rfl⟩ : syracuseStep 3373949 = 1265231) (by norm_num)
theorem B3996557 : Blo 1776089 3996557 := bbase (se 3 (by rfl) ⟨749354, by rfl⟩ : syracuseStep 3996557 = 1498709) (by norm_num)
theorem B4496269 : Blo 1776089 4496269 := bbase (se 3 (by rfl) ⟨843050, by rfl⟩ : syracuseStep 4496269 = 1686101) (by norm_num)
theorem B3603373 : Blo 1776089 3603373 := bbase (se 3 (by rfl) ⟨675632, by rfl⟩ : syracuseStep 3603373 = 1351265) (by norm_num)
theorem B8534965 : Blo 1776089 8534965 := bbase (se 5 (by rfl) ⟨400076, by rfl⟩ : syracuseStep 8534965 = 800153) (by norm_num)
theorem B3996629 : Blo 1776089 3996629 := bbase (se 7 (by rfl) ⟨46835, by rfl⟩ : syracuseStep 3996629 = 93671) (by norm_num)
theorem B9608149 : Blo 1776089 9608149 := bbase (se 7 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 9608149 = 225191) (by norm_num)
theorem B2997229 : Blo 1776089 2997229 := bbase (se 3 (by rfl) ⟨561980, by rfl⟩ : syracuseStep 2997229 = 1123961) (by norm_num)
theorem B4496381 : Blo 1776089 4496381 := bbase (se 3 (by rfl) ⟨843071, by rfl⟩ : syracuseStep 4496381 = 1686143) (by norm_num)
theorem B2702341 : Blo 1776089 2702341 := bbase (se 4 (by rfl) ⟨253344, by rfl⟩ : syracuseStep 2702341 = 506689) (by norm_num)
theorem B6749189 : Blo 1776089 6749189 := bbase (se 4 (by rfl) ⟨632736, by rfl⟩ : syracuseStep 6749189 = 1265473) (by norm_num)
theorem B2530325 : Blo 1776089 2530325 := bbase (se 6 (by rfl) ⟨59304, by rfl⟩ : syracuseStep 2530325 = 118609) (by norm_num)
theorem B5061653 : Blo 1776089 5061653 := bbase (se 6 (by rfl) ⟨118632, by rfl⟩ : syracuseStep 5061653 = 237265) (by norm_num)
theorem B3996701 : Blo 1776089 3996701 := bbase (se 3 (by rfl) ⟨749381, by rfl⟩ : syracuseStep 3996701 = 1498763) (by norm_num)
theorem B2997317 : Blo 1776089 2997317 := bbase (se 4 (by rfl) ⟨280998, by rfl⟩ : syracuseStep 2997317 = 561997) (by norm_num)
theorem B3996773 : Blo 1776089 3996773 := bbase (se 4 (by rfl) ⟨374697, by rfl⟩ : syracuseStep 3996773 = 749395) (by norm_num)
theorem B27368597 : Blo 1776089 27368597 := bbase (se 6 (by rfl) ⟨641451, by rfl⟩ : syracuseStep 27368597 = 1282903) (by norm_num)
theorem B3374237 : Blo 1776089 3374237 := bbase (se 3 (by rfl) ⟨632669, by rfl⟩ : syracuseStep 3374237 = 1265339) (by norm_num)
theorem B3996845 : Blo 1776089 3996845 := bbase (se 3 (by rfl) ⟨749408, by rfl⟩ : syracuseStep 3996845 = 1498817) (by norm_num)
theorem B4496573 : Blo 1776089 4496573 := bbase (se 3 (by rfl) ⟨843107, by rfl⟩ : syracuseStep 4496573 = 1686215) (by norm_num)
theorem B2997445 : Blo 1776089 2997445 := bbase (se 4 (by rfl) ⟨281010, by rfl⟩ : syracuseStep 2997445 = 562021) (by norm_num)
theorem B3996917 : Blo 1776089 3996917 := bbase (se 5 (by rfl) ⟨187355, by rfl⟩ : syracuseStep 3996917 = 374711) (by norm_num)
theorem B4562173 : Blo 1776089 4562173 := bbase (se 3 (by rfl) ⟨855407, by rfl⟩ : syracuseStep 4562173 = 1710815) (by norm_num)
theorem B5995781 : Blo 1776089 5995781 := bbase (se 4 (by rfl) ⟨562104, by rfl⟩ : syracuseStep 5995781 = 1124209) (by norm_num)
theorem B5692693 : Blo 1776089 5692693 := bbase (se 6 (by rfl) ⟨133422, by rfl⟩ : syracuseStep 5692693 = 266845) (by norm_num)
theorem B2997533 : Blo 1776089 2997533 := bbase (se 3 (by rfl) ⟨562037, by rfl⟩ : syracuseStep 2997533 = 1124075) (by norm_num)
theorem B6749477 : Blo 1776089 6749477 := bbase (se 4 (by rfl) ⟨632763, by rfl⟩ : syracuseStep 6749477 = 1265527) (by norm_num)
theorem B1998121 : Blo 1776089 1998121 := bbase (se 2 (by rfl) ⟨749295, by rfl⟩ : syracuseStep 1998121 = 1498591) (by norm_num)
theorem B3374389 : Blo 1776089 3374389 := bbase (se 5 (by rfl) ⟨158174, by rfl⟩ : syracuseStep 3374389 = 316349) (by norm_num)
theorem B3996989 : Blo 1776089 3996989 := bbase (se 3 (by rfl) ⟨749435, by rfl⟩ : syracuseStep 3996989 = 1498871) (by norm_num)
theorem B1998157 : Blo 1776089 1998157 := bbase (se 3 (by rfl) ⟨374654, by rfl⟩ : syracuseStep 1998157 = 749309) (by norm_num)
theorem B1998193 : Blo 1776089 1998193 := bbase (se 2 (by rfl) ⟨749322, by rfl⟩ : syracuseStep 1998193 = 1498645) (by norm_num)
theorem B3202429 : Blo 1776089 3202429 := bbase (se 3 (by rfl) ⟨600455, by rfl⟩ : syracuseStep 3202429 = 1200911) (by norm_num)
theorem B3997061 : Blo 1776089 3997061 := bbase (se 4 (by rfl) ⟨374724, by rfl⟩ : syracuseStep 3997061 = 749449) (by norm_num)
theorem B1998229 : Blo 1776089 1998229 := bbase (se 6 (by rfl) ⟨46833, by rfl⟩ : syracuseStep 1998229 = 93667) (by norm_num)
theorem B2997661 : Blo 1776089 2997661 := bbase (se 3 (by rfl) ⟨562061, by rfl⟩ : syracuseStep 2997661 = 1124123) (by norm_num)
theorem B1998265 : Blo 1776089 1998265 := bbase (se 2 (by rfl) ⟨749349, by rfl⟩ : syracuseStep 1998265 = 1498699) (by norm_num)
theorem B5062085 : Blo 1776089 5062085 := bbase (se 4 (by rfl) ⟨474570, by rfl⟩ : syracuseStep 5062085 = 949141) (by norm_num)
theorem B3997133 : Blo 1776089 3997133 := bbase (se 3 (by rfl) ⟨749462, by rfl⟩ : syracuseStep 3997133 = 1498925) (by norm_num)
theorem B1998301 : Blo 1776089 1998301 := bbase (se 3 (by rfl) ⟨374681, by rfl⟩ : syracuseStep 1998301 = 749363) (by norm_num)
theorem B2997749 : Blo 1776089 2997749 := bbase (se 5 (by rfl) ⟨140519, by rfl⟩ : syracuseStep 2997749 = 281039) (by norm_num)
theorem B6839797 : Blo 1776089 6839797 := bbase (se 5 (by rfl) ⟨320615, by rfl⟩ : syracuseStep 6839797 = 641231) (by norm_num)
theorem B1998337 : Blo 1776089 1998337 := bbase (se 2 (by rfl) ⟨749376, by rfl⟩ : syracuseStep 1998337 = 1498753) (by norm_num)
theorem B3202573 : Blo 1776089 3202573 := bbase (se 3 (by rfl) ⟨600482, by rfl⟩ : syracuseStep 3202573 = 1200965) (by norm_num)
theorem B3997205 : Blo 1776089 3997205 := bbase (se 6 (by rfl) ⟨93684, by rfl⟩ : syracuseStep 3997205 = 187369) (by norm_num)
theorem B4496917 : Blo 1776089 4496917 := bbase (se 6 (by rfl) ⟨105396, by rfl⟩ : syracuseStep 4496917 = 210793) (by norm_num)
theorem B16440853 : Blo 1776089 16440853 := bbase (se 6 (by rfl) ⟨385332, by rfl⟩ : syracuseStep 16440853 = 770665) (by norm_num)
theorem B1998373 : Blo 1776089 1998373 := bbase (se 4 (by rfl) ⟨187347, by rfl⟩ : syracuseStep 1998373 = 374695) (by norm_num)
theorem B6159925 : Blo 1776089 6159925 := bbase (se 5 (by rfl) ⟨288746, by rfl⟩ : syracuseStep 6159925 = 577493) (by norm_num)
theorem B1998409 : Blo 1776089 1998409 := bbase (se 2 (by rfl) ⟨749403, by rfl⟩ : syracuseStep 1998409 = 1498807) (by norm_num)
theorem B3997277 : Blo 1776089 3997277 := bbase (se 3 (by rfl) ⟨749489, by rfl⟩ : syracuseStep 3997277 = 1498979) (by norm_num)
theorem B3374693 : Blo 1776089 3374693 := bbase (se 4 (by rfl) ⟨316377, by rfl⟩ : syracuseStep 3374693 = 632755) (by norm_num)
theorem B1998445 : Blo 1776089 1998445 := bbase (se 3 (by rfl) ⟨374708, by rfl⟩ : syracuseStep 1998445 = 749417) (by norm_num)
theorem B4267637 : Blo 1776089 4267637 := bbase (se 5 (by rfl) ⟨200045, by rfl⟩ : syracuseStep 4267637 = 400091) (by norm_num)
theorem B2997877 : Blo 1776089 2997877 := bbase (se 5 (by rfl) ⟨140525, by rfl⟩ : syracuseStep 2997877 = 281051) (by norm_num)
theorem B4497029 : Blo 1776089 4497029 := bbase (se 4 (by rfl) ⟨421596, by rfl⟩ : syracuseStep 4497029 = 843193) (by norm_num)
theorem B1998481 : Blo 1776089 1998481 := bbase (se 2 (by rfl) ⟨749430, by rfl⟩ : syracuseStep 1998481 = 1498861) (by norm_num)
theorem B25960085 : Blo 1776089 25960085 := bbase (se 6 (by rfl) ⟨608439, by rfl⟩ : syracuseStep 25960085 = 1216879) (by norm_num)
theorem B3997349 : Blo 1776089 3997349 := bbase (se 4 (by rfl) ⟨374751, by rfl⟩ : syracuseStep 3997349 = 749503) (by norm_num)
theorem B1998517 : Blo 1776089 1998517 := bbase (se 5 (by rfl) ⟨93680, by rfl⟩ : syracuseStep 1998517 = 187361) (by norm_num)
theorem B5996213 : Blo 1776089 5996213 := bbase (se 5 (by rfl) ⟨281072, by rfl⟩ : syracuseStep 5996213 = 562145) (by norm_num)
theorem B2997965 : Blo 1776089 2997965 := bbase (se 3 (by rfl) ⟨562118, by rfl⟩ : syracuseStep 2997965 = 1124237) (by norm_num)
theorem B1998553 : Blo 1776089 1998553 := bbase (se 2 (by rfl) ⟨749457, by rfl⟩ : syracuseStep 1998553 = 1498915) (by norm_num)
theorem B3997421 : Blo 1776089 3997421 := bbase (se 3 (by rfl) ⟨749516, by rfl⟩ : syracuseStep 3997421 = 1499033) (by norm_num)
theorem B1998589 : Blo 1776089 1998589 := bbase (se 3 (by rfl) ⟨374735, by rfl⟩ : syracuseStep 1998589 = 749471) (by norm_num)
theorem B1998625 : Blo 1776089 1998625 := bbase (se 2 (by rfl) ⟨749484, by rfl⟩ : syracuseStep 1998625 = 1498969) (by norm_num)
theorem B3997493 : Blo 1776089 3997493 := bbase (se 5 (by rfl) ⟨187382, by rfl⟩ : syracuseStep 3997493 = 374765) (by norm_num)
theorem B1998661 : Blo 1776089 1998661 := bbase (se 4 (by rfl) ⟨187374, by rfl⟩ : syracuseStep 1998661 = 374749) (by norm_num)
theorem B4497221 : Blo 1776089 4497221 := bbase (se 4 (by rfl) ⟨421614, by rfl⟩ : syracuseStep 4497221 = 843229) (by norm_num)
theorem B2998093 : Blo 1776089 2998093 := bbase (se 3 (by rfl) ⟨562142, by rfl⟩ : syracuseStep 2998093 = 1124285) (by norm_num)
theorem B1998697 : Blo 1776089 1998697 := bbase (se 2 (by rfl) ⟨749511, by rfl⟩ : syracuseStep 1998697 = 1499023) (by norm_num)
theorem B3997565 : Blo 1776089 3997565 := bbase (se 3 (by rfl) ⟨749543, by rfl⟩ : syracuseStep 3997565 = 1499087) (by norm_num)
theorem B1998733 : Blo 1776089 1998733 := bbase (se 3 (by rfl) ⟨374762, by rfl⟩ : syracuseStep 1998733 = 749525) (by norm_num)
theorem B2998181 : Blo 1776089 2998181 := bbase (se 4 (by rfl) ⟨281079, by rfl⟩ : syracuseStep 2998181 = 562159) (by norm_num)
theorem B8994725 : Blo 1776089 8994725 := bbase (se 4 (by rfl) ⟨843255, by rfl⟩ : syracuseStep 8994725 = 1686511) (by norm_num)
theorem B1998769 : Blo 1776089 1998769 := bbase (se 2 (by rfl) ⟨749538, by rfl⟩ : syracuseStep 1998769 = 1499077) (by norm_num)
theorem B3997637 : Blo 1776089 3997637 := bbase (se 4 (by rfl) ⟨374778, by rfl⟩ : syracuseStep 3997637 = 749557) (by norm_num)
theorem B1998805 : Blo 1776089 1998805 := bbase (se 7 (by rfl) ⟨23423, by rfl⟩ : syracuseStep 1998805 = 46847) (by norm_num)
theorem B1777667 : Blo 1776089 1777667 := bstep (se 1 (by rfl) ⟨1333250, by rfl⟩ : syracuseStep 1777667 = 2666501) B2666501
theorem B2998289 : Blo 1776089 2998289 := bstep (se 2 (by rfl) ⟨1124358, by rfl⟩ : syracuseStep 2998289 = 2248717) B2248717
theorem B1777683 : Blo 1776089 1777683 := bstep (se 1 (by rfl) ⟨1333262, by rfl⟩ : syracuseStep 1777683 = 2666525) B2666525
theorem B1777699 : Blo 1776089 1777699 := bstep (se 1 (by rfl) ⟨1333274, by rfl⟩ : syracuseStep 1777699 = 2666549) B2666549
theorem B3997745 : Blo 1776089 3997745 := bstep (se 2 (by rfl) ⟨1499154, by rfl⟩ : syracuseStep 3997745 = 2998309) B2998309
theorem B1777715 : Blo 1776089 1777715 := bstep (se 1 (by rfl) ⟨1333286, by rfl⟩ : syracuseStep 1777715 = 2666573) B2666573
theorem B3997763 : Blo 1776089 3997763 := bstep (se 1 (by rfl) ⟨2998322, by rfl⟩ : syracuseStep 3997763 = 5996645) B5996645
theorem B1777731 : Blo 1776089 1777731 := bstep (se 1 (by rfl) ⟨1333298, by rfl⟩ : syracuseStep 1777731 = 2666597) B2666597
theorem B6078545 : Blo 1776089 6078545 := bstep (se 2 (by rfl) ⟨2279454, by rfl⟩ : syracuseStep 6078545 = 4558909) B4558909
theorem B1998931 : Blo 1776089 1998931 := bstep (se 1 (by rfl) ⟨1499198, by rfl⟩ : syracuseStep 1998931 = 2998397) B2998397
theorem B1777747 : Blo 1776089 1777747 := bstep (se 1 (by rfl) ⟨1333310, by rfl⟩ : syracuseStep 1777747 = 2666621) B2666621
theorem B1777763 : Blo 1776089 1777763 := bstep (se 1 (by rfl) ⟨1333322, by rfl⟩ : syracuseStep 1777763 = 2666645) B2666645
theorem B5062769 : Blo 1776089 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B1777779 : Blo 1776089 1777779 := bstep (se 1 (by rfl) ⟨1333334, by rfl⟩ : syracuseStep 1777779 = 2666669) B2666669
theorem B1777795 : Blo 1776089 1777795 := bstep (se 1 (by rfl) ⟨1333346, by rfl⟩ : syracuseStep 1777795 = 2666693) B2666693
theorem B10125445 : Blo 1776089 10125445 := bstep (se 4 (by rfl) ⟨949260, by rfl⟩ : syracuseStep 10125445 = 1898521) B1898521
theorem B2998417 : Blo 1776089 2998417 := bstep (se 2 (by rfl) ⟨1124406, by rfl⟩ : syracuseStep 2998417 = 2248813) B2248813
theorem B1777811 : Blo 1776089 1777811 := bstep (se 1 (by rfl) ⟨1333358, by rfl⟩ : syracuseStep 1777811 = 2666717) B2666717
theorem B1777827 : Blo 1776089 1777827 := bstep (se 1 (by rfl) ⟨1333370, by rfl⟩ : syracuseStep 1777827 = 2666741) B2666741
theorem B2998451 : Blo 1776089 2998451 := bstep (se 1 (by rfl) ⟨2248838, by rfl⟩ : syracuseStep 2998451 = 4497677) B4497677
theorem B1777843 : Blo 1776089 1777843 := bstep (se 1 (by rfl) ⟨1333382, by rfl⟩ : syracuseStep 1777843 = 2666765) B2666765
theorem B2531521 : Blo 1776089 2531521 := bstep (se 2 (by rfl) ⟨949320, by rfl⟩ : syracuseStep 2531521 = 1898641) B1898641
theorem B1777859 : Blo 1776089 1777859 := bstep (se 1 (by rfl) ⟨1333394, by rfl⟩ : syracuseStep 1777859 = 2666789) B2666789
theorem B12804293 : Blo 1776089 12804293 := bstep (se 4 (by rfl) ⟨1200402, by rfl⟩ : syracuseStep 12804293 = 2400805) B2400805
theorem B5996753 : Blo 1776089 5996753 := bstep (se 2 (by rfl) ⟨2248782, by rfl⟩ : syracuseStep 5996753 = 4497565) B4497565
theorem B1777875 : Blo 1776089 1777875 := bstep (se 1 (by rfl) ⟨1333406, by rfl⟩ : syracuseStep 1777875 = 2666813) B2666813
theorem B1999075 : Blo 1776089 1999075 := bstep (se 1 (by rfl) ⟨1499306, by rfl⟩ : syracuseStep 1999075 = 2998613) B2998613
theorem B1777891 : Blo 1776089 1777891 := bstep (se 1 (by rfl) ⟨1333418, by rfl⟩ : syracuseStep 1777891 = 2666837) B2666837
theorem B6750449 : Blo 1776089 6750449 := bstep (se 2 (by rfl) ⟨2531418, by rfl⟩ : syracuseStep 6750449 = 5062837) B5062837
theorem B1777907 : Blo 1776089 1777907 := bstep (se 1 (by rfl) ⟨1333430, by rfl⟩ : syracuseStep 1777907 = 2666861) B2666861
theorem B1777923 : Blo 1776089 1777923 := bstep (se 1 (by rfl) ⟨1333442, by rfl⟩ : syracuseStep 1777923 = 2666885) B2666885
theorem B1777939 : Blo 1776089 1777939 := bstep (se 1 (by rfl) ⟨1333454, by rfl⟩ : syracuseStep 1777939 = 2666909) B2666909
theorem B1777955 : Blo 1776089 1777955 := bstep (se 1 (by rfl) ⟨1333466, by rfl⟩ : syracuseStep 1777955 = 2666933) B2666933
theorem B2998579 : Blo 1776089 2998579 := bstep (se 1 (by rfl) ⟨2248934, by rfl⟩ : syracuseStep 2998579 = 4497869) B4497869
theorem B1777971 : Blo 1776089 1777971 := bstep (se 1 (by rfl) ⟨1333478, by rfl⟩ : syracuseStep 1777971 = 2666957) B2666957
theorem B1777987 : Blo 1776089 1777987 := bstep (se 1 (by rfl) ⟨1333490, by rfl⟩ : syracuseStep 1777987 = 2666981) B2666981
theorem B12157253 : Blo 1776089 12157253 := bstep (se 4 (by rfl) ⟨1139742, by rfl⟩ : syracuseStep 12157253 = 2279485) B2279485
theorem B3998033 : Blo 1776089 3998033 := bstep (se 2 (by rfl) ⟨1499262, by rfl⟩ : syracuseStep 3998033 = 2998525) B2998525
theorem B1778003 : Blo 1776089 1778003 := bstep (se 1 (by rfl) ⟨1333502, by rfl⟩ : syracuseStep 1778003 = 2667005) B2667005
theorem B3998051 : Blo 1776089 3998051 := bstep (se 1 (by rfl) ⟨2998538, by rfl⟩ : syracuseStep 3998051 = 5997077) B5997077
theorem B1778019 : Blo 1776089 1778019 := bstep (se 1 (by rfl) ⟨1333514, by rfl⟩ : syracuseStep 1778019 = 2667029) B2667029
theorem B3039601 : Blo 1776089 3039601 := bstep (se 2 (by rfl) ⟨1139850, by rfl⟩ : syracuseStep 3039601 = 2279701) B2279701
theorem B5693809 : Blo 1776089 5693809 := bstep (se 2 (by rfl) ⟨2135178, by rfl⟩ : syracuseStep 5693809 = 4270357) B4270357
theorem B1999219 : Blo 1776089 1999219 := bstep (se 1 (by rfl) ⟨1499414, by rfl⟩ : syracuseStep 1999219 = 2998829) B2998829
theorem B1778035 : Blo 1776089 1778035 := bstep (se 1 (by rfl) ⟨1333526, by rfl⟩ : syracuseStep 1778035 = 2667053) B2667053
theorem B1778051 : Blo 1776089 1778051 := bstep (se 1 (by rfl) ⟨1333538, by rfl⟩ : syracuseStep 1778051 = 2667077) B2667077
theorem B1778067 : Blo 1776089 1778067 := bstep (se 1 (by rfl) ⟨1333550, by rfl⟩ : syracuseStep 1778067 = 2667101) B2667101
theorem B1778083 : Blo 1776089 1778083 := bstep (se 1 (by rfl) ⟨1333562, by rfl⟩ : syracuseStep 1778083 = 2667125) B2667125
theorem B2998721 : Blo 1776089 2998721 := bstep (se 2 (by rfl) ⟨1124520, by rfl⟩ : syracuseStep 2998721 = 2249041) B2249041
theorem B3039697 : Blo 1776089 3039697 := bstep (se 2 (by rfl) ⟨1139886, by rfl⟩ : syracuseStep 3039697 = 2279773) B2279773
theorem B5693923 : Blo 1776089 5693923 := bstep (se 1 (by rfl) ⟨4270442, by rfl⟩ : syracuseStep 5693923 = 8540885) B8540885
theorem B5767661 : Blo 1776089 5767661 := bstep (se 3 (by rfl) ⟨1081436, by rfl⟩ : syracuseStep 5767661 = 2162873) B2162873
theorem B1999363 : Blo 1776089 1999363 := bstep (se 1 (by rfl) ⟨1499522, by rfl⟩ : syracuseStep 1999363 = 2999045) B2999045
theorem B2998849 : Blo 1776089 2998849 := bstep (se 2 (by rfl) ⟨1124568, by rfl⟩ : syracuseStep 2998849 = 2249137) B2249137
theorem B4498001 : Blo 1776089 4498001 := bstep (se 2 (by rfl) ⟨1686750, by rfl⟩ : syracuseStep 4498001 = 3373501) B3373501
theorem B2998883 : Blo 1776089 2998883 := bstep (se 1 (by rfl) ⟨2249162, by rfl⟩ : syracuseStep 2998883 = 4498325) B4498325
theorem B15188579 : Blo 1776089 15188579 := bstep (se 1 (by rfl) ⟨11391434, by rfl⟩ : syracuseStep 15188579 = 22782869) B22782869
theorem B3998321 : Blo 1776089 3998321 := bstep (se 2 (by rfl) ⟨1499370, by rfl⟩ : syracuseStep 3998321 = 2998741) B2998741
theorem B4268675 : Blo 1776089 4268675 := bstep (se 1 (by rfl) ⟨3201506, by rfl⟩ : syracuseStep 4268675 = 6403013) B6403013
theorem B4498051 : Blo 1776089 4498051 := bstep (se 1 (by rfl) ⟨3373538, by rfl⟩ : syracuseStep 4498051 = 6747077) B6747077
theorem B3998339 : Blo 1776089 3998339 := bstep (se 1 (by rfl) ⟨2998754, by rfl⟩ : syracuseStep 3998339 = 5997509) B5997509
theorem B1999507 : Blo 1776089 1999507 := bstep (se 1 (by rfl) ⟨1499630, by rfl⟩ : syracuseStep 1999507 = 2999261) B2999261
theorem B2999011 : Blo 1776089 2999011 := bstep (se 1 (by rfl) ⟨2249258, by rfl⟩ : syracuseStep 2999011 = 4498517) B4498517
theorem B5997293 : Blo 1776089 5997293 := bstep (se 3 (by rfl) ⟨1124492, by rfl⟩ : syracuseStep 5997293 = 2248985) B2248985
theorem B4801265 : Blo 1776089 4801265 := bstep (se 2 (by rfl) ⟨1800474, by rfl⟩ : syracuseStep 4801265 = 3600949) B3600949
theorem B4498193 : Blo 1776089 4498193 := bstep (se 2 (by rfl) ⟨1686822, by rfl⟩ : syracuseStep 4498193 = 3373645) B3373645
theorem B5997347 : Blo 1776089 5997347 := bstep (se 1 (by rfl) ⟨4498010, by rfl⟩ : syracuseStep 5997347 = 8996021) B8996021
theorem B1999651 : Blo 1776089 1999651 := bstep (se 1 (by rfl) ⟨1499738, by rfl⟩ : syracuseStep 1999651 = 2999477) B2999477
theorem B3203921 : Blo 1776089 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B8995697 : Blo 1776089 8995697 := bstep (se 2 (by rfl) ⟨3373386, by rfl⟩ : syracuseStep 8995697 = 6746773) B6746773
theorem B2999153 : Blo 1776089 2999153 := bstep (se 2 (by rfl) ⟨1124682, by rfl⟩ : syracuseStep 2999153 = 2249365) B2249365
theorem B3998609 : Blo 1776089 3998609 := bstep (se 2 (by rfl) ⟨1499478, by rfl⟩ : syracuseStep 3998609 = 2998957) B2998957
theorem B3998627 : Blo 1776089 3998627 := bstep (se 1 (by rfl) ⟨2998970, by rfl⟩ : syracuseStep 3998627 = 5997941) B5997941
theorem B1999795 : Blo 1776089 1999795 := bstep (se 1 (by rfl) ⟨1499846, by rfl⟩ : syracuseStep 1999795 = 2999693) B2999693
theorem B3793891 : Blo 1776089 3793891 := bstep (se 1 (by rfl) ⟨2845418, by rfl⟩ : syracuseStep 3793891 = 5690837) B5690837
theorem B20251619 : Blo 1776089 20251619 := bstep (se 1 (by rfl) ⟨15188714, by rfl⟩ : syracuseStep 20251619 = 30377429) B30377429
theorem B2999281 : Blo 1776089 2999281 := bstep (se 2 (by rfl) ⟨1124730, by rfl⟩ : syracuseStep 2999281 = 2249461) B2249461
theorem B2999315 : Blo 1776089 2999315 := bstep (se 1 (by rfl) ⟨2249486, by rfl⟩ : syracuseStep 2999315 = 4498973) B4498973
theorem B5997617 : Blo 1776089 5997617 := bstep (se 2 (by rfl) ⟨2249106, by rfl⟩ : syracuseStep 5997617 = 4498213) B4498213
theorem B1999939 : Blo 1776089 1999939 := bstep (se 1 (by rfl) ⟨1499954, by rfl⟩ : syracuseStep 1999939 = 2999909) B2999909
theorem B12330053 : Blo 1776089 12330053 := bstep (se 4 (by rfl) ⟨1155942, by rfl⟩ : syracuseStep 12330053 = 2311885) B2311885
theorem B2999443 : Blo 1776089 2999443 := bstep (se 1 (by rfl) ⟨2249582, by rfl⟩ : syracuseStep 2999443 = 4499165) B4499165
theorem B6931619 : Blo 1776089 6931619 := bstep (se 1 (by rfl) ⟨5198714, by rfl⟩ : syracuseStep 6931619 = 10397429) B10397429
theorem B3998897 : Blo 1776089 3998897 := bstep (se 2 (by rfl) ⟨1499586, by rfl⟩ : syracuseStep 3998897 = 2999173) B2999173
theorem B5694641 : Blo 1776089 5694641 := bstep (se 2 (by rfl) ⟨2135490, by rfl⟩ : syracuseStep 5694641 = 4270981) B4270981
theorem B3998915 : Blo 1776089 3998915 := bstep (se 1 (by rfl) ⟨2999186, by rfl⟩ : syracuseStep 3998915 = 5998373) B5998373
theorem B2000083 : Blo 1776089 2000083 := bstep (se 1 (by rfl) ⟨1500062, by rfl⟩ : syracuseStep 2000083 = 3000125) B3000125
theorem B11379953 : Blo 1776089 11379953 := bstep (se 2 (by rfl) ⟨4267482, by rfl⟩ : syracuseStep 11379953 = 8534965) B8534965
theorem B2999585 : Blo 1776089 2999585 := bstep (se 2 (by rfl) ⟨1124844, by rfl⟩ : syracuseStep 2999585 = 2249689) B2249689
theorem B6489379 : Blo 1776089 6489379 := bstep (se 1 (by rfl) ⟨4867034, by rfl⟩ : syracuseStep 6489379 = 9734069) B9734069
theorem B7202125 : Blo 1776089 7202125 := bstep (se 3 (by rfl) ⟨1350398, by rfl⟩ : syracuseStep 7202125 = 2700797) B2700797
theorem B2000227 : Blo 1776089 2000227 := bstep (se 1 (by rfl) ⟨1500170, by rfl⟩ : syracuseStep 2000227 = 3000341) B3000341
theorem B2999713 : Blo 1776089 2999713 := bstep (se 2 (by rfl) ⟨1124892, by rfl⟩ : syracuseStep 2999713 = 2249785) B2249785
theorem B2999747 : Blo 1776089 2999747 := bstep (se 1 (by rfl) ⟨2249810, by rfl⟩ : syracuseStep 2999747 = 4499621) B4499621
theorem B3999185 : Blo 1776089 3999185 := bstep (se 2 (by rfl) ⟨1499694, by rfl⟩ : syracuseStep 3999185 = 2999389) B2999389
theorem B3999203 : Blo 1776089 3999203 := bstep (se 1 (by rfl) ⟨2999402, by rfl⟩ : syracuseStep 3999203 = 5998805) B5998805
theorem B31204835 : Blo 1776089 31204835 := bstep (se 1 (by rfl) ⟨23403626, by rfl⟩ : syracuseStep 31204835 = 46807253) B46807253
theorem B2434547 : Blo 1776089 2434547 := bstep (se 1 (by rfl) ⟨1825910, by rfl⟩ : syracuseStep 2434547 = 3651821) B3651821
theorem B10806833 : Blo 1776089 10806833 := bstep (se 2 (by rfl) ⟨4052562, by rfl⟩ : syracuseStep 10806833 = 8105125) B8105125
theorem B2999875 : Blo 1776089 2999875 := bstep (se 1 (by rfl) ⟨2249906, by rfl⟩ : syracuseStep 2999875 = 4499813) B4499813
theorem B5998157 : Blo 1776089 5998157 := bstep (se 3 (by rfl) ⟨1124654, by rfl⟩ : syracuseStep 5998157 = 2249309) B2249309
theorem B13502051 : Blo 1776089 13502051 := bstep (se 1 (by rfl) ⟨10126538, by rfl⟩ : syracuseStep 13502051 = 20253077) B20253077
theorem B5998211 : Blo 1776089 5998211 := bstep (se 1 (by rfl) ⟨4498658, by rfl⟩ : syracuseStep 5998211 = 8997317) B8997317
theorem B5695181 : Blo 1776089 5695181 := bstep (se 3 (by rfl) ⟨1067846, by rfl⟩ : syracuseStep 5695181 = 2135693) B2135693
theorem B3000017 : Blo 1776089 3000017 := bstep (se 2 (by rfl) ⟨1125006, by rfl⟩ : syracuseStep 3000017 = 2250013) B2250013
theorem B2664161 : Blo 1776089 2664161 := bstep (se 2 (by rfl) ⟨999060, by rfl⟩ : syracuseStep 2664161 = 1998121) B1998121
theorem B4499185 : Blo 1776089 4499185 := bstep (se 2 (by rfl) ⟨1687194, by rfl⟩ : syracuseStep 4499185 = 3374389) B3374389
theorem B3999473 : Blo 1776089 3999473 := bstep (se 2 (by rfl) ⟨1499802, by rfl⟩ : syracuseStep 3999473 = 2999605) B2999605
theorem B2664179 : Blo 1776089 2664179 := bstep (se 1 (by rfl) ⟨1998134, by rfl⟩ : syracuseStep 2664179 = 3996269) B3996269
theorem B3999491 : Blo 1776089 3999491 := bstep (se 1 (by rfl) ⟨2999618, by rfl⟩ : syracuseStep 3999491 = 5999237) B5999237
theorem B2664209 : Blo 1776089 2664209 := bstep (se 2 (by rfl) ⟨999078, by rfl⟩ : syracuseStep 2664209 = 1998157) B1998157
theorem B2664227 : Blo 1776089 2664227 := bstep (se 1 (by rfl) ⟨1998170, by rfl⟩ : syracuseStep 2664227 = 3996341) B3996341
theorem B6743843 : Blo 1776089 6743843 := bstep (se 1 (by rfl) ⟨5057882, by rfl⟩ : syracuseStep 6743843 = 10115765) B10115765
theorem B6743857 : Blo 1776089 6743857 := bstep (se 2 (by rfl) ⟨2528946, by rfl⟩ : syracuseStep 6743857 = 5057893) B5057893
theorem B2664257 : Blo 1776089 2664257 := bstep (se 2 (by rfl) ⟨999096, by rfl⟩ : syracuseStep 2664257 = 1998193) B1998193
theorem B4269905 : Blo 1776089 4269905 := bstep (se 2 (by rfl) ⟨1601214, by rfl⟩ : syracuseStep 4269905 = 3202429) B3202429
theorem B3000145 : Blo 1776089 3000145 := bstep (se 2 (by rfl) ⟨1125054, by rfl⟩ : syracuseStep 3000145 = 2250109) B2250109
theorem B2664275 : Blo 1776089 2664275 := bstep (se 1 (by rfl) ⟨1998206, by rfl⟩ : syracuseStep 2664275 = 3996413) B3996413
theorem B2664305 : Blo 1776089 2664305 := bstep (se 2 (by rfl) ⟨999114, by rfl⟩ : syracuseStep 2664305 = 1998229) B1998229
theorem B3000179 : Blo 1776089 3000179 := bstep (se 1 (by rfl) ⟨2250134, by rfl⟩ : syracuseStep 3000179 = 4500269) B4500269
theorem B2664323 : Blo 1776089 2664323 := bstep (se 1 (by rfl) ⟨1998242, by rfl⟩ : syracuseStep 2664323 = 3996485) B3996485
theorem B5998481 : Blo 1776089 5998481 := bstep (se 2 (by rfl) ⟨2249430, by rfl⟩ : syracuseStep 5998481 = 4498861) B4498861
theorem B2664353 : Blo 1776089 2664353 := bstep (se 2 (by rfl) ⟨999132, by rfl⟩ : syracuseStep 2664353 = 1998265) B1998265
theorem B2664371 : Blo 1776089 2664371 := bstep (se 1 (by rfl) ⟨1998278, by rfl⟩ : syracuseStep 2664371 = 3996557) B3996557
theorem B2664401 : Blo 1776089 2664401 := bstep (se 2 (by rfl) ⟨999150, by rfl⟩ : syracuseStep 2664401 = 1998301) B1998301
theorem B2664419 : Blo 1776089 2664419 := bstep (se 1 (by rfl) ⟨1998314, by rfl⟩ : syracuseStep 2664419 = 3996629) B3996629
theorem B9119729 : Blo 1776089 9119729 := bstep (se 2 (by rfl) ⟨3419898, by rfl⟩ : syracuseStep 9119729 = 6839797) B6839797
theorem B3000307 : Blo 1776089 3000307 := bstep (se 1 (by rfl) ⟨2250230, by rfl⟩ : syracuseStep 3000307 = 4500461) B4500461
theorem B2664449 : Blo 1776089 2664449 := bstep (se 2 (by rfl) ⟨999168, by rfl⟩ : syracuseStep 2664449 = 1998337) B1998337
theorem B4499459 : Blo 1776089 4499459 := bstep (se 1 (by rfl) ⟨3374594, by rfl⟩ : syracuseStep 4499459 = 6749189) B6749189
theorem B16205837 : Blo 1776089 16205837 := bstep (se 3 (by rfl) ⟨3038594, by rfl⟩ : syracuseStep 16205837 = 6077189) B6077189
theorem B4270097 : Blo 1776089 4270097 := bstep (se 2 (by rfl) ⟨1601286, by rfl⟩ : syracuseStep 4270097 = 3202573) B3202573
theorem B3999761 : Blo 1776089 3999761 := bstep (se 2 (by rfl) ⟨1499910, by rfl⟩ : syracuseStep 3999761 = 2999821) B2999821
theorem B2664467 : Blo 1776089 2664467 := bstep (se 1 (by rfl) ⟨1998350, by rfl⟩ : syracuseStep 2664467 = 3996701) B3996701
theorem B3999779 : Blo 1776089 3999779 := bstep (se 1 (by rfl) ⟨2999834, by rfl⟩ : syracuseStep 3999779 = 5999669) B5999669
theorem B2664497 : Blo 1776089 2664497 := bstep (se 2 (by rfl) ⟨999186, by rfl⟩ : syracuseStep 2664497 = 1998373) B1998373
theorem B2664515 : Blo 1776089 2664515 := bstep (se 1 (by rfl) ⟨1998386, by rfl⟩ : syracuseStep 2664515 = 3996773) B3996773
theorem B4802627 : Blo 1776089 4802627 := bstep (se 1 (by rfl) ⟨3601970, by rfl⟩ : syracuseStep 4802627 = 7203941) B7203941
theorem B2664545 : Blo 1776089 2664545 := bstep (se 2 (by rfl) ⟨999204, by rfl⟩ : syracuseStep 2664545 = 1998409) B1998409
theorem B18245731 : Blo 1776089 18245731 := bstep (se 1 (by rfl) ⟨13684298, by rfl⟩ : syracuseStep 18245731 = 27368597) B27368597
theorem B6408305 : Blo 1776089 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B2664563 : Blo 1776089 2664563 := bstep (se 1 (by rfl) ⟨1998422, by rfl⟩ : syracuseStep 2664563 = 3996845) B3996845
theorem B3000449 : Blo 1776089 3000449 := bstep (se 2 (by rfl) ⟨1125168, by rfl⟩ : syracuseStep 3000449 = 2250337) B2250337
theorem B2664593 : Blo 1776089 2664593 := bstep (se 2 (by rfl) ⟨999222, by rfl⟩ : syracuseStep 2664593 = 1998445) B1998445
theorem B2664611 : Blo 1776089 2664611 := bstep (se 1 (by rfl) ⟨1998458, by rfl⟩ : syracuseStep 2664611 = 3996917) B3996917
theorem B2664641 : Blo 1776089 2664641 := bstep (se 2 (by rfl) ⟨999240, by rfl⟩ : syracuseStep 2664641 = 1998481) B1998481
theorem B4499651 : Blo 1776089 4499651 := bstep (se 1 (by rfl) ⟨3374738, by rfl⟩ : syracuseStep 4499651 = 6749477) B6749477
theorem B2664659 : Blo 1776089 2664659 := bstep (se 1 (by rfl) ⟨1998494, by rfl⟩ : syracuseStep 2664659 = 3996989) B3996989
theorem B2664689 : Blo 1776089 2664689 := bstep (se 2 (by rfl) ⟨999258, by rfl⟩ : syracuseStep 2664689 = 1998517) B1998517
theorem B2664707 : Blo 1776089 2664707 := bstep (se 1 (by rfl) ⟨1998530, by rfl⟩ : syracuseStep 2664707 = 3997061) B3997061
theorem B2664737 : Blo 1776089 2664737 := bstep (se 2 (by rfl) ⟨999276, by rfl⟩ : syracuseStep 2664737 = 1998553) B1998553
theorem B8997155 : Blo 1776089 8997155 := bstep (se 1 (by rfl) ⟨6747866, by rfl⟩ : syracuseStep 8997155 = 13495733) B13495733
theorem B4000049 : Blo 1776089 4000049 := bstep (se 2 (by rfl) ⟨1500018, by rfl⟩ : syracuseStep 4000049 = 3000037) B3000037
theorem B2664755 : Blo 1776089 2664755 := bstep (se 1 (by rfl) ⟨1998566, by rfl⟩ : syracuseStep 2664755 = 3997133) B3997133
theorem B46803253 : Blo 1776089 46803253 := bstep (se 5 (by rfl) ⟨2193902, by rfl⟩ : syracuseStep 46803253 = 4387805) B4387805
theorem B4000067 : Blo 1776089 4000067 := bstep (se 1 (by rfl) ⟨3000050, by rfl⟩ : syracuseStep 4000067 = 6000101) B6000101
theorem B2664785 : Blo 1776089 2664785 := bstep (se 2 (by rfl) ⟨999294, by rfl⟩ : syracuseStep 2664785 = 1998589) B1998589
theorem B2664803 : Blo 1776089 2664803 := bstep (se 1 (by rfl) ⟨1998602, by rfl⟩ : syracuseStep 2664803 = 3997205) B3997205
theorem B2664833 : Blo 1776089 2664833 := bstep (se 2 (by rfl) ⟨999312, by rfl⟩ : syracuseStep 2664833 = 1998625) B1998625
theorem B2664851 : Blo 1776089 2664851 := bstep (se 1 (by rfl) ⟨1998638, by rfl⟩ : syracuseStep 2664851 = 3997277) B3997277
theorem B2845091 : Blo 1776089 2845091 := bstep (se 1 (by rfl) ⟨2133818, by rfl⟩ : syracuseStep 2845091 = 4267637) B4267637
theorem B5999021 : Blo 1776089 5999021 := bstep (se 3 (by rfl) ⟨1124816, by rfl⟩ : syracuseStep 5999021 = 2249633) B2249633
theorem B2664881 : Blo 1776089 2664881 := bstep (se 2 (by rfl) ⟨999330, by rfl⟩ : syracuseStep 2664881 = 1998661) B1998661
theorem B2664899 : Blo 1776089 2664899 := bstep (se 1 (by rfl) ⟨1998674, by rfl⟩ : syracuseStep 2664899 = 3997349) B3997349
theorem B51243461 : Blo 1776089 51243461 := bstep (se 4 (by rfl) ⟨4804074, by rfl⟩ : syracuseStep 51243461 = 9608149) B9608149
theorem B2664929 : Blo 1776089 2664929 := bstep (se 2 (by rfl) ⟨999348, by rfl⟩ : syracuseStep 2664929 = 1998697) B1998697
theorem B5999075 : Blo 1776089 5999075 := bstep (se 1 (by rfl) ⟨4499306, by rfl⟩ : syracuseStep 5999075 = 8998613) B8998613
theorem B2664947 : Blo 1776089 2664947 := bstep (se 1 (by rfl) ⟨1998710, by rfl⟩ : syracuseStep 2664947 = 3997421) B3997421
theorem B2664977 : Blo 1776089 2664977 := bstep (se 2 (by rfl) ⟨999366, by rfl⟩ : syracuseStep 2664977 = 1998733) B1998733
theorem B2664995 : Blo 1776089 2664995 := bstep (se 1 (by rfl) ⟨1998746, by rfl⟩ : syracuseStep 2664995 = 3997493) B3997493
theorem B2665025 : Blo 1776089 2665025 := bstep (se 2 (by rfl) ⟨999384, by rfl⟩ : syracuseStep 2665025 = 1998769) B1998769
theorem B4000337 : Blo 1776089 4000337 := bstep (se 2 (by rfl) ⟨1500126, by rfl⟩ : syracuseStep 4000337 = 3000253) B3000253
theorem B2665043 : Blo 1776089 2665043 := bstep (se 1 (by rfl) ⟨1998782, by rfl⟩ : syracuseStep 2665043 = 3997565) B3997565
theorem B4000355 : Blo 1776089 4000355 := bstep (se 1 (by rfl) ⟨3000266, by rfl⟩ : syracuseStep 4000355 = 6000533) B6000533
theorem B2665073 : Blo 1776089 2665073 := bstep (se 2 (by rfl) ⟨999402, by rfl⟩ : syracuseStep 2665073 = 1998805) B1998805
theorem B2665091 : Blo 1776089 2665091 := bstep (se 1 (by rfl) ⟨1998818, by rfl⟩ : syracuseStep 2665091 = 3997637) B3997637
theorem B2665121 : Blo 1776089 2665121 := bstep (se 2 (by rfl) ⟨999420, by rfl⟩ : syracuseStep 2665121 = 1998841) B1998841
theorem B2665139 : Blo 1776089 2665139 := bstep (se 1 (by rfl) ⟨1998854, by rfl⟩ : syracuseStep 2665139 = 3997709) B3997709
theorem B2886323 : Blo 1776089 2886323 := bstep (se 1 (by rfl) ⟨2164742, by rfl⟩ : syracuseStep 2886323 = 4329485) B4329485
theorem B14412485 : Blo 1776089 14412485 := bstep (se 4 (by rfl) ⟨1351170, by rfl⟩ : syracuseStep 14412485 = 2702341) B2702341
theorem B2665169 : Blo 1776089 2665169 := bstep (se 2 (by rfl) ⟨999438, by rfl⟩ : syracuseStep 2665169 = 1998877) B1998877
theorem B2665187 : Blo 1776089 2665187 := bstep (se 1 (by rfl) ⟨1998890, by rfl⟩ : syracuseStep 2665187 = 3997781) B3997781
theorem B4270819 : Blo 1776089 4270819 := bstep (se 1 (by rfl) ⟨3203114, by rfl⟩ : syracuseStep 4270819 = 6406229) B6406229
theorem B2886371 : Blo 1776089 2886371 := bstep (se 1 (by rfl) ⟨2164778, by rfl⟩ : syracuseStep 2886371 = 4329557) B4329557
theorem B5999345 : Blo 1776089 5999345 := bstep (se 2 (by rfl) ⟨2249754, by rfl⟩ : syracuseStep 5999345 = 4499509) B4499509
theorem B2665217 : Blo 1776089 2665217 := bstep (se 2 (by rfl) ⟨999456, by rfl⟩ : syracuseStep 2665217 = 1998913) B1998913
theorem B2665235 : Blo 1776089 2665235 := bstep (se 1 (by rfl) ⟨1998926, by rfl⟩ : syracuseStep 2665235 = 3997853) B3997853
theorem B2665265 : Blo 1776089 2665265 := bstep (se 2 (by rfl) ⟨999474, by rfl⟩ : syracuseStep 2665265 = 1998949) B1998949
theorem B3795761 : Blo 1776089 3795761 := bstep (se 2 (by rfl) ⟨1423410, by rfl⟩ : syracuseStep 3795761 = 2846821) B2846821
theorem B2665283 : Blo 1776089 2665283 := bstep (se 1 (by rfl) ⟨1998962, by rfl⟩ : syracuseStep 2665283 = 3997925) B3997925
theorem B2665313 : Blo 1776089 2665313 := bstep (se 2 (by rfl) ⟨999492, by rfl⟩ : syracuseStep 2665313 = 1998985) B1998985
theorem B15174499 : Blo 1776089 15174499 := bstep (se 1 (by rfl) ⟨11380874, by rfl⟩ : syracuseStep 15174499 = 22761749) B22761749
theorem B4000625 : Blo 1776089 4000625 := bstep (se 2 (by rfl) ⟨1500234, by rfl⟩ : syracuseStep 4000625 = 3000469) B3000469
theorem B2665331 : Blo 1776089 2665331 := bstep (se 1 (by rfl) ⟨1998998, by rfl⟩ : syracuseStep 2665331 = 3997997) B3997997
theorem B4000643 : Blo 1776089 4000643 := bstep (se 1 (by rfl) ⟨3000482, by rfl⟩ : syracuseStep 4000643 = 6000965) B6000965
theorem B2665361 : Blo 1776089 2665361 := bstep (se 2 (by rfl) ⟨999510, by rfl⟩ : syracuseStep 2665361 = 1999021) B1999021
theorem B2665379 : Blo 1776089 2665379 := bstep (se 1 (by rfl) ⟨1999034, by rfl⟩ : syracuseStep 2665379 = 3998069) B3998069
theorem B2665409 : Blo 1776089 2665409 := bstep (se 2 (by rfl) ⟨999528, by rfl⟩ : syracuseStep 2665409 = 1999057) B1999057
theorem B2665427 : Blo 1776089 2665427 := bstep (se 1 (by rfl) ⟨1999070, by rfl⟩ : syracuseStep 2665427 = 3998141) B3998141
theorem B2665457 : Blo 1776089 2665457 := bstep (se 2 (by rfl) ⟨999546, by rfl⟩ : syracuseStep 2665457 = 1999093) B1999093
theorem B2665475 : Blo 1776089 2665475 := bstep (se 1 (by rfl) ⟨1999106, by rfl⟩ : syracuseStep 2665475 = 3998213) B3998213
theorem B2665505 : Blo 1776089 2665505 := bstep (se 2 (by rfl) ⟨999564, by rfl⟩ : syracuseStep 2665505 = 1999129) B1999129
theorem B2665523 : Blo 1776089 2665523 := bstep (se 1 (by rfl) ⟨1999142, by rfl⟩ : syracuseStep 2665523 = 3998285) B3998285
theorem B5401667 : Blo 1776089 5401667 := bstep (se 1 (by rfl) ⟨4051250, by rfl⟩ : syracuseStep 5401667 = 8102501) B8102501
theorem B8997965 : Blo 1776089 8997965 := bstep (se 3 (by rfl) ⟨1687118, by rfl⟩ : syracuseStep 8997965 = 3374237) B3374237
theorem B2665553 : Blo 1776089 2665553 := bstep (se 2 (by rfl) ⟨999582, by rfl⟩ : syracuseStep 2665553 = 1999165) B1999165
theorem B2665571 : Blo 1776089 2665571 := bstep (se 1 (by rfl) ⟨1999178, by rfl⟩ : syracuseStep 2665571 = 3998357) B3998357
theorem B4500593 : Blo 1776089 4500593 := bstep (se 2 (by rfl) ⟨1687722, by rfl⟩ : syracuseStep 4500593 = 3375445) B3375445
theorem B2665601 : Blo 1776089 2665601 := bstep (se 2 (by rfl) ⟨999600, by rfl⟩ : syracuseStep 2665601 = 1999201) B1999201
theorem B2665619 : Blo 1776089 2665619 := bstep (se 1 (by rfl) ⟨1999214, by rfl⟩ : syracuseStep 2665619 = 3998429) B3998429
theorem B7589027 : Blo 1776089 7589027 := bstep (se 1 (by rfl) ⟨5691770, by rfl⟩ : syracuseStep 7589027 = 11383541) B11383541
theorem B4500643 : Blo 1776089 4500643 := bstep (se 1 (by rfl) ⟨3375482, by rfl⟩ : syracuseStep 4500643 = 6750965) B6750965
theorem B2665649 : Blo 1776089 2665649 := bstep (se 2 (by rfl) ⟨999618, by rfl⟩ : syracuseStep 2665649 = 1999237) B1999237
theorem B2665667 : Blo 1776089 2665667 := bstep (se 1 (by rfl) ⟨1999250, by rfl⟩ : syracuseStep 2665667 = 3998501) B3998501
theorem B2665697 : Blo 1776089 2665697 := bstep (se 2 (by rfl) ⟨999636, by rfl⟩ : syracuseStep 2665697 = 1999273) B1999273
theorem B2247907 : Blo 1776089 2247907 := bstep (se 1 (by rfl) ⟨1685930, by rfl⟩ : syracuseStep 2247907 = 3371861) B3371861
theorem B6745315 : Blo 1776089 6745315 := bstep (se 1 (by rfl) ⟨5058986, by rfl⟩ : syracuseStep 6745315 = 10117973) B10117973
theorem B2845937 : Blo 1776089 2845937 := bstep (se 2 (by rfl) ⟨1067226, by rfl⟩ : syracuseStep 2845937 = 2134453) B2134453
theorem B2665715 : Blo 1776089 2665715 := bstep (se 1 (by rfl) ⟨1999286, by rfl⟩ : syracuseStep 2665715 = 3998573) B3998573
theorem B5999885 : Blo 1776089 5999885 := bstep (se 3 (by rfl) ⟨1124978, by rfl⟩ : syracuseStep 5999885 = 2249957) B2249957
theorem B2665745 : Blo 1776089 2665745 := bstep (se 2 (by rfl) ⟨999654, by rfl⟩ : syracuseStep 2665745 = 1999309) B1999309
theorem B2665763 : Blo 1776089 2665763 := bstep (se 1 (by rfl) ⟨1999322, by rfl⟩ : syracuseStep 2665763 = 3998645) B3998645
theorem B4500785 : Blo 1776089 4500785 := bstep (se 2 (by rfl) ⟨1687794, by rfl⟩ : syracuseStep 4500785 = 3375589) B3375589
theorem B2665793 : Blo 1776089 2665793 := bstep (se 2 (by rfl) ⟨999672, by rfl⟩ : syracuseStep 2665793 = 1999345) B1999345
theorem B2248003 : Blo 1776089 2248003 := bstep (se 1 (by rfl) ⟨1686002, by rfl⟩ : syracuseStep 2248003 = 3372005) B3372005
theorem B5999939 : Blo 1776089 5999939 := bstep (se 1 (by rfl) ⟨4499954, by rfl⟩ : syracuseStep 5999939 = 8999909) B8999909
theorem B2665811 : Blo 1776089 2665811 := bstep (se 1 (by rfl) ⟨1999358, by rfl⟩ : syracuseStep 2665811 = 3998717) B3998717
theorem B2665841 : Blo 1776089 2665841 := bstep (se 2 (by rfl) ⟨999690, by rfl⟩ : syracuseStep 2665841 = 1999381) B1999381
theorem B2665859 : Blo 1776089 2665859 := bstep (se 1 (by rfl) ⟨1999394, by rfl⟩ : syracuseStep 2665859 = 3998789) B3998789
theorem B2665889 : Blo 1776089 2665889 := bstep (se 2 (by rfl) ⟨999708, by rfl⟩ : syracuseStep 2665889 = 1999417) B1999417
theorem B2665907 : Blo 1776089 2665907 := bstep (se 1 (by rfl) ⟨1999430, by rfl⟩ : syracuseStep 2665907 = 3998861) B3998861
theorem B2665937 : Blo 1776089 2665937 := bstep (se 2 (by rfl) ⟨999726, by rfl⟩ : syracuseStep 2665937 = 1999453) B1999453
theorem B2665955 : Blo 1776089 2665955 := bstep (se 1 (by rfl) ⟨1999466, by rfl⟩ : syracuseStep 2665955 = 3998933) B3998933
theorem B2665985 : Blo 1776089 2665985 := bstep (se 2 (by rfl) ⟨999744, by rfl⟩ : syracuseStep 2665985 = 1999489) B1999489
theorem B5058065 : Blo 1776089 5058065 := bstep (se 2 (by rfl) ⟨1896774, by rfl⟩ : syracuseStep 5058065 = 3793549) B3793549
theorem B2666003 : Blo 1776089 2666003 := bstep (se 1 (by rfl) ⟨1999502, by rfl⟩ : syracuseStep 2666003 = 3999005) B3999005
theorem B2666033 : Blo 1776089 2666033 := bstep (se 2 (by rfl) ⟨999762, by rfl⟩ : syracuseStep 2666033 = 1999525) B1999525
theorem B2666051 : Blo 1776089 2666051 := bstep (se 1 (by rfl) ⟨1999538, by rfl⟩ : syracuseStep 2666051 = 3999077) B3999077
theorem B12815941 : Blo 1776089 12815941 := bstep (se 4 (by rfl) ⟨1201494, by rfl⟩ : syracuseStep 12815941 = 2402989) B2402989
theorem B6000209 : Blo 1776089 6000209 := bstep (se 2 (by rfl) ⟨2250078, by rfl⟩ : syracuseStep 6000209 = 4500157) B4500157
theorem B2666081 : Blo 1776089 2666081 := bstep (se 2 (by rfl) ⟨999780, by rfl⟩ : syracuseStep 2666081 = 1999561) B1999561
theorem B2666099 : Blo 1776089 2666099 := bstep (se 1 (by rfl) ⟨1999574, by rfl⟩ : syracuseStep 2666099 = 3999149) B3999149
theorem B2666129 : Blo 1776089 2666129 := bstep (se 2 (by rfl) ⟨999798, by rfl⟩ : syracuseStep 2666129 = 1999597) B1999597
theorem B3796625 : Blo 1776089 3796625 := bstep (se 2 (by rfl) ⟨1423734, by rfl⟩ : syracuseStep 3796625 = 2847469) B2847469
theorem B2666147 : Blo 1776089 2666147 := bstep (se 1 (by rfl) ⟨1999610, by rfl⟩ : syracuseStep 2666147 = 3999221) B3999221
theorem B2666177 : Blo 1776089 2666177 := bstep (se 2 (by rfl) ⟨999816, by rfl⟩ : syracuseStep 2666177 = 1999633) B1999633
theorem B9875141 : Blo 1776089 9875141 := bstep (se 4 (by rfl) ⟨925794, by rfl⟩ : syracuseStep 9875141 = 1851589) B1851589
theorem B2666195 : Blo 1776089 2666195 := bstep (se 1 (by rfl) ⟨1999646, by rfl⟩ : syracuseStep 2666195 = 3999293) B3999293
theorem B2846449 : Blo 1776089 2846449 := bstep (se 2 (by rfl) ⟨1067418, by rfl⟩ : syracuseStep 2846449 = 2134837) B2134837
theorem B2666225 : Blo 1776089 2666225 := bstep (se 2 (by rfl) ⟨999834, by rfl⟩ : syracuseStep 2666225 = 1999669) B1999669
theorem B2666243 : Blo 1776089 2666243 := bstep (se 1 (by rfl) ⟨1999682, by rfl⟩ : syracuseStep 2666243 = 3999365) B3999365
theorem B2666273 : Blo 1776089 2666273 := bstep (se 2 (by rfl) ⟨999852, by rfl⟩ : syracuseStep 2666273 = 1999705) B1999705
theorem B2248499 : Blo 1776089 2248499 := bstep (se 1 (by rfl) ⟨1686374, by rfl⟩ : syracuseStep 2248499 = 3372749) B3372749
theorem B2666291 : Blo 1776089 2666291 := bstep (se 1 (by rfl) ⟨1999718, by rfl⟩ : syracuseStep 2666291 = 3999437) B3999437
theorem B2666321 : Blo 1776089 2666321 := bstep (se 2 (by rfl) ⟨999870, by rfl⟩ : syracuseStep 2666321 = 1999741) B1999741
theorem B2666339 : Blo 1776089 2666339 := bstep (se 1 (by rfl) ⟨1999754, by rfl⟩ : syracuseStep 2666339 = 3999509) B3999509
theorem B2666369 : Blo 1776089 2666369 := bstep (se 2 (by rfl) ⟨999888, by rfl⟩ : syracuseStep 2666369 = 1999777) B1999777
theorem B2666387 : Blo 1776089 2666387 := bstep (se 1 (by rfl) ⟨1999790, by rfl⟩ : syracuseStep 2666387 = 3999581) B3999581
theorem B2666417 : Blo 1776089 2666417 := bstep (se 2 (by rfl) ⟨999906, by rfl⟩ : syracuseStep 2666417 = 1999813) B1999813
theorem B2666435 : Blo 1776089 2666435 := bstep (se 1 (by rfl) ⟨1999826, by rfl⟩ : syracuseStep 2666435 = 3999653) B3999653
theorem B2666465 : Blo 1776089 2666465 := bstep (se 2 (by rfl) ⟨999924, by rfl⟩ : syracuseStep 2666465 = 1999849) B1999849
theorem B2666483 : Blo 1776089 2666483 := bstep (se 1 (by rfl) ⟨1999862, by rfl⟩ : syracuseStep 2666483 = 3999725) B3999725
theorem B2666513 : Blo 1776089 2666513 := bstep (se 2 (by rfl) ⟨999942, by rfl⟩ : syracuseStep 2666513 = 1999885) B1999885
theorem B2666531 : Blo 1776089 2666531 := bstep (se 1 (by rfl) ⟨1999898, by rfl⟩ : syracuseStep 2666531 = 3999797) B3999797
theorem B2666561 : Blo 1776089 2666561 := bstep (se 2 (by rfl) ⟨999960, by rfl⟩ : syracuseStep 2666561 = 1999921) B1999921
theorem B2666579 : Blo 1776089 2666579 := bstep (se 1 (by rfl) ⟨1999934, by rfl⟩ : syracuseStep 2666579 = 3999869) B3999869
theorem B6000749 : Blo 1776089 6000749 := bstep (se 3 (by rfl) ⟨1125140, by rfl⟩ : syracuseStep 6000749 = 2250281) B2250281
theorem B2666609 : Blo 1776089 2666609 := bstep (se 2 (by rfl) ⟨999978, by rfl⟩ : syracuseStep 2666609 = 1999957) B1999957
theorem B2666627 : Blo 1776089 2666627 := bstep (se 1 (by rfl) ⟨1999970, by rfl⟩ : syracuseStep 2666627 = 3999941) B3999941
theorem B11382925 : Blo 1776089 11382925 := bstep (se 3 (by rfl) ⟨2134298, by rfl⟩ : syracuseStep 11382925 = 4268597) B4268597
theorem B2666657 : Blo 1776089 2666657 := bstep (se 2 (by rfl) ⟨999996, by rfl⟩ : syracuseStep 2666657 = 1999993) B1999993
theorem B6000803 : Blo 1776089 6000803 := bstep (se 1 (by rfl) ⟨4500602, by rfl⟩ : syracuseStep 6000803 = 9001205) B9001205
theorem B5058737 : Blo 1776089 5058737 := bstep (se 2 (by rfl) ⟨1897026, by rfl⟩ : syracuseStep 5058737 = 3794053) B3794053
theorem B9605297 : Blo 1776089 9605297 := bstep (se 2 (by rfl) ⟨3601986, by rfl⟩ : syracuseStep 9605297 = 7203973) B7203973
theorem B2666675 : Blo 1776089 2666675 := bstep (se 1 (by rfl) ⟨2000006, by rfl⟩ : syracuseStep 2666675 = 4000013) B4000013
theorem B2666705 : Blo 1776089 2666705 := bstep (se 2 (by rfl) ⟨1000014, by rfl⟩ : syracuseStep 2666705 = 2000029) B2000029
theorem B2666723 : Blo 1776089 2666723 := bstep (se 1 (by rfl) ⟨2000042, by rfl⟩ : syracuseStep 2666723 = 4000085) B4000085
theorem B2666753 : Blo 1776089 2666753 := bstep (se 2 (by rfl) ⟨1000032, by rfl⟩ : syracuseStep 2666753 = 2000065) B2000065
theorem B2666771 : Blo 1776089 2666771 := bstep (se 1 (by rfl) ⟨2000078, by rfl⟩ : syracuseStep 2666771 = 4000157) B4000157
theorem B2666801 : Blo 1776089 2666801 := bstep (se 2 (by rfl) ⟨1000050, by rfl⟩ : syracuseStep 2666801 = 2000101) B2000101
theorem B46174517 : Blo 1776089 46174517 := bstep (se 5 (by rfl) ⟨2164430, by rfl⟩ : syracuseStep 46174517 = 4328861) B4328861
theorem B2666819 : Blo 1776089 2666819 := bstep (se 1 (by rfl) ⟨2000114, by rfl⟩ : syracuseStep 2666819 = 4000229) B4000229
theorem B6082897 : Blo 1776089 6082897 := bstep (se 2 (by rfl) ⟨2281086, by rfl⟩ : syracuseStep 6082897 = 4562173) B4562173
theorem B1896787 : Blo 1776089 1896787 := bstep (se 1 (by rfl) ⟨1422590, by rfl⟩ : syracuseStep 1896787 = 2845181) B2845181
theorem B2847059 : Blo 1776089 2847059 := bstep (se 1 (by rfl) ⟨2135294, by rfl⟩ : syracuseStep 2847059 = 4270589) B4270589
theorem B2666849 : Blo 1776089 2666849 := bstep (se 2 (by rfl) ⟨1000068, by rfl⟩ : syracuseStep 2666849 = 2000137) B2000137
theorem B32420209 : Blo 1776089 32420209 := bstep (se 2 (by rfl) ⟨12157578, by rfl⟩ : syracuseStep 32420209 = 24315157) B24315157
theorem B7590257 : Blo 1776089 7590257 := bstep (se 2 (by rfl) ⟨2846346, by rfl⟩ : syracuseStep 7590257 = 5692693) B5692693
theorem B2666867 : Blo 1776089 2666867 := bstep (se 1 (by rfl) ⟨2000150, by rfl⟩ : syracuseStep 2666867 = 4000301) B4000301
theorem B2666897 : Blo 1776089 2666897 := bstep (se 2 (by rfl) ⟨1000086, by rfl⟩ : syracuseStep 2666897 = 2000173) B2000173
theorem B2666915 : Blo 1776089 2666915 := bstep (se 1 (by rfl) ⟨2000186, by rfl⟩ : syracuseStep 2666915 = 4000373) B4000373
theorem B2666945 : Blo 1776089 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B2666963 : Blo 1776089 2666963 := bstep (se 1 (by rfl) ⟨2000222, by rfl⟩ : syracuseStep 2666963 = 4000445) B4000445
theorem B2666993 : Blo 1776089 2666993 := bstep (se 2 (by rfl) ⟨1000122, by rfl⟩ : syracuseStep 2666993 = 2000245) B2000245
theorem B2249203 : Blo 1776089 2249203 := bstep (se 1 (by rfl) ⟨1686902, by rfl⟩ : syracuseStep 2249203 = 3373805) B3373805
theorem B2667011 : Blo 1776089 2667011 := bstep (se 1 (by rfl) ⟨2000258, by rfl⟩ : syracuseStep 2667011 = 4000517) B4000517
theorem B2667041 : Blo 1776089 2667041 := bstep (se 2 (by rfl) ⟨1000140, by rfl⟩ : syracuseStep 2667041 = 2000281) B2000281
theorem B2667059 : Blo 1776089 2667059 := bstep (se 1 (by rfl) ⟨2000294, by rfl⟩ : syracuseStep 2667059 = 4000589) B4000589
theorem B2667089 : Blo 1776089 2667089 := bstep (se 2 (by rfl) ⟨1000158, by rfl⟩ : syracuseStep 2667089 = 2000317) B2000317
theorem B2249299 : Blo 1776089 2249299 := bstep (se 1 (by rfl) ⟨1686974, by rfl⟩ : syracuseStep 2249299 = 3373949) B3373949
theorem B2667107 : Blo 1776089 2667107 := bstep (se 1 (by rfl) ⟨2000330, by rfl⟩ : syracuseStep 2667107 = 4000661) B4000661
theorem B4559537 : Blo 1776089 4559537 := bstep (se 2 (by rfl) ⟨1709826, by rfl⟩ : syracuseStep 4559537 = 3419653) B3419653
theorem B8213233 : Blo 1776089 8213233 := bstep (se 2 (by rfl) ⟨3079962, by rfl⟩ : syracuseStep 8213233 = 6159925) B6159925
theorem B1897219 : Blo 1776089 1897219 := bstep (se 1 (by rfl) ⟨1422914, by rfl⟩ : syracuseStep 1897219 = 2845829) B2845829
theorem B5059523 : Blo 1776089 5059523 := bstep (se 1 (by rfl) ⟨3794642, by rfl⟩ : syracuseStep 5059523 = 7589285) B7589285
theorem B2249795 : Blo 1776089 2249795 := bstep (se 1 (by rfl) ⟨1687346, by rfl⟩ : syracuseStep 2249795 = 3374693) B3374693
theorem B17306723 : Blo 1776089 17306723 := bstep (se 1 (by rfl) ⟨12980042, by rfl⟩ : syracuseStep 17306723 = 25960085) B25960085
theorem B8991971 : Blo 1776089 8991971 := bstep (se 1 (by rfl) ⟨6743978, by rfl⟩ : syracuseStep 8991971 = 13487957) B13487957
theorem B5059853 : Blo 1776089 5059853 := bstep (se 3 (by rfl) ⟨948722, by rfl⟩ : syracuseStep 5059853 = 1897445) B1897445
theorem B2848051 : Blo 1776089 2848051 := bstep (se 1 (by rfl) ⟨2136038, by rfl⟩ : syracuseStep 2848051 = 4272077) B4272077
theorem B5059921 : Blo 1776089 5059921 := bstep (se 2 (by rfl) ⟨1897470, by rfl⟩ : syracuseStep 5059921 = 3794941) B3794941
theorem B4806001 : Blo 1776089 4806001 := bstep (se 2 (by rfl) ⟨1802250, by rfl⟩ : syracuseStep 4806001 = 3604501) B3604501
theorem B6747533 : Blo 1776089 6747533 := bstep (se 3 (by rfl) ⟨1265162, by rfl⟩ : syracuseStep 6747533 = 2530325) B2530325
theorem B17315299 : Blo 1776089 17315299 := bstep (se 1 (by rfl) ⟨12986474, by rfl⟩ : syracuseStep 17315299 = 25972949) B25972949
theorem B17085923 : Blo 1776089 17085923 := bstep (se 1 (by rfl) ⟨12814442, by rfl⟩ : syracuseStep 17085923 = 25628885) B25628885
theorem B3372529 : Blo 1776089 3372529 := bstep (se 2 (by rfl) ⟨1264698, by rfl⟩ : syracuseStep 3372529 = 2529397) B2529397
theorem B5404195 : Blo 1776089 5404195 := bstep (se 1 (by rfl) ⟨4053146, by rfl⟩ : syracuseStep 5404195 = 8106293) B8106293
theorem B2135587 : Blo 1776089 2135587 := bstep (se 1 (by rfl) ⟨1601690, by rfl⟩ : syracuseStep 2135587 = 3203381) B3203381
theorem B2528867 : Blo 1776089 2528867 := bstep (se 1 (by rfl) ⟨1896650, by rfl⟩ : syracuseStep 2528867 = 3793301) B3793301
theorem B5060195 : Blo 1776089 5060195 := bstep (se 1 (by rfl) ⟨3795146, by rfl⟩ : syracuseStep 5060195 = 7590293) B7590293
theorem B2135683 : Blo 1776089 2135683 := bstep (se 1 (by rfl) ⟨1601762, by rfl⟩ : syracuseStep 2135683 = 3203525) B3203525
theorem B5691053 : Blo 1776089 5691053 := bstep (se 3 (by rfl) ⟨1067072, by rfl⟩ : syracuseStep 5691053 = 2134145) B2134145
theorem B2135731 : Blo 1776089 2135731 := bstep (se 1 (by rfl) ⟨1601798, by rfl⟩ : syracuseStep 2135731 = 3203597) B3203597
theorem B6076109 : Blo 1776089 6076109 := bstep (se 3 (by rfl) ⟨1139270, by rfl⟩ : syracuseStep 6076109 = 2278541) B2278541
theorem B3372931 : Blo 1776089 3372931 := bstep (se 1 (by rfl) ⟨2529698, by rfl⟩ : syracuseStep 3372931 = 5059397) B5059397
theorem B8542115 : Blo 1776089 8542115 := bstep (se 1 (by rfl) ⟨6406586, by rfl⟩ : syracuseStep 8542115 = 12813173) B12813173
theorem B3372977 : Blo 1776089 3372977 := bstep (se 2 (by rfl) ⟨1264866, by rfl⟩ : syracuseStep 3372977 = 2529733) B2529733
theorem B4388785 : Blo 1776089 4388785 := bstep (se 2 (by rfl) ⟨1645794, by rfl⟩ : syracuseStep 4388785 = 3291589) B3291589
theorem B9000881 : Blo 1776089 9000881 := bstep (se 2 (by rfl) ⟨3375330, by rfl⟩ : syracuseStep 9000881 = 6750661) B6750661
theorem B1898483 : Blo 1776089 1898483 := bstep (se 1 (by rfl) ⟨1423862, by rfl⟩ : syracuseStep 1898483 = 2847725) B2847725
theorem B8992781 : Blo 1776089 8992781 := bstep (se 3 (by rfl) ⟨1686146, by rfl⟩ : syracuseStep 8992781 = 3372293) B3372293
theorem B1923107 : Blo 1776089 1923107 := bstep (se 1 (by rfl) ⟨1442330, by rfl⟩ : syracuseStep 1923107 = 2884661) B2884661
theorem B2701363 : Blo 1776089 2701363 := bstep (se 1 (by rfl) ⟨2026022, by rfl⟩ : syracuseStep 2701363 = 4052045) B4052045
theorem B2529425 : Blo 1776089 2529425 := bstep (se 2 (by rfl) ⟨948534, by rfl⟩ : syracuseStep 2529425 = 1897069) B1897069
theorem B5994701 : Blo 1776089 5994701 := bstep (se 3 (by rfl) ⟨1124006, by rfl⟩ : syracuseStep 5994701 = 2248013) B2248013
theorem B9607373 : Blo 1776089 9607373 := bstep (se 3 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 9607373 = 3602765) B3602765
theorem B3373265 : Blo 1776089 3373265 := bstep (se 2 (by rfl) ⟨1264974, by rfl⟩ : syracuseStep 3373265 = 2529949) B2529949
theorem B2529505 : Blo 1776089 2529505 := bstep (se 2 (by rfl) ⟨948564, by rfl⟩ : syracuseStep 2529505 = 1897129) B1897129
theorem B5994755 : Blo 1776089 5994755 := bstep (se 1 (by rfl) ⟨4496066, by rfl⟩ : syracuseStep 5994755 = 8992133) B8992133
theorem B11385157 : Blo 1776089 11385157 := bstep (se 4 (by rfl) ⟨1067358, by rfl⟩ : syracuseStep 11385157 = 2134717) B2134717
theorem B8542577 : Blo 1776089 8542577 := bstep (se 2 (by rfl) ⟨3203466, by rfl⟩ : syracuseStep 8542577 = 6406933) B6406933
theorem B1825187 : Blo 1776089 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B5061037 : Blo 1776089 5061037 := bstep (se 3 (by rfl) ⟨948944, by rfl⟩ : syracuseStep 5061037 = 1897889) B1897889
theorem B1776099 : Blo 1776089 1776099 := bstep (se 1 (by rfl) ⟨1332074, by rfl⟩ : syracuseStep 1776099 = 2664149) B2664149
theorem B1776115 : Blo 1776089 1776115 := bstep (se 1 (by rfl) ⟨1332086, by rfl⟩ : syracuseStep 1776115 = 2664173) B2664173
theorem B1776131 : Blo 1776089 1776131 := bstep (se 1 (by rfl) ⟨1332098, by rfl⟩ : syracuseStep 1776131 = 2664197) B2664197
theorem B17783309 : Blo 1776089 17783309 := bstep (se 3 (by rfl) ⟨3334370, by rfl⟩ : syracuseStep 17783309 = 6668741) B6668741
theorem B5995025 : Blo 1776089 5995025 := bstep (se 2 (by rfl) ⟨2248134, by rfl⟩ : syracuseStep 5995025 = 4496269) B4496269
theorem B1776147 : Blo 1776089 1776147 := bstep (se 1 (by rfl) ⟨1332110, by rfl⟩ : syracuseStep 1776147 = 2664221) B2664221
theorem B1776163 : Blo 1776089 1776163 := bstep (se 1 (by rfl) ⟨1332122, by rfl⟩ : syracuseStep 1776163 = 2664245) B2664245
theorem B1776179 : Blo 1776089 1776179 := bstep (se 1 (by rfl) ⟨1332134, by rfl⟩ : syracuseStep 1776179 = 2664269) B2664269
theorem B1776195 : Blo 1776089 1776195 := bstep (se 1 (by rfl) ⟨1332146, by rfl⟩ : syracuseStep 1776195 = 2664293) B2664293
theorem B5061197 : Blo 1776089 5061197 := bstep (se 3 (by rfl) ⟨948974, by rfl⟩ : syracuseStep 5061197 = 1897949) B1897949
theorem B1776211 : Blo 1776089 1776211 := bstep (se 1 (by rfl) ⟨1332158, by rfl⟩ : syracuseStep 1776211 = 2664317) B2664317
theorem B1776227 : Blo 1776089 1776227 := bstep (se 1 (by rfl) ⟨1332170, by rfl⟩ : syracuseStep 1776227 = 2664341) B2664341
theorem B1776243 : Blo 1776089 1776243 := bstep (se 1 (by rfl) ⟨1332182, by rfl⟩ : syracuseStep 1776243 = 2664365) B2664365
theorem B1776259 : Blo 1776089 1776259 := bstep (se 1 (by rfl) ⟨1332194, by rfl⟩ : syracuseStep 1776259 = 2664389) B2664389
theorem B14408333 : Blo 1776089 14408333 := bstep (se 3 (by rfl) ⟨2701562, by rfl⟩ : syracuseStep 14408333 = 5403125) B5403125
theorem B3996305 : Blo 1776089 3996305 := bstep (se 2 (by rfl) ⟨1498614, by rfl⟩ : syracuseStep 3996305 = 2997229) B2997229
theorem B1776275 : Blo 1776089 1776275 := bstep (se 1 (by rfl) ⟨1332206, by rfl⟩ : syracuseStep 1776275 = 2664413) B2664413
theorem B3996323 : Blo 1776089 3996323 := bstep (se 1 (by rfl) ⟨2997242, by rfl⟩ : syracuseStep 3996323 = 5994485) B5994485
theorem B1776291 : Blo 1776089 1776291 := bstep (se 1 (by rfl) ⟨1332218, by rfl⟩ : syracuseStep 1776291 = 2664437) B2664437
theorem B1776307 : Blo 1776089 1776307 := bstep (se 1 (by rfl) ⟨1332230, by rfl⟩ : syracuseStep 1776307 = 2664461) B2664461
theorem B1776323 : Blo 1776089 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B10803917 : Blo 1776089 10803917 := bstep (se 3 (by rfl) ⟨2025734, by rfl⟩ : syracuseStep 10803917 = 4051469) B4051469
theorem B1776339 : Blo 1776089 1776339 := bstep (se 1 (by rfl) ⟨1332254, by rfl⟩ : syracuseStep 1776339 = 2664509) B2664509
theorem B1776355 : Blo 1776089 1776355 := bstep (se 1 (by rfl) ⟨1332266, by rfl⟩ : syracuseStep 1776355 = 2664533) B2664533
theorem B1776371 : Blo 1776089 1776371 := bstep (se 1 (by rfl) ⟨1332278, by rfl⟩ : syracuseStep 1776371 = 2664557) B2664557
theorem B1776387 : Blo 1776089 1776387 := bstep (se 1 (by rfl) ⟨1332290, by rfl⟩ : syracuseStep 1776387 = 2664581) B2664581
theorem B5061379 : Blo 1776089 5061379 := bstep (se 1 (by rfl) ⟨3796034, by rfl⟩ : syracuseStep 5061379 = 7592069) B7592069
theorem B7592717 : Blo 1776089 7592717 := bstep (se 3 (by rfl) ⟨1423634, by rfl⟩ : syracuseStep 7592717 = 2847269) B2847269
theorem B1776403 : Blo 1776089 1776403 := bstep (se 1 (by rfl) ⟨1332302, by rfl⟩ : syracuseStep 1776403 = 2664605) B2664605
theorem B1776419 : Blo 1776089 1776419 := bstep (se 1 (by rfl) ⟨1332314, by rfl⟩ : syracuseStep 1776419 = 2664629) B2664629
theorem B1776435 : Blo 1776089 1776435 := bstep (se 1 (by rfl) ⟨1332326, by rfl⟩ : syracuseStep 1776435 = 2664653) B2664653
theorem B1776451 : Blo 1776089 1776451 := bstep (se 1 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 1776451 = 2664677) B2664677
theorem B1776467 : Blo 1776089 1776467 := bstep (se 1 (by rfl) ⟨1332350, by rfl⟩ : syracuseStep 1776467 = 2664701) B2664701
theorem B1776483 : Blo 1776089 1776483 := bstep (se 1 (by rfl) ⟨1332362, by rfl⟩ : syracuseStep 1776483 = 2664725) B2664725
theorem B1776499 : Blo 1776089 1776499 := bstep (se 1 (by rfl) ⟨1332374, by rfl⟩ : syracuseStep 1776499 = 2664749) B2664749
theorem B1776515 : Blo 1776089 1776515 := bstep (se 1 (by rfl) ⟨1332386, by rfl⟩ : syracuseStep 1776515 = 2664773) B2664773
theorem B1776531 : Blo 1776089 1776531 := bstep (se 1 (by rfl) ⟨1332398, by rfl⟩ : syracuseStep 1776531 = 2664797) B2664797
theorem B2997155 : Blo 1776089 2997155 := bstep (se 1 (by rfl) ⟨2247866, by rfl⟩ : syracuseStep 2997155 = 4495733) B4495733
theorem B1776547 : Blo 1776089 1776547 := bstep (se 1 (by rfl) ⟨1332410, by rfl⟩ : syracuseStep 1776547 = 2664821) B2664821
theorem B3373987 : Blo 1776089 3373987 := bstep (se 1 (by rfl) ⟨2530490, by rfl⟩ : syracuseStep 3373987 = 5060981) B5060981
theorem B3996593 : Blo 1776089 3996593 := bstep (se 2 (by rfl) ⟨1498722, by rfl⟩ : syracuseStep 3996593 = 2997445) B2997445
theorem B1776563 : Blo 1776089 1776563 := bstep (se 1 (by rfl) ⟨1332422, by rfl⟩ : syracuseStep 1776563 = 2664845) B2664845
theorem B3996611 : Blo 1776089 3996611 := bstep (se 1 (by rfl) ⟨2997458, by rfl⟩ : syracuseStep 3996611 = 5994917) B5994917
theorem B1776579 : Blo 1776089 1776579 := bstep (se 1 (by rfl) ⟨1332434, by rfl⟩ : syracuseStep 1776579 = 2664869) B2664869
theorem B1776595 : Blo 1776089 1776595 := bstep (se 1 (by rfl) ⟨1332446, by rfl⟩ : syracuseStep 1776595 = 2664893) B2664893
theorem B1776611 : Blo 1776089 1776611 := bstep (se 1 (by rfl) ⟨1332458, by rfl⟩ : syracuseStep 1776611 = 2664917) B2664917
theorem B3202019 : Blo 1776089 3202019 := bstep (se 1 (by rfl) ⟨2401514, by rfl⟩ : syracuseStep 3202019 = 4803029) B4803029
theorem B1776627 : Blo 1776089 1776627 := bstep (se 1 (by rfl) ⟨1332470, by rfl⟩ : syracuseStep 1776627 = 2664941) B2664941
theorem B2530291 : Blo 1776089 2530291 := bstep (se 1 (by rfl) ⟨1897718, by rfl⟩ : syracuseStep 2530291 = 3795437) B3795437
theorem B1776643 : Blo 1776089 1776643 := bstep (se 1 (by rfl) ⟨1332482, by rfl⟩ : syracuseStep 1776643 = 2664965) B2664965
theorem B1776659 : Blo 1776089 1776659 := bstep (se 1 (by rfl) ⟨1332494, by rfl⟩ : syracuseStep 1776659 = 2664989) B2664989
theorem B2997283 : Blo 1776089 2997283 := bstep (se 1 (by rfl) ⟨2247962, by rfl⟩ : syracuseStep 2997283 = 4495925) B4495925
theorem B1776675 : Blo 1776089 1776675 := bstep (se 1 (by rfl) ⟨1332506, by rfl⟩ : syracuseStep 1776675 = 2665013) B2665013
theorem B5995565 : Blo 1776089 5995565 := bstep (se 3 (by rfl) ⟨1124168, by rfl⟩ : syracuseStep 5995565 = 2248337) B2248337
theorem B1776691 : Blo 1776089 1776691 := bstep (se 1 (by rfl) ⟨1332518, by rfl⟩ : syracuseStep 1776691 = 2665037) B2665037
theorem B1776707 : Blo 1776089 1776707 := bstep (se 1 (by rfl) ⟨1332530, by rfl⟩ : syracuseStep 1776707 = 2665061) B2665061
theorem B1776723 : Blo 1776089 1776723 := bstep (se 1 (by rfl) ⟨1332542, by rfl⟩ : syracuseStep 1776723 = 2665085) B2665085
theorem B5995619 : Blo 1776089 5995619 := bstep (se 1 (by rfl) ⟨4496714, by rfl⟩ : syracuseStep 5995619 = 8993429) B8993429
theorem B1776739 : Blo 1776089 1776739 := bstep (se 1 (by rfl) ⟨1332554, by rfl⟩ : syracuseStep 1776739 = 2665109) B2665109
theorem B1776755 : Blo 1776089 1776755 := bstep (se 1 (by rfl) ⟨1332566, by rfl⟩ : syracuseStep 1776755 = 2665133) B2665133
theorem B1776771 : Blo 1776089 1776771 := bstep (se 1 (by rfl) ⟨1332578, by rfl⟩ : syracuseStep 1776771 = 2665157) B2665157
theorem B1776787 : Blo 1776089 1776787 := bstep (se 1 (by rfl) ⟨1332590, by rfl⟩ : syracuseStep 1776787 = 2665181) B2665181
theorem B1776803 : Blo 1776089 1776803 := bstep (se 1 (by rfl) ⟨1332602, by rfl⟩ : syracuseStep 1776803 = 2665205) B2665205
theorem B2997425 : Blo 1776089 2997425 := bstep (se 2 (by rfl) ⟨1124034, by rfl⟩ : syracuseStep 2997425 = 2248069) B2248069
theorem B1776819 : Blo 1776089 1776819 := bstep (se 1 (by rfl) ⟨1332614, by rfl⟩ : syracuseStep 1776819 = 2665229) B2665229
theorem B22764725 : Blo 1776089 22764725 := bstep (se 5 (by rfl) ⟨1067096, by rfl⟩ : syracuseStep 22764725 = 2134193) B2134193
theorem B1776835 : Blo 1776089 1776835 := bstep (se 1 (by rfl) ⟨1332626, by rfl⟩ : syracuseStep 1776835 = 2665253) B2665253
theorem B3996881 : Blo 1776089 3996881 := bstep (se 2 (by rfl) ⟨1498830, by rfl⟩ : syracuseStep 3996881 = 2997661) B2997661
theorem B4496593 : Blo 1776089 4496593 := bstep (se 2 (by rfl) ⟨1686222, by rfl⟩ : syracuseStep 4496593 = 3372445) B3372445
theorem B1776851 : Blo 1776089 1776851 := bstep (se 1 (by rfl) ⟨1332638, by rfl⟩ : syracuseStep 1776851 = 2665277) B2665277
theorem B3996899 : Blo 1776089 3996899 := bstep (se 1 (by rfl) ⟨2997674, by rfl⟩ : syracuseStep 3996899 = 5995349) B5995349
theorem B1776867 : Blo 1776089 1776867 := bstep (se 1 (by rfl) ⟨1332650, by rfl⟩ : syracuseStep 1776867 = 2665301) B2665301
theorem B5692643 : Blo 1776089 5692643 := bstep (se 1 (by rfl) ⟨4269482, by rfl⟩ : syracuseStep 5692643 = 8538965) B8538965
theorem B1776883 : Blo 1776089 1776883 := bstep (se 1 (by rfl) ⟨1332662, by rfl⟩ : syracuseStep 1776883 = 2665325) B2665325
theorem B1776899 : Blo 1776089 1776899 := bstep (se 1 (by rfl) ⟨1332674, by rfl⟩ : syracuseStep 1776899 = 2665349) B2665349
theorem B8543501 : Blo 1776089 8543501 := bstep (se 3 (by rfl) ⟨1601906, by rfl⟩ : syracuseStep 8543501 = 3203813) B3203813
theorem B1776915 : Blo 1776089 1776915 := bstep (se 1 (by rfl) ⟨1332686, by rfl⟩ : syracuseStep 1776915 = 2665373) B2665373
theorem B1776931 : Blo 1776089 1776931 := bstep (se 1 (by rfl) ⟨1332698, by rfl⟩ : syracuseStep 1776931 = 2665397) B2665397
theorem B2997553 : Blo 1776089 2997553 := bstep (se 2 (by rfl) ⟨1124082, by rfl⟩ : syracuseStep 2997553 = 2248165) B2248165
theorem B1776947 : Blo 1776089 1776947 := bstep (se 1 (by rfl) ⟨1332710, by rfl⟩ : syracuseStep 1776947 = 2665421) B2665421
theorem B1776963 : Blo 1776089 1776963 := bstep (se 1 (by rfl) ⟨1332722, by rfl⟩ : syracuseStep 1776963 = 2665445) B2665445
theorem B15392069 : Blo 1776089 15392069 := bstep (se 4 (by rfl) ⟨1443006, by rfl⟩ : syracuseStep 15392069 = 2886013) B2886013
theorem B2997587 : Blo 1776089 2997587 := bstep (se 1 (by rfl) ⟨2248190, by rfl⟩ : syracuseStep 2997587 = 4496381) B4496381
theorem B1776979 : Blo 1776089 1776979 := bstep (se 1 (by rfl) ⟨1332734, by rfl⟩ : syracuseStep 1776979 = 2665469) B2665469
theorem B1776995 : Blo 1776089 1776995 := bstep (se 1 (by rfl) ⟨1332746, by rfl⟩ : syracuseStep 1776995 = 2665493) B2665493
theorem B3374435 : Blo 1776089 3374435 := bstep (se 1 (by rfl) ⟨2530826, by rfl⟩ : syracuseStep 3374435 = 5061653) B5061653
theorem B5995889 : Blo 1776089 5995889 := bstep (se 2 (by rfl) ⟨2248458, by rfl⟩ : syracuseStep 5995889 = 4496917) B4496917
theorem B1777011 : Blo 1776089 1777011 := bstep (se 1 (by rfl) ⟨1332758, by rfl⟩ : syracuseStep 1777011 = 2665517) B2665517
theorem B21921137 : Blo 1776089 21921137 := bstep (se 2 (by rfl) ⟨8220426, by rfl⟩ : syracuseStep 21921137 = 16440853) B16440853
theorem B1998211 : Blo 1776089 1998211 := bstep (se 1 (by rfl) ⟨1498658, by rfl⟩ : syracuseStep 1998211 = 2997317) B2997317
theorem B1777027 : Blo 1776089 1777027 := bstep (se 1 (by rfl) ⟨1332770, by rfl⟩ : syracuseStep 1777027 = 2665541) B2665541
theorem B1777043 : Blo 1776089 1777043 := bstep (se 1 (by rfl) ⟨1332782, by rfl⟩ : syracuseStep 1777043 = 2665565) B2665565
theorem B10116515 : Blo 1776089 10116515 := bstep (se 1 (by rfl) ⟨7587386, by rfl⟩ : syracuseStep 10116515 = 15174773) B15174773
theorem B1777059 : Blo 1776089 1777059 := bstep (se 1 (by rfl) ⟨1332794, by rfl⟩ : syracuseStep 1777059 = 2665589) B2665589
theorem B1777075 : Blo 1776089 1777075 := bstep (se 1 (by rfl) ⟨1332806, by rfl⟩ : syracuseStep 1777075 = 2665613) B2665613
theorem B1777091 : Blo 1776089 1777091 := bstep (se 1 (by rfl) ⟨1332818, by rfl⟩ : syracuseStep 1777091 = 2665637) B2665637
theorem B2530769 : Blo 1776089 2530769 := bstep (se 2 (by rfl) ⟨949038, by rfl⟩ : syracuseStep 2530769 = 1898077) B1898077
theorem B2997715 : Blo 1776089 2997715 := bstep (se 1 (by rfl) ⟨2248286, by rfl⟩ : syracuseStep 2997715 = 4496573) B4496573
theorem B1777107 : Blo 1776089 1777107 := bstep (se 1 (by rfl) ⟨1332830, by rfl⟩ : syracuseStep 1777107 = 2665661) B2665661
theorem B4496867 : Blo 1776089 4496867 := bstep (se 1 (by rfl) ⟨3372650, by rfl⟩ : syracuseStep 4496867 = 6745301) B6745301
theorem B1777123 : Blo 1776089 1777123 := bstep (se 1 (by rfl) ⟨1332842, by rfl⟩ : syracuseStep 1777123 = 2665685) B2665685
theorem B3997169 : Blo 1776089 3997169 := bstep (se 2 (by rfl) ⟨1498938, by rfl⟩ : syracuseStep 3997169 = 2997877) B2997877
theorem B1777139 : Blo 1776089 1777139 := bstep (se 1 (by rfl) ⟨1332854, by rfl⟩ : syracuseStep 1777139 = 2665709) B2665709
theorem B3997187 : Blo 1776089 3997187 := bstep (se 1 (by rfl) ⟨2997890, by rfl⟩ : syracuseStep 3997187 = 5995781) B5995781
theorem B1777155 : Blo 1776089 1777155 := bstep (se 1 (by rfl) ⟨1332866, by rfl⟩ : syracuseStep 1777155 = 2665733) B2665733
theorem B1998355 : Blo 1776089 1998355 := bstep (se 1 (by rfl) ⟨1498766, by rfl⟩ : syracuseStep 1998355 = 2997533) B2997533
theorem B1777171 : Blo 1776089 1777171 := bstep (se 1 (by rfl) ⟨1332878, by rfl⟩ : syracuseStep 1777171 = 2665757) B2665757
theorem B1777187 : Blo 1776089 1777187 := bstep (se 1 (by rfl) ⟨1332890, by rfl⟩ : syracuseStep 1777187 = 2665781) B2665781
theorem B1777203 : Blo 1776089 1777203 := bstep (se 1 (by rfl) ⟨1332902, by rfl⟩ : syracuseStep 1777203 = 2665805) B2665805
theorem B1777219 : Blo 1776089 1777219 := bstep (se 1 (by rfl) ⟨1332914, by rfl⟩ : syracuseStep 1777219 = 2665829) B2665829
theorem B2530883 : Blo 1776089 2530883 := bstep (se 1 (by rfl) ⟨1898162, by rfl⟩ : syracuseStep 2530883 = 3796325) B3796325
theorem B19217989 : Blo 1776089 19217989 := bstep (se 4 (by rfl) ⟨1801686, by rfl⟩ : syracuseStep 19217989 = 3603373) B3603373
theorem B1777235 : Blo 1776089 1777235 := bstep (se 1 (by rfl) ⟨1332926, by rfl⟩ : syracuseStep 1777235 = 2665853) B2665853
theorem B2997857 : Blo 1776089 2997857 := bstep (se 2 (by rfl) ⟨1124196, by rfl⟩ : syracuseStep 2997857 = 2248393) B2248393
theorem B1777251 : Blo 1776089 1777251 := bstep (se 1 (by rfl) ⟨1332938, by rfl⟩ : syracuseStep 1777251 = 2665877) B2665877
theorem B1777267 : Blo 1776089 1777267 := bstep (se 1 (by rfl) ⟨1332950, by rfl⟩ : syracuseStep 1777267 = 2665901) B2665901
theorem B1777283 : Blo 1776089 1777283 := bstep (se 1 (by rfl) ⟨1332962, by rfl⟩ : syracuseStep 1777283 = 2665925) B2665925
theorem B3374723 : Blo 1776089 3374723 := bstep (se 1 (by rfl) ⟨2531042, by rfl⟩ : syracuseStep 3374723 = 5062085) B5062085
theorem B1777299 : Blo 1776089 1777299 := bstep (se 1 (by rfl) ⟨1332974, by rfl⟩ : syracuseStep 1777299 = 2665949) B2665949
theorem B2530963 : Blo 1776089 2530963 := bstep (se 1 (by rfl) ⟨1898222, by rfl⟩ : syracuseStep 2530963 = 3796445) B3796445
theorem B1998499 : Blo 1776089 1998499 := bstep (se 1 (by rfl) ⟨1498874, by rfl⟩ : syracuseStep 1998499 = 2997749) B2997749
theorem B4497059 : Blo 1776089 4497059 := bstep (se 1 (by rfl) ⟨3372794, by rfl⟩ : syracuseStep 4497059 = 6745589) B6745589
theorem B1777315 : Blo 1776089 1777315 := bstep (se 1 (by rfl) ⟨1332986, by rfl⟩ : syracuseStep 1777315 = 2665973) B2665973
theorem B1777331 : Blo 1776089 1777331 := bstep (se 1 (by rfl) ⟨1332998, by rfl⟩ : syracuseStep 1777331 = 2665997) B2665997
theorem B1777347 : Blo 1776089 1777347 := bstep (se 1 (by rfl) ⟨1333010, by rfl⟩ : syracuseStep 1777347 = 2666021) B2666021
theorem B1777363 : Blo 1776089 1777363 := bstep (se 1 (by rfl) ⟨1333022, by rfl⟩ : syracuseStep 1777363 = 2666045) B2666045
theorem B2997985 : Blo 1776089 2997985 := bstep (se 2 (by rfl) ⟨1124244, by rfl⟩ : syracuseStep 2997985 = 2248489) B2248489
theorem B1777379 : Blo 1776089 1777379 := bstep (se 1 (by rfl) ⟨1333034, by rfl⟩ : syracuseStep 1777379 = 2666069) B2666069
theorem B83222243 : Blo 1776089 83222243 := bstep (se 1 (by rfl) ⟨62416682, by rfl⟩ : syracuseStep 83222243 = 124833365) B124833365
theorem B8535793 : Blo 1776089 8535793 := bstep (se 2 (by rfl) ⟨3200922, by rfl⟩ : syracuseStep 8535793 = 6401845) B6401845
theorem B1777395 : Blo 1776089 1777395 := bstep (se 1 (by rfl) ⟨1333046, by rfl⟩ : syracuseStep 1777395 = 2666093) B2666093
theorem B2998019 : Blo 1776089 2998019 := bstep (se 1 (by rfl) ⟨2248514, by rfl⟩ : syracuseStep 2998019 = 4497029) B4497029
theorem B1777411 : Blo 1776089 1777411 := bstep (se 1 (by rfl) ⟨1333058, by rfl⟩ : syracuseStep 1777411 = 2666117) B2666117
theorem B3997457 : Blo 1776089 3997457 := bstep (se 2 (by rfl) ⟨1499046, by rfl⟩ : syracuseStep 3997457 = 2998093) B2998093
theorem B1777427 : Blo 1776089 1777427 := bstep (se 1 (by rfl) ⟨1333070, by rfl⟩ : syracuseStep 1777427 = 2666141) B2666141
theorem B3997475 : Blo 1776089 3997475 := bstep (se 1 (by rfl) ⟨2998106, by rfl⟩ : syracuseStep 3997475 = 5996213) B5996213
theorem B1777443 : Blo 1776089 1777443 := bstep (se 1 (by rfl) ⟨1333082, by rfl⟩ : syracuseStep 1777443 = 2666165) B2666165
theorem B1998643 : Blo 1776089 1998643 := bstep (se 1 (by rfl) ⟨1498982, by rfl⟩ : syracuseStep 1998643 = 2997965) B2997965
theorem B1777459 : Blo 1776089 1777459 := bstep (se 1 (by rfl) ⟨1333094, by rfl⟩ : syracuseStep 1777459 = 2666189) B2666189
theorem B1777475 : Blo 1776089 1777475 := bstep (se 1 (by rfl) ⟨1333106, by rfl⟩ : syracuseStep 1777475 = 2666213) B2666213
theorem B1777491 : Blo 1776089 1777491 := bstep (se 1 (by rfl) ⟨1333118, by rfl⟩ : syracuseStep 1777491 = 2666237) B2666237
theorem B1777507 : Blo 1776089 1777507 := bstep (se 1 (by rfl) ⟨1333130, by rfl⟩ : syracuseStep 1777507 = 2666261) B2666261
theorem B1777523 : Blo 1776089 1777523 := bstep (se 1 (by rfl) ⟨1333142, by rfl⟩ : syracuseStep 1777523 = 2666285) B2666285
theorem B2998147 : Blo 1776089 2998147 := bstep (se 1 (by rfl) ⟨2248610, by rfl⟩ : syracuseStep 2998147 = 4497221) B4497221
theorem B1777539 : Blo 1776089 1777539 := bstep (se 1 (by rfl) ⟨1333154, by rfl⟩ : syracuseStep 1777539 = 2666309) B2666309
theorem B5996429 : Blo 1776089 5996429 := bstep (se 3 (by rfl) ⟨1124330, by rfl⟩ : syracuseStep 5996429 = 2248661) B2248661
theorem B1777555 : Blo 1776089 1777555 := bstep (se 1 (by rfl) ⟨1333166, by rfl⟩ : syracuseStep 1777555 = 2666333) B2666333
theorem B1777571 : Blo 1776089 1777571 := bstep (se 1 (by rfl) ⟨1333178, by rfl⟩ : syracuseStep 1777571 = 2666357) B2666357
theorem B1777587 : Blo 1776089 1777587 := bstep (se 1 (by rfl) ⟨1333190, by rfl⟩ : syracuseStep 1777587 = 2666381) B2666381
theorem B1998787 : Blo 1776089 1998787 := bstep (se 1 (by rfl) ⟨1499090, by rfl⟩ : syracuseStep 1998787 = 2998181) B2998181
theorem B5996483 : Blo 1776089 5996483 := bstep (se 1 (by rfl) ⟨4497362, by rfl⟩ : syracuseStep 5996483 = 8994725) B8994725
theorem B1777603 : Blo 1776089 1777603 := bstep (se 1 (by rfl) ⟨1333202, by rfl⟩ : syracuseStep 1777603 = 2666405) B2666405
theorem B1777619 : Blo 1776089 1777619 := bstep (se 1 (by rfl) ⟨1333214, by rfl⟩ : syracuseStep 1777619 = 2666429) B2666429
theorem B3039203 : Blo 1776089 3039203 := bstep (se 1 (by rfl) ⟨2279402, by rfl⟩ : syracuseStep 3039203 = 4558805) B4558805
theorem B5693411 : Blo 1776089 5693411 := bstep (se 1 (by rfl) ⟨4270058, by rfl⟩ : syracuseStep 5693411 = 8540117) B8540117
theorem B1777635 : Blo 1776089 1777635 := bstep (se 1 (by rfl) ⟨1333226, by rfl⟩ : syracuseStep 1777635 = 2666453) B2666453
theorem B1777651 : Blo 1776089 1777651 := bstep (se 1 (by rfl) ⟨1333238, by rfl⟩ : syracuseStep 1777651 = 2666477) B2666477
theorem B1998859 : Blo 1776089 1998859 := bstep (se 1 (by rfl) ⟨1499144, by rfl⟩ : syracuseStep 1998859 = 2998289) B2998289
theorem B1777675 : Blo 1776089 1777675 := bstep (se 1 (by rfl) ⟨1333256, by rfl⟩ : syracuseStep 1777675 = 2666513) B2666513
theorem B1777687 : Blo 1776089 1777687 := bstep (se 1 (by rfl) ⟨1333265, by rfl⟩ : syracuseStep 1777687 = 2666531) B2666531
theorem B1777707 : Blo 1776089 1777707 := bstep (se 1 (by rfl) ⟨1333280, by rfl⟩ : syracuseStep 1777707 = 2666561) B2666561
theorem B11386925 : Blo 1776089 11386925 := bstep (se 3 (by rfl) ⟨2135048, by rfl⟩ : syracuseStep 11386925 = 4270097) B4270097
theorem B1777719 : Blo 1776089 1777719 := bstep (se 1 (by rfl) ⟨1333289, by rfl⟩ : syracuseStep 1777719 = 2666579) B2666579
theorem B1777739 : Blo 1776089 1777739 := bstep (se 1 (by rfl) ⟨1333304, by rfl⟩ : syracuseStep 1777739 = 2666609) B2666609
theorem B3375179 : Blo 1776089 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B1777751 : Blo 1776089 1777751 := bstep (se 1 (by rfl) ⟨1333313, by rfl⟩ : syracuseStep 1777751 = 2666627) B2666627
theorem B1777771 : Blo 1776089 1777771 := bstep (se 1 (by rfl) ⟨1333328, by rfl⟩ : syracuseStep 1777771 = 2666657) B2666657
theorem B1998967 : Blo 1776089 1998967 := bstep (se 1 (by rfl) ⟨1499225, by rfl⟩ : syracuseStep 1998967 = 2998451) B2998451
theorem B1777783 : Blo 1776089 1777783 := bstep (se 1 (by rfl) ⟨1333337, by rfl⟩ : syracuseStep 1777783 = 2666675) B2666675
theorem B8536195 : Blo 1776089 8536195 := bstep (se 1 (by rfl) ⟨6402146, by rfl⟩ : syracuseStep 8536195 = 12804293) B12804293
theorem B3997835 : Blo 1776089 3997835 := bstep (se 1 (by rfl) ⟨2998376, by rfl⟩ : syracuseStep 3997835 = 5996753) B5996753
theorem B1777803 : Blo 1776089 1777803 := bstep (se 1 (by rfl) ⟨1333352, by rfl⟩ : syracuseStep 1777803 = 2666705) B2666705
theorem B1777815 : Blo 1776089 1777815 := bstep (se 1 (by rfl) ⟨1333361, by rfl⟩ : syracuseStep 1777815 = 2666723) B2666723
theorem B1777835 : Blo 1776089 1777835 := bstep (se 1 (by rfl) ⟨1333376, by rfl⟩ : syracuseStep 1777835 = 2666753) B2666753
theorem B13500593 : Blo 1776089 13500593 := bstep (se 2 (by rfl) ⟨5062722, by rfl⟩ : syracuseStep 13500593 = 10125445) B10125445
theorem B1777847 : Blo 1776089 1777847 := bstep (se 1 (by rfl) ⟨1333385, by rfl⟩ : syracuseStep 1777847 = 2666771) B2666771
theorem B3997889 : Blo 1776089 3997889 := bstep (se 2 (by rfl) ⟨1499208, by rfl⟩ : syracuseStep 3997889 = 2998417) B2998417
theorem B1777867 : Blo 1776089 1777867 := bstep (se 1 (by rfl) ⟨1333400, by rfl⟩ : syracuseStep 1777867 = 2666801) B2666801
theorem B1777879 : Blo 1776089 1777879 := bstep (se 1 (by rfl) ⟨1333409, by rfl⟩ : syracuseStep 1777879 = 2666819) B2666819
theorem B1777899 : Blo 1776089 1777899 := bstep (se 1 (by rfl) ⟨1333424, by rfl⟩ : syracuseStep 1777899 = 2666849) B2666849
theorem B1777911 : Blo 1776089 1777911 := bstep (se 1 (by rfl) ⟨1333433, by rfl⟩ : syracuseStep 1777911 = 2666867) B2666867
theorem B3375361 : Blo 1776089 3375361 := bstep (se 2 (by rfl) ⟨1265760, by rfl⟩ : syracuseStep 3375361 = 2531521) B2531521
theorem B1777931 : Blo 1776089 1777931 := bstep (se 1 (by rfl) ⟨1333448, by rfl⟩ : syracuseStep 1777931 = 2666897) B2666897
theorem B1777943 : Blo 1776089 1777943 := bstep (se 1 (by rfl) ⟨1333457, by rfl⟩ : syracuseStep 1777943 = 2666915) B2666915
theorem B1999147 : Blo 1776089 1999147 := bstep (se 1 (by rfl) ⟨1499360, by rfl⟩ : syracuseStep 1999147 = 2998721) B2998721
theorem B1777963 : Blo 1776089 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B1777975 : Blo 1776089 1777975 := bstep (se 1 (by rfl) ⟨1333481, by rfl⟩ : syracuseStep 1777975 = 2666963) B2666963
theorem B1777995 : Blo 1776089 1777995 := bstep (se 1 (by rfl) ⟨1333496, by rfl⟩ : syracuseStep 1777995 = 2666993) B2666993
theorem B1778007 : Blo 1776089 1778007 := bstep (se 1 (by rfl) ⟨1333505, by rfl⟩ : syracuseStep 1778007 = 2667011) B2667011
theorem B1778027 : Blo 1776089 1778027 := bstep (se 1 (by rfl) ⟨1333520, by rfl⟩ : syracuseStep 1778027 = 2667041) B2667041
theorem B20513141 : Blo 1776089 20513141 := bstep (se 5 (by rfl) ⟨961553, by rfl⟩ : syracuseStep 20513141 = 1923107) B1923107
theorem B1778039 : Blo 1776089 1778039 := bstep (se 1 (by rfl) ⟨1333529, by rfl⟩ : syracuseStep 1778039 = 2667059) B2667059
theorem B2998667 : Blo 1776089 2998667 := bstep (se 1 (by rfl) ⟨2249000, by rfl⟩ : syracuseStep 2998667 = 4498001) B4498001
theorem B1778059 : Blo 1776089 1778059 := bstep (se 1 (by rfl) ⟨1333544, by rfl⟩ : syracuseStep 1778059 = 2667089) B2667089
theorem B1999255 : Blo 1776089 1999255 := bstep (se 1 (by rfl) ⟨1499441, by rfl⟩ : syracuseStep 1999255 = 2998883) B2998883
theorem B10125719 : Blo 1776089 10125719 := bstep (se 1 (by rfl) ⟨7594289, by rfl⟩ : syracuseStep 10125719 = 15188579) B15188579
theorem B3998105 : Blo 1776089 3998105 := bstep (se 2 (by rfl) ⟨1499289, by rfl⟩ : syracuseStep 3998105 = 2998579) B2998579
theorem B1778071 : Blo 1776089 1778071 := bstep (se 1 (by rfl) ⟨1333553, by rfl⟩ : syracuseStep 1778071 = 2667107) B2667107
theorem B15180209 : Blo 1776089 15180209 := bstep (se 2 (by rfl) ⟨5692578, by rfl⟩ : syracuseStep 15180209 = 11385157) B11385157
theorem B8110529 : Blo 1776089 8110529 := bstep (se 2 (by rfl) ⟨3041448, by rfl⟩ : syracuseStep 8110529 = 6082897) B6082897
theorem B3039691 : Blo 1776089 3039691 := bstep (se 1 (by rfl) ⟨2279768, by rfl⟩ : syracuseStep 3039691 = 4559537) B4559537
theorem B3998195 : Blo 1776089 3998195 := bstep (se 1 (by rfl) ⟨2998646, by rfl⟩ : syracuseStep 3998195 = 5997293) B5997293
theorem B2998795 : Blo 1776089 2998795 := bstep (se 1 (by rfl) ⟨2249096, by rfl⟩ : syracuseStep 2998795 = 4498193) B4498193
theorem B3998231 : Blo 1776089 3998231 := bstep (se 1 (by rfl) ⟨2998673, by rfl⟩ : syracuseStep 3998231 = 5997347) B5997347
theorem B8995373 : Blo 1776089 8995373 := bstep (se 3 (by rfl) ⟨1686632, by rfl⟩ : syracuseStep 8995373 = 3373265) B3373265
theorem B5997131 : Blo 1776089 5997131 := bstep (se 1 (by rfl) ⟨4497848, by rfl⟩ : syracuseStep 5997131 = 8995697) B8995697
theorem B1999435 : Blo 1776089 1999435 := bstep (se 1 (by rfl) ⟨1499576, by rfl⟩ : syracuseStep 1999435 = 2999153) B2999153
theorem B13501079 : Blo 1776089 13501079 := bstep (se 1 (by rfl) ⟨10125809, by rfl⟩ : syracuseStep 13501079 = 20251619) B20251619
theorem B2998937 : Blo 1776089 2998937 := bstep (se 2 (by rfl) ⟨1124601, by rfl⟩ : syracuseStep 2998937 = 2249203) B2249203
theorem B1999543 : Blo 1776089 1999543 := bstep (se 1 (by rfl) ⟨1499657, by rfl⟩ : syracuseStep 1999543 = 2999315) B2999315
theorem B3998411 : Blo 1776089 3998411 := bstep (se 1 (by rfl) ⟨2998808, by rfl⟩ : syracuseStep 3998411 = 5997617) B5997617
theorem B3998465 : Blo 1776089 3998465 := bstep (se 2 (by rfl) ⟨1499424, by rfl⟩ : syracuseStep 3998465 = 2998849) B2998849
theorem B4621079 : Blo 1776089 4621079 := bstep (se 1 (by rfl) ⟨3465809, by rfl⟩ : syracuseStep 4621079 = 6931619) B6931619
theorem B2999065 : Blo 1776089 2999065 := bstep (se 2 (by rfl) ⟨1124649, by rfl⟩ : syracuseStep 2999065 = 2249299) B2249299
theorem B7586635 : Blo 1776089 7586635 := bstep (se 1 (by rfl) ⟨5689976, by rfl⟩ : syracuseStep 7586635 = 11379953) B11379953
theorem B5997401 : Blo 1776089 5997401 := bstep (se 2 (by rfl) ⟨2249025, by rfl⟩ : syracuseStep 5997401 = 4498051) B4498051
theorem B1999723 : Blo 1776089 1999723 := bstep (se 1 (by rfl) ⟨1499792, by rfl⟩ : syracuseStep 1999723 = 2999585) B2999585
theorem B4498355 : Blo 1776089 4498355 := bstep (se 1 (by rfl) ⟨3373766, by rfl⟩ : syracuseStep 4498355 = 6747533) B6747533
theorem B1999831 : Blo 1776089 1999831 := bstep (se 1 (by rfl) ⟨1499873, by rfl⟩ : syracuseStep 1999831 = 2999747) B2999747
theorem B3998681 : Blo 1776089 3998681 := bstep (se 2 (by rfl) ⟨1499505, by rfl⟩ : syracuseStep 3998681 = 2999011) B2999011
theorem B5694425 : Blo 1776089 5694425 := bstep (se 2 (by rfl) ⟨2135409, by rfl⟩ : syracuseStep 5694425 = 4270819) B4270819
theorem B93627413 : Blo 1776089 93627413 := bstep (se 6 (by rfl) ⟨2194392, by rfl⟩ : syracuseStep 93627413 = 4388785) B4388785
theorem B3998771 : Blo 1776089 3998771 := bstep (se 1 (by rfl) ⟨2999078, by rfl⟩ : syracuseStep 3998771 = 5998157) B5998157
theorem B3998807 : Blo 1776089 3998807 := bstep (se 1 (by rfl) ⟨2999105, by rfl⟩ : syracuseStep 3998807 = 5998211) B5998211
theorem B7586909 : Blo 1776089 7586909 := bstep (se 3 (by rfl) ⟨1422545, by rfl⟩ : syracuseStep 7586909 = 2845091) B2845091
theorem B4867165 : Blo 1776089 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B3794035 : Blo 1776089 3794035 := bstep (se 1 (by rfl) ⟨2845526, by rfl⟩ : syracuseStep 3794035 = 5691053) B5691053
theorem B2000011 : Blo 1776089 2000011 := bstep (se 1 (by rfl) ⟨1500008, by rfl⟩ : syracuseStep 2000011 = 3000017) B3000017
theorem B4498649 : Blo 1776089 4498649 := bstep (se 2 (by rfl) ⟨1686993, by rfl⟩ : syracuseStep 4498649 = 3373987) B3373987
theorem B2000119 : Blo 1776089 2000119 := bstep (se 1 (by rfl) ⟨1500089, by rfl⟩ : syracuseStep 2000119 = 3000179) B3000179
theorem B3998987 : Blo 1776089 3998987 := bstep (se 1 (by rfl) ⟨2999240, by rfl⟩ : syracuseStep 3998987 = 5998481) B5998481
theorem B5694743 : Blo 1776089 5694743 := bstep (se 1 (by rfl) ⟨4271057, by rfl⟩ : syracuseStep 5694743 = 8542115) B8542115
theorem B3999041 : Blo 1776089 3999041 := bstep (se 2 (by rfl) ⟨1499640, by rfl⟩ : syracuseStep 3999041 = 2999281) B2999281
theorem B6079819 : Blo 1776089 6079819 := bstep (se 1 (by rfl) ⟨4559864, by rfl⟩ : syracuseStep 6079819 = 9119729) B9119729
theorem B2999639 : Blo 1776089 2999639 := bstep (se 1 (by rfl) ⟨2249729, by rfl⟩ : syracuseStep 2999639 = 4499459) B4499459
theorem B2000299 : Blo 1776089 2000299 := bstep (se 1 (by rfl) ⟨1500224, by rfl⟩ : syracuseStep 2000299 = 3000449) B3000449
theorem B2999767 : Blo 1776089 2999767 := bstep (se 1 (by rfl) ⟨2249825, by rfl⟩ : syracuseStep 2999767 = 4499651) B4499651
theorem B5998103 : Blo 1776089 5998103 := bstep (se 1 (by rfl) ⟨4498577, by rfl⟩ : syracuseStep 5998103 = 8997155) B8997155
theorem B3999257 : Blo 1776089 3999257 := bstep (se 2 (by rfl) ⟨1499721, by rfl⟩ : syracuseStep 3999257 = 2999443) B2999443
theorem B5695051 : Blo 1776089 5695051 := bstep (se 1 (by rfl) ⟨4271288, by rfl⟩ : syracuseStep 5695051 = 8542577) B8542577
theorem B6743645 : Blo 1776089 6743645 := bstep (se 3 (by rfl) ⟨1264433, by rfl⟩ : syracuseStep 6743645 = 2528867) B2528867
theorem B15189605 : Blo 1776089 15189605 := bstep (se 4 (by rfl) ⟨1424025, by rfl⟩ : syracuseStep 15189605 = 2848051) B2848051
theorem B3999347 : Blo 1776089 3999347 := bstep (se 1 (by rfl) ⟨2999510, by rfl⟩ : syracuseStep 3999347 = 5999021) B5999021
theorem B34162307 : Blo 1776089 34162307 := bstep (se 1 (by rfl) ⟨25621730, by rfl⟩ : syracuseStep 34162307 = 51243461) B51243461
theorem B3999383 : Blo 1776089 3999383 := bstep (se 1 (by rfl) ⟨2999537, by rfl⟩ : syracuseStep 3999383 = 5999075) B5999075
theorem B8652505 : Blo 1776089 8652505 := bstep (se 2 (by rfl) ⟨3244689, by rfl⟩ : syracuseStep 8652505 = 6489379) B6489379
theorem B2664203 : Blo 1776089 2664203 := bstep (se 1 (by rfl) ⟨1998152, by rfl⟩ : syracuseStep 2664203 = 3996305) B3996305
theorem B9602833 : Blo 1776089 9602833 := bstep (se 2 (by rfl) ⟨3601062, by rfl⟩ : syracuseStep 9602833 = 7202125) B7202125
theorem B2664215 : Blo 1776089 2664215 := bstep (se 1 (by rfl) ⟨1998161, by rfl⟩ : syracuseStep 2664215 = 3996323) B3996323
theorem B7202611 : Blo 1776089 7202611 := bstep (se 1 (by rfl) ⟨5401958, by rfl⟩ : syracuseStep 7202611 = 10803917) B10803917
theorem B6408001 : Blo 1776089 6408001 := bstep (se 2 (by rfl) ⟨2403000, by rfl⟩ : syracuseStep 6408001 = 4806001) B4806001
theorem B3999563 : Blo 1776089 3999563 := bstep (se 1 (by rfl) ⟨2999672, by rfl⟩ : syracuseStep 3999563 = 5999345) B5999345
theorem B2664281 : Blo 1776089 2664281 := bstep (se 2 (by rfl) ⟨999105, by rfl⟩ : syracuseStep 2664281 = 1998211) B1998211
theorem B30787445 : Blo 1776089 30787445 := bstep (se 5 (by rfl) ⟨1443161, by rfl⟩ : syracuseStep 30787445 = 2886323) B2886323
theorem B3999617 : Blo 1776089 3999617 := bstep (se 2 (by rfl) ⟨1499856, by rfl⟩ : syracuseStep 3999617 = 2999713) B2999713
theorem B2664395 : Blo 1776089 2664395 := bstep (se 1 (by rfl) ⟨1998296, by rfl⟩ : syracuseStep 2664395 = 3996593) B3996593
theorem B2664407 : Blo 1776089 2664407 := bstep (se 1 (by rfl) ⟨1998305, by rfl⟩ : syracuseStep 2664407 = 3996611) B3996611
theorem B2664473 : Blo 1776089 2664473 := bstep (se 2 (by rfl) ⟨999177, by rfl⟩ : syracuseStep 2664473 = 1998355) B1998355
theorem B5998643 : Blo 1776089 5998643 := bstep (se 1 (by rfl) ⟨4498982, by rfl⟩ : syracuseStep 5998643 = 8997965) B8997965
theorem B3000395 : Blo 1776089 3000395 := bstep (se 1 (by rfl) ⟨2250296, by rfl⟩ : syracuseStep 3000395 = 4500593) B4500593
theorem B3999833 : Blo 1776089 3999833 := bstep (se 2 (by rfl) ⟨1499937, by rfl⟩ : syracuseStep 3999833 = 2999875) B2999875
theorem B2664587 : Blo 1776089 2664587 := bstep (se 1 (by rfl) ⟨1998440, by rfl⟩ : syracuseStep 2664587 = 3996881) B3996881
theorem B2664599 : Blo 1776089 2664599 := bstep (se 1 (by rfl) ⟨1998449, by rfl⟩ : syracuseStep 2664599 = 3996899) B3996899
theorem B3795095 : Blo 1776089 3795095 := bstep (se 1 (by rfl) ⟨2846321, by rfl⟩ : syracuseStep 3795095 = 5692643) B5692643
theorem B3999923 : Blo 1776089 3999923 := bstep (se 1 (by rfl) ⟨2999942, by rfl⟩ : syracuseStep 3999923 = 5999885) B5999885
theorem B5695667 : Blo 1776089 5695667 := bstep (se 1 (by rfl) ⟨4271750, by rfl⟩ : syracuseStep 5695667 = 8543501) B8543501
theorem B3000523 : Blo 1776089 3000523 := bstep (se 1 (by rfl) ⟨2250392, by rfl⟩ : syracuseStep 3000523 = 4500785) B4500785
theorem B3999959 : Blo 1776089 3999959 := bstep (se 1 (by rfl) ⟨2999969, by rfl⟩ : syracuseStep 3999959 = 5999939) B5999939
theorem B2664665 : Blo 1776089 2664665 := bstep (se 2 (by rfl) ⟨999249, by rfl⟩ : syracuseStep 2664665 = 1998499) B1998499
theorem B6744343 : Blo 1776089 6744343 := bstep (se 1 (by rfl) ⟨5058257, by rfl⟩ : syracuseStep 6744343 = 10116515) B10116515
theorem B11381057 : Blo 1776089 11381057 := bstep (se 2 (by rfl) ⟨4267896, by rfl⟩ : syracuseStep 11381057 = 8535793) B8535793
theorem B3795265 : Blo 1776089 3795265 := bstep (se 2 (by rfl) ⟨1423224, by rfl⟩ : syracuseStep 3795265 = 2846449) B2846449
theorem B5998913 : Blo 1776089 5998913 := bstep (se 2 (by rfl) ⟨2249592, by rfl⟩ : syracuseStep 5998913 = 4499185) B4499185
theorem B2664779 : Blo 1776089 2664779 := bstep (se 1 (by rfl) ⟨1998584, by rfl⟩ : syracuseStep 2664779 = 3997169) B3997169
theorem B2664791 : Blo 1776089 2664791 := bstep (se 1 (by rfl) ⟨1998593, by rfl⟩ : syracuseStep 2664791 = 3997187) B3997187
theorem B4000139 : Blo 1776089 4000139 := bstep (se 1 (by rfl) ⟨3000104, by rfl⟩ : syracuseStep 4000139 = 6000209) B6000209
theorem B2664857 : Blo 1776089 2664857 := bstep (se 2 (by rfl) ⟨999321, by rfl⟩ : syracuseStep 2664857 = 1998643) B1998643
theorem B4000193 : Blo 1776089 4000193 := bstep (se 2 (by rfl) ⟨1500072, by rfl⟩ : syracuseStep 4000193 = 3000145) B3000145
theorem B2664971 : Blo 1776089 2664971 := bstep (se 1 (by rfl) ⟨1998728, by rfl⟩ : syracuseStep 2664971 = 3997457) B3997457
theorem B2664983 : Blo 1776089 2664983 := bstep (se 1 (by rfl) ⟨1998737, by rfl⟩ : syracuseStep 2664983 = 3997475) B3997475
theorem B2665049 : Blo 1776089 2665049 := bstep (se 2 (by rfl) ⟨999393, by rfl⟩ : syracuseStep 2665049 = 1998787) B1998787
theorem B8104541 : Blo 1776089 8104541 := bstep (se 3 (by rfl) ⟨1519601, by rfl⟩ : syracuseStep 8104541 = 3039203) B3039203
theorem B3795607 : Blo 1776089 3795607 := bstep (se 1 (by rfl) ⟨2846705, by rfl⟩ : syracuseStep 3795607 = 5693411) B5693411
theorem B4000409 : Blo 1776089 4000409 := bstep (se 2 (by rfl) ⟨1500153, by rfl⟩ : syracuseStep 4000409 = 3000307) B3000307
theorem B2665163 : Blo 1776089 2665163 := bstep (se 1 (by rfl) ⟨1998872, by rfl⟩ : syracuseStep 2665163 = 3997745) B3997745
theorem B43215565 : Blo 1776089 43215565 := bstep (se 3 (by rfl) ⟨8102918, by rfl⟩ : syracuseStep 43215565 = 16205837) B16205837
theorem B2665175 : Blo 1776089 2665175 := bstep (se 1 (by rfl) ⟨1998881, by rfl⟩ : syracuseStep 2665175 = 3997763) B3997763
theorem B4000499 : Blo 1776089 4000499 := bstep (se 1 (by rfl) ⟨3000374, by rfl⟩ : syracuseStep 4000499 = 6000749) B6000749
theorem B4000535 : Blo 1776089 4000535 := bstep (se 1 (by rfl) ⟨3000401, by rfl⟩ : syracuseStep 4000535 = 6000803) B6000803
theorem B2665241 : Blo 1776089 2665241 := bstep (se 2 (by rfl) ⟨999465, by rfl⟩ : syracuseStep 2665241 = 1998931) B1998931
theorem B4500299 : Blo 1776089 4500299 := bstep (se 1 (by rfl) ⟨3375224, by rfl⟩ : syracuseStep 4500299 = 6750449) B6750449
theorem B5999453 : Blo 1776089 5999453 := bstep (se 3 (by rfl) ⟨1124897, by rfl⟩ : syracuseStep 5999453 = 2249795) B2249795
theorem B8104835 : Blo 1776089 8104835 := bstep (se 1 (by rfl) ⟨6078626, by rfl⟩ : syracuseStep 8104835 = 12157253) B12157253
theorem B2665355 : Blo 1776089 2665355 := bstep (se 1 (by rfl) ⟨1999016, by rfl⟩ : syracuseStep 2665355 = 3998033) B3998033
theorem B2665367 : Blo 1776089 2665367 := bstep (se 1 (by rfl) ⟨1999025, by rfl⟩ : syracuseStep 2665367 = 3998051) B3998051
theorem B2665433 : Blo 1776089 2665433 := bstep (se 2 (by rfl) ⟨999537, by rfl⟩ : syracuseStep 2665433 = 1999075) B1999075
theorem B3845107 : Blo 1776089 3845107 := bstep (se 1 (by rfl) ⟨2883830, by rfl⟩ : syracuseStep 3845107 = 5767661) B5767661
theorem B6745133 : Blo 1776089 6745133 := bstep (se 3 (by rfl) ⟨1264712, by rfl⟩ : syracuseStep 6745133 = 2529425) B2529425
theorem B2665547 : Blo 1776089 2665547 := bstep (se 1 (by rfl) ⟨1999160, by rfl⟩ : syracuseStep 2665547 = 3998321) B3998321
theorem B2845783 : Blo 1776089 2845783 := bstep (se 1 (by rfl) ⟨2134337, by rfl⟩ : syracuseStep 2845783 = 4268675) B4268675
theorem B2665559 : Blo 1776089 2665559 := bstep (se 1 (by rfl) ⟨1999169, by rfl⟩ : syracuseStep 2665559 = 3998339) B3998339
theorem B2665625 : Blo 1776089 2665625 := bstep (se 2 (by rfl) ⟨999609, by rfl⟩ : syracuseStep 2665625 = 1999219) B1999219
theorem B2665739 : Blo 1776089 2665739 := bstep (se 1 (by rfl) ⟨1999304, by rfl⟩ : syracuseStep 2665739 = 3998609) B3998609
theorem B2665751 : Blo 1776089 2665751 := bstep (se 1 (by rfl) ⟨1999313, by rfl⟩ : syracuseStep 2665751 = 3998627) B3998627
theorem B2665817 : Blo 1776089 2665817 := bstep (se 2 (by rfl) ⟨999681, by rfl⟩ : syracuseStep 2665817 = 1999363) B1999363
theorem B8220035 : Blo 1776089 8220035 := bstep (se 1 (by rfl) ⟨6165026, by rfl⟩ : syracuseStep 8220035 = 12330053) B12330053
theorem B11537815 : Blo 1776089 11537815 := bstep (se 1 (by rfl) ⟨8653361, by rfl⟩ : syracuseStep 11537815 = 17306723) B17306723
theorem B2665931 : Blo 1776089 2665931 := bstep (se 1 (by rfl) ⟨1999448, by rfl⟩ : syracuseStep 2665931 = 3998897) B3998897
theorem B3796427 : Blo 1776089 3796427 := bstep (se 1 (by rfl) ⟨2847320, by rfl⟩ : syracuseStep 3796427 = 5694641) B5694641
theorem B2665943 : Blo 1776089 2665943 := bstep (se 1 (by rfl) ⟨1999457, by rfl⟩ : syracuseStep 2665943 = 3998915) B3998915
theorem B2666009 : Blo 1776089 2666009 := bstep (se 2 (by rfl) ⟨999753, by rfl⟩ : syracuseStep 2666009 = 1999507) B1999507
theorem B2666123 : Blo 1776089 2666123 := bstep (se 1 (by rfl) ⟨1999592, by rfl⟩ : syracuseStep 2666123 = 3999185) B3999185
theorem B2666135 : Blo 1776089 2666135 := bstep (se 1 (by rfl) ⟨1999601, by rfl⟩ : syracuseStep 2666135 = 3999203) B3999203
theorem B20803223 : Blo 1776089 20803223 := bstep (se 1 (by rfl) ⟨15602417, by rfl⟩ : syracuseStep 20803223 = 31204835) B31204835
theorem B11390615 : Blo 1776089 11390615 := bstep (se 1 (by rfl) ⟨8542961, by rfl⟩ : syracuseStep 11390615 = 17085923) B17085923
theorem B7204555 : Blo 1776089 7204555 := bstep (se 1 (by rfl) ⟨5403416, by rfl⟩ : syracuseStep 7204555 = 10806833) B10806833
theorem B2666201 : Blo 1776089 2666201 := bstep (se 2 (by rfl) ⟨999825, by rfl⟩ : syracuseStep 2666201 = 1999651) B1999651
theorem B4050739 : Blo 1776089 4050739 := bstep (se 1 (by rfl) ⟨3038054, by rfl⟩ : syracuseStep 4050739 = 6076109) B6076109
theorem B3796787 : Blo 1776089 3796787 := bstep (se 1 (by rfl) ⟨2847590, by rfl⟩ : syracuseStep 3796787 = 5695181) B5695181
theorem B2666315 : Blo 1776089 2666315 := bstep (se 1 (by rfl) ⟨1999736, by rfl⟩ : syracuseStep 2666315 = 3999473) B3999473
theorem B2666327 : Blo 1776089 2666327 := bstep (se 1 (by rfl) ⟨1999745, by rfl⟩ : syracuseStep 2666327 = 3999491) B3999491
theorem B2846603 : Blo 1776089 2846603 := bstep (se 1 (by rfl) ⟨2134952, by rfl⟩ : syracuseStep 2846603 = 4269905) B4269905
theorem B2666393 : Blo 1776089 2666393 := bstep (se 2 (by rfl) ⟨999897, by rfl⟩ : syracuseStep 2666393 = 1999795) B1999795
theorem B2248651 : Blo 1776089 2248651 := bstep (se 1 (by rfl) ⟨1686488, by rfl⟩ : syracuseStep 2248651 = 3372977) B3372977
theorem B6000587 : Blo 1776089 6000587 := bstep (se 1 (by rfl) ⟨4500440, by rfl⟩ : syracuseStep 6000587 = 9000881) B9000881
theorem B5058521 : Blo 1776089 5058521 := bstep (se 2 (by rfl) ⟨1896945, by rfl⟩ : syracuseStep 5058521 = 3793891) B3793891
theorem B6492125 : Blo 1776089 6492125 := bstep (se 3 (by rfl) ⟨1217273, by rfl⟩ : syracuseStep 6492125 = 2434547) B2434547
theorem B2666507 : Blo 1776089 2666507 := bstep (se 1 (by rfl) ⟨1999880, by rfl⟩ : syracuseStep 2666507 = 3999761) B3999761
theorem B2666519 : Blo 1776089 2666519 := bstep (se 1 (by rfl) ⟨1999889, by rfl⟩ : syracuseStep 2666519 = 3999779) B3999779
theorem B4272203 : Blo 1776089 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B2666585 : Blo 1776089 2666585 := bstep (se 2 (by rfl) ⟨999969, by rfl⟩ : syracuseStep 2666585 = 1999939) B1999939
theorem B2666699 : Blo 1776089 2666699 := bstep (se 1 (by rfl) ⟨2000024, by rfl⟩ : syracuseStep 2666699 = 4000049) B4000049
theorem B2666711 : Blo 1776089 2666711 := bstep (se 1 (by rfl) ⟨2000033, by rfl⟩ : syracuseStep 2666711 = 4000067) B4000067
theorem B6000857 : Blo 1776089 6000857 := bstep (se 2 (by rfl) ⟨2250321, by rfl⟩ : syracuseStep 6000857 = 4500643) B4500643
theorem B2666777 : Blo 1776089 2666777 := bstep (se 2 (by rfl) ⟨1000041, by rfl⟩ : syracuseStep 2666777 = 2000083) B2000083
theorem B8999261 : Blo 1776089 8999261 := bstep (se 3 (by rfl) ⟨1687361, by rfl⟩ : syracuseStep 8999261 = 3374723) B3374723
theorem B2666891 : Blo 1776089 2666891 := bstep (se 1 (by rfl) ⟨2000168, by rfl⟩ : syracuseStep 2666891 = 4000337) B4000337
theorem B2666903 : Blo 1776089 2666903 := bstep (se 1 (by rfl) ⟨2000177, by rfl⟩ : syracuseStep 2666903 = 4000355) B4000355
theorem B9605555 : Blo 1776089 9605555 := bstep (se 1 (by rfl) ⟨7204166, by rfl⟩ : syracuseStep 9605555 = 14408333) B14408333
theorem B6746561 : Blo 1776089 6746561 := bstep (se 2 (by rfl) ⟨2529960, by rfl⟩ : syracuseStep 6746561 = 5059921) B5059921
theorem B2666969 : Blo 1776089 2666969 := bstep (se 2 (by rfl) ⟨1000113, by rfl⟩ : syracuseStep 2666969 = 2000227) B2000227
theorem B2667083 : Blo 1776089 2667083 := bstep (se 1 (by rfl) ⟨2000312, by rfl⟩ : syracuseStep 2667083 = 4000625) B4000625
theorem B2667095 : Blo 1776089 2667095 := bstep (se 1 (by rfl) ⟨2000321, by rfl⟩ : syracuseStep 2667095 = 4000643) B4000643
theorem B2134679 : Blo 1776089 2134679 := bstep (se 1 (by rfl) ⟨1601009, by rfl⟩ : syracuseStep 2134679 = 3202019) B3202019
theorem B20247245 : Blo 1776089 20247245 := bstep (se 3 (by rfl) ⟨3796358, by rfl⟩ : syracuseStep 20247245 = 7592717) B7592717
theorem B3601111 : Blo 1776089 3601111 := bstep (se 1 (by rfl) ⟨2700833, by rfl⟩ : syracuseStep 3601111 = 5401667) B5401667
theorem B7205593 : Blo 1776089 7205593 := bstep (se 2 (by rfl) ⟨2702097, by rfl⟩ : syracuseStep 7205593 = 5404195) B5404195
theorem B2847449 : Blo 1776089 2847449 := bstep (se 2 (by rfl) ⟨1067793, by rfl⟩ : syracuseStep 2847449 = 2135587) B2135587
theorem B5059351 : Blo 1776089 5059351 := bstep (se 1 (by rfl) ⟨3794513, by rfl⟩ : syracuseStep 5059351 = 7589027) B7589027
theorem B15176483 : Blo 1776089 15176483 := bstep (se 1 (by rfl) ⟨11382362, by rfl⟩ : syracuseStep 15176483 = 22764725) B22764725
theorem B10122029 : Blo 1776089 10122029 := bstep (se 3 (by rfl) ⟨1897880, by rfl⟩ : syracuseStep 10122029 = 3795761) B3795761
theorem B1897291 : Blo 1776089 1897291 := bstep (se 1 (by rfl) ⟨1422968, by rfl⟩ : syracuseStep 1897291 = 2845937) B2845937
theorem B2847577 : Blo 1776089 2847577 := bstep (se 2 (by rfl) ⟨1067841, by rfl⟩ : syracuseStep 2847577 = 2135683) B2135683
theorem B10261379 : Blo 1776089 10261379 := bstep (se 1 (by rfl) ⟨7696034, by rfl⟩ : syracuseStep 10261379 = 15392069) B15392069
theorem B2249623 : Blo 1776089 2249623 := bstep (se 1 (by rfl) ⟨1687217, by rfl⟩ : syracuseStep 2249623 = 3374435) B3374435
theorem B2847641 : Blo 1776089 2847641 := bstep (se 2 (by rfl) ⟨1067865, by rfl⟩ : syracuseStep 2847641 = 2135731) B2135731
theorem B3372043 : Blo 1776089 3372043 := bstep (se 1 (by rfl) ⟨2529032, by rfl⟩ : syracuseStep 3372043 = 5058065) B5058065
theorem B8991809 : Blo 1776089 8991809 := bstep (se 2 (by rfl) ⟨3371928, by rfl⟩ : syracuseStep 8991809 = 6743857) B6743857
theorem B6583427 : Blo 1776089 6583427 := bstep (se 1 (by rfl) ⟨4937570, by rfl⟩ : syracuseStep 6583427 = 9875141) B9875141
theorem B55481495 : Blo 1776089 55481495 := bstep (se 1 (by rfl) ⟨41611121, by rfl⟩ : syracuseStep 55481495 = 83222243) B83222243
theorem B4052363 : Blo 1776089 4052363 := bstep (se 1 (by rfl) ⟨3039272, by rfl⟩ : syracuseStep 4052363 = 6078545) B6078545
theorem B3601817 : Blo 1776089 3601817 := bstep (se 2 (by rfl) ⟨1350681, by rfl⟩ : syracuseStep 3601817 = 2701363) B2701363
theorem B3372491 : Blo 1776089 3372491 := bstep (se 1 (by rfl) ⟨2529368, by rfl⟩ : syracuseStep 3372491 = 5058737) B5058737
theorem B6403531 : Blo 1776089 6403531 := bstep (se 1 (by rfl) ⟨4802648, by rfl⟩ : syracuseStep 6403531 = 9605297) B9605297
theorem B24327641 : Blo 1776089 24327641 := bstep (se 2 (by rfl) ⟨9122865, by rfl⟩ : syracuseStep 24327641 = 18245731) B18245731
theorem B15177233 : Blo 1776089 15177233 := bstep (se 2 (by rfl) ⟨5691462, by rfl⟩ : syracuseStep 15177233 = 11382925) B11382925
theorem B30783011 : Blo 1776089 30783011 := bstep (se 1 (by rfl) ⟨23087258, by rfl⟩ : syracuseStep 30783011 = 46174517) B46174517
theorem B1898039 : Blo 1776089 1898039 := bstep (se 1 (by rfl) ⟨1423529, by rfl⟩ : syracuseStep 1898039 = 2847059) B2847059
theorem B5060171 : Blo 1776089 5060171 := bstep (se 1 (by rfl) ⟨3795128, by rfl⟩ : syracuseStep 5060171 = 7590257) B7590257
theorem B3372673 : Blo 1776089 3372673 := bstep (se 2 (by rfl) ⟨1264752, by rfl⟩ : syracuseStep 3372673 = 2529505) B2529505
theorem B62404337 : Blo 1776089 62404337 := bstep (se 2 (by rfl) ⟨23401626, by rfl⟩ : syracuseStep 62404337 = 46803253) B46803253
theorem B43226945 : Blo 1776089 43226945 := bstep (se 2 (by rfl) ⟨16210104, by rfl⟩ : syracuseStep 43226945 = 32420209) B32420209
theorem B4052801 : Blo 1776089 4052801 := bstep (se 2 (by rfl) ⟨1519800, by rfl⟩ : syracuseStep 4052801 = 3039601) B3039601
theorem B7591745 : Blo 1776089 7591745 := bstep (se 2 (by rfl) ⟨2846904, by rfl⟩ : syracuseStep 7591745 = 5693809) B5693809
theorem B3200843 : Blo 1776089 3200843 := bstep (se 1 (by rfl) ⟨2400632, by rfl⟩ : syracuseStep 3200843 = 4801265) B4801265
theorem B6748049 : Blo 1776089 6748049 := bstep (se 2 (by rfl) ⟨2530518, by rfl⟩ : syracuseStep 6748049 = 5061037) B5061037
theorem B4052929 : Blo 1776089 4052929 := bstep (se 2 (by rfl) ⟨1519848, by rfl⟩ : syracuseStep 4052929 = 3039697) B3039697
theorem B3373015 : Blo 1776089 3373015 := bstep (se 1 (by rfl) ⟨2529761, by rfl⟩ : syracuseStep 3373015 = 5059523) B5059523
theorem B7591897 : Blo 1776089 7591897 := bstep (se 2 (by rfl) ⟨2846961, by rfl⟩ : syracuseStep 7591897 = 5693923) B5693923
theorem B5994647 : Blo 1776089 5994647 := bstep (se 1 (by rfl) ⟨4495985, by rfl⟩ : syracuseStep 5994647 = 8991971) B8991971
theorem B3373235 : Blo 1776089 3373235 := bstep (se 1 (by rfl) ⟨2529926, by rfl⟩ : syracuseStep 3373235 = 5059853) B5059853
theorem B10950977 : Blo 1776089 10950977 := bstep (se 2 (by rfl) ⟨4106616, by rfl⟩ : syracuseStep 10950977 = 8213233) B8213233
theorem B2529625 : Blo 1776089 2529625 := bstep (se 2 (by rfl) ⟨948609, by rfl⟩ : syracuseStep 2529625 = 1897219) B1897219
theorem B6748505 : Blo 1776089 6748505 := bstep (se 2 (by rfl) ⟨2530689, by rfl⟩ : syracuseStep 6748505 = 5061379) B5061379
theorem B3373463 : Blo 1776089 3373463 := bstep (se 1 (by rfl) ⟨2530097, by rfl⟩ : syracuseStep 3373463 = 5060195) B5060195
theorem B9001367 : Blo 1776089 9001367 := bstep (se 1 (by rfl) ⟨6751025, by rfl⟩ : syracuseStep 9001367 = 13502051) B13502051
theorem B20232665 : Blo 1776089 20232665 := bstep (se 2 (by rfl) ⟨7587249, by rfl⟩ : syracuseStep 20232665 = 15174499) B15174499
theorem B1776107 : Blo 1776089 1776107 := bstep (se 1 (by rfl) ⟨1332080, by rfl⟩ : syracuseStep 1776107 = 2664161) B2664161
theorem B1776119 : Blo 1776089 1776119 := bstep (se 1 (by rfl) ⟨1332089, by rfl⟩ : syracuseStep 1776119 = 2664179) B2664179
theorem B1776139 : Blo 1776089 1776139 := bstep (se 1 (by rfl) ⟨1332104, by rfl⟩ : syracuseStep 1776139 = 2664209) B2664209
theorem B1776151 : Blo 1776089 1776151 := bstep (se 1 (by rfl) ⟨1332113, by rfl⟩ : syracuseStep 1776151 = 2664227) B2664227
theorem B4495895 : Blo 1776089 4495895 := bstep (se 1 (by rfl) ⟨3371921, by rfl⟩ : syracuseStep 4495895 = 6743843) B6743843
theorem B1776171 : Blo 1776089 1776171 := bstep (se 1 (by rfl) ⟨1332128, by rfl⟩ : syracuseStep 1776171 = 2664257) B2664257
theorem B6748717 : Blo 1776089 6748717 := bstep (se 3 (by rfl) ⟨1265384, by rfl⟩ : syracuseStep 6748717 = 2530769) B2530769
theorem B1776183 : Blo 1776089 1776183 := bstep (se 1 (by rfl) ⟨1332137, by rfl⟩ : syracuseStep 1776183 = 2664275) B2664275
theorem B1776203 : Blo 1776089 1776203 := bstep (se 1 (by rfl) ⟨1332152, by rfl⟩ : syracuseStep 1776203 = 2664305) B2664305
theorem B1776215 : Blo 1776089 1776215 := bstep (se 1 (by rfl) ⟨1332161, by rfl⟩ : syracuseStep 1776215 = 2664323) B2664323
theorem B1776235 : Blo 1776089 1776235 := bstep (se 1 (by rfl) ⟨1332176, by rfl⟩ : syracuseStep 1776235 = 2664353) B2664353
theorem B1776247 : Blo 1776089 1776247 := bstep (se 1 (by rfl) ⟨1332185, by rfl⟩ : syracuseStep 1776247 = 2664371) B2664371
theorem B1776267 : Blo 1776089 1776267 := bstep (se 1 (by rfl) ⟨1332200, by rfl⟩ : syracuseStep 1776267 = 2664401) B2664401
theorem B1776279 : Blo 1776089 1776279 := bstep (se 1 (by rfl) ⟨1332209, by rfl⟩ : syracuseStep 1776279 = 2664419) B2664419
theorem B3373721 : Blo 1776089 3373721 := bstep (se 2 (by rfl) ⟨1265145, by rfl⟩ : syracuseStep 3373721 = 2530291) B2530291
theorem B1776299 : Blo 1776089 1776299 := bstep (se 1 (by rfl) ⟨1332224, by rfl⟩ : syracuseStep 1776299 = 2664449) B2664449
theorem B5995187 : Blo 1776089 5995187 := bstep (se 1 (by rfl) ⟨4496390, by rfl⟩ : syracuseStep 5995187 = 8992781) B8992781
theorem B1776311 : Blo 1776089 1776311 := bstep (se 1 (by rfl) ⟨1332233, by rfl⟩ : syracuseStep 1776311 = 2664467) B2664467
theorem B1776331 : Blo 1776089 1776331 := bstep (se 1 (by rfl) ⟨1332248, by rfl⟩ : syracuseStep 1776331 = 2664497) B2664497
theorem B47422157 : Blo 1776089 47422157 := bstep (se 3 (by rfl) ⟨8891654, by rfl⟩ : syracuseStep 47422157 = 17783309) B17783309
theorem B1776343 : Blo 1776089 1776343 := bstep (se 1 (by rfl) ⟨1332257, by rfl⟩ : syracuseStep 1776343 = 2664515) B2664515
theorem B3996377 : Blo 1776089 3996377 := bstep (se 2 (by rfl) ⟨1498641, by rfl⟩ : syracuseStep 3996377 = 2997283) B2997283
theorem B3201751 : Blo 1776089 3201751 := bstep (se 1 (by rfl) ⟨2401313, by rfl⟩ : syracuseStep 3201751 = 4802627) B4802627
theorem B1776363 : Blo 1776089 1776363 := bstep (se 1 (by rfl) ⟨1332272, by rfl⟩ : syracuseStep 1776363 = 2664545) B2664545
theorem B1776375 : Blo 1776089 1776375 := bstep (se 1 (by rfl) ⟨1332281, by rfl⟩ : syracuseStep 1776375 = 2664563) B2664563
theorem B1776395 : Blo 1776089 1776395 := bstep (se 1 (by rfl) ⟨1332296, by rfl⟩ : syracuseStep 1776395 = 2664593) B2664593
theorem B1776407 : Blo 1776089 1776407 := bstep (se 1 (by rfl) ⟨1332305, by rfl⟩ : syracuseStep 1776407 = 2664611) B2664611
theorem B1776427 : Blo 1776089 1776427 := bstep (se 1 (by rfl) ⟨1332320, by rfl⟩ : syracuseStep 1776427 = 2664641) B2664641
theorem B3996467 : Blo 1776089 3996467 := bstep (se 1 (by rfl) ⟨2997350, by rfl⟩ : syracuseStep 3996467 = 5994701) B5994701
theorem B6404915 : Blo 1776089 6404915 := bstep (se 1 (by rfl) ⟨4803686, by rfl⟩ : syracuseStep 6404915 = 9607373) B9607373
theorem B1776439 : Blo 1776089 1776439 := bstep (se 1 (by rfl) ⟨1332329, by rfl⟩ : syracuseStep 1776439 = 2664659) B2664659
theorem B1776459 : Blo 1776089 1776459 := bstep (se 1 (by rfl) ⟨1332344, by rfl⟩ : syracuseStep 1776459 = 2664689) B2664689
theorem B3996503 : Blo 1776089 3996503 := bstep (se 1 (by rfl) ⟨2997377, by rfl⟩ : syracuseStep 3996503 = 5994755) B5994755
theorem B1776471 : Blo 1776089 1776471 := bstep (se 1 (by rfl) ⟨1332353, by rfl⟩ : syracuseStep 1776471 = 2664707) B2664707
theorem B6749021 : Blo 1776089 6749021 := bstep (se 3 (by rfl) ⟨1265441, by rfl⟩ : syracuseStep 6749021 = 2530883) B2530883
theorem B1776491 : Blo 1776089 1776491 := bstep (se 1 (by rfl) ⟨1332368, by rfl⟩ : syracuseStep 1776491 = 2664737) B2664737
theorem B1776503 : Blo 1776089 1776503 := bstep (se 1 (by rfl) ⟨1332377, by rfl⟩ : syracuseStep 1776503 = 2664755) B2664755
theorem B1776523 : Blo 1776089 1776523 := bstep (se 1 (by rfl) ⟨1332392, by rfl⟩ : syracuseStep 1776523 = 2664785) B2664785
theorem B1776535 : Blo 1776089 1776535 := bstep (se 1 (by rfl) ⟨1332401, by rfl⟩ : syracuseStep 1776535 = 2664803) B2664803
theorem B1776555 : Blo 1776089 1776555 := bstep (se 1 (by rfl) ⟨1332416, by rfl⟩ : syracuseStep 1776555 = 2664833) B2664833
theorem B1776567 : Blo 1776089 1776567 := bstep (se 1 (by rfl) ⟨1332425, by rfl⟩ : syracuseStep 1776567 = 2664851) B2664851
theorem B5995457 : Blo 1776089 5995457 := bstep (se 2 (by rfl) ⟨2248296, by rfl⟩ : syracuseStep 5995457 = 4496593) B4496593
theorem B1776587 : Blo 1776089 1776587 := bstep (se 1 (by rfl) ⟨1332440, by rfl⟩ : syracuseStep 1776587 = 2664881) B2664881
theorem B1776599 : Blo 1776089 1776599 := bstep (se 1 (by rfl) ⟨1332449, by rfl⟩ : syracuseStep 1776599 = 2664899) B2664899
theorem B2997209 : Blo 1776089 2997209 := bstep (se 2 (by rfl) ⟨1123953, by rfl⟩ : syracuseStep 2997209 = 2247907) B2247907
theorem B8993753 : Blo 1776089 8993753 := bstep (se 2 (by rfl) ⟨3372657, by rfl⟩ : syracuseStep 8993753 = 6745315) B6745315
theorem B1776619 : Blo 1776089 1776619 := bstep (se 1 (by rfl) ⟨1332464, by rfl⟩ : syracuseStep 1776619 = 2664929) B2664929
theorem B1776631 : Blo 1776089 1776631 := bstep (se 1 (by rfl) ⟨1332473, by rfl⟩ : syracuseStep 1776631 = 2664947) B2664947
theorem B3996683 : Blo 1776089 3996683 := bstep (se 1 (by rfl) ⟨2997512, by rfl⟩ : syracuseStep 3996683 = 5995025) B5995025
theorem B1776651 : Blo 1776089 1776651 := bstep (se 1 (by rfl) ⟨1332488, by rfl⟩ : syracuseStep 1776651 = 2664977) B2664977
theorem B1776663 : Blo 1776089 1776663 := bstep (se 1 (by rfl) ⟨1332497, by rfl⟩ : syracuseStep 1776663 = 2664995) B2664995
theorem B1776683 : Blo 1776089 1776683 := bstep (se 1 (by rfl) ⟨1332512, by rfl⟩ : syracuseStep 1776683 = 2665025) B2665025
theorem B3374131 : Blo 1776089 3374131 := bstep (se 1 (by rfl) ⟨2530598, by rfl⟩ : syracuseStep 3374131 = 5061197) B5061197
theorem B1776695 : Blo 1776089 1776695 := bstep (se 1 (by rfl) ⟨1332521, by rfl⟩ : syracuseStep 1776695 = 2665043) B2665043
theorem B3996737 : Blo 1776089 3996737 := bstep (se 2 (by rfl) ⟨1498776, by rfl⟩ : syracuseStep 3996737 = 2997553) B2997553
theorem B1776715 : Blo 1776089 1776715 := bstep (se 1 (by rfl) ⟨1332536, by rfl⟩ : syracuseStep 1776715 = 2665073) B2665073
theorem B1776727 : Blo 1776089 1776727 := bstep (se 1 (by rfl) ⟨1332545, by rfl⟩ : syracuseStep 1776727 = 2665091) B2665091
theorem B2997337 : Blo 1776089 2997337 := bstep (se 2 (by rfl) ⟨1124001, by rfl⟩ : syracuseStep 2997337 = 2248003) B2248003
theorem B10116197 : Blo 1776089 10116197 := bstep (se 4 (by rfl) ⟨948393, by rfl⟩ : syracuseStep 10116197 = 1896787) B1896787
theorem B1776747 : Blo 1776089 1776747 := bstep (se 1 (by rfl) ⟨1332560, by rfl⟩ : syracuseStep 1776747 = 2665121) B2665121
theorem B1776759 : Blo 1776089 1776759 := bstep (se 1 (by rfl) ⟨1332569, by rfl⟩ : syracuseStep 1776759 = 2665139) B2665139
theorem B9608323 : Blo 1776089 9608323 := bstep (se 1 (by rfl) ⟨7206242, by rfl⟩ : syracuseStep 9608323 = 14412485) B14412485
theorem B1776779 : Blo 1776089 1776779 := bstep (se 1 (by rfl) ⟨1332584, by rfl⟩ : syracuseStep 1776779 = 2665169) B2665169
theorem B1776791 : Blo 1776089 1776791 := bstep (se 1 (by rfl) ⟨1332593, by rfl⟩ : syracuseStep 1776791 = 2665187) B2665187
theorem B1924247 : Blo 1776089 1924247 := bstep (se 1 (by rfl) ⟨1443185, by rfl⟩ : syracuseStep 1924247 = 2886371) B2886371
theorem B1776811 : Blo 1776089 1776811 := bstep (se 1 (by rfl) ⟨1332608, by rfl⟩ : syracuseStep 1776811 = 2665217) B2665217
theorem B1776823 : Blo 1776089 1776823 := bstep (se 1 (by rfl) ⟨1332617, by rfl⟩ : syracuseStep 1776823 = 2665235) B2665235
theorem B1776843 : Blo 1776089 1776843 := bstep (se 1 (by rfl) ⟨1332632, by rfl⟩ : syracuseStep 1776843 = 2665265) B2665265
theorem B1776855 : Blo 1776089 1776855 := bstep (se 1 (by rfl) ⟨1332641, by rfl⟩ : syracuseStep 1776855 = 2665283) B2665283
theorem B1776875 : Blo 1776089 1776875 := bstep (se 1 (by rfl) ⟨1332656, by rfl⟩ : syracuseStep 1776875 = 2665313) B2665313
theorem B1776887 : Blo 1776089 1776887 := bstep (se 1 (by rfl) ⟨1332665, by rfl⟩ : syracuseStep 1776887 = 2665331) B2665331
theorem B1776907 : Blo 1776089 1776907 := bstep (se 1 (by rfl) ⟨1332680, by rfl⟩ : syracuseStep 1776907 = 2665361) B2665361
theorem B1998103 : Blo 1776089 1998103 := bstep (se 1 (by rfl) ⟨1498577, by rfl⟩ : syracuseStep 1998103 = 2997155) B2997155
theorem B3996953 : Blo 1776089 3996953 := bstep (se 2 (by rfl) ⟨1498857, by rfl⟩ : syracuseStep 3996953 = 2997715) B2997715
theorem B1776919 : Blo 1776089 1776919 := bstep (se 1 (by rfl) ⟨1332689, by rfl⟩ : syracuseStep 1776919 = 2665379) B2665379
theorem B1776939 : Blo 1776089 1776939 := bstep (se 1 (by rfl) ⟨1332704, by rfl⟩ : syracuseStep 1776939 = 2665409) B2665409
theorem B1776951 : Blo 1776089 1776951 := bstep (se 1 (by rfl) ⟨1332713, by rfl⟩ : syracuseStep 1776951 = 2665427) B2665427
theorem B4496705 : Blo 1776089 4496705 := bstep (se 2 (by rfl) ⟨1686264, by rfl⟩ : syracuseStep 4496705 = 3372529) B3372529
theorem B1776971 : Blo 1776089 1776971 := bstep (se 1 (by rfl) ⟨1332728, by rfl⟩ : syracuseStep 1776971 = 2665457) B2665457
theorem B1776983 : Blo 1776089 1776983 := bstep (se 1 (by rfl) ⟨1332737, by rfl⟩ : syracuseStep 1776983 = 2665475) B2665475
theorem B1777003 : Blo 1776089 1777003 := bstep (se 1 (by rfl) ⟨1332752, by rfl⟩ : syracuseStep 1777003 = 2665505) B2665505
theorem B3997043 : Blo 1776089 3997043 := bstep (se 1 (by rfl) ⟨2997782, by rfl⟩ : syracuseStep 3997043 = 5995565) B5995565
theorem B1777015 : Blo 1776089 1777015 := bstep (se 1 (by rfl) ⟨1332761, by rfl⟩ : syracuseStep 1777015 = 2665523) B2665523
theorem B1777035 : Blo 1776089 1777035 := bstep (se 1 (by rfl) ⟨1332776, by rfl⟩ : syracuseStep 1777035 = 2665553) B2665553
theorem B3997079 : Blo 1776089 3997079 := bstep (se 1 (by rfl) ⟨2997809, by rfl⟩ : syracuseStep 3997079 = 5995619) B5995619
theorem B1777047 : Blo 1776089 1777047 := bstep (se 1 (by rfl) ⟨1332785, by rfl⟩ : syracuseStep 1777047 = 2665571) B2665571
theorem B1777067 : Blo 1776089 1777067 := bstep (se 1 (by rfl) ⟨1332800, by rfl⟩ : syracuseStep 1777067 = 2665601) B2665601
theorem B25623985 : Blo 1776089 25623985 := bstep (se 2 (by rfl) ⟨9608994, by rfl⟩ : syracuseStep 25623985 = 19217989) B19217989
theorem B17087921 : Blo 1776089 17087921 := bstep (se 2 (by rfl) ⟨6407970, by rfl⟩ : syracuseStep 17087921 = 12815941) B12815941
theorem B1777079 : Blo 1776089 1777079 := bstep (se 1 (by rfl) ⟨1332809, by rfl⟩ : syracuseStep 1777079 = 2665619) B2665619
theorem B1998283 : Blo 1776089 1998283 := bstep (se 1 (by rfl) ⟨1498712, by rfl⟩ : syracuseStep 1998283 = 2997425) B2997425
theorem B1777099 : Blo 1776089 1777099 := bstep (se 1 (by rfl) ⟨1332824, by rfl⟩ : syracuseStep 1777099 = 2665649) B2665649
theorem B1777111 : Blo 1776089 1777111 := bstep (se 1 (by rfl) ⟨1332833, by rfl⟩ : syracuseStep 1777111 = 2665667) B2665667
theorem B5995997 : Blo 1776089 5995997 := bstep (se 3 (by rfl) ⟨1124249, by rfl⟩ : syracuseStep 5995997 = 2248499) B2248499
theorem B1777131 : Blo 1776089 1777131 := bstep (se 1 (by rfl) ⟨1332848, by rfl⟩ : syracuseStep 1777131 = 2665697) B2665697
theorem B1777143 : Blo 1776089 1777143 := bstep (se 1 (by rfl) ⟨1332857, by rfl⟩ : syracuseStep 1777143 = 2665715) B2665715
theorem B1777163 : Blo 1776089 1777163 := bstep (se 1 (by rfl) ⟨1332872, by rfl⟩ : syracuseStep 1777163 = 2665745) B2665745
theorem B1777175 : Blo 1776089 1777175 := bstep (se 1 (by rfl) ⟨1332881, by rfl⟩ : syracuseStep 1777175 = 2665763) B2665763
theorem B3374617 : Blo 1776089 3374617 := bstep (se 2 (by rfl) ⟨1265481, by rfl⟩ : syracuseStep 3374617 = 2530963) B2530963
theorem B1777195 : Blo 1776089 1777195 := bstep (se 1 (by rfl) ⟨1332896, by rfl⟩ : syracuseStep 1777195 = 2665793) B2665793
theorem B8543789 : Blo 1776089 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B1998391 : Blo 1776089 1998391 := bstep (se 1 (by rfl) ⟨1498793, by rfl⟩ : syracuseStep 1998391 = 2997587) B2997587
theorem B1777207 : Blo 1776089 1777207 := bstep (se 1 (by rfl) ⟨1332905, by rfl⟩ : syracuseStep 1777207 = 2665811) B2665811
theorem B3997259 : Blo 1776089 3997259 := bstep (se 1 (by rfl) ⟨2997944, by rfl⟩ : syracuseStep 3997259 = 5995889) B5995889
theorem B1777227 : Blo 1776089 1777227 := bstep (se 1 (by rfl) ⟨1332920, by rfl⟩ : syracuseStep 1777227 = 2665841) B2665841
theorem B14614091 : Blo 1776089 14614091 := bstep (se 1 (by rfl) ⟨10960568, by rfl⟩ : syracuseStep 14614091 = 21921137) B21921137
theorem B1777239 : Blo 1776089 1777239 := bstep (se 1 (by rfl) ⟨1332929, by rfl⟩ : syracuseStep 1777239 = 2665859) B2665859
theorem B1777259 : Blo 1776089 1777259 := bstep (se 1 (by rfl) ⟨1332944, by rfl⟩ : syracuseStep 1777259 = 2665889) B2665889
theorem B1777271 : Blo 1776089 1777271 := bstep (se 1 (by rfl) ⟨1332953, by rfl⟩ : syracuseStep 1777271 = 2665907) B2665907
theorem B3997313 : Blo 1776089 3997313 := bstep (se 2 (by rfl) ⟨1498992, by rfl⟩ : syracuseStep 3997313 = 2997985) B2997985
theorem B1777291 : Blo 1776089 1777291 := bstep (se 1 (by rfl) ⟨1332968, by rfl⟩ : syracuseStep 1777291 = 2665937) B2665937
theorem B2997911 : Blo 1776089 2997911 := bstep (se 1 (by rfl) ⟨2248433, by rfl⟩ : syracuseStep 2997911 = 4496867) B4496867
theorem B1777303 : Blo 1776089 1777303 := bstep (se 1 (by rfl) ⟨1332977, by rfl⟩ : syracuseStep 1777303 = 2665955) B2665955
theorem B1777323 : Blo 1776089 1777323 := bstep (se 1 (by rfl) ⟨1332992, by rfl⟩ : syracuseStep 1777323 = 2665985) B2665985
theorem B1777335 : Blo 1776089 1777335 := bstep (se 1 (by rfl) ⟨1333001, by rfl⟩ : syracuseStep 1777335 = 2666003) B2666003
theorem B1777355 : Blo 1776089 1777355 := bstep (se 1 (by rfl) ⟨1333016, by rfl⟩ : syracuseStep 1777355 = 2666033) B2666033
theorem B1777367 : Blo 1776089 1777367 := bstep (se 1 (by rfl) ⟨1333025, by rfl⟩ : syracuseStep 1777367 = 2666051) B2666051
theorem B1998571 : Blo 1776089 1998571 := bstep (se 1 (by rfl) ⟨1498928, by rfl⟩ : syracuseStep 1998571 = 2997857) B2997857
theorem B1777387 : Blo 1776089 1777387 := bstep (se 1 (by rfl) ⟨1333040, by rfl⟩ : syracuseStep 1777387 = 2666081) B2666081
theorem B1777399 : Blo 1776089 1777399 := bstep (se 1 (by rfl) ⟨1333049, by rfl⟩ : syracuseStep 1777399 = 2666099) B2666099
theorem B1777419 : Blo 1776089 1777419 := bstep (se 1 (by rfl) ⟨1333064, by rfl⟩ : syracuseStep 1777419 = 2666129) B2666129
theorem B2531083 : Blo 1776089 2531083 := bstep (se 1 (by rfl) ⟨1898312, by rfl⟩ : syracuseStep 2531083 = 3796625) B3796625
theorem B2998039 : Blo 1776089 2998039 := bstep (se 1 (by rfl) ⟨2248529, by rfl⟩ : syracuseStep 2998039 = 4497059) B4497059
theorem B1777431 : Blo 1776089 1777431 := bstep (se 1 (by rfl) ⟨1333073, by rfl⟩ : syracuseStep 1777431 = 2666147) B2666147
theorem B1777451 : Blo 1776089 1777451 := bstep (se 1 (by rfl) ⟨1333088, by rfl⟩ : syracuseStep 1777451 = 2666177) B2666177
theorem B1777463 : Blo 1776089 1777463 := bstep (se 1 (by rfl) ⟨1333097, by rfl⟩ : syracuseStep 1777463 = 2666195) B2666195
theorem B1777483 : Blo 1776089 1777483 := bstep (se 1 (by rfl) ⟨1333112, by rfl⟩ : syracuseStep 1777483 = 2666225) B2666225
theorem B1998679 : Blo 1776089 1998679 := bstep (se 1 (by rfl) ⟨1499009, by rfl⟩ : syracuseStep 1998679 = 2998019) B2998019
theorem B3997529 : Blo 1776089 3997529 := bstep (se 2 (by rfl) ⟨1499073, by rfl⟩ : syracuseStep 3997529 = 2998147) B2998147
theorem B4497241 : Blo 1776089 4497241 := bstep (se 2 (by rfl) ⟨1686465, by rfl⟩ : syracuseStep 4497241 = 3372931) B3372931
theorem B1777495 : Blo 1776089 1777495 := bstep (se 1 (by rfl) ⟨1333121, by rfl⟩ : syracuseStep 1777495 = 2666243) B2666243
theorem B92348261 : Blo 1776089 92348261 := bstep (se 4 (by rfl) ⟨8657649, by rfl⟩ : syracuseStep 92348261 = 17315299) B17315299
theorem B1777515 : Blo 1776089 1777515 := bstep (se 1 (by rfl) ⟨1333136, by rfl⟩ : syracuseStep 1777515 = 2666273) B2666273
theorem B1777527 : Blo 1776089 1777527 := bstep (se 1 (by rfl) ⟨1333145, by rfl⟩ : syracuseStep 1777527 = 2666291) B2666291
theorem B1777547 : Blo 1776089 1777547 := bstep (se 1 (by rfl) ⟨1333160, by rfl⟩ : syracuseStep 1777547 = 2666321) B2666321
theorem B1777559 : Blo 1776089 1777559 := bstep (se 1 (by rfl) ⟨1333169, by rfl⟩ : syracuseStep 1777559 = 2666339) B2666339
theorem B1777579 : Blo 1776089 1777579 := bstep (se 1 (by rfl) ⟨1333184, by rfl⟩ : syracuseStep 1777579 = 2666369) B2666369
theorem B3997619 : Blo 1776089 3997619 := bstep (se 1 (by rfl) ⟨2998214, by rfl⟩ : syracuseStep 3997619 = 5996429) B5996429
theorem B1777591 : Blo 1776089 1777591 := bstep (se 1 (by rfl) ⟨1333193, by rfl⟩ : syracuseStep 1777591 = 2666387) B2666387
theorem B1777611 : Blo 1776089 1777611 := bstep (se 1 (by rfl) ⟨1333208, by rfl⟩ : syracuseStep 1777611 = 2666417) B2666417
theorem B3997655 : Blo 1776089 3997655 := bstep (se 1 (by rfl) ⟨2998241, by rfl⟩ : syracuseStep 3997655 = 5996483) B5996483
theorem B1777623 : Blo 1776089 1777623 := bstep (se 1 (by rfl) ⟨1333217, by rfl⟩ : syracuseStep 1777623 = 2666435) B2666435
theorem B5062621 : Blo 1776089 5062621 := bstep (se 3 (by rfl) ⟨949241, by rfl⟩ : syracuseStep 5062621 = 1898483) B1898483
theorem B1777643 : Blo 1776089 1777643 := bstep (se 1 (by rfl) ⟨1333232, by rfl⟩ : syracuseStep 1777643 = 2666465) B2666465
theorem B1777655 : Blo 1776089 1777655 := bstep (se 1 (by rfl) ⟨1333241, by rfl⟩ : syracuseStep 1777655 = 2666483) B2666483
theorem B1777671 : Blo 1776089 1777671 := bstep (se 1 (by rfl) ⟨1333253, by rfl⟩ : syracuseStep 1777671 = 2666507) B2666507
theorem B1777679 : Blo 1776089 1777679 := bstep (se 1 (by rfl) ⟨1333259, by rfl⟩ : syracuseStep 1777679 = 2666519) B2666519
theorem B1777723 : Blo 1776089 1777723 := bstep (se 1 (by rfl) ⟨1333292, by rfl⟩ : syracuseStep 1777723 = 2666585) B2666585
theorem B1777799 : Blo 1776089 1777799 := bstep (se 1 (by rfl) ⟨1333349, by rfl⟩ : syracuseStep 1777799 = 2666699) B2666699
theorem B1777807 : Blo 1776089 1777807 := bstep (se 1 (by rfl) ⟨1333355, by rfl⟩ : syracuseStep 1777807 = 2666711) B2666711
theorem B1777851 : Blo 1776089 1777851 := bstep (se 1 (by rfl) ⟨1333388, by rfl⟩ : syracuseStep 1777851 = 2666777) B2666777
theorem B1999111 : Blo 1776089 1999111 := bstep (se 1 (by rfl) ⟨1499333, by rfl⟩ : syracuseStep 1999111 = 2998667) B2998667
theorem B1777927 : Blo 1776089 1777927 := bstep (se 1 (by rfl) ⟨1333445, by rfl⟩ : syracuseStep 1777927 = 2666891) B2666891
theorem B6750479 : Blo 1776089 6750479 := bstep (se 1 (by rfl) ⟨5062859, by rfl⟩ : syracuseStep 6750479 = 10125719) B10125719
theorem B1777935 : Blo 1776089 1777935 := bstep (se 1 (by rfl) ⟨1333451, by rfl⟩ : syracuseStep 1777935 = 2666903) B2666903
theorem B4497707 : Blo 1776089 4497707 := bstep (se 1 (by rfl) ⟨3373280, by rfl⟩ : syracuseStep 4497707 = 6746561) B6746561
theorem B5407019 : Blo 1776089 5407019 := bstep (se 1 (by rfl) ⟨4055264, by rfl⟩ : syracuseStep 5407019 = 8110529) B8110529
theorem B1777979 : Blo 1776089 1777979 := bstep (se 1 (by rfl) ⟨1333484, by rfl⟩ : syracuseStep 1777979 = 2666969) B2666969
theorem B5996915 : Blo 1776089 5996915 := bstep (se 1 (by rfl) ⟨4497686, by rfl⟩ : syracuseStep 5996915 = 8995373) B8995373
theorem B3998087 : Blo 1776089 3998087 := bstep (se 1 (by rfl) ⟨2998565, by rfl⟩ : syracuseStep 3998087 = 5997131) B5997131
theorem B1778055 : Blo 1776089 1778055 := bstep (se 1 (by rfl) ⟨1333541, by rfl⟩ : syracuseStep 1778055 = 2667083) B2667083
theorem B1778063 : Blo 1776089 1778063 := bstep (se 1 (by rfl) ⟨1333547, by rfl⟩ : syracuseStep 1778063 = 2667095) B2667095
theorem B1999291 : Blo 1776089 1999291 := bstep (se 1 (by rfl) ⟨1499468, by rfl⟩ : syracuseStep 1999291 = 2998937) B2998937
theorem B3080719 : Blo 1776089 3080719 := bstep (se 1 (by rfl) ⟨2310539, by rfl⟩ : syracuseStep 3080719 = 4621079) B4621079
theorem B10117655 : Blo 1776089 10117655 := bstep (se 1 (by rfl) ⟨7588241, by rfl⟩ : syracuseStep 10117655 = 15176483) B15176483
theorem B3998267 : Blo 1776089 3998267 := bstep (se 1 (by rfl) ⟨2998700, by rfl⟩ : syracuseStep 3998267 = 5997401) B5997401
theorem B6840919 : Blo 1776089 6840919 := bstep (se 1 (by rfl) ⟨5130689, by rfl⟩ : syracuseStep 6840919 = 10261379) B10261379
theorem B2998903 : Blo 1776089 2998903 := bstep (se 1 (by rfl) ⟨2249177, by rfl⟩ : syracuseStep 2998903 = 4498355) B4498355
theorem B3998393 : Blo 1776089 3998393 := bstep (se 2 (by rfl) ⟨1499397, by rfl⟩ : syracuseStep 3998393 = 2998795) B2998795
theorem B2999099 : Blo 1776089 2999099 := bstep (se 1 (by rfl) ⟨2249324, by rfl⟩ : syracuseStep 2999099 = 4498649) B4498649
theorem B1999759 : Blo 1776089 1999759 := bstep (se 1 (by rfl) ⟨1499819, by rfl⟩ : syracuseStep 1999759 = 2999639) B2999639
theorem B2401211 : Blo 1776089 2401211 := bstep (se 1 (by rfl) ⟨1800908, by rfl⟩ : syracuseStep 2401211 = 3601817) B3601817
theorem B4801481 : Blo 1776089 4801481 := bstep (se 2 (by rfl) ⟨1800555, by rfl⟩ : syracuseStep 4801481 = 3601111) B3601111
theorem B10118155 : Blo 1776089 10118155 := bstep (se 1 (by rfl) ⟨7588616, by rfl⟩ : syracuseStep 10118155 = 15177233) B15177233
theorem B3998735 : Blo 1776089 3998735 := bstep (se 1 (by rfl) ⟨2999051, by rfl⟩ : syracuseStep 3998735 = 5998103) B5998103
theorem B10806301 : Blo 1776089 10806301 := bstep (se 3 (by rfl) ⟨2026181, by rfl⟩ : syracuseStep 10806301 = 4052363) B4052363
theorem B3998753 : Blo 1776089 3998753 := bstep (se 2 (by rfl) ⟨1499532, by rfl⟩ : syracuseStep 3998753 = 2999065) B2999065
theorem B10126403 : Blo 1776089 10126403 := bstep (se 1 (by rfl) ⟨7594802, by rfl⟩ : syracuseStep 10126403 = 15189605) B15189605
theorem B22774871 : Blo 1776089 22774871 := bstep (se 1 (by rfl) ⟨17081153, by rfl⟩ : syracuseStep 22774871 = 34162307) B34162307
theorem B2999497 : Blo 1776089 2999497 := bstep (se 2 (by rfl) ⟨1124811, by rfl⟩ : syracuseStep 2999497 = 2249623) B2249623
theorem B4498699 : Blo 1776089 4498699 := bstep (se 1 (by rfl) ⟨3374024, by rfl⟩ : syracuseStep 4498699 = 6748049) B6748049
theorem B3999095 : Blo 1776089 3999095 := bstep (se 1 (by rfl) ⟨2999321, by rfl⟩ : syracuseStep 3999095 = 5998643) B5998643
theorem B2000263 : Blo 1776089 2000263 := bstep (se 1 (by rfl) ⟨1500197, by rfl⟩ : syracuseStep 2000263 = 3000395) B3000395
theorem B4498841 : Blo 1776089 4498841 := bstep (se 2 (by rfl) ⟨1687065, by rfl⟩ : syracuseStep 4498841 = 3374131) B3374131
theorem B3794377 : Blo 1776089 3794377 := bstep (se 2 (by rfl) ⟨1422891, by rfl⟩ : syracuseStep 3794377 = 2845783) B2845783
theorem B6489553 : Blo 1776089 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B13493789 : Blo 1776089 13493789 := bstep (se 3 (by rfl) ⟨2530085, by rfl⟩ : syracuseStep 13493789 = 5060171) B5060171
theorem B7587371 : Blo 1776089 7587371 := bstep (se 1 (by rfl) ⟨5690528, by rfl⟩ : syracuseStep 7587371 = 11381057) B11381057
theorem B7300651 : Blo 1776089 7300651 := bstep (se 1 (by rfl) ⟨5475488, by rfl⟩ : syracuseStep 7300651 = 10950977) B10950977
theorem B3999275 : Blo 1776089 3999275 := bstep (se 1 (by rfl) ⟨2999456, by rfl⟩ : syracuseStep 3999275 = 5998913) B5998913
theorem B4499003 : Blo 1776089 4499003 := bstep (se 1 (by rfl) ⟨3374252, by rfl⟩ : syracuseStep 4499003 = 6748505) B6748505
theorem B21612109 : Blo 1776089 21612109 := bstep (se 3 (by rfl) ⟨4052270, by rfl⟩ : syracuseStep 21612109 = 8104541) B8104541
theorem B2664137 : Blo 1776089 2664137 := bstep (se 2 (by rfl) ⟨999051, by rfl⟩ : syracuseStep 2664137 = 1998103) B1998103
theorem B2664251 : Blo 1776089 2664251 := bstep (se 1 (by rfl) ⟨1998188, by rfl⟩ : syracuseStep 2664251 = 3996377) B3996377
theorem B2664311 : Blo 1776089 2664311 := bstep (se 1 (by rfl) ⟨1998233, by rfl⟩ : syracuseStep 2664311 = 3996467) B3996467
theorem B4269943 : Blo 1776089 4269943 := bstep (se 1 (by rfl) ⟨3202457, by rfl⟩ : syracuseStep 4269943 = 6404915) B6404915
theorem B3000199 : Blo 1776089 3000199 := bstep (se 1 (by rfl) ⟨2250149, by rfl⟩ : syracuseStep 3000199 = 4500299) B4500299
theorem B2664335 : Blo 1776089 2664335 := bstep (se 1 (by rfl) ⟨1998251, by rfl⟩ : syracuseStep 2664335 = 3996503) B3996503
theorem B4499347 : Blo 1776089 4499347 := bstep (se 1 (by rfl) ⟨3374510, by rfl⟩ : syracuseStep 4499347 = 6749021) B6749021
theorem B3999635 : Blo 1776089 3999635 := bstep (se 1 (by rfl) ⟨2999726, by rfl⟩ : syracuseStep 3999635 = 5999453) B5999453
theorem B2664377 : Blo 1776089 2664377 := bstep (se 2 (by rfl) ⟨999141, by rfl⟩ : syracuseStep 2664377 = 1998283) B1998283
theorem B8538041 : Blo 1776089 8538041 := bstep (se 2 (by rfl) ⟨3201765, by rfl⟩ : syracuseStep 8538041 = 6403531) B6403531
theorem B3999689 : Blo 1776089 3999689 := bstep (se 2 (by rfl) ⟨1499883, by rfl⟩ : syracuseStep 3999689 = 2999767) B2999767
theorem B2664455 : Blo 1776089 2664455 := bstep (se 1 (by rfl) ⟨1998341, by rfl⟩ : syracuseStep 2664455 = 3996683) B3996683
theorem B4499489 : Blo 1776089 4499489 := bstep (se 2 (by rfl) ⟨1687308, by rfl⟩ : syracuseStep 4499489 = 3374617) B3374617
theorem B2664491 : Blo 1776089 2664491 := bstep (se 1 (by rfl) ⟨1998368, by rfl⟩ : syracuseStep 2664491 = 3996737) B3996737
theorem B6744131 : Blo 1776089 6744131 := bstep (se 1 (by rfl) ⟨5058098, by rfl⟩ : syracuseStep 6744131 = 10116197) B10116197
theorem B2664521 : Blo 1776089 2664521 := bstep (se 2 (by rfl) ⟨999195, by rfl⟩ : syracuseStep 2664521 = 1998391) B1998391
theorem B2664635 : Blo 1776089 2664635 := bstep (se 1 (by rfl) ⟨1998476, by rfl⟩ : syracuseStep 2664635 = 3996953) B3996953
theorem B2664695 : Blo 1776089 2664695 := bstep (se 1 (by rfl) ⟨1998521, by rfl⟩ : syracuseStep 2664695 = 3997043) B3997043
theorem B2664719 : Blo 1776089 2664719 := bstep (se 1 (by rfl) ⟨1998539, by rfl⟩ : syracuseStep 2664719 = 3997079) B3997079
theorem B11536673 : Blo 1776089 11536673 := bstep (se 2 (by rfl) ⟨4326252, by rfl⟩ : syracuseStep 11536673 = 8652505) B8652505
theorem B2664761 : Blo 1776089 2664761 := bstep (se 2 (by rfl) ⟨999285, by rfl⟩ : syracuseStep 2664761 = 1998571) B1998571
theorem B5695859 : Blo 1776089 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B2664839 : Blo 1776089 2664839 := bstep (se 1 (by rfl) ⟨1998629, by rfl⟩ : syracuseStep 2664839 = 3997259) B3997259
theorem B9742727 : Blo 1776089 9742727 := bstep (se 1 (by rfl) ⟨7307045, by rfl⟩ : syracuseStep 9742727 = 14614091) B14614091
theorem B5400985 : Blo 1776089 5400985 := bstep (se 2 (by rfl) ⟨2025369, by rfl⟩ : syracuseStep 5400985 = 4050739) B4050739
theorem B9603481 : Blo 1776089 9603481 := bstep (se 2 (by rfl) ⟨3601305, by rfl⟩ : syracuseStep 9603481 = 7202611) B7202611
theorem B2664875 : Blo 1776089 2664875 := bstep (se 1 (by rfl) ⟨1998656, by rfl⟩ : syracuseStep 2664875 = 3997313) B3997313
theorem B2664905 : Blo 1776089 2664905 := bstep (se 2 (by rfl) ⟨999339, by rfl⟩ : syracuseStep 2664905 = 1998679) B1998679
theorem B2665019 : Blo 1776089 2665019 := bstep (se 1 (by rfl) ⟨1998764, by rfl⟩ : syracuseStep 2665019 = 3997529) B3997529
theorem B61565507 : Blo 1776089 61565507 := bstep (se 1 (by rfl) ⟨46174130, by rfl⟩ : syracuseStep 61565507 = 92348261) B92348261
theorem B2665079 : Blo 1776089 2665079 := bstep (se 1 (by rfl) ⟨1998809, by rfl⟩ : syracuseStep 2665079 = 3997619) B3997619
theorem B4000391 : Blo 1776089 4000391 := bstep (se 1 (by rfl) ⟨3000293, by rfl⟩ : syracuseStep 4000391 = 6000587) B6000587
theorem B2665103 : Blo 1776089 2665103 := bstep (se 1 (by rfl) ⟨1998827, by rfl⟩ : syracuseStep 2665103 = 3997655) B3997655
theorem B4328083 : Blo 1776089 4328083 := bstep (se 1 (by rfl) ⟨3246062, by rfl⟩ : syracuseStep 4328083 = 6492125) B6492125
theorem B2665145 : Blo 1776089 2665145 := bstep (se 2 (by rfl) ⟨999429, by rfl⟩ : syracuseStep 2665145 = 1998859) B1998859
theorem B2665223 : Blo 1776089 2665223 := bstep (se 1 (by rfl) ⟨1998917, by rfl⟩ : syracuseStep 2665223 = 3997835) B3997835
theorem B2665259 : Blo 1776089 2665259 := bstep (se 1 (by rfl) ⟨1998944, by rfl⟩ : syracuseStep 2665259 = 3997889) B3997889
theorem B4000571 : Blo 1776089 4000571 := bstep (se 1 (by rfl) ⟨3000428, by rfl⟩ : syracuseStep 4000571 = 6000857) B6000857
theorem B2665289 : Blo 1776089 2665289 := bstep (se 2 (by rfl) ⟨999483, by rfl⟩ : syracuseStep 2665289 = 1998967) B1998967
theorem B11381593 : Blo 1776089 11381593 := bstep (se 2 (by rfl) ⟨4268097, by rfl⟩ : syracuseStep 11381593 = 8536195) B8536195
theorem B5999507 : Blo 1776089 5999507 := bstep (se 1 (by rfl) ⟨4499630, by rfl⟩ : syracuseStep 5999507 = 8999261) B8999261
theorem B13675427 : Blo 1776089 13675427 := bstep (se 1 (by rfl) ⟨10256570, by rfl⟩ : syracuseStep 13675427 = 20513141) B20513141
theorem B4000697 : Blo 1776089 4000697 := bstep (se 2 (by rfl) ⟨1500261, by rfl⟩ : syracuseStep 4000697 = 3000523) B3000523
theorem B2665403 : Blo 1776089 2665403 := bstep (se 1 (by rfl) ⟨1999052, by rfl⟩ : syracuseStep 2665403 = 3998105) B3998105
theorem B10120139 : Blo 1776089 10120139 := bstep (se 1 (by rfl) ⟨7590104, by rfl⟩ : syracuseStep 10120139 = 15180209) B15180209
theorem B2665463 : Blo 1776089 2665463 := bstep (se 1 (by rfl) ⟨1999097, by rfl⟩ : syracuseStep 2665463 = 3998195) B3998195
theorem B4500481 : Blo 1776089 4500481 := bstep (se 2 (by rfl) ⟨1687680, by rfl⟩ : syracuseStep 4500481 = 3375361) B3375361
theorem B2665487 : Blo 1776089 2665487 := bstep (se 1 (by rfl) ⟨1999115, by rfl⟩ : syracuseStep 2665487 = 3998231) B3998231
theorem B2665529 : Blo 1776089 2665529 := bstep (se 2 (by rfl) ⟨999573, by rfl⟩ : syracuseStep 2665529 = 1999147) B1999147
theorem B5131325 : Blo 1776089 5131325 := bstep (se 3 (by rfl) ⟨962123, by rfl⟩ : syracuseStep 5131325 = 1924247) B1924247
theorem B147950653 : Blo 1776089 147950653 := bstep (se 3 (by rfl) ⟨27740747, by rfl⟩ : syracuseStep 147950653 = 55481495) B55481495
theorem B2665607 : Blo 1776089 2665607 := bstep (se 1 (by rfl) ⟨1999205, by rfl⟩ : syracuseStep 2665607 = 3998411) B3998411
theorem B2665643 : Blo 1776089 2665643 := bstep (se 1 (by rfl) ⟨1999232, by rfl⟩ : syracuseStep 2665643 = 3998465) B3998465
theorem B2665673 : Blo 1776089 2665673 := bstep (se 2 (by rfl) ⟨999627, by rfl⟩ : syracuseStep 2665673 = 1999255) B1999255
theorem B2665787 : Blo 1776089 2665787 := bstep (se 1 (by rfl) ⟨1999340, by rfl⟩ : syracuseStep 2665787 = 3998681) B3998681
theorem B3796283 : Blo 1776089 3796283 := bstep (se 1 (by rfl) ⟨2847212, by rfl⟩ : syracuseStep 3796283 = 5694425) B5694425
theorem B62418275 : Blo 1776089 62418275 := bstep (se 1 (by rfl) ⟨46813706, by rfl⟩ : syracuseStep 62418275 = 93627413) B93627413
theorem B2665847 : Blo 1776089 2665847 := bstep (se 1 (by rfl) ⟨1999385, by rfl⟩ : syracuseStep 2665847 = 3998771) B3998771
theorem B2665871 : Blo 1776089 2665871 := bstep (se 1 (by rfl) ⟨1999403, by rfl⟩ : syracuseStep 2665871 = 3998807) B3998807
theorem B8998289 : Blo 1776089 8998289 := bstep (se 2 (by rfl) ⟨3374358, by rfl⟩ : syracuseStep 8998289 = 6748717) B6748717
theorem B5057939 : Blo 1776089 5057939 := bstep (se 1 (by rfl) ⟨3793454, by rfl⟩ : syracuseStep 5057939 = 7586909) B7586909
theorem B2665913 : Blo 1776089 2665913 := bstep (se 2 (by rfl) ⟨999717, by rfl⟩ : syracuseStep 2665913 = 1999435) B1999435
theorem B2665991 : Blo 1776089 2665991 := bstep (se 1 (by rfl) ⟨1999493, by rfl⟩ : syracuseStep 2665991 = 3998987) B3998987
theorem B2666027 : Blo 1776089 2666027 := bstep (se 1 (by rfl) ⟨1999520, by rfl⟩ : syracuseStep 2666027 = 3999041) B3999041
theorem B2666057 : Blo 1776089 2666057 := bstep (se 2 (by rfl) ⟨999771, by rfl⟩ : syracuseStep 2666057 = 1999543) B1999543
theorem B2248327 : Blo 1776089 2248327 := bstep (se 1 (by rfl) ⟨1686245, by rfl⟩ : syracuseStep 2248327 = 3372491) B3372491
theorem B2666171 : Blo 1776089 2666171 := bstep (se 1 (by rfl) ⟨1999628, by rfl⟩ : syracuseStep 2666171 = 3999257) B3999257
theorem B6745801 : Blo 1776089 6745801 := bstep (se 2 (by rfl) ⟨2529675, by rfl⟩ : syracuseStep 6745801 = 5059351) B5059351
theorem B38424293 : Blo 1776089 38424293 := bstep (se 4 (by rfl) ⟨3602277, by rfl⟩ : syracuseStep 38424293 = 7204555) B7204555
theorem B2666231 : Blo 1776089 2666231 := bstep (se 1 (by rfl) ⟨1999673, by rfl⟩ : syracuseStep 2666231 = 3999347) B3999347
theorem B2666255 : Blo 1776089 2666255 := bstep (se 1 (by rfl) ⟨1999691, by rfl⟩ : syracuseStep 2666255 = 3999383) B3999383
theorem B3796769 : Blo 1776089 3796769 := bstep (se 2 (by rfl) ⟨1423788, by rfl⟩ : syracuseStep 3796769 = 2847577) B2847577
theorem B17076005 : Blo 1776089 17076005 := bstep (se 4 (by rfl) ⟨1600875, by rfl⟩ : syracuseStep 17076005 = 3201751) B3201751
theorem B2666297 : Blo 1776089 2666297 := bstep (se 2 (by rfl) ⟨999861, by rfl⟩ : syracuseStep 2666297 = 1999723) B1999723
theorem B41602891 : Blo 1776089 41602891 := bstep (se 1 (by rfl) ⟨31202168, by rfl⟩ : syracuseStep 41602891 = 62404337) B62404337
theorem B2666375 : Blo 1776089 2666375 := bstep (se 1 (by rfl) ⟨1999781, by rfl⟩ : syracuseStep 2666375 = 3999563) B3999563
theorem B20524963 : Blo 1776089 20524963 := bstep (se 1 (by rfl) ⟨15393722, by rfl⟩ : syracuseStep 20524963 = 30787445) B30787445
theorem B2666411 : Blo 1776089 2666411 := bstep (se 1 (by rfl) ⟨1999808, by rfl⟩ : syracuseStep 2666411 = 3999617) B3999617
theorem B2666441 : Blo 1776089 2666441 := bstep (se 2 (by rfl) ⟨999915, by rfl⟩ : syracuseStep 2666441 = 1999831) B1999831
theorem B2666555 : Blo 1776089 2666555 := bstep (se 1 (by rfl) ⟨1999916, by rfl⟩ : syracuseStep 2666555 = 3999833) B3999833
theorem B82088029 : Blo 1776089 82088029 := bstep (se 3 (by rfl) ⟨15391505, by rfl⟩ : syracuseStep 82088029 = 30783011) B30783011
theorem B2248823 : Blo 1776089 2248823 := bstep (se 1 (by rfl) ⟨1686617, by rfl⟩ : syracuseStep 2248823 = 3373235) B3373235
theorem B2666615 : Blo 1776089 2666615 := bstep (se 1 (by rfl) ⟨1999961, by rfl⟩ : syracuseStep 2666615 = 3999923) B3999923
theorem B3797111 : Blo 1776089 3797111 := bstep (se 1 (by rfl) ⟨2847833, by rfl⟩ : syracuseStep 3797111 = 5695667) B5695667
theorem B2666639 : Blo 1776089 2666639 := bstep (se 1 (by rfl) ⟨1999979, by rfl⟩ : syracuseStep 2666639 = 3999959) B3999959
theorem B5058713 : Blo 1776089 5058713 := bstep (se 2 (by rfl) ⟨1897017, by rfl⟩ : syracuseStep 5058713 = 3794035) B3794035
theorem B2666681 : Blo 1776089 2666681 := bstep (se 2 (by rfl) ⟨1000005, by rfl⟩ : syracuseStep 2666681 = 2000011) B2000011
theorem B2666759 : Blo 1776089 2666759 := bstep (se 1 (by rfl) ⟨2000069, by rfl⟩ : syracuseStep 2666759 = 4000139) B4000139
theorem B2248975 : Blo 1776089 2248975 := bstep (se 1 (by rfl) ⟨1686731, by rfl⟩ : syracuseStep 2248975 = 3373463) B3373463
theorem B6000911 : Blo 1776089 6000911 := bstep (se 1 (by rfl) ⟨4500683, by rfl⟩ : syracuseStep 6000911 = 9001367) B9001367
theorem B2666795 : Blo 1776089 2666795 := bstep (se 1 (by rfl) ⟨2000096, by rfl⟩ : syracuseStep 2666795 = 4000193) B4000193
theorem B13488443 : Blo 1776089 13488443 := bstep (se 1 (by rfl) ⟨10116332, by rfl⟩ : syracuseStep 13488443 = 20232665) B20232665
theorem B2666825 : Blo 1776089 2666825 := bstep (se 2 (by rfl) ⟨1000059, by rfl⟩ : syracuseStep 2666825 = 2000119) B2000119
theorem B8106425 : Blo 1776089 8106425 := bstep (se 2 (by rfl) ⟨3039909, by rfl⟩ : syracuseStep 8106425 = 6079819) B6079819
theorem B2249147 : Blo 1776089 2249147 := bstep (se 1 (by rfl) ⟨1686860, by rfl⟩ : syracuseStep 2249147 = 3373721) B3373721
theorem B2666939 : Blo 1776089 2666939 := bstep (se 1 (by rfl) ⟨2000204, by rfl⟩ : syracuseStep 2666939 = 4000409) B4000409
theorem B2666999 : Blo 1776089 2666999 := bstep (se 1 (by rfl) ⟨2000249, by rfl⟩ : syracuseStep 2666999 = 4000499) B4000499
theorem B2667023 : Blo 1776089 2667023 := bstep (se 1 (by rfl) ⟨2000267, by rfl⟩ : syracuseStep 2667023 = 4000535) B4000535
theorem B2667065 : Blo 1776089 2667065 := bstep (se 2 (by rfl) ⟨1000149, by rfl⟩ : syracuseStep 2667065 = 2000299) B2000299
theorem B34165313 : Blo 1776089 34165313 := bstep (se 2 (by rfl) ⟨12811992, by rfl⟩ : syracuseStep 34165313 = 25623985) B25623985
theorem B5403223 : Blo 1776089 5403223 := bstep (se 1 (by rfl) ⟨4052417, by rfl⟩ : syracuseStep 5403223 = 8104835) B8104835
theorem B11391947 : Blo 1776089 11391947 := bstep (se 1 (by rfl) ⟨8543960, by rfl⟩ : syracuseStep 11391947 = 17087921) B17087921
theorem B7590941 : Blo 1776089 7590941 := bstep (se 3 (by rfl) ⟨1423301, by rfl⟩ : syracuseStep 7590941 = 2846603) B2846603
theorem B5403905 : Blo 1776089 5403905 := bstep (se 2 (by rfl) ⟨2026464, by rfl⟩ : syracuseStep 5403905 = 4052929) B4052929
theorem B10122529 : Blo 1776089 10122529 := bstep (se 2 (by rfl) ⟨3795948, by rfl⟩ : syracuseStep 10122529 = 7591897) B7591897
theorem B3372347 : Blo 1776089 3372347 := bstep (se 1 (by rfl) ⟨2529260, by rfl⟩ : syracuseStep 3372347 = 5058521) B5058521
theorem B7591283 : Blo 1776089 7591283 := bstep (se 1 (by rfl) ⟨5693462, by rfl⟩ : syracuseStep 7591283 = 11386925) B11386925
theorem B2250119 : Blo 1776089 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B2848135 : Blo 1776089 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B9000395 : Blo 1776089 9000395 := bstep (se 1 (by rfl) ⟨6750296, by rfl⟩ : syracuseStep 9000395 = 13500593) B13500593
theorem B6403703 : Blo 1776089 6403703 := bstep (se 1 (by rfl) ⟨4802777, by rfl⟩ : syracuseStep 6403703 = 9605555) B9605555
theorem B8992457 : Blo 1776089 8992457 := bstep (se 2 (by rfl) ⟨3372171, by rfl⟩ : syracuseStep 8992457 = 6744343) B6744343
theorem B9000719 : Blo 1776089 9000719 := bstep (se 1 (by rfl) ⟨6750539, by rfl⟩ : syracuseStep 9000719 = 13501079) B13501079
theorem B3372833 : Blo 1776089 3372833 := bstep (se 2 (by rfl) ⟨1264812, by rfl⟩ : syracuseStep 3372833 = 2529625) B2529625
theorem B13498163 : Blo 1776089 13498163 := bstep (se 1 (by rfl) ⟨10123622, by rfl⟩ : syracuseStep 13498163 = 20247245) B20247245
theorem B1898299 : Blo 1776089 1898299 := bstep (se 1 (by rfl) ⟨1423724, by rfl⟩ : syracuseStep 1898299 = 2847449) B2847449
theorem B6748019 : Blo 1776089 6748019 := bstep (se 1 (by rfl) ⟨5061014, by rfl⟩ : syracuseStep 6748019 = 10122029) B10122029
theorem B4052921 : Blo 1776089 4052921 := bstep (se 2 (by rfl) ⟨1519845, by rfl⟩ : syracuseStep 4052921 = 3039691) B3039691
theorem B5994539 : Blo 1776089 5994539 := bstep (se 1 (by rfl) ⟨4495904, by rfl⟩ : syracuseStep 5994539 = 8991809) B8991809
theorem B15185981 : Blo 1776089 15185981 := bstep (se 3 (by rfl) ⟨2847371, by rfl⟩ : syracuseStep 15185981 = 5694743) B5694743
theorem B4388951 : Blo 1776089 4388951 := bstep (se 1 (by rfl) ⟨3291713, by rfl⟩ : syracuseStep 4388951 = 6583427) B6583427
theorem B5060809 : Blo 1776089 5060809 := bstep (se 2 (by rfl) ⟨1897803, by rfl⟩ : syracuseStep 5060809 = 3795607) B3795607
theorem B57620753 : Blo 1776089 57620753 := bstep (se 2 (by rfl) ⟨21607782, by rfl⟩ : syracuseStep 57620753 = 43215565) B43215565
theorem B9607457 : Blo 1776089 9607457 := bstep (se 2 (by rfl) ⟨3602796, by rfl⟩ : syracuseStep 9607457 = 7205593) B7205593
theorem B16218427 : Blo 1776089 16218427 := bstep (se 1 (by rfl) ⟨12163820, by rfl⟩ : syracuseStep 16218427 = 24327641) B24327641
theorem B21920093 : Blo 1776089 21920093 := bstep (se 3 (by rfl) ⟨4110017, by rfl⟩ : syracuseStep 21920093 = 8220035) B8220035
theorem B4495763 : Blo 1776089 4495763 := bstep (se 1 (by rfl) ⟨3371822, by rfl⟩ : syracuseStep 4495763 = 6743645) B6743645
theorem B10115513 : Blo 1776089 10115513 := bstep (se 2 (by rfl) ⟨3793317, by rfl⟩ : syracuseStep 10115513 = 7586635) B7586635
theorem B2529721 : Blo 1776089 2529721 := bstep (se 2 (by rfl) ⟨948645, by rfl⟩ : syracuseStep 2529721 = 1897291) B1897291
theorem B1776135 : Blo 1776089 1776135 := bstep (se 1 (by rfl) ⟨1332101, by rfl⟩ : syracuseStep 1776135 = 2664203) B2664203
theorem B1776143 : Blo 1776089 1776143 := bstep (se 1 (by rfl) ⟨1332107, by rfl⟩ : syracuseStep 1776143 = 2664215) B2664215
theorem B10123805 : Blo 1776089 10123805 := bstep (se 3 (by rfl) ⟨1898213, by rfl⟩ : syracuseStep 10123805 = 3796427) B3796427
theorem B28817963 : Blo 1776089 28817963 := bstep (se 1 (by rfl) ⟨21613472, by rfl⟩ : syracuseStep 28817963 = 43226945) B43226945
theorem B2701867 : Blo 1776089 2701867 := bstep (se 1 (by rfl) ⟨2026400, by rfl⟩ : syracuseStep 2701867 = 4052801) B4052801
theorem B5061163 : Blo 1776089 5061163 := bstep (se 1 (by rfl) ⟨3795872, by rfl⟩ : syracuseStep 5061163 = 7591745) B7591745
theorem B1776187 : Blo 1776089 1776187 := bstep (se 1 (by rfl) ⟨1332140, by rfl⟩ : syracuseStep 1776187 = 2664281) B2664281
theorem B1776263 : Blo 1776089 1776263 := bstep (se 1 (by rfl) ⟨1332197, by rfl⟩ : syracuseStep 1776263 = 2664395) B2664395
theorem B1776271 : Blo 1776089 1776271 := bstep (se 1 (by rfl) ⟨1332203, by rfl⟩ : syracuseStep 1776271 = 2664407) B2664407
theorem B5126809 : Blo 1776089 5126809 := bstep (se 2 (by rfl) ⟨1922553, by rfl⟩ : syracuseStep 5126809 = 3845107) B3845107
theorem B4496057 : Blo 1776089 4496057 := bstep (se 2 (by rfl) ⟨1686021, by rfl⟩ : syracuseStep 4496057 = 3372043) B3372043
theorem B1776315 : Blo 1776089 1776315 := bstep (se 1 (by rfl) ⟨1332236, by rfl⟩ : syracuseStep 1776315 = 2664473) B2664473
theorem B1776391 : Blo 1776089 1776391 := bstep (se 1 (by rfl) ⟨1332293, by rfl⟩ : syracuseStep 1776391 = 2664587) B2664587
theorem B3996431 : Blo 1776089 3996431 := bstep (se 1 (by rfl) ⟨2997323, by rfl⟩ : syracuseStep 3996431 = 5994647) B5994647
theorem B1776399 : Blo 1776089 1776399 := bstep (se 1 (by rfl) ⟨1332299, by rfl⟩ : syracuseStep 1776399 = 2664599) B2664599
theorem B2530063 : Blo 1776089 2530063 := bstep (se 1 (by rfl) ⟨1897547, by rfl⟩ : syracuseStep 2530063 = 3795095) B3795095
theorem B3996449 : Blo 1776089 3996449 := bstep (se 2 (by rfl) ⟨1498668, by rfl⟩ : syracuseStep 3996449 = 2997337) B2997337
theorem B1776443 : Blo 1776089 1776443 := bstep (se 1 (by rfl) ⟨1332332, by rfl⟩ : syracuseStep 1776443 = 2664665) B2664665
theorem B5061437 : Blo 1776089 5061437 := bstep (se 3 (by rfl) ⟨949019, by rfl⟩ : syracuseStep 5061437 = 1898039) B1898039
theorem B12811097 : Blo 1776089 12811097 := bstep (se 2 (by rfl) ⟨4804161, by rfl⟩ : syracuseStep 12811097 = 9608323) B9608323
theorem B1776519 : Blo 1776089 1776519 := bstep (se 1 (by rfl) ⟨1332389, by rfl⟩ : syracuseStep 1776519 = 2664779) B2664779
theorem B1776527 : Blo 1776089 1776527 := bstep (se 1 (by rfl) ⟨1332395, by rfl⟩ : syracuseStep 1776527 = 2664791) B2664791
theorem B1776571 : Blo 1776089 1776571 := bstep (se 1 (by rfl) ⟨1332428, by rfl⟩ : syracuseStep 1776571 = 2664857) B2664857
theorem B20241413 : Blo 1776089 20241413 := bstep (se 4 (by rfl) ⟨1897632, by rfl⟩ : syracuseStep 20241413 = 3795265) B3795265
theorem B1776647 : Blo 1776089 1776647 := bstep (se 1 (by rfl) ⟨1332485, by rfl⟩ : syracuseStep 1776647 = 2664971) B2664971
theorem B2997263 : Blo 1776089 2997263 := bstep (se 1 (by rfl) ⟨2247947, by rfl⟩ : syracuseStep 2997263 = 4495895) B4495895
theorem B1776655 : Blo 1776089 1776655 := bstep (se 1 (by rfl) ⟨1332491, by rfl⟩ : syracuseStep 1776655 = 2664983) B2664983
theorem B1776699 : Blo 1776089 1776699 := bstep (se 1 (by rfl) ⟨1332524, by rfl⟩ : syracuseStep 1776699 = 2665049) B2665049
theorem B5692477 : Blo 1776089 5692477 := bstep (se 3 (by rfl) ⟨1067339, by rfl⟩ : syracuseStep 5692477 = 2134679) B2134679
theorem B3996791 : Blo 1776089 3996791 := bstep (se 1 (by rfl) ⟨2997593, by rfl⟩ : syracuseStep 3996791 = 5995187) B5995187
theorem B1776775 : Blo 1776089 1776775 := bstep (se 1 (by rfl) ⟨1332581, by rfl⟩ : syracuseStep 1776775 = 2665163) B2665163
theorem B1776783 : Blo 1776089 1776783 := bstep (se 1 (by rfl) ⟨1332587, by rfl⟩ : syracuseStep 1776783 = 2665175) B2665175
theorem B1776827 : Blo 1776089 1776827 := bstep (se 1 (by rfl) ⟨1332620, by rfl⟩ : syracuseStep 1776827 = 2665241) B2665241
theorem B15383753 : Blo 1776089 15383753 := bstep (se 2 (by rfl) ⟨5768907, by rfl⟩ : syracuseStep 15383753 = 11537815) B11537815
theorem B126459085 : Blo 1776089 126459085 := bstep (se 3 (by rfl) ⟨23711078, by rfl⟩ : syracuseStep 126459085 = 47422157) B47422157
theorem B1776903 : Blo 1776089 1776903 := bstep (se 1 (by rfl) ⟨1332677, by rfl⟩ : syracuseStep 1776903 = 2665355) B2665355
theorem B1776911 : Blo 1776089 1776911 := bstep (se 1 (by rfl) ⟨1332683, by rfl⟩ : syracuseStep 1776911 = 2665367) B2665367
theorem B3996971 : Blo 1776089 3996971 := bstep (se 1 (by rfl) ⟨2997728, by rfl⟩ : syracuseStep 3996971 = 5995457) B5995457
theorem B1998139 : Blo 1776089 1998139 := bstep (se 1 (by rfl) ⟨1498604, by rfl⟩ : syracuseStep 1998139 = 2997209) B2997209
theorem B5995835 : Blo 1776089 5995835 := bstep (se 1 (by rfl) ⟨4496876, by rfl⟩ : syracuseStep 5995835 = 8993753) B8993753
theorem B1776955 : Blo 1776089 1776955 := bstep (se 1 (by rfl) ⟨1332716, by rfl⟩ : syracuseStep 1776955 = 2665433) B2665433
theorem B4496755 : Blo 1776089 4496755 := bstep (se 1 (by rfl) ⟨3372566, by rfl⟩ : syracuseStep 4496755 = 6745133) B6745133
theorem B1777031 : Blo 1776089 1777031 := bstep (se 1 (by rfl) ⟨1332773, by rfl⟩ : syracuseStep 1777031 = 2665547) B2665547
theorem B1777039 : Blo 1776089 1777039 := bstep (se 1 (by rfl) ⟨1332779, by rfl⟩ : syracuseStep 1777039 = 2665559) B2665559
theorem B7593401 : Blo 1776089 7593401 := bstep (se 2 (by rfl) ⟨2847525, by rfl⟩ : syracuseStep 7593401 = 5695051) B5695051
theorem B1777083 : Blo 1776089 1777083 := bstep (se 1 (by rfl) ⟨1332812, by rfl⟩ : syracuseStep 1777083 = 2665625) B2665625
theorem B4496897 : Blo 1776089 4496897 := bstep (se 2 (by rfl) ⟨1686336, by rfl⟩ : syracuseStep 4496897 = 3372673) B3372673
theorem B1777159 : Blo 1776089 1777159 := bstep (se 1 (by rfl) ⟨1332869, by rfl⟩ : syracuseStep 1777159 = 2665739) B2665739
theorem B1777167 : Blo 1776089 1777167 := bstep (se 1 (by rfl) ⟨1332875, by rfl⟩ : syracuseStep 1777167 = 2665751) B2665751
theorem B8535581 : Blo 1776089 8535581 := bstep (se 3 (by rfl) ⟨1600421, by rfl⟩ : syracuseStep 8535581 = 3200843) B3200843
theorem B2997803 : Blo 1776089 2997803 := bstep (se 1 (by rfl) ⟨2248352, by rfl⟩ : syracuseStep 2997803 = 4496705) B4496705
theorem B1777211 : Blo 1776089 1777211 := bstep (se 1 (by rfl) ⟨1332908, by rfl⟩ : syracuseStep 1777211 = 2665817) B2665817
theorem B1777287 : Blo 1776089 1777287 := bstep (se 1 (by rfl) ⟨1332965, by rfl⟩ : syracuseStep 1777287 = 2665931) B2665931
theorem B1777295 : Blo 1776089 1777295 := bstep (se 1 (by rfl) ⟨1332971, by rfl⟩ : syracuseStep 1777295 = 2665943) B2665943
theorem B3997331 : Blo 1776089 3997331 := bstep (se 1 (by rfl) ⟨2997998, by rfl⟩ : syracuseStep 3997331 = 5995997) B5995997
theorem B3374777 : Blo 1776089 3374777 := bstep (se 2 (by rfl) ⟨1265541, by rfl⟩ : syracuseStep 3374777 = 2531083) B2531083
theorem B1777339 : Blo 1776089 1777339 := bstep (se 1 (by rfl) ⟨1333004, by rfl⟩ : syracuseStep 1777339 = 2666009) B2666009
theorem B12803777 : Blo 1776089 12803777 := bstep (se 2 (by rfl) ⟨4801416, by rfl⟩ : syracuseStep 12803777 = 9602833) B9602833
theorem B3997385 : Blo 1776089 3997385 := bstep (se 2 (by rfl) ⟨1499019, by rfl⟩ : syracuseStep 3997385 = 2998039) B2998039
theorem B7593709 : Blo 1776089 7593709 := bstep (se 3 (by rfl) ⟨1423820, by rfl⟩ : syracuseStep 7593709 = 2847641) B2847641
theorem B8544001 : Blo 1776089 8544001 := bstep (se 2 (by rfl) ⟨3204000, by rfl⟩ : syracuseStep 8544001 = 6408001) B6408001
theorem B1777415 : Blo 1776089 1777415 := bstep (se 1 (by rfl) ⟨1333061, by rfl⟩ : syracuseStep 1777415 = 2666123) B2666123
theorem B1998607 : Blo 1776089 1998607 := bstep (se 1 (by rfl) ⟨1498955, by rfl⟩ : syracuseStep 1998607 = 2997911) B2997911
theorem B1777423 : Blo 1776089 1777423 := bstep (se 1 (by rfl) ⟨1333067, by rfl⟩ : syracuseStep 1777423 = 2666135) B2666135
theorem B13868815 : Blo 1776089 13868815 := bstep (se 1 (by rfl) ⟨10401611, by rfl⟩ : syracuseStep 13868815 = 20803223) B20803223
theorem B7593743 : Blo 1776089 7593743 := bstep (se 1 (by rfl) ⟨5695307, by rfl⟩ : syracuseStep 7593743 = 11390615) B11390615
theorem B5996321 : Blo 1776089 5996321 := bstep (se 2 (by rfl) ⟨2248620, by rfl⟩ : syracuseStep 5996321 = 4497241) B4497241
theorem B1777467 : Blo 1776089 1777467 := bstep (se 1 (by rfl) ⟨1333100, by rfl⟩ : syracuseStep 1777467 = 2666201) B2666201
theorem B2531191 : Blo 1776089 2531191 := bstep (se 1 (by rfl) ⟨1898393, by rfl⟩ : syracuseStep 2531191 = 3796787) B3796787
theorem B1777543 : Blo 1776089 1777543 := bstep (se 1 (by rfl) ⟨1333157, by rfl⟩ : syracuseStep 1777543 = 2666315) B2666315
theorem B1777551 : Blo 1776089 1777551 := bstep (se 1 (by rfl) ⟨1333163, by rfl⟩ : syracuseStep 1777551 = 2666327) B2666327
theorem B2998201 : Blo 1776089 2998201 := bstep (se 2 (by rfl) ⟨1124325, by rfl⟩ : syracuseStep 2998201 = 2248651) B2248651
theorem B1777595 : Blo 1776089 1777595 := bstep (se 1 (by rfl) ⟨1333196, by rfl⟩ : syracuseStep 1777595 = 2666393) B2666393
theorem B4497353 : Blo 1776089 4497353 := bstep (se 2 (by rfl) ⟨1686507, by rfl⟩ : syracuseStep 4497353 = 3373015) B3373015
theorem B6750161 : Blo 1776089 6750161 := bstep (se 2 (by rfl) ⟨2531310, by rfl⟩ : syracuseStep 6750161 = 5062621) B5062621
theorem B1777703 : Blo 1776089 1777703 := bstep (se 1 (by rfl) ⟨1333277, by rfl⟩ : syracuseStep 1777703 = 2666555) B2666555
theorem B1777743 : Blo 1776089 1777743 := bstep (se 1 (by rfl) ⟨1333307, by rfl⟩ : syracuseStep 1777743 = 2666615) B2666615
theorem B2531407 : Blo 1776089 2531407 := bstep (se 1 (by rfl) ⟨1898555, by rfl⟩ : syracuseStep 2531407 = 3797111) B3797111
theorem B1777759 : Blo 1776089 1777759 := bstep (se 1 (by rfl) ⟨1333319, by rfl⟩ : syracuseStep 1777759 = 2666639) B2666639
theorem B1777787 : Blo 1776089 1777787 := bstep (se 1 (by rfl) ⟨1333340, by rfl⟩ : syracuseStep 1777787 = 2666681) B2666681
theorem B1777839 : Blo 1776089 1777839 := bstep (se 1 (by rfl) ⟨1333379, by rfl⟩ : syracuseStep 1777839 = 2666759) B2666759
theorem B2998471 : Blo 1776089 2998471 := bstep (se 1 (by rfl) ⟨2248853, by rfl⟩ : syracuseStep 2998471 = 4497707) B4497707
theorem B1777863 : Blo 1776089 1777863 := bstep (se 1 (by rfl) ⟨1333397, by rfl⟩ : syracuseStep 1777863 = 2666795) B2666795
theorem B3604679 : Blo 1776089 3604679 := bstep (se 1 (by rfl) ⟨2703509, by rfl⟩ : syracuseStep 3604679 = 5407019) B5407019
theorem B1777883 : Blo 1776089 1777883 := bstep (se 1 (by rfl) ⟨1333412, by rfl⟩ : syracuseStep 1777883 = 2666825) B2666825
theorem B3997943 : Blo 1776089 3997943 := bstep (se 1 (by rfl) ⟨2998457, by rfl⟩ : syracuseStep 3997943 = 5996915) B5996915
theorem B1777959 : Blo 1776089 1777959 := bstep (se 1 (by rfl) ⟨1333469, by rfl⟩ : syracuseStep 1777959 = 2666939) B2666939
theorem B5996861 : Blo 1776089 5996861 := bstep (se 3 (by rfl) ⟨1124411, by rfl⟩ : syracuseStep 5996861 = 2248823) B2248823
theorem B1777999 : Blo 1776089 1777999 := bstep (se 1 (by rfl) ⟨1333499, by rfl⟩ : syracuseStep 1777999 = 2666999) B2666999
theorem B1778015 : Blo 1776089 1778015 := bstep (se 1 (by rfl) ⟨1333511, by rfl⟩ : syracuseStep 1778015 = 2667023) B2667023
theorem B2998633 : Blo 1776089 2998633 := bstep (se 2 (by rfl) ⟨1124487, by rfl⟩ : syracuseStep 2998633 = 2248975) B2248975
theorem B1778043 : Blo 1776089 1778043 := bstep (se 1 (by rfl) ⟨1333532, by rfl⟩ : syracuseStep 1778043 = 2667065) B2667065
theorem B7201313 : Blo 1776089 7201313 := bstep (se 2 (by rfl) ⟨2700492, by rfl⟩ : syracuseStep 7201313 = 5400985) B5400985
theorem B12804641 : Blo 1776089 12804641 := bstep (se 2 (by rfl) ⟨4801740, by rfl⟩ : syracuseStep 12804641 = 9603481) B9603481
theorem B1999399 : Blo 1776089 1999399 := bstep (se 1 (by rfl) ⟨1499549, by rfl⟩ : syracuseStep 1999399 = 2999099) B2999099
theorem B7594631 : Blo 1776089 7594631 := bstep (se 1 (by rfl) ⟨5695973, by rfl⟩ : syracuseStep 7594631 = 11391947) B11391947
theorem B6750935 : Blo 1776089 6750935 := bstep (se 1 (by rfl) ⟨5063201, by rfl⟩ : syracuseStep 6750935 = 10126403) B10126403
theorem B3998537 : Blo 1776089 3998537 := bstep (se 2 (by rfl) ⟨1499451, by rfl⟩ : syracuseStep 3998537 = 2998903) B2998903
theorem B2999227 : Blo 1776089 2999227 := bstep (se 1 (by rfl) ⟨2249420, by rfl⟩ : syracuseStep 2999227 = 4498841) B4498841
theorem B15188957 : Blo 1776089 15188957 := bstep (se 3 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 15188957 = 5695859) B5695859
theorem B8995859 : Blo 1776089 8995859 := bstep (se 1 (by rfl) ⟨6746894, by rfl⟩ : syracuseStep 8995859 = 13493789) B13493789
theorem B2999335 : Blo 1776089 2999335 := bstep (se 1 (by rfl) ⟨2249501, by rfl⟩ : syracuseStep 2999335 = 4499003) B4499003
theorem B5997725 : Blo 1776089 5997725 := bstep (se 3 (by rfl) ⟨1124573, by rfl⟩ : syracuseStep 5997725 = 2249147) B2249147
theorem B4498679 : Blo 1776089 4498679 := bstep (se 1 (by rfl) ⟨3374009, by rfl⟩ : syracuseStep 4498679 = 6748019) B6748019
theorem B2999659 : Blo 1776089 2999659 := bstep (se 1 (by rfl) ⟨2249744, by rfl⟩ : syracuseStep 2999659 = 4499489) B4499489
theorem B2925967 : Blo 1776089 2925967 := bstep (se 1 (by rfl) ⟨2194475, by rfl⟩ : syracuseStep 2925967 = 4388951) B4388951
theorem B38413835 : Blo 1776089 38413835 := bstep (se 1 (by rfl) ⟨28810376, by rfl⟩ : syracuseStep 38413835 = 57620753) B57620753
theorem B3999329 : Blo 1776089 3999329 := bstep (se 2 (by rfl) ⟨1499748, by rfl⟩ : syracuseStep 3999329 = 2999497) B2999497
theorem B6743675 : Blo 1776089 6743675 := bstep (se 1 (by rfl) ⟨5057756, by rfl⟩ : syracuseStep 6743675 = 10115513) B10115513
theorem B5998265 : Blo 1776089 5998265 := bstep (se 2 (by rfl) ⟨2249349, by rfl⟩ : syracuseStep 5998265 = 4498699) B4498699
theorem B19211975 : Blo 1776089 19211975 := bstep (se 1 (by rfl) ⟨14408981, by rfl⟩ : syracuseStep 19211975 = 28817963) B28817963
theorem B41043671 : Blo 1776089 41043671 := bstep (se 1 (by rfl) ⟨30782753, by rfl⟩ : syracuseStep 41043671 = 61565507) B61565507
theorem B2664185 : Blo 1776089 2664185 := bstep (se 2 (by rfl) ⟨999069, by rfl⟩ : syracuseStep 2664185 = 1998139) B1998139
theorem B2664287 : Blo 1776089 2664287 := bstep (se 1 (by rfl) ⟨1998215, by rfl⟩ : syracuseStep 2664287 = 3996431) B3996431
theorem B2664299 : Blo 1776089 2664299 := bstep (se 1 (by rfl) ⟨1998224, by rfl⟩ : syracuseStep 2664299 = 3996449) B3996449
theorem B3999671 : Blo 1776089 3999671 := bstep (se 1 (by rfl) ⟨2999753, by rfl⟩ : syracuseStep 3999671 = 5999507) B5999507
theorem B8652737 : Blo 1776089 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B13494275 : Blo 1776089 13494275 := bstep (se 1 (by rfl) ⟨10120706, by rfl⟩ : syracuseStep 13494275 = 20241413) B20241413
theorem B9734201 : Blo 1776089 9734201 := bstep (se 2 (by rfl) ⟨3650325, by rfl⟩ : syracuseStep 9734201 = 7300651) B7300651
theorem B2664527 : Blo 1776089 2664527 := bstep (se 1 (by rfl) ⟨1998395, by rfl⟩ : syracuseStep 2664527 = 3996791) B3996791
theorem B2664647 : Blo 1776089 2664647 := bstep (se 1 (by rfl) ⟨1998485, by rfl⟩ : syracuseStep 2664647 = 3996971) B3996971
theorem B5998859 : Blo 1776089 5998859 := bstep (se 1 (by rfl) ⟨4499144, by rfl⟩ : syracuseStep 5998859 = 8998289) B8998289
theorem B2664809 : Blo 1776089 2664809 := bstep (se 2 (by rfl) ⟨999303, by rfl⟩ : syracuseStep 2664809 = 1998607) B1998607
theorem B18491753 : Blo 1776089 18491753 := bstep (se 2 (by rfl) ⟨6934407, by rfl⟩ : syracuseStep 18491753 = 13868815) B13868815
theorem B2664887 : Blo 1776089 2664887 := bstep (se 1 (by rfl) ⟨1998665, by rfl⟩ : syracuseStep 2664887 = 3997331) B3997331
theorem B55470521 : Blo 1776089 55470521 := bstep (se 2 (by rfl) ⟨20801445, by rfl⟩ : syracuseStep 55470521 = 41602891) B41602891
theorem B2664923 : Blo 1776089 2664923 := bstep (se 1 (by rfl) ⟨1998692, by rfl⟩ : syracuseStep 2664923 = 3997385) B3997385
theorem B10807789 : Blo 1776089 10807789 := bstep (se 3 (by rfl) ⟨2026460, by rfl⟩ : syracuseStep 10807789 = 4052921) B4052921
theorem B4000265 : Blo 1776089 4000265 := bstep (se 2 (by rfl) ⟨1500099, by rfl⟩ : syracuseStep 4000265 = 3000199) B3000199
theorem B5999129 : Blo 1776089 5999129 := bstep (se 2 (by rfl) ⟨2249673, by rfl⟩ : syracuseStep 5999129 = 4499347) B4499347
theorem B4500107 : Blo 1776089 4500107 := bstep (se 1 (by rfl) ⟨3375080, by rfl⟩ : syracuseStep 4500107 = 6750161) B6750161
theorem B4500319 : Blo 1776089 4500319 := bstep (se 1 (by rfl) ⟨3375239, by rfl⟩ : syracuseStep 4500319 = 6750479) B6750479
theorem B4000607 : Blo 1776089 4000607 := bstep (se 1 (by rfl) ⟨3000455, by rfl⟩ : syracuseStep 4000607 = 6000911) B6000911
theorem B2665391 : Blo 1776089 2665391 := bstep (se 1 (by rfl) ⟨1999043, by rfl⟩ : syracuseStep 2665391 = 3998087) B3998087
theorem B2665481 : Blo 1776089 2665481 := bstep (se 2 (by rfl) ⟨999555, by rfl⟩ : syracuseStep 2665481 = 1999111) B1999111
theorem B6745103 : Blo 1776089 6745103 := bstep (se 1 (by rfl) ⟨5058827, by rfl⟩ : syracuseStep 6745103 = 10117655) B10117655
theorem B2665511 : Blo 1776089 2665511 := bstep (se 1 (by rfl) ⟨1999133, by rfl⟩ : syracuseStep 2665511 = 3998267) B3998267
theorem B22776875 : Blo 1776089 22776875 := bstep (se 1 (by rfl) ⟨17082656, by rfl⟩ : syracuseStep 22776875 = 34165313) B34165313
theorem B2665595 : Blo 1776089 2665595 := bstep (se 1 (by rfl) ⟨1999196, by rfl⟩ : syracuseStep 2665595 = 3998393) B3998393
theorem B2665721 : Blo 1776089 2665721 := bstep (se 2 (by rfl) ⟨999645, by rfl⟩ : syracuseStep 2665721 = 1999291) B1999291
theorem B2665823 : Blo 1776089 2665823 := bstep (se 1 (by rfl) ⟨1999367, by rfl⟩ : syracuseStep 2665823 = 3998735) B3998735
theorem B2665835 : Blo 1776089 2665835 := bstep (se 1 (by rfl) ⟨1999376, by rfl⟩ : syracuseStep 2665835 = 3998753) B3998753
theorem B15183247 : Blo 1776089 15183247 := bstep (se 1 (by rfl) ⟨11387435, by rfl⟩ : syracuseStep 15183247 = 22774871) B22774871
theorem B30764461 : Blo 1776089 30764461 := bstep (se 3 (by rfl) ⟨5768336, by rfl⟩ : syracuseStep 30764461 = 11536673) B11536673
theorem B25619885 : Blo 1776089 25619885 := bstep (se 3 (by rfl) ⟨4803728, by rfl⟩ : syracuseStep 25619885 = 9607457) B9607457
theorem B7204297 : Blo 1776089 7204297 := bstep (se 2 (by rfl) ⟨2701611, by rfl⟩ : syracuseStep 7204297 = 5403223) B5403223
theorem B5770777 : Blo 1776089 5770777 := bstep (se 2 (by rfl) ⟨2164041, by rfl⟩ : syracuseStep 5770777 = 4328083) B4328083
theorem B6835745 : Blo 1776089 6835745 := bstep (se 2 (by rfl) ⟨2563404, by rfl⟩ : syracuseStep 6835745 = 5126809) B5126809
theorem B2248231 : Blo 1776089 2248231 := bstep (se 1 (by rfl) ⟨1686173, by rfl⟩ : syracuseStep 2248231 = 3372347) B3372347
theorem B2666063 : Blo 1776089 2666063 := bstep (se 1 (by rfl) ⟨1999547, by rfl⟩ : syracuseStep 2666063 = 3999095) B3999095
theorem B6000263 : Blo 1776089 6000263 := bstep (se 1 (by rfl) ⟨4500197, by rfl⟩ : syracuseStep 6000263 = 9000395) B9000395
theorem B6000317 : Blo 1776089 6000317 := bstep (se 3 (by rfl) ⟨1125059, by rfl⟩ : syracuseStep 6000317 = 2250119) B2250119
theorem B5058247 : Blo 1776089 5058247 := bstep (se 1 (by rfl) ⟨3793685, by rfl⟩ : syracuseStep 5058247 = 7587371) B7587371
theorem B2666183 : Blo 1776089 2666183 := bstep (se 1 (by rfl) ⟨1999637, by rfl⟩ : syracuseStep 2666183 = 3999275) B3999275
theorem B15175457 : Blo 1776089 15175457 := bstep (se 2 (by rfl) ⟨5690796, by rfl⟩ : syracuseStep 15175457 = 11381593) B11381593
theorem B6000479 : Blo 1776089 6000479 := bstep (se 1 (by rfl) ⟨4500359, by rfl⟩ : syracuseStep 6000479 = 9000719) B9000719
theorem B2666345 : Blo 1776089 2666345 := bstep (se 2 (by rfl) ⟨999879, by rfl⟩ : syracuseStep 2666345 = 1999759) B1999759
theorem B2248555 : Blo 1776089 2248555 := bstep (se 1 (by rfl) ⟨1686416, by rfl⟩ : syracuseStep 2248555 = 3372833) B3372833
theorem B8998775 : Blo 1776089 8998775 := bstep (se 1 (by rfl) ⟨6749081, by rfl⟩ : syracuseStep 8998775 = 13498163) B13498163
theorem B2666423 : Blo 1776089 2666423 := bstep (se 1 (by rfl) ⟨1999817, by rfl⟩ : syracuseStep 2666423 = 3999635) B3999635
theorem B2666459 : Blo 1776089 2666459 := bstep (se 1 (by rfl) ⟨1999844, by rfl⟩ : syracuseStep 2666459 = 3999689) B3999689
theorem B6000641 : Blo 1776089 6000641 := bstep (se 2 (by rfl) ⟨2250240, by rfl⟩ : syracuseStep 6000641 = 4500481) B4500481
theorem B7589969 : Blo 1776089 7589969 := bstep (se 2 (by rfl) ⟨2846238, by rfl⟩ : syracuseStep 7589969 = 5692477) B5692477
theorem B197267537 : Blo 1776089 197267537 := bstep (se 2 (by rfl) ⟨73975326, by rfl⟩ : syracuseStep 197267537 = 147950653) B147950653
theorem B168612113 : Blo 1776089 168612113 := bstep (se 2 (by rfl) ⟨63229542, by rfl⟩ : syracuseStep 168612113 = 126459085) B126459085
theorem B17076541 : Blo 1776089 17076541 := bstep (se 3 (by rfl) ⟨3201851, by rfl⟩ : syracuseStep 17076541 = 6403703) B6403703
theorem B13496705 : Blo 1776089 13496705 := bstep (se 2 (by rfl) ⟨5061264, by rfl⟩ : syracuseStep 13496705 = 10122529) B10122529
theorem B2666927 : Blo 1776089 2666927 := bstep (se 1 (by rfl) ⟨2000195, by rfl⟩ : syracuseStep 2666927 = 4000391) B4000391
theorem B2667017 : Blo 1776089 2667017 := bstep (se 2 (by rfl) ⟨1000131, by rfl⟩ : syracuseStep 2667017 = 2000263) B2000263
theorem B3797513 : Blo 1776089 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B2667047 : Blo 1776089 2667047 := bstep (se 1 (by rfl) ⟨2000285, by rfl⟩ : syracuseStep 2667047 = 4000571) B4000571
theorem B8540731 : Blo 1776089 8540731 := bstep (se 1 (by rfl) ⟨6405548, by rfl⟩ : syracuseStep 8540731 = 12811097) B12811097
theorem B5059169 : Blo 1776089 5059169 := bstep (se 2 (by rfl) ⟨1897188, by rfl⟩ : syracuseStep 5059169 = 3794377) B3794377
theorem B2667131 : Blo 1776089 2667131 := bstep (se 1 (by rfl) ⟨2000348, by rfl⟩ : syracuseStep 2667131 = 4000697) B4000697
theorem B6746759 : Blo 1776089 6746759 := bstep (se 1 (by rfl) ⟨5060069, by rfl⟩ : syracuseStep 6746759 = 10120139) B10120139
theorem B3420883 : Blo 1776089 3420883 := bstep (se 1 (by rfl) ⟨2565662, by rfl⟩ : syracuseStep 3420883 = 5131325) B5131325
theorem B28816145 : Blo 1776089 28816145 := bstep (se 2 (by rfl) ⟨10806054, by rfl⟩ : syracuseStep 28816145 = 21612109) B21612109
theorem B41612183 : Blo 1776089 41612183 := bstep (se 1 (by rfl) ⟨31209137, by rfl⟩ : syracuseStep 41612183 = 62418275) B62418275
theorem B3371959 : Blo 1776089 3371959 := bstep (se 1 (by rfl) ⟨2528969, by rfl⟩ : syracuseStep 3371959 = 5057939) B5057939
theorem B11392001 : Blo 1776089 11392001 := bstep (se 2 (by rfl) ⟨4272000, by rfl⟩ : syracuseStep 11392001 = 8544001) B8544001
theorem B5690387 : Blo 1776089 5690387 := bstep (se 1 (by rfl) ⟨4267790, by rfl⟩ : syracuseStep 5690387 = 8535581) B8535581
theorem B2249851 : Blo 1776089 2249851 := bstep (se 1 (by rfl) ⟨1687388, by rfl⟩ : syracuseStep 2249851 = 3374777) B3374777
theorem B6403229 : Blo 1776089 6403229 := bstep (se 3 (by rfl) ⟨1200605, by rfl⟩ : syracuseStep 6403229 = 2401211) B2401211
theorem B11384003 : Blo 1776089 11384003 := bstep (se 1 (by rfl) ⟨8538002, by rfl⟩ : syracuseStep 11384003 = 17076005) B17076005
theorem B27366617 : Blo 1776089 27366617 := bstep (se 2 (by rfl) ⟨10262481, by rfl⟩ : syracuseStep 27366617 = 20524963) B20524963
theorem B16430501 : Blo 1776089 16430501 := bstep (se 4 (by rfl) ⟨1540359, by rfl⟩ : syracuseStep 16430501 = 3080719) B3080719
theorem B109450705 : Blo 1776089 109450705 := bstep (se 2 (by rfl) ⟨41044014, by rfl⟩ : syracuseStep 109450705 = 82088029) B82088029
theorem B8992295 : Blo 1776089 8992295 := bstep (se 1 (by rfl) ⟨6744221, by rfl⟩ : syracuseStep 8992295 = 13488443) B13488443
theorem B6747745 : Blo 1776089 6747745 := bstep (se 2 (by rfl) ⟨2530404, by rfl⟩ : syracuseStep 6747745 = 5060809) B5060809
theorem B5404283 : Blo 1776089 5404283 := bstep (se 1 (by rfl) ⟨4053212, by rfl⟩ : syracuseStep 5404283 = 8106425) B8106425
theorem B13489901 : Blo 1776089 13489901 := bstep (se 3 (by rfl) ⟨2529356, by rfl⟩ : syracuseStep 13489901 = 5058713) B5058713
theorem B21624569 : Blo 1776089 21624569 := bstep (se 2 (by rfl) ⟨8109213, by rfl⟩ : syracuseStep 21624569 = 16218427) B16218427
theorem B36484901 : Blo 1776089 36484901 := bstep (se 4 (by rfl) ⟨3420459, by rfl⟩ : syracuseStep 36484901 = 6840919) B6840919
theorem B3200987 : Blo 1776089 3200987 := bstep (se 1 (by rfl) ⟨2400740, by rfl⟩ : syracuseStep 3200987 = 4801481) B4801481
theorem B5060627 : Blo 1776089 5060627 := bstep (se 1 (by rfl) ⟨3795470, by rfl⟩ : syracuseStep 5060627 = 7590941) B7590941
theorem B3602489 : Blo 1776089 3602489 := bstep (se 2 (by rfl) ⟨1350933, by rfl⟩ : syracuseStep 3602489 = 2701867) B2701867
theorem B6748217 : Blo 1776089 6748217 := bstep (se 2 (by rfl) ⟨2530581, by rfl⟩ : syracuseStep 6748217 = 5061163) B5061163
theorem B3602603 : Blo 1776089 3602603 := bstep (se 1 (by rfl) ⟨2701952, by rfl⟩ : syracuseStep 3602603 = 5403905) B5403905
theorem B5060855 : Blo 1776089 5060855 := bstep (se 1 (by rfl) ⟨3795641, by rfl⟩ : syracuseStep 5060855 = 7591283) B7591283
theorem B3373417 : Blo 1776089 3373417 := bstep (se 2 (by rfl) ⟨1265031, by rfl⟩ : syracuseStep 3373417 = 2530063) B2530063
theorem B1776091 : Blo 1776089 1776091 := bstep (se 1 (by rfl) ⟨1332068, by rfl⟩ : syracuseStep 1776091 = 2664137) B2664137
theorem B5994971 : Blo 1776089 5994971 := bstep (se 1 (by rfl) ⟨4496228, by rfl⟩ : syracuseStep 5994971 = 8992457) B8992457
theorem B1776167 : Blo 1776089 1776167 := bstep (se 1 (by rfl) ⟨1332125, by rfl⟩ : syracuseStep 1776167 = 2664251) B2664251
theorem B1776207 : Blo 1776089 1776207 := bstep (se 1 (by rfl) ⟨1332155, by rfl⟩ : syracuseStep 1776207 = 2664311) B2664311
theorem B1776223 : Blo 1776089 1776223 := bstep (se 1 (by rfl) ⟨1332167, by rfl⟩ : syracuseStep 1776223 = 2664335) B2664335
theorem B1776251 : Blo 1776089 1776251 := bstep (se 1 (by rfl) ⟨1332188, by rfl⟩ : syracuseStep 1776251 = 2664377) B2664377
theorem B5692027 : Blo 1776089 5692027 := bstep (se 1 (by rfl) ⟨4269020, by rfl⟩ : syracuseStep 5692027 = 8538041) B8538041
theorem B1776303 : Blo 1776089 1776303 := bstep (se 1 (by rfl) ⟨1332227, by rfl⟩ : syracuseStep 1776303 = 2664455) B2664455
theorem B13490873 : Blo 1776089 13490873 := bstep (se 2 (by rfl) ⟨5059077, by rfl⟩ : syracuseStep 13490873 = 10118155) B10118155
theorem B3996359 : Blo 1776089 3996359 := bstep (se 1 (by rfl) ⟨2997269, by rfl⟩ : syracuseStep 3996359 = 5994539) B5994539
theorem B1776327 : Blo 1776089 1776327 := bstep (se 1 (by rfl) ⟨1332245, by rfl⟩ : syracuseStep 1776327 = 2664491) B2664491
theorem B14408401 : Blo 1776089 14408401 := bstep (se 2 (by rfl) ⟨5403150, by rfl⟩ : syracuseStep 14408401 = 10806301) B10806301
theorem B10123987 : Blo 1776089 10123987 := bstep (se 1 (by rfl) ⟨7592990, by rfl⟩ : syracuseStep 10123987 = 15185981) B15185981
theorem B4496087 : Blo 1776089 4496087 := bstep (se 1 (by rfl) ⟨3372065, by rfl⟩ : syracuseStep 4496087 = 6744131) B6744131
theorem B1776347 : Blo 1776089 1776347 := bstep (se 1 (by rfl) ⟨1332260, by rfl⟩ : syracuseStep 1776347 = 2664521) B2664521
theorem B1776423 : Blo 1776089 1776423 := bstep (se 1 (by rfl) ⟨1332317, by rfl⟩ : syracuseStep 1776423 = 2664635) B2664635
theorem B1776463 : Blo 1776089 1776463 := bstep (se 1 (by rfl) ⟨1332347, by rfl⟩ : syracuseStep 1776463 = 2664695) B2664695
theorem B1776479 : Blo 1776089 1776479 := bstep (se 1 (by rfl) ⟨1332359, by rfl⟩ : syracuseStep 1776479 = 2664719) B2664719
theorem B1776507 : Blo 1776089 1776507 := bstep (se 1 (by rfl) ⟨1332380, by rfl⟩ : syracuseStep 1776507 = 2664761) B2664761
theorem B14613395 : Blo 1776089 14613395 := bstep (se 1 (by rfl) ⟨10960046, by rfl⟩ : syracuseStep 14613395 = 21920093) B21920093
theorem B1776559 : Blo 1776089 1776559 := bstep (se 1 (by rfl) ⟨1332419, by rfl⟩ : syracuseStep 1776559 = 2664839) B2664839
theorem B6495151 : Blo 1776089 6495151 := bstep (se 1 (by rfl) ⟨4871363, by rfl⟩ : syracuseStep 6495151 = 9742727) B9742727
theorem B2997175 : Blo 1776089 2997175 := bstep (se 1 (by rfl) ⟨2247881, by rfl⟩ : syracuseStep 2997175 = 4495763) B4495763
theorem B1776583 : Blo 1776089 1776583 := bstep (se 1 (by rfl) ⟨1332437, by rfl⟩ : syracuseStep 1776583 = 2664875) B2664875
theorem B1776603 : Blo 1776089 1776603 := bstep (se 1 (by rfl) ⟨1332452, by rfl⟩ : syracuseStep 1776603 = 2664905) B2664905
theorem B10124261 : Blo 1776089 10124261 := bstep (se 4 (by rfl) ⟨949149, by rfl⟩ : syracuseStep 10124261 = 1898299) B1898299
theorem B6749203 : Blo 1776089 6749203 := bstep (se 1 (by rfl) ⟨5061902, by rfl⟩ : syracuseStep 6749203 = 10123805) B10123805
theorem B1776679 : Blo 1776089 1776679 := bstep (se 1 (by rfl) ⟨1332509, by rfl⟩ : syracuseStep 1776679 = 2665019) B2665019
theorem B1776719 : Blo 1776089 1776719 := bstep (se 1 (by rfl) ⟨1332539, by rfl⟩ : syracuseStep 1776719 = 2665079) B2665079
theorem B1776735 : Blo 1776089 1776735 := bstep (se 1 (by rfl) ⟨1332551, by rfl⟩ : syracuseStep 1776735 = 2665103) B2665103
theorem B2997371 : Blo 1776089 2997371 := bstep (se 1 (by rfl) ⟨2248028, by rfl⟩ : syracuseStep 2997371 = 4496057) B4496057
theorem B1776763 : Blo 1776089 1776763 := bstep (se 1 (by rfl) ⟨1332572, by rfl⟩ : syracuseStep 1776763 = 2665145) B2665145
theorem B5995673 : Blo 1776089 5995673 := bstep (se 2 (by rfl) ⟨2248377, by rfl⟩ : syracuseStep 5995673 = 4496755) B4496755
theorem B1776815 : Blo 1776089 1776815 := bstep (se 1 (by rfl) ⟨1332611, by rfl⟩ : syracuseStep 1776815 = 2665223) B2665223
theorem B1776839 : Blo 1776089 1776839 := bstep (se 1 (by rfl) ⟨1332629, by rfl⟩ : syracuseStep 1776839 = 2665259) B2665259
theorem B3374291 : Blo 1776089 3374291 := bstep (se 1 (by rfl) ⟨2530718, by rfl⟩ : syracuseStep 3374291 = 5061437) B5061437
theorem B1776859 : Blo 1776089 1776859 := bstep (se 1 (by rfl) ⟨1332644, by rfl⟩ : syracuseStep 1776859 = 2665289) B2665289
theorem B9116951 : Blo 1776089 9116951 := bstep (se 1 (by rfl) ⟨6837713, by rfl⟩ : syracuseStep 9116951 = 13675427) B13675427
theorem B1776935 : Blo 1776089 1776935 := bstep (se 1 (by rfl) ⟨1332701, by rfl⟩ : syracuseStep 1776935 = 2665403) B2665403
theorem B1776975 : Blo 1776089 1776975 := bstep (se 1 (by rfl) ⟨1332731, by rfl⟩ : syracuseStep 1776975 = 2665463) B2665463
theorem B1998175 : Blo 1776089 1998175 := bstep (se 1 (by rfl) ⟨1498631, by rfl⟩ : syracuseStep 1998175 = 2997263) B2997263
theorem B1776991 : Blo 1776089 1776991 := bstep (se 1 (by rfl) ⟨1332743, by rfl⟩ : syracuseStep 1776991 = 2665487) B2665487
theorem B1777019 : Blo 1776089 1777019 := bstep (se 1 (by rfl) ⟨1332764, by rfl⟩ : syracuseStep 1777019 = 2665529) B2665529
theorem B1777071 : Blo 1776089 1777071 := bstep (se 1 (by rfl) ⟨1332803, by rfl⟩ : syracuseStep 1777071 = 2665607) B2665607
theorem B1777095 : Blo 1776089 1777095 := bstep (se 1 (by rfl) ⟨1332821, by rfl⟩ : syracuseStep 1777095 = 2665643) B2665643
theorem B10255835 : Blo 1776089 10255835 := bstep (se 1 (by rfl) ⟨7691876, by rfl⟩ : syracuseStep 10255835 = 15383753) B15383753
theorem B1777115 : Blo 1776089 1777115 := bstep (se 1 (by rfl) ⟨1332836, by rfl⟩ : syracuseStep 1777115 = 2665673) B2665673
theorem B2997769 : Blo 1776089 2997769 := bstep (se 2 (by rfl) ⟨1124163, by rfl⟩ : syracuseStep 2997769 = 2248327) B2248327
theorem B3997223 : Blo 1776089 3997223 := bstep (se 1 (by rfl) ⟨2997917, by rfl⟩ : syracuseStep 3997223 = 5995835) B5995835
theorem B1777191 : Blo 1776089 1777191 := bstep (se 1 (by rfl) ⟨1332893, by rfl⟩ : syracuseStep 1777191 = 2665787) B2665787
theorem B2530855 : Blo 1776089 2530855 := bstep (se 1 (by rfl) ⟨1898141, by rfl⟩ : syracuseStep 2530855 = 3796283) B3796283
theorem B1777231 : Blo 1776089 1777231 := bstep (se 1 (by rfl) ⟨1332923, by rfl⟩ : syracuseStep 1777231 = 2665847) B2665847
theorem B1777247 : Blo 1776089 1777247 := bstep (se 1 (by rfl) ⟨1332935, by rfl⟩ : syracuseStep 1777247 = 2665871) B2665871
theorem B8994401 : Blo 1776089 8994401 := bstep (se 2 (by rfl) ⟨3372900, by rfl⟩ : syracuseStep 8994401 = 6745801) B6745801
theorem B1777275 : Blo 1776089 1777275 := bstep (se 1 (by rfl) ⟨1332956, by rfl⟩ : syracuseStep 1777275 = 2665913) B2665913
theorem B5062267 : Blo 1776089 5062267 := bstep (se 1 (by rfl) ⟨3796700, by rfl⟩ : syracuseStep 5062267 = 7593401) B7593401
theorem B13491845 : Blo 1776089 13491845 := bstep (se 4 (by rfl) ⟨1264860, by rfl⟩ : syracuseStep 13491845 = 2529721) B2529721
theorem B10124945 : Blo 1776089 10124945 := bstep (se 2 (by rfl) ⟨3796854, by rfl⟩ : syracuseStep 10124945 = 7593709) B7593709
theorem B2997931 : Blo 1776089 2997931 := bstep (se 1 (by rfl) ⟨2248448, by rfl⟩ : syracuseStep 2997931 = 4496897) B4496897
theorem B1777327 : Blo 1776089 1777327 := bstep (se 1 (by rfl) ⟨1332995, by rfl⟩ : syracuseStep 1777327 = 2665991) B2665991
theorem B1998535 : Blo 1776089 1998535 := bstep (se 1 (by rfl) ⟨1498901, by rfl⟩ : syracuseStep 1998535 = 2997803) B2997803
theorem B1777351 : Blo 1776089 1777351 := bstep (se 1 (by rfl) ⟨1333013, by rfl⟩ : syracuseStep 1777351 = 2666027) B2666027
theorem B1777371 : Blo 1776089 1777371 := bstep (se 1 (by rfl) ⟨1333028, by rfl⟩ : syracuseStep 1777371 = 2666057) B2666057
theorem B1777447 : Blo 1776089 1777447 := bstep (se 1 (by rfl) ⟨1333085, by rfl⟩ : syracuseStep 1777447 = 2666171) B2666171
theorem B8535851 : Blo 1776089 8535851 := bstep (se 1 (by rfl) ⟨6401888, by rfl⟩ : syracuseStep 8535851 = 12803777) B12803777
theorem B25616195 : Blo 1776089 25616195 := bstep (se 1 (by rfl) ⟨19212146, by rfl⟩ : syracuseStep 25616195 = 38424293) B38424293
theorem B5693257 : Blo 1776089 5693257 := bstep (se 2 (by rfl) ⟨2134971, by rfl⟩ : syracuseStep 5693257 = 4269943) B4269943
theorem B3374921 : Blo 1776089 3374921 := bstep (se 2 (by rfl) ⟨1265595, by rfl⟩ : syracuseStep 3374921 = 2531191) B2531191
theorem B1777487 : Blo 1776089 1777487 := bstep (se 1 (by rfl) ⟨1333115, by rfl⟩ : syracuseStep 1777487 = 2666231) B2666231
theorem B1777503 : Blo 1776089 1777503 := bstep (se 1 (by rfl) ⟨1333127, by rfl⟩ : syracuseStep 1777503 = 2666255) B2666255
theorem B5062495 : Blo 1776089 5062495 := bstep (se 1 (by rfl) ⟨3796871, by rfl⟩ : syracuseStep 5062495 = 7593743) B7593743
theorem B3997547 : Blo 1776089 3997547 := bstep (se 1 (by rfl) ⟨2998160, by rfl⟩ : syracuseStep 3997547 = 5996321) B5996321
theorem B2531179 : Blo 1776089 2531179 := bstep (se 1 (by rfl) ⟨1898384, by rfl⟩ : syracuseStep 2531179 = 3796769) B3796769
theorem B1777531 : Blo 1776089 1777531 := bstep (se 1 (by rfl) ⟨1333148, by rfl⟩ : syracuseStep 1777531 = 2666297) B2666297
theorem B3997601 : Blo 1776089 3997601 := bstep (se 2 (by rfl) ⟨1499100, by rfl⟩ : syracuseStep 3997601 = 2998201) B2998201
theorem B1777583 : Blo 1776089 1777583 := bstep (se 1 (by rfl) ⟨1333187, by rfl⟩ : syracuseStep 1777583 = 2666375) B2666375
theorem B1777607 : Blo 1776089 1777607 := bstep (se 1 (by rfl) ⟨1333205, by rfl⟩ : syracuseStep 1777607 = 2666411) B2666411
theorem B2998235 : Blo 1776089 2998235 := bstep (se 1 (by rfl) ⟨2248676, by rfl⟩ : syracuseStep 2998235 = 4497353) B4497353
theorem B1777627 : Blo 1776089 1777627 := bstep (se 1 (by rfl) ⟨1333220, by rfl⟩ : syracuseStep 1777627 = 2666441) B2666441
theorem B3375209 : Blo 1776089 3375209 := bstep (se 2 (by rfl) ⟨1265703, by rfl⟩ : syracuseStep 3375209 = 2531407) B2531407
theorem B3997907 : Blo 1776089 3997907 := bstep (se 1 (by rfl) ⟨2998430, by rfl⟩ : syracuseStep 3997907 = 5996861) B5996861
theorem B3997961 : Blo 1776089 3997961 := bstep (se 2 (by rfl) ⟨1499235, by rfl⟩ : syracuseStep 3997961 = 2998471) B2998471
theorem B1777951 : Blo 1776089 1777951 := bstep (se 1 (by rfl) ⟨1333463, by rfl⟩ : syracuseStep 1777951 = 2666927) B2666927
theorem B1778011 : Blo 1776089 1778011 := bstep (se 1 (by rfl) ⟨1333508, by rfl⟩ : syracuseStep 1778011 = 2667017) B2667017
theorem B2531675 : Blo 1776089 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B4800875 : Blo 1776089 4800875 := bstep (se 1 (by rfl) ⟨3600656, by rfl⟩ : syracuseStep 4800875 = 7201313) B7201313
theorem B8536427 : Blo 1776089 8536427 := bstep (se 1 (by rfl) ⟨6402320, by rfl⟩ : syracuseStep 8536427 = 12804641) B12804641
theorem B1778031 : Blo 1776089 1778031 := bstep (se 1 (by rfl) ⟨1333523, by rfl⟩ : syracuseStep 1778031 = 2667047) B2667047
theorem B1778087 : Blo 1776089 1778087 := bstep (se 1 (by rfl) ⟨1333565, by rfl⟩ : syracuseStep 1778087 = 2667131) B2667131
theorem B4497839 : Blo 1776089 4497839 := bstep (se 1 (by rfl) ⟨3373379, by rfl⟩ : syracuseStep 4497839 = 6746759) B6746759
theorem B5063087 : Blo 1776089 5063087 := bstep (se 1 (by rfl) ⟨3797315, by rfl⟩ : syracuseStep 5063087 = 7594631) B7594631
theorem B4497889 : Blo 1776089 4497889 := bstep (se 2 (by rfl) ⟨1686708, by rfl⟩ : syracuseStep 4497889 = 3373417) B3373417
theorem B3998177 : Blo 1776089 3998177 := bstep (se 2 (by rfl) ⟨1499316, by rfl⟩ : syracuseStep 3998177 = 2998633) B2998633
theorem B19210763 : Blo 1776089 19210763 := bstep (se 1 (by rfl) ⟨14408072, by rfl⟩ : syracuseStep 19210763 = 28816145) B28816145
theorem B14410385 : Blo 1776089 14410385 := bstep (se 2 (by rfl) ⟨5403894, by rfl⟩ : syracuseStep 14410385 = 10807789) B10807789
theorem B10125971 : Blo 1776089 10125971 := bstep (se 1 (by rfl) ⟨7594478, by rfl⟩ : syracuseStep 10125971 = 15188957) B15188957
theorem B7594667 : Blo 1776089 7594667 := bstep (se 1 (by rfl) ⟨5696000, by rfl⟩ : syracuseStep 7594667 = 11392001) B11392001
theorem B3793591 : Blo 1776089 3793591 := bstep (se 1 (by rfl) ⟨2845193, by rfl⟩ : syracuseStep 3793591 = 5690387) B5690387
theorem B5997239 : Blo 1776089 5997239 := bstep (se 1 (by rfl) ⟨4497929, by rfl⟩ : syracuseStep 5997239 = 8995859) B8995859
theorem B11387641 : Blo 1776089 11387641 := bstep (se 2 (by rfl) ⟨4270365, by rfl⟩ : syracuseStep 11387641 = 8540731) B8540731
theorem B4268819 : Blo 1776089 4268819 := bstep (se 1 (by rfl) ⟨3201614, by rfl⟩ : syracuseStep 4268819 = 6403229) B6403229
theorem B3998483 : Blo 1776089 3998483 := bstep (se 1 (by rfl) ⟨2998862, by rfl⟩ : syracuseStep 3998483 = 5997725) B5997725
theorem B2999119 : Blo 1776089 2999119 := bstep (se 1 (by rfl) ⟨2249339, by rfl⟩ : syracuseStep 2999119 = 4498679) B4498679
theorem B19211201 : Blo 1776089 19211201 := bstep (se 2 (by rfl) ⟨7204200, by rfl⟩ : syracuseStep 19211201 = 14408401) B14408401
theorem B10953667 : Blo 1776089 10953667 := bstep (se 1 (by rfl) ⟨8215250, by rfl⟩ : syracuseStep 10953667 = 16430501) B16430501
theorem B25609223 : Blo 1776089 25609223 := bstep (se 1 (by rfl) ⟨19206917, by rfl⟩ : syracuseStep 25609223 = 38413835) B38413835
theorem B3998843 : Blo 1776089 3998843 := bstep (se 1 (by rfl) ⟨2999132, by rfl⟩ : syracuseStep 3998843 = 5998265) B5998265
theorem B27362447 : Blo 1776089 27362447 := bstep (se 1 (by rfl) ⟨20521835, by rfl⟩ : syracuseStep 27362447 = 41043671) B41043671
theorem B24323267 : Blo 1776089 24323267 := bstep (se 1 (by rfl) ⟨18242450, by rfl⟩ : syracuseStep 24323267 = 36484901) B36484901
theorem B8660201 : Blo 1776089 8660201 := bstep (se 2 (by rfl) ⟨3247575, by rfl⟩ : syracuseStep 8660201 = 6495151) B6495151
theorem B3998969 : Blo 1776089 3998969 := bstep (se 2 (by rfl) ⟨1499613, by rfl⟩ : syracuseStep 3998969 = 2999227) B2999227
theorem B5768491 : Blo 1776089 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B8996183 : Blo 1776089 8996183 := bstep (se 1 (by rfl) ⟨6747137, by rfl⟩ : syracuseStep 8996183 = 13494275) B13494275
theorem B6489467 : Blo 1776089 6489467 := bstep (se 1 (by rfl) ⟨4867100, by rfl⟩ : syracuseStep 6489467 = 9734201) B9734201
theorem B4498811 : Blo 1776089 4498811 := bstep (se 1 (by rfl) ⟨3374108, by rfl⟩ : syracuseStep 4498811 = 6748217) B6748217
theorem B3999113 : Blo 1776089 3999113 := bstep (se 2 (by rfl) ⟨1499667, by rfl⟩ : syracuseStep 3999113 = 2999335) B2999335
theorem B2401735 : Blo 1776089 2401735 := bstep (se 1 (by rfl) ⟨1801301, by rfl⟩ : syracuseStep 2401735 = 3602603) B3602603
theorem B2999801 : Blo 1776089 2999801 := bstep (se 2 (by rfl) ⟨1124925, by rfl⟩ : syracuseStep 2999801 = 2249851) B2249851
theorem B3999239 : Blo 1776089 3999239 := bstep (se 1 (by rfl) ⟨2999429, by rfl⟩ : syracuseStep 3999239 = 5998859) B5998859
theorem B3999419 : Blo 1776089 3999419 := bstep (se 1 (by rfl) ⟨2999564, by rfl⟩ : syracuseStep 3999419 = 5999129) B5999129
theorem B3000071 : Blo 1776089 3000071 := bstep (se 1 (by rfl) ⟨2250053, by rfl⟩ : syracuseStep 3000071 = 4500107) B4500107
theorem B2664233 : Blo 1776089 2664233 := bstep (se 2 (by rfl) ⟨999087, by rfl⟩ : syracuseStep 2664233 = 1998175) B1998175
theorem B2664239 : Blo 1776089 2664239 := bstep (se 1 (by rfl) ⟨1998179, by rfl⟩ : syracuseStep 2664239 = 3996359) B3996359
theorem B3999545 : Blo 1776089 3999545 := bstep (se 2 (by rfl) ⟨1499829, by rfl⟩ : syracuseStep 3999545 = 2999659) B2999659
theorem B20244329 : Blo 1776089 20244329 := bstep (se 2 (by rfl) ⟨7591623, by rfl⟩ : syracuseStep 20244329 = 15183247) B15183247
theorem B3901289 : Blo 1776089 3901289 := bstep (se 2 (by rfl) ⟨1462983, by rfl⟩ : syracuseStep 3901289 = 2925967) B2925967
theorem B41019281 : Blo 1776089 41019281 := bstep (se 2 (by rfl) ⟨15382230, by rfl⟩ : syracuseStep 41019281 = 30764461) B30764461
theorem B145934273 : Blo 1776089 145934273 := bstep (se 2 (by rfl) ⟨54725352, by rfl⟩ : syracuseStep 145934273 = 109450705) B109450705
theorem B7694369 : Blo 1776089 7694369 := bstep (se 2 (by rfl) ⟨2885388, by rfl⟩ : syracuseStep 7694369 = 5770777) B5770777
theorem B8996993 : Blo 1776089 8996993 := bstep (se 2 (by rfl) ⟨3373872, by rfl⟩ : syracuseStep 8996993 = 6747745) B6747745
theorem B6744329 : Blo 1776089 6744329 := bstep (se 2 (by rfl) ⟨2529123, by rfl⟩ : syracuseStep 6744329 = 5058247) B5058247
theorem B2664713 : Blo 1776089 2664713 := bstep (se 2 (by rfl) ⟨999267, by rfl⟩ : syracuseStep 2664713 = 1998535) B1998535
theorem B4557163 : Blo 1776089 4557163 := bstep (se 1 (by rfl) ⟨3417872, by rfl⟩ : syracuseStep 4557163 = 6835745) B6835745
theorem B2664815 : Blo 1776089 2664815 := bstep (se 1 (by rfl) ⟨1998611, by rfl⟩ : syracuseStep 2664815 = 3997223) B3997223
theorem B4000175 : Blo 1776089 4000175 := bstep (se 1 (by rfl) ⟨3000131, by rfl⟩ : syracuseStep 4000175 = 6000263) B6000263
theorem B4000211 : Blo 1776089 4000211 := bstep (se 1 (by rfl) ⟨3000158, by rfl⟩ : syracuseStep 4000211 = 6000317) B6000317
theorem B4000319 : Blo 1776089 4000319 := bstep (se 1 (by rfl) ⟨3000239, by rfl⟩ : syracuseStep 4000319 = 6000479) B6000479
theorem B2665031 : Blo 1776089 2665031 := bstep (se 1 (by rfl) ⟨1998773, by rfl⟩ : syracuseStep 2665031 = 3997547) B3997547
theorem B5999183 : Blo 1776089 5999183 := bstep (se 1 (by rfl) ⟨4499387, by rfl⟩ : syracuseStep 5999183 = 8998775) B8998775
theorem B2665067 : Blo 1776089 2665067 := bstep (se 1 (by rfl) ⟨1998800, by rfl⟩ : syracuseStep 2665067 = 3997601) B3997601
theorem B4000427 : Blo 1776089 4000427 := bstep (se 1 (by rfl) ⟨3000320, by rfl⟩ : syracuseStep 4000427 = 6000641) B6000641
theorem B2403119 : Blo 1776089 2403119 := bstep (se 1 (by rfl) ⟨1802339, by rfl⟩ : syracuseStep 2403119 = 3604679) B3604679
theorem B2665295 : Blo 1776089 2665295 := bstep (se 1 (by rfl) ⟨1998971, by rfl⟩ : syracuseStep 2665295 = 3997943) B3997943
theorem B8997803 : Blo 1776089 8997803 := bstep (se 1 (by rfl) ⟨6748352, by rfl⟩ : syracuseStep 8997803 = 13496705) B13496705
theorem B22768721 : Blo 1776089 22768721 := bstep (se 2 (by rfl) ⟨8538270, by rfl⟩ : syracuseStep 22768721 = 17076541) B17076541
theorem B4500623 : Blo 1776089 4500623 := bstep (se 1 (by rfl) ⟨3375467, by rfl⟩ : syracuseStep 4500623 = 6750935) B6750935
theorem B2665691 : Blo 1776089 2665691 := bstep (se 1 (by rfl) ⟨1999268, by rfl⟩ : syracuseStep 2665691 = 3998537) B3998537
theorem B72977645 : Blo 1776089 72977645 := bstep (se 3 (by rfl) ⟨13683308, by rfl⟩ : syracuseStep 72977645 = 27366617) B27366617
theorem B27741455 : Blo 1776089 27741455 := bstep (se 1 (by rfl) ⟨20806091, by rfl⟩ : syracuseStep 27741455 = 41612183) B41612183
theorem B2665865 : Blo 1776089 2665865 := bstep (se 2 (by rfl) ⟨999699, by rfl⟩ : syracuseStep 2665865 = 1999399) B1999399
theorem B7589335 : Blo 1776089 7589335 := bstep (se 1 (by rfl) ⟨5692001, by rfl⟩ : syracuseStep 7589335 = 11384003) B11384003
theorem B7589369 : Blo 1776089 7589369 := bstep (se 2 (by rfl) ⟨2846013, by rfl⟩ : syracuseStep 7589369 = 5692027) B5692027
theorem B2666219 : Blo 1776089 2666219 := bstep (se 1 (by rfl) ⟨1999664, by rfl⟩ : syracuseStep 2666219 = 3999329) B3999329
theorem B6000425 : Blo 1776089 6000425 := bstep (se 2 (by rfl) ⟨2250159, by rfl⟩ : syracuseStep 6000425 = 4500319) B4500319
theorem B12807983 : Blo 1776089 12807983 := bstep (se 1 (by rfl) ⟨9605987, by rfl⟩ : syracuseStep 12807983 = 19211975) B19211975
theorem B2666447 : Blo 1776089 2666447 := bstep (se 1 (by rfl) ⟨1999835, by rfl⟩ : syracuseStep 2666447 = 3999671) B3999671
theorem B2133991 : Blo 1776089 2133991 := bstep (se 1 (by rfl) ⟨1600493, by rfl⟩ : syracuseStep 2133991 = 3200987) B3200987
theorem B8998937 : Blo 1776089 8998937 := bstep (se 2 (by rfl) ⟨3374601, by rfl⟩ : syracuseStep 8998937 = 6749203) B6749203
theorem B2666843 : Blo 1776089 2666843 := bstep (se 1 (by rfl) ⟨2000132, by rfl⟩ : syracuseStep 2666843 = 4000265) B4000265
theorem B2667071 : Blo 1776089 2667071 := bstep (se 1 (by rfl) ⟨2000303, by rfl⟩ : syracuseStep 2667071 = 4000607) B4000607
theorem B9605729 : Blo 1776089 9605729 := bstep (se 2 (by rfl) ⟨3602148, by rfl⟩ : syracuseStep 9605729 = 7204297) B7204297
theorem B15184583 : Blo 1776089 15184583 := bstep (se 1 (by rfl) ⟨11388437, by rfl⟩ : syracuseStep 15184583 = 22776875) B22776875
theorem B2249527 : Blo 1776089 2249527 := bstep (se 1 (by rfl) ⟨1687145, by rfl⟩ : syracuseStep 2249527 = 3374291) B3374291
theorem B6837223 : Blo 1776089 6837223 := bstep (se 1 (by rfl) ⟨5127917, by rfl⟩ : syracuseStep 6837223 = 10255835) B10255835
theorem B7591009 : Blo 1776089 7591009 := bstep (se 2 (by rfl) ⟨2846628, by rfl⟩ : syracuseStep 7591009 = 5693257) B5693257
theorem B5690567 : Blo 1776089 5690567 := bstep (se 1 (by rfl) ⟨4267925, by rfl⟩ : syracuseStep 5690567 = 8535851) B8535851
theorem B17077463 : Blo 1776089 17077463 := bstep (se 1 (by rfl) ⟨12808097, by rfl⟩ : syracuseStep 17077463 = 25616195) B25616195
theorem B2249947 : Blo 1776089 2249947 := bstep (se 1 (by rfl) ⟨1687460, by rfl⟩ : syracuseStep 2249947 = 3374921) B3374921
theorem B5059979 : Blo 1776089 5059979 := bstep (se 1 (by rfl) ⟨3794984, by rfl⟩ : syracuseStep 5059979 = 7589969) B7589969
theorem B131511691 : Blo 1776089 131511691 := bstep (se 1 (by rfl) ⟨98633768, by rfl⟩ : syracuseStep 131511691 = 197267537) B197267537
theorem B9606637 : Blo 1776089 9606637 := bstep (se 3 (by rfl) ⟨1801244, by rfl⟩ : syracuseStep 9606637 = 3602489) B3602489
theorem B3372779 : Blo 1776089 3372779 := bstep (se 1 (by rfl) ⟨2529584, by rfl⟩ : syracuseStep 3372779 = 5059169) B5059169
theorem B449632301 : Blo 1776089 449632301 := bstep (se 3 (by rfl) ⟨84306056, by rfl⟩ : syracuseStep 449632301 = 168612113) B168612113
theorem B24311869 : Blo 1776089 24311869 := bstep (se 3 (by rfl) ⟨4558475, by rfl⟩ : syracuseStep 24311869 = 9116951) B9116951
theorem B13498649 : Blo 1776089 13498649 := bstep (se 2 (by rfl) ⟨5061993, by rfl⟩ : syracuseStep 13498649 = 10123987) B10123987
theorem B4561177 : Blo 1776089 4561177 := bstep (se 2 (by rfl) ⟨1710441, by rfl⟩ : syracuseStep 4561177 = 3420883) B3420883
theorem B5994863 : Blo 1776089 5994863 := bstep (se 1 (by rfl) ⟨4496147, by rfl⟩ : syracuseStep 5994863 = 8992295) B8992295
theorem B4495783 : Blo 1776089 4495783 := bstep (se 1 (by rfl) ⟨3371837, by rfl⟩ : syracuseStep 4495783 = 6743675) B6743675
theorem B3602855 : Blo 1776089 3602855 := bstep (se 1 (by rfl) ⟨2702141, by rfl⟩ : syracuseStep 3602855 = 5404283) B5404283
theorem B147921389 : Blo 1776089 147921389 := bstep (se 3 (by rfl) ⟨27735260, by rfl⟩ : syracuseStep 147921389 = 55470521) B55470521
theorem B8993267 : Blo 1776089 8993267 := bstep (se 1 (by rfl) ⟨6744950, by rfl⟩ : syracuseStep 8993267 = 13489901) B13489901
theorem B1776123 : Blo 1776089 1776123 := bstep (se 1 (by rfl) ⟨1332092, by rfl⟩ : syracuseStep 1776123 = 2664185) B2664185
theorem B14416379 : Blo 1776089 14416379 := bstep (se 1 (by rfl) ⟨10812284, by rfl⟩ : syracuseStep 14416379 = 21624569) B21624569
theorem B1776191 : Blo 1776089 1776191 := bstep (se 1 (by rfl) ⟨1332143, by rfl⟩ : syracuseStep 1776191 = 2664287) B2664287
theorem B1776199 : Blo 1776089 1776199 := bstep (se 1 (by rfl) ⟨1332149, by rfl⟩ : syracuseStep 1776199 = 2664299) B2664299
theorem B3996233 : Blo 1776089 3996233 := bstep (se 2 (by rfl) ⟨1498587, by rfl⟩ : syracuseStep 3996233 = 2997175) B2997175
theorem B4495945 : Blo 1776089 4495945 := bstep (se 2 (by rfl) ⟨1685979, by rfl⟩ : syracuseStep 4495945 = 3371959) B3371959
theorem B3373751 : Blo 1776089 3373751 := bstep (se 1 (by rfl) ⟨2530313, by rfl⟩ : syracuseStep 3373751 = 5060627) B5060627
theorem B1776351 : Blo 1776089 1776351 := bstep (se 1 (by rfl) ⟨1332263, by rfl⟩ : syracuseStep 1776351 = 2664527) B2664527
theorem B1776431 : Blo 1776089 1776431 := bstep (se 1 (by rfl) ⟨1332323, by rfl⟩ : syracuseStep 1776431 = 2664647) B2664647
theorem B3373903 : Blo 1776089 3373903 := bstep (se 1 (by rfl) ⟨2530427, by rfl⟩ : syracuseStep 3373903 = 5060855) B5060855
theorem B155876213 : Blo 1776089 155876213 := bstep (se 5 (by rfl) ⟨7306697, by rfl⟩ : syracuseStep 155876213 = 14613395) B14613395
theorem B1776539 : Blo 1776089 1776539 := bstep (se 1 (by rfl) ⟨1332404, by rfl⟩ : syracuseStep 1776539 = 2664809) B2664809
theorem B12327835 : Blo 1776089 12327835 := bstep (se 1 (by rfl) ⟨9245876, by rfl⟩ : syracuseStep 12327835 = 18491753) B18491753
theorem B1776591 : Blo 1776089 1776591 := bstep (se 1 (by rfl) ⟨1332443, by rfl⟩ : syracuseStep 1776591 = 2664887) B2664887
theorem B3996647 : Blo 1776089 3996647 := bstep (se 1 (by rfl) ⟨2997485, by rfl⟩ : syracuseStep 3996647 = 5994971) B5994971
theorem B1776615 : Blo 1776089 1776615 := bstep (se 1 (by rfl) ⟨1332461, by rfl⟩ : syracuseStep 1776615 = 2664923) B2664923
theorem B8993915 : Blo 1776089 8993915 := bstep (se 1 (by rfl) ⟨6745436, by rfl⟩ : syracuseStep 8993915 = 13490873) B13490873
theorem B2997391 : Blo 1776089 2997391 := bstep (se 1 (by rfl) ⟨2248043, by rfl⟩ : syracuseStep 2997391 = 4496087) B4496087
theorem B13499621 : Blo 1776089 13499621 := bstep (se 4 (by rfl) ⟨1265589, by rfl⟩ : syracuseStep 13499621 = 2531179) B2531179
theorem B1776927 : Blo 1776089 1776927 := bstep (se 1 (by rfl) ⟨1332695, by rfl⟩ : syracuseStep 1776927 = 2665391) B2665391
theorem B6749507 : Blo 1776089 6749507 := bstep (se 1 (by rfl) ⟨5062130, by rfl⟩ : syracuseStep 6749507 = 10124261) B10124261
theorem B1776987 : Blo 1776089 1776987 := bstep (se 1 (by rfl) ⟨1332740, by rfl⟩ : syracuseStep 1776987 = 2665481) B2665481
theorem B4496735 : Blo 1776089 4496735 := bstep (se 1 (by rfl) ⟨3372551, by rfl⟩ : syracuseStep 4496735 = 6745103) B6745103
theorem B3997025 : Blo 1776089 3997025 := bstep (se 2 (by rfl) ⟨1498884, by rfl⟩ : syracuseStep 3997025 = 2997769) B2997769
theorem B1777007 : Blo 1776089 1777007 := bstep (se 1 (by rfl) ⟨1332755, by rfl⟩ : syracuseStep 1777007 = 2665511) B2665511
theorem B2997641 : Blo 1776089 2997641 := bstep (se 2 (by rfl) ⟨1124115, by rfl⟩ : syracuseStep 2997641 = 2248231) B2248231
theorem B3374473 : Blo 1776089 3374473 := bstep (se 2 (by rfl) ⟨1265427, by rfl⟩ : syracuseStep 3374473 = 2530855) B2530855
theorem B1998247 : Blo 1776089 1998247 := bstep (se 1 (by rfl) ⟨1498685, by rfl⟩ : syracuseStep 1998247 = 2997371) B2997371
theorem B1777063 : Blo 1776089 1777063 := bstep (se 1 (by rfl) ⟨1332797, by rfl⟩ : syracuseStep 1777063 = 2665595) B2665595
theorem B3997115 : Blo 1776089 3997115 := bstep (se 1 (by rfl) ⟨2997836, by rfl⟩ : syracuseStep 3997115 = 5995673) B5995673
theorem B6749689 : Blo 1776089 6749689 := bstep (se 2 (by rfl) ⟨2531133, by rfl⟩ : syracuseStep 6749689 = 5062267) B5062267
theorem B1777147 : Blo 1776089 1777147 := bstep (se 1 (by rfl) ⟨1332860, by rfl⟩ : syracuseStep 1777147 = 2665721) B2665721
theorem B3997241 : Blo 1776089 3997241 := bstep (se 2 (by rfl) ⟨1498965, by rfl⟩ : syracuseStep 3997241 = 2997931) B2997931
theorem B1777215 : Blo 1776089 1777215 := bstep (se 1 (by rfl) ⟨1332911, by rfl⟩ : syracuseStep 1777215 = 2665823) B2665823
theorem B1777223 : Blo 1776089 1777223 := bstep (se 1 (by rfl) ⟨1332917, by rfl⟩ : syracuseStep 1777223 = 2665835) B2665835
theorem B17079923 : Blo 1776089 17079923 := bstep (se 1 (by rfl) ⟨12809942, by rfl⟩ : syracuseStep 17079923 = 25619885) B25619885
theorem B1777375 : Blo 1776089 1777375 := bstep (se 1 (by rfl) ⟨1333031, by rfl⟩ : syracuseStep 1777375 = 2666063) B2666063
theorem B5996267 : Blo 1776089 5996267 := bstep (se 1 (by rfl) ⟨4497200, by rfl⟩ : syracuseStep 5996267 = 8994401) B8994401
theorem B8994563 : Blo 1776089 8994563 := bstep (se 1 (by rfl) ⟨6745922, by rfl⟩ : syracuseStep 8994563 = 13491845) B13491845
theorem B6749963 : Blo 1776089 6749963 := bstep (se 1 (by rfl) ⟨5062472, by rfl⟩ : syracuseStep 6749963 = 10124945) B10124945
theorem B6749993 : Blo 1776089 6749993 := bstep (se 2 (by rfl) ⟨2531247, by rfl⟩ : syracuseStep 6749993 = 5062495) B5062495
theorem B1777455 : Blo 1776089 1777455 := bstep (se 1 (by rfl) ⟨1333091, by rfl⟩ : syracuseStep 1777455 = 2666183) B2666183
theorem B2998073 : Blo 1776089 2998073 := bstep (se 2 (by rfl) ⟨1124277, by rfl⟩ : syracuseStep 2998073 = 2248555) B2248555
theorem B10116971 : Blo 1776089 10116971 := bstep (se 1 (by rfl) ⟨7587728, by rfl⟩ : syracuseStep 10116971 = 15175457) B15175457
theorem B1777563 : Blo 1776089 1777563 := bstep (se 1 (by rfl) ⟨1333172, by rfl⟩ : syracuseStep 1777563 = 2666345) B2666345
theorem B1777615 : Blo 1776089 1777615 := bstep (se 1 (by rfl) ⟨1333211, by rfl⟩ : syracuseStep 1777615 = 2666423) B2666423
theorem B1998823 : Blo 1776089 1998823 := bstep (se 1 (by rfl) ⟨1499117, by rfl⟩ : syracuseStep 1998823 = 2998235) B2998235
theorem B1777639 : Blo 1776089 1777639 := bstep (se 1 (by rfl) ⟨1333229, by rfl⟩ : syracuseStep 1777639 = 2666459) B2666459
theorem B1777895 : Blo 1776089 1777895 := bstep (se 1 (by rfl) ⟨1333421, by rfl⟩ : syracuseStep 1777895 = 2666843) B2666843
theorem B2998559 : Blo 1776089 2998559 := bstep (se 1 (by rfl) ⟨2248919, by rfl⟩ : syracuseStep 2998559 = 4497839) B4497839
theorem B129663301 : Blo 1776089 129663301 := bstep (se 4 (by rfl) ⟨12155934, by rfl⟩ : syracuseStep 129663301 = 24311869) B24311869
theorem B1778047 : Blo 1776089 1778047 := bstep (se 1 (by rfl) ⟨1333535, by rfl⟩ : syracuseStep 1778047 = 2667071) B2667071
theorem B6750647 : Blo 1776089 6750647 := bstep (se 1 (by rfl) ⟨5062985, by rfl⟩ : syracuseStep 6750647 = 10125971) B10125971
theorem B5063111 : Blo 1776089 5063111 := bstep (se 1 (by rfl) ⟨3797333, by rfl⟩ : syracuseStep 5063111 = 7594667) B7594667
theorem B3998159 : Blo 1776089 3998159 := bstep (se 1 (by rfl) ⟨2998619, by rfl⟩ : syracuseStep 3998159 = 5997239) B5997239
theorem B5997185 : Blo 1776089 5997185 := bstep (se 2 (by rfl) ⟨2248944, by rfl⟩ : syracuseStep 5997185 = 4497889) B4497889
theorem B17072815 : Blo 1776089 17072815 := bstep (se 1 (by rfl) ⟨12804611, by rfl⟩ : syracuseStep 17072815 = 25609223) B25609223
theorem B3793711 : Blo 1776089 3793711 := bstep (se 1 (by rfl) ⟨2845283, by rfl⟩ : syracuseStep 3793711 = 5690567) B5690567
theorem B5997455 : Blo 1776089 5997455 := bstep (se 1 (by rfl) ⟨4498091, by rfl⟩ : syracuseStep 5997455 = 8996183) B8996183
theorem B6751133 : Blo 1776089 6751133 := bstep (se 3 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 6751133 = 2531675) B2531675
theorem B4326311 : Blo 1776089 4326311 := bstep (se 1 (by rfl) ⟨3244733, by rfl⟩ : syracuseStep 4326311 = 6489467) B6489467
theorem B2999207 : Blo 1776089 2999207 := bstep (se 1 (by rfl) ⟨2249405, by rfl⟩ : syracuseStep 2999207 = 4498811) B4498811
theorem B1999867 : Blo 1776089 1999867 := bstep (se 1 (by rfl) ⟨1499900, by rfl⟩ : syracuseStep 1999867 = 2999801) B2999801
theorem B2999369 : Blo 1776089 2999369 := bstep (se 2 (by rfl) ⟨1124763, by rfl⟩ : syracuseStep 2999369 = 2249527) B2249527
theorem B4498537 : Blo 1776089 4498537 := bstep (se 2 (by rfl) ⟨1686951, by rfl⟩ : syracuseStep 4498537 = 3373903) B3373903
theorem B3998825 : Blo 1776089 3998825 := bstep (se 2 (by rfl) ⟨1499559, by rfl⟩ : syracuseStep 3998825 = 2999119) B2999119
theorem B13501565 : Blo 1776089 13501565 := bstep (se 3 (by rfl) ⟨2531543, by rfl⟩ : syracuseStep 13501565 = 5063087) B5063087
theorem B2000047 : Blo 1776089 2000047 := bstep (se 1 (by rfl) ⟨1500035, by rfl⟩ : syracuseStep 2000047 = 3000071) B3000071
theorem B27346187 : Blo 1776089 27346187 := bstep (se 1 (by rfl) ⟨20509640, by rfl⟩ : syracuseStep 27346187 = 41019281) B41019281
theorem B97289515 : Blo 1776089 97289515 := bstep (se 1 (by rfl) ⟨72967136, by rfl⟩ : syracuseStep 97289515 = 145934273) B145934273
theorem B5129579 : Blo 1776089 5129579 := bstep (se 1 (by rfl) ⟨3847184, by rfl⟩ : syracuseStep 5129579 = 7694369) B7694369
theorem B5997995 : Blo 1776089 5997995 := bstep (se 1 (by rfl) ⟨4498496, by rfl⟩ : syracuseStep 5997995 = 8996993) B8996993
theorem B2401903 : Blo 1776089 2401903 := bstep (se 1 (by rfl) ⟨1801427, by rfl⟩ : syracuseStep 2401903 = 3602855) B3602855
theorem B2999929 : Blo 1776089 2999929 := bstep (se 2 (by rfl) ⟨1124973, by rfl⟩ : syracuseStep 2999929 = 2249947) B2249947
theorem B9610919 : Blo 1776089 9610919 := bstep (se 1 (by rfl) ⟨7208189, by rfl⟩ : syracuseStep 9610919 = 14416379) B14416379
theorem B2664155 : Blo 1776089 2664155 := bstep (se 1 (by rfl) ⟨1998116, by rfl⟩ : syracuseStep 2664155 = 3996233) B3996233
theorem B3999455 : Blo 1776089 3999455 := bstep (se 1 (by rfl) ⟨2999591, by rfl⟩ : syracuseStep 3999455 = 5999183) B5999183
theorem B8996669 : Blo 1776089 8996669 := bstep (se 3 (by rfl) ⟨1686875, by rfl⟩ : syracuseStep 8996669 = 3373751) B3373751
theorem B4499297 : Blo 1776089 4499297 := bstep (se 2 (by rfl) ⟨1687236, by rfl⟩ : syracuseStep 4499297 = 3374473) B3374473
theorem B2664329 : Blo 1776089 2664329 := bstep (se 2 (by rfl) ⟨999123, by rfl⟩ : syracuseStep 2664329 = 1998247) B1998247
theorem B103917475 : Blo 1776089 103917475 := bstep (se 1 (by rfl) ⟨77938106, by rfl⟩ : syracuseStep 103917475 = 155876213) B155876213
theorem B5998535 : Blo 1776089 5998535 := bstep (se 1 (by rfl) ⟨4498901, by rfl⟩ : syracuseStep 5998535 = 8997803) B8997803
theorem B10119113 : Blo 1776089 10119113 := bstep (se 2 (by rfl) ⟨3794667, by rfl⟩ : syracuseStep 10119113 = 7589335) B7589335
theorem B2664431 : Blo 1776089 2664431 := bstep (se 1 (by rfl) ⟨1998323, by rfl⟩ : syracuseStep 2664431 = 3996647) B3996647
theorem B3000415 : Blo 1776089 3000415 := bstep (se 1 (by rfl) ⟨2250311, by rfl⟩ : syracuseStep 3000415 = 4500623) B4500623
theorem B34154621 : Blo 1776089 34154621 := bstep (se 3 (by rfl) ⟨6403991, by rfl⟩ : syracuseStep 34154621 = 12807983) B12807983
theorem B6408317 : Blo 1776089 6408317 := bstep (se 3 (by rfl) ⟨1201559, by rfl⟩ : syracuseStep 6408317 = 2403119) B2403119
theorem B4499671 : Blo 1776089 4499671 := bstep (se 1 (by rfl) ⟨3374753, by rfl⟩ : syracuseStep 4499671 = 6749507) B6749507
theorem B2664683 : Blo 1776089 2664683 := bstep (se 1 (by rfl) ⟨1998512, by rfl⟩ : syracuseStep 2664683 = 3997025) B3997025
theorem B2664743 : Blo 1776089 2664743 := bstep (se 1 (by rfl) ⟨1998557, by rfl⟩ : syracuseStep 2664743 = 3997115) B3997115
theorem B2664827 : Blo 1776089 2664827 := bstep (se 1 (by rfl) ⟨1998620, by rfl⟩ : syracuseStep 2664827 = 3997241) B3997241
theorem B92375477 : Blo 1776089 92375477 := bstep (se 5 (by rfl) ⟨4330100, by rfl⟩ : syracuseStep 92375477 = 8660201) B8660201
theorem B4499975 : Blo 1776089 4499975 := bstep (se 1 (by rfl) ⟨3374981, by rfl⟩ : syracuseStep 4499975 = 6749963) B6749963
theorem B4499995 : Blo 1776089 4499995 := bstep (se 1 (by rfl) ⟨3374996, by rfl⟩ : syracuseStep 4499995 = 6749993) B6749993
theorem B4000283 : Blo 1776089 4000283 := bstep (se 1 (by rfl) ⟨3000212, by rfl⟩ : syracuseStep 4000283 = 6000425) B6000425
theorem B11381285 : Blo 1776089 11381285 := bstep (se 4 (by rfl) ⟨1066995, by rfl⟩ : syracuseStep 11381285 = 2133991) B2133991
theorem B6744647 : Blo 1776089 6744647 := bstep (se 1 (by rfl) ⟨5058485, by rfl⟩ : syracuseStep 6744647 = 10116971) B10116971
theorem B2665097 : Blo 1776089 2665097 := bstep (se 2 (by rfl) ⟨999411, by rfl⟩ : syracuseStep 2665097 = 1998823) B1998823
theorem B5999291 : Blo 1776089 5999291 := bstep (se 1 (by rfl) ⟨4499468, by rfl⟩ : syracuseStep 5999291 = 8998937) B8998937
theorem B2665271 : Blo 1776089 2665271 := bstep (se 1 (by rfl) ⟨1998953, by rfl⟩ : syracuseStep 2665271 = 3997907) B3997907
theorem B2665307 : Blo 1776089 2665307 := bstep (se 1 (by rfl) ⟨1998980, by rfl⟩ : syracuseStep 2665307 = 3997961) B3997961
theorem B2665451 : Blo 1776089 2665451 := bstep (se 1 (by rfl) ⟨1999088, by rfl⟩ : syracuseStep 2665451 = 3998177) B3998177
theorem B12807175 : Blo 1776089 12807175 := bstep (se 1 (by rfl) ⟨9605381, by rfl⟩ : syracuseStep 12807175 = 19210763) B19210763
theorem B6081569 : Blo 1776089 6081569 := bstep (se 2 (by rfl) ⟨2280588, by rfl⟩ : syracuseStep 6081569 = 4561177) B4561177
theorem B2665655 : Blo 1776089 2665655 := bstep (se 1 (by rfl) ⟨1999241, by rfl⟩ : syracuseStep 2665655 = 3998483) B3998483
theorem B12807467 : Blo 1776089 12807467 := bstep (se 1 (by rfl) ⟨9605600, by rfl⟩ : syracuseStep 12807467 = 19211201) B19211201
theorem B2665895 : Blo 1776089 2665895 := bstep (se 1 (by rfl) ⟨1999421, by rfl⟩ : syracuseStep 2665895 = 3998843) B3998843
theorem B16215511 : Blo 1776089 16215511 := bstep (se 1 (by rfl) ⟨12161633, by rfl⟩ : syracuseStep 16215511 = 24323267) B24323267
theorem B2665979 : Blo 1776089 2665979 := bstep (se 1 (by rfl) ⟨1999484, by rfl⟩ : syracuseStep 2665979 = 3998969) B3998969
theorem B5058121 : Blo 1776089 5058121 := bstep (se 2 (by rfl) ⟨1896795, by rfl⟩ : syracuseStep 5058121 = 3793591) B3793591
theorem B2666075 : Blo 1776089 2666075 := bstep (se 1 (by rfl) ⟨1999556, by rfl⟩ : syracuseStep 2666075 = 3999113) B3999113
theorem B15183521 : Blo 1776089 15183521 := bstep (se 2 (by rfl) ⟨5693820, by rfl⟩ : syracuseStep 15183521 = 11387641) B11387641
theorem B2666159 : Blo 1776089 2666159 := bstep (se 1 (by rfl) ⟨1999619, by rfl⟩ : syracuseStep 2666159 = 3999239) B3999239
theorem B2666279 : Blo 1776089 2666279 := bstep (se 1 (by rfl) ⟨1999709, by rfl⟩ : syracuseStep 2666279 = 3999419) B3999419
theorem B16437113 : Blo 1776089 16437113 := bstep (se 2 (by rfl) ⟨6163917, by rfl⟩ : syracuseStep 16437113 = 12327835) B12327835
theorem B2666363 : Blo 1776089 2666363 := bstep (se 1 (by rfl) ⟨1999772, by rfl⟩ : syracuseStep 2666363 = 3999545) B3999545
theorem B13496219 : Blo 1776089 13496219 := bstep (se 1 (by rfl) ⟨10122164, by rfl⟩ : syracuseStep 13496219 = 20244329) B20244329
theorem B10121345 : Blo 1776089 10121345 := bstep (se 2 (by rfl) ⟨3795504, by rfl⟩ : syracuseStep 10121345 = 7591009) B7591009
theorem B8999099 : Blo 1776089 8999099 := bstep (se 1 (by rfl) ⟨6749324, by rfl⟩ : syracuseStep 8999099 = 13498649) B13498649
theorem B2666783 : Blo 1776089 2666783 := bstep (se 1 (by rfl) ⟨2000087, by rfl⟩ : syracuseStep 2666783 = 4000175) B4000175
theorem B2666807 : Blo 1776089 2666807 := bstep (se 1 (by rfl) ⟨2000105, by rfl⟩ : syracuseStep 2666807 = 4000211) B4000211
theorem B2666879 : Blo 1776089 2666879 := bstep (se 1 (by rfl) ⟨2000159, by rfl⟩ : syracuseStep 2666879 = 4000319) B4000319
theorem B2666951 : Blo 1776089 2666951 := bstep (se 1 (by rfl) ⟨2000213, by rfl⟩ : syracuseStep 2666951 = 4000427) B4000427
theorem B12808849 : Blo 1776089 12808849 := bstep (se 2 (by rfl) ⟨4803318, by rfl⟩ : syracuseStep 12808849 = 9606637) B9606637
theorem B8999585 : Blo 1776089 8999585 := bstep (se 2 (by rfl) ⟨3374844, by rfl⟩ : syracuseStep 8999585 = 6749689) B6749689
theorem B11383517 : Blo 1776089 11383517 := bstep (se 3 (by rfl) ⟨2134409, by rfl⟩ : syracuseStep 11383517 = 4268819) B4268819
theorem B8999747 : Blo 1776089 8999747 := bstep (se 1 (by rfl) ⟨6749810, by rfl⟩ : syracuseStep 8999747 = 13499621) B13499621
theorem B18494303 : Blo 1776089 18494303 := bstep (se 1 (by rfl) ⟨13870727, by rfl⟩ : syracuseStep 18494303 = 27741455) B27741455
theorem B5059579 : Blo 1776089 5059579 := bstep (se 1 (by rfl) ⟨3794684, by rfl⟩ : syracuseStep 5059579 = 7589369) B7589369
theorem B1199019469 : Blo 1776089 1199019469 := bstep (se 3 (by rfl) ⟨224816150, by rfl⟩ : syracuseStep 1199019469 = 449632301) B449632301
theorem B5690951 : Blo 1776089 5690951 := bstep (se 1 (by rfl) ⟨4268213, by rfl⟩ : syracuseStep 5690951 = 8536427) B8536427
theorem B9000557 : Blo 1776089 9000557 := bstep (se 3 (by rfl) ⟨1687604, by rfl⟩ : syracuseStep 9000557 = 3375209) B3375209
theorem B6403819 : Blo 1776089 6403819 := bstep (se 1 (by rfl) ⟨4802864, by rfl⟩ : syracuseStep 6403819 = 9605729) B9605729
theorem B9606923 : Blo 1776089 9606923 := bstep (se 1 (by rfl) ⟨7205192, by rfl⟩ : syracuseStep 9606923 = 14410385) B14410385
theorem B10123055 : Blo 1776089 10123055 := bstep (se 1 (by rfl) ⟨7592291, by rfl⟩ : syracuseStep 10123055 = 15184583) B15184583
theorem B6076217 : Blo 1776089 6076217 := bstep (se 2 (by rfl) ⟨2278581, by rfl⟩ : syracuseStep 6076217 = 4557163) B4557163
theorem B5994377 : Blo 1776089 5994377 := bstep (se 2 (by rfl) ⟨2247891, by rfl⟩ : syracuseStep 5994377 = 4495783) B4495783
theorem B18241631 : Blo 1776089 18241631 := bstep (se 1 (by rfl) ⟨13681223, by rfl⟩ : syracuseStep 18241631 = 27362447) B27362447
theorem B5994593 : Blo 1776089 5994593 := bstep (se 2 (by rfl) ⟨2247972, by rfl⟩ : syracuseStep 5994593 = 4495945) B4495945
theorem B11384975 : Blo 1776089 11384975 := bstep (se 1 (by rfl) ⟨8538731, by rfl⟩ : syracuseStep 11384975 = 17077463) B17077463
theorem B3373319 : Blo 1776089 3373319 := bstep (se 1 (by rfl) ⟨2529989, by rfl⟩ : syracuseStep 3373319 = 5059979) B5059979
theorem B12802333 : Blo 1776089 12802333 := bstep (se 3 (by rfl) ⟨2400437, by rfl⟩ : syracuseStep 12802333 = 4800875) B4800875
theorem B41613749 : Blo 1776089 41613749 := bstep (se 5 (by rfl) ⟨1950644, by rfl⟩ : syracuseStep 41613749 = 3901289) B3901289
theorem B1776155 : Blo 1776089 1776155 := bstep (se 1 (by rfl) ⟨1332116, by rfl⟩ : syracuseStep 1776155 = 2664233) B2664233
theorem B1776159 : Blo 1776089 1776159 := bstep (se 1 (by rfl) ⟨1332119, by rfl⟩ : syracuseStep 1776159 = 2664239) B2664239
theorem B14604889 : Blo 1776089 14604889 := bstep (se 2 (by rfl) ⟨5476833, by rfl⟩ : syracuseStep 14604889 = 10953667) B10953667
theorem B9116297 : Blo 1776089 9116297 := bstep (se 2 (by rfl) ⟨3418611, by rfl⟩ : syracuseStep 9116297 = 6837223) B6837223
theorem B4496219 : Blo 1776089 4496219 := bstep (se 1 (by rfl) ⟨3372164, by rfl⟩ : syracuseStep 4496219 = 6744329) B6744329
theorem B1776475 : Blo 1776089 1776475 := bstep (se 1 (by rfl) ⟨1332356, by rfl⟩ : syracuseStep 1776475 = 2664713) B2664713
theorem B3996521 : Blo 1776089 3996521 := bstep (se 2 (by rfl) ⟨1498695, by rfl⟩ : syracuseStep 3996521 = 2997391) B2997391
theorem B3996575 : Blo 1776089 3996575 := bstep (se 1 (by rfl) ⟨2997431, by rfl⟩ : syracuseStep 3996575 = 5994863) B5994863
theorem B1776543 : Blo 1776089 1776543 := bstep (se 1 (by rfl) ⟨1332407, by rfl⟩ : syracuseStep 1776543 = 2664815) B2664815
theorem B45546461 : Blo 1776089 45546461 := bstep (se 3 (by rfl) ⟨8539961, by rfl⟩ : syracuseStep 45546461 = 17079923) B17079923
theorem B98614259 : Blo 1776089 98614259 := bstep (se 1 (by rfl) ⟨73960694, by rfl⟩ : syracuseStep 98614259 = 147921389) B147921389
theorem B5995511 : Blo 1776089 5995511 := bstep (se 1 (by rfl) ⟨4496633, by rfl⟩ : syracuseStep 5995511 = 8993267) B8993267
theorem B1776687 : Blo 1776089 1776687 := bstep (se 1 (by rfl) ⟨1332515, by rfl⟩ : syracuseStep 1776687 = 2665031) B2665031
theorem B7691321 : Blo 1776089 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B1776711 : Blo 1776089 1776711 := bstep (se 1 (by rfl) ⟨1332533, by rfl⟩ : syracuseStep 1776711 = 2665067) B2665067
theorem B175348921 : Blo 1776089 175348921 := bstep (se 2 (by rfl) ⟨65755845, by rfl⟩ : syracuseStep 175348921 = 131511691) B131511691
theorem B1776863 : Blo 1776089 1776863 := bstep (se 1 (by rfl) ⟨1332647, by rfl⟩ : syracuseStep 1776863 = 2665295) B2665295
theorem B3202313 : Blo 1776089 3202313 := bstep (se 2 (by rfl) ⟨1200867, by rfl⟩ : syracuseStep 3202313 = 2401735) B2401735
theorem B8994077 : Blo 1776089 8994077 := bstep (se 3 (by rfl) ⟨1686389, by rfl⟩ : syracuseStep 8994077 = 3372779) B3372779
theorem B15179147 : Blo 1776089 15179147 := bstep (se 1 (by rfl) ⟨11384360, by rfl⟩ : syracuseStep 15179147 = 22768721) B22768721
theorem B5995943 : Blo 1776089 5995943 := bstep (se 1 (by rfl) ⟨4496957, by rfl⟩ : syracuseStep 5995943 = 8993915) B8993915
theorem B1777127 : Blo 1776089 1777127 := bstep (se 1 (by rfl) ⟨1332845, by rfl⟩ : syracuseStep 1777127 = 2665691) B2665691
theorem B48651763 : Blo 1776089 48651763 := bstep (se 1 (by rfl) ⟨36488822, by rfl⟩ : syracuseStep 48651763 = 72977645) B72977645
theorem B2997823 : Blo 1776089 2997823 := bstep (se 1 (by rfl) ⟨2248367, by rfl⟩ : syracuseStep 2997823 = 4496735) B4496735
theorem B1998427 : Blo 1776089 1998427 := bstep (se 1 (by rfl) ⟨1498820, by rfl⟩ : syracuseStep 1998427 = 2997641) B2997641
theorem B1777243 : Blo 1776089 1777243 := bstep (se 1 (by rfl) ⟨1332932, by rfl⟩ : syracuseStep 1777243 = 2665865) B2665865
theorem B3997511 : Blo 1776089 3997511 := bstep (se 1 (by rfl) ⟨2998133, by rfl⟩ : syracuseStep 3997511 = 5996267) B5996267
theorem B1777479 : Blo 1776089 1777479 := bstep (se 1 (by rfl) ⟨1333109, by rfl⟩ : syracuseStep 1777479 = 2666219) B2666219
theorem B5996375 : Blo 1776089 5996375 := bstep (se 1 (by rfl) ⟨4497281, by rfl⟩ : syracuseStep 5996375 = 8994563) B8994563
theorem B1998715 : Blo 1776089 1998715 := bstep (se 1 (by rfl) ⟨1499036, by rfl⟩ : syracuseStep 1998715 = 2998073) B2998073
theorem B1777631 : Blo 1776089 1777631 := bstep (se 1 (by rfl) ⟨1333223, by rfl⟩ : syracuseStep 1777631 = 2666447) B2666447
theorem B1999039 : Blo 1776089 1999039 := bstep (se 1 (by rfl) ⟨1499279, by rfl⟩ : syracuseStep 1999039 = 2998559) B2998559
theorem B1777855 : Blo 1776089 1777855 := bstep (se 1 (by rfl) ⟨1333391, by rfl⟩ : syracuseStep 1777855 = 2666783) B2666783
theorem B1777871 : Blo 1776089 1777871 := bstep (se 1 (by rfl) ⟨1333403, by rfl⟩ : syracuseStep 1777871 = 2666807) B2666807
theorem B1777919 : Blo 1776089 1777919 := bstep (se 1 (by rfl) ⟨1333439, by rfl⟩ : syracuseStep 1777919 = 2666879) B2666879
theorem B1777967 : Blo 1776089 1777967 := bstep (se 1 (by rfl) ⟨1333475, by rfl⟩ : syracuseStep 1777967 = 2666951) B2666951
theorem B3375407 : Blo 1776089 3375407 := bstep (se 1 (by rfl) ⟨2531555, by rfl⟩ : syracuseStep 3375407 = 5063111) B5063111
theorem B30359933 : Blo 1776089 30359933 := bstep (se 3 (by rfl) ⟨5692487, by rfl⟩ : syracuseStep 30359933 = 11384975) B11384975
theorem B3998123 : Blo 1776089 3998123 := bstep (se 1 (by rfl) ⟨2998592, by rfl⟩ : syracuseStep 3998123 = 5997185) B5997185
theorem B172884401 : Blo 1776089 172884401 := bstep (se 2 (by rfl) ⟨64831650, by rfl⟩ : syracuseStep 172884401 = 129663301) B129663301
theorem B3998303 : Blo 1776089 3998303 := bstep (se 1 (by rfl) ⟨2998727, by rfl⟩ : syracuseStep 3998303 = 5997455) B5997455
theorem B1999471 : Blo 1776089 1999471 := bstep (se 1 (by rfl) ⟨1499603, by rfl⟩ : syracuseStep 1999471 = 2999207) B2999207
theorem B1999579 : Blo 1776089 1999579 := bstep (se 1 (by rfl) ⟨1499684, by rfl⟩ : syracuseStep 1999579 = 2999369) B2999369
theorem B19473185 : Blo 1776089 19473185 := bstep (se 2 (by rfl) ⟨7302444, by rfl⟩ : syracuseStep 19473185 = 14604889) B14604889
theorem B3998663 : Blo 1776089 3998663 := bstep (se 1 (by rfl) ⟨2998997, by rfl⟩ : syracuseStep 3998663 = 5997995) B5997995
theorem B3793967 : Blo 1776089 3793967 := bstep (se 1 (by rfl) ⟨2845475, by rfl⟩ : syracuseStep 3793967 = 5690951) B5690951
theorem B6407279 : Blo 1776089 6407279 := bstep (se 1 (by rfl) ⟨4805459, by rfl⟩ : syracuseStep 6407279 = 9610919) B9610919
theorem B5997779 : Blo 1776089 5997779 := bstep (se 1 (by rfl) ⟨4498334, by rfl⟩ : syracuseStep 5997779 = 8996669) B8996669
theorem B2999531 : Blo 1776089 2999531 := bstep (se 1 (by rfl) ⟨2249648, by rfl⟩ : syracuseStep 2999531 = 4499297) B4499297
theorem B3999023 : Blo 1776089 3999023 := bstep (se 1 (by rfl) ⟨2999267, by rfl⟩ : syracuseStep 3999023 = 5998535) B5998535
theorem B5998049 : Blo 1776089 5998049 := bstep (se 2 (by rfl) ⟨2249268, by rfl⟩ : syracuseStep 5998049 = 4498537) B4498537
theorem B2999983 : Blo 1776089 2999983 := bstep (se 1 (by rfl) ⟨2249987, by rfl⟩ : syracuseStep 2999983 = 4499975) B4499975
theorem B7587523 : Blo 1776089 7587523 := bstep (se 1 (by rfl) ⟨5690642, by rfl⟩ : syracuseStep 7587523 = 11381285) B11381285
theorem B3999527 : Blo 1776089 3999527 := bstep (se 1 (by rfl) ⟨2999645, by rfl⟩ : syracuseStep 3999527 = 5999291) B5999291
theorem B2664347 : Blo 1776089 2664347 := bstep (se 1 (by rfl) ⟨1998260, by rfl⟩ : syracuseStep 2664347 = 3996521) B3996521
theorem B2664383 : Blo 1776089 2664383 := bstep (se 1 (by rfl) ⟨1998287, by rfl⟩ : syracuseStep 2664383 = 3996575) B3996575
theorem B21620681 : Blo 1776089 21620681 := bstep (se 2 (by rfl) ⟨8107755, by rfl⟩ : syracuseStep 21620681 = 16215511) B16215511
theorem B65742839 : Blo 1776089 65742839 := bstep (se 1 (by rfl) ⟨49307129, by rfl⟩ : syracuseStep 65742839 = 98614259) B98614259
theorem B6744161 : Blo 1776089 6744161 := bstep (se 2 (by rfl) ⟨2529060, by rfl⟩ : syracuseStep 6744161 = 5058121) B5058121
theorem B2664569 : Blo 1776089 2664569 := bstep (se 2 (by rfl) ⟨999213, by rfl⟩ : syracuseStep 2664569 = 1998427) B1998427
theorem B3999905 : Blo 1776089 3999905 := bstep (se 2 (by rfl) ⟨1499964, by rfl⟩ : syracuseStep 3999905 = 2999929) B2999929
theorem B8538311 : Blo 1776089 8538311 := bstep (se 1 (by rfl) ⟨6403733, by rfl⟩ : syracuseStep 8538311 = 12807467) B12807467
theorem B49318141 : Blo 1776089 49318141 := bstep (se 3 (by rfl) ⟨9247151, by rfl⟩ : syracuseStep 49318141 = 18494303) B18494303
theorem B10119431 : Blo 1776089 10119431 := bstep (se 1 (by rfl) ⟨7589573, by rfl⟩ : syracuseStep 10119431 = 15179147) B15179147
theorem B8538425 : Blo 1776089 8538425 := bstep (se 2 (by rfl) ⟨3201909, by rfl⟩ : syracuseStep 8538425 = 6403819) B6403819
theorem B11536829 : Blo 1776089 11536829 := bstep (se 3 (by rfl) ⟨2163155, by rfl⟩ : syracuseStep 11536829 = 4326311) B4326311
theorem B2664953 : Blo 1776089 2664953 := bstep (se 2 (by rfl) ⟨999357, by rfl⟩ : syracuseStep 2664953 = 1998715) B1998715
theorem B2665007 : Blo 1776089 2665007 := bstep (se 1 (by rfl) ⟨1998755, by rfl⟩ : syracuseStep 2665007 = 3997511) B3997511
theorem B8997479 : Blo 1776089 8997479 := bstep (se 1 (by rfl) ⟨6748109, by rfl⟩ : syracuseStep 8997479 = 13496219) B13496219
theorem B5999399 : Blo 1776089 5999399 := bstep (se 1 (by rfl) ⟨4499549, by rfl⟩ : syracuseStep 5999399 = 8999099) B8999099
theorem B4000553 : Blo 1776089 4000553 := bstep (se 2 (by rfl) ⟨1500207, by rfl⟩ : syracuseStep 4000553 = 3000415) B3000415
theorem B5999561 : Blo 1776089 5999561 := bstep (se 2 (by rfl) ⟨2249835, by rfl⟩ : syracuseStep 5999561 = 4499671) B4499671
theorem B4500431 : Blo 1776089 4500431 := bstep (se 1 (by rfl) ⟨3375323, by rfl⟩ : syracuseStep 4500431 = 6750647) B6750647
theorem B2665439 : Blo 1776089 2665439 := bstep (se 1 (by rfl) ⟨1999079, by rfl⟩ : syracuseStep 2665439 = 3998159) B3998159
theorem B5999723 : Blo 1776089 5999723 := bstep (se 1 (by rfl) ⟨4499792, by rfl⟩ : syracuseStep 5999723 = 8999585) B8999585
theorem B7589011 : Blo 1776089 7589011 := bstep (se 1 (by rfl) ⟨5691758, by rfl⟩ : syracuseStep 7589011 = 11383517) B11383517
theorem B5999831 : Blo 1776089 5999831 := bstep (se 1 (by rfl) ⟨4499873, by rfl⟩ : syracuseStep 5999831 = 8999747) B8999747
theorem B4500755 : Blo 1776089 4500755 := bstep (se 1 (by rfl) ⟨3375566, by rfl⟩ : syracuseStep 4500755 = 6751133) B6751133
theorem B8539501 : Blo 1776089 8539501 := bstep (se 3 (by rfl) ⟨1601156, by rfl⟩ : syracuseStep 8539501 = 3202313) B3202313
theorem B5999993 : Blo 1776089 5999993 := bstep (se 2 (by rfl) ⟨2249997, by rfl⟩ : syracuseStep 5999993 = 4499995) B4499995
theorem B2665883 : Blo 1776089 2665883 := bstep (se 1 (by rfl) ⟨1999412, by rfl⟩ : syracuseStep 2665883 = 3998825) B3998825
theorem B18230791 : Blo 1776089 18230791 := bstep (se 1 (by rfl) ⟨13673093, by rfl⟩ : syracuseStep 18230791 = 27346187) B27346187
theorem B5058281 : Blo 1776089 5058281 := bstep (se 2 (by rfl) ⟨1896855, by rfl⟩ : syracuseStep 5058281 = 3793711) B3793711
theorem B6000371 : Blo 1776089 6000371 := bstep (se 1 (by rfl) ⟨4500278, by rfl⟩ : syracuseStep 6000371 = 9000557) B9000557
theorem B2666303 : Blo 1776089 2666303 := bstep (se 1 (by rfl) ⟨1999727, by rfl⟩ : syracuseStep 2666303 = 3999455) B3999455
theorem B4050811 : Blo 1776089 4050811 := bstep (se 1 (by rfl) ⟨3038108, by rfl⟩ : syracuseStep 4050811 = 6076217) B6076217
theorem B6746075 : Blo 1776089 6746075 := bstep (se 1 (by rfl) ⟨5059556, by rfl⟩ : syracuseStep 6746075 = 10119113) B10119113
theorem B6746105 : Blo 1776089 6746105 := bstep (se 2 (by rfl) ⟨2529789, by rfl⟩ : syracuseStep 6746105 = 5059579) B5059579
theorem B2666489 : Blo 1776089 2666489 := bstep (se 2 (by rfl) ⟨999933, by rfl⟩ : syracuseStep 2666489 = 1999867) B1999867
theorem B17076233 : Blo 1776089 17076233 := bstep (se 2 (by rfl) ⟨6403587, by rfl⟩ : syracuseStep 17076233 = 12807175) B12807175
theorem B12161087 : Blo 1776089 12161087 := bstep (se 1 (by rfl) ⟨9120815, by rfl⟩ : syracuseStep 12161087 = 18241631) B18241631
theorem B22769747 : Blo 1776089 22769747 := bstep (se 1 (by rfl) ⟨17077310, by rfl⟩ : syracuseStep 22769747 = 34154621) B34154621
theorem B4272211 : Blo 1776089 4272211 := bstep (se 1 (by rfl) ⟨3204158, by rfl⟩ : syracuseStep 4272211 = 6408317) B6408317
theorem B2248879 : Blo 1776089 2248879 := bstep (se 1 (by rfl) ⟨1686659, by rfl⟩ : syracuseStep 2248879 = 3373319) B3373319
theorem B2666729 : Blo 1776089 2666729 := bstep (se 2 (by rfl) ⟨1000023, by rfl⟩ : syracuseStep 2666729 = 2000047) B2000047
theorem B27742499 : Blo 1776089 27742499 := bstep (se 1 (by rfl) ⟨20806874, by rfl⟩ : syracuseStep 27742499 = 41613749) B41613749
theorem B61583651 : Blo 1776089 61583651 := bstep (se 1 (by rfl) ⟨46187738, by rfl⟩ : syracuseStep 61583651 = 92375477) B92375477
theorem B2666855 : Blo 1776089 2666855 := bstep (se 1 (by rfl) ⟨2000141, by rfl⟩ : syracuseStep 2666855 = 4000283) B4000283
theorem B30364307 : Blo 1776089 30364307 := bstep (se 1 (by rfl) ⟨22773230, by rfl⟩ : syracuseStep 30364307 = 45546461) B45546461
theorem B64869017 : Blo 1776089 64869017 := bstep (se 2 (by rfl) ⟨24325881, by rfl⟩ : syracuseStep 64869017 = 48651763) B48651763
theorem B554226533 : Blo 1776089 554226533 := bstep (se 4 (by rfl) ⟨51958737, by rfl⟩ : syracuseStep 554226533 = 103917475) B103917475
theorem B10122347 : Blo 1776089 10122347 := bstep (se 1 (by rfl) ⟨7591760, by rfl⟩ : syracuseStep 10122347 = 15183521) B15183521
theorem B10958075 : Blo 1776089 10958075 := bstep (se 1 (by rfl) ⟨8218556, by rfl⟩ : syracuseStep 10958075 = 16437113) B16437113
theorem B6747563 : Blo 1776089 6747563 := bstep (se 1 (by rfl) ⟨5060672, by rfl⟩ : syracuseStep 6747563 = 10121345) B10121345
theorem B17069777 : Blo 1776089 17069777 := bstep (se 2 (by rfl) ⟨6401166, by rfl⟩ : syracuseStep 17069777 = 12802333) B12802333
theorem B12810149 : Blo 1776089 12810149 := bstep (se 4 (by rfl) ⟨1200951, by rfl⟩ : syracuseStep 12810149 = 2401903) B2401903
theorem B9001043 : Blo 1776089 9001043 := bstep (se 1 (by rfl) ⟨6750782, by rfl⟩ : syracuseStep 9001043 = 13501565) B13501565
theorem B17078465 : Blo 1776089 17078465 := bstep (se 2 (by rfl) ⟨6404424, by rfl⟩ : syracuseStep 17078465 = 12808849) B12808849
theorem B22763753 : Blo 1776089 22763753 := bstep (se 2 (by rfl) ⟨8536407, by rfl⟩ : syracuseStep 22763753 = 17072815) B17072815
theorem B13678877 : Blo 1776089 13678877 := bstep (se 3 (by rfl) ⟨2564789, by rfl⟩ : syracuseStep 13678877 = 5129579) B5129579
theorem B1776103 : Blo 1776089 1776103 := bstep (se 1 (by rfl) ⟨1332077, by rfl⟩ : syracuseStep 1776103 = 2664155) B2664155
theorem B6404615 : Blo 1776089 6404615 := bstep (se 1 (by rfl) ⟨4803461, by rfl⟩ : syracuseStep 6404615 = 9606923) B9606923
theorem B6748703 : Blo 1776089 6748703 := bstep (se 1 (by rfl) ⟨5061527, by rfl⟩ : syracuseStep 6748703 = 10123055) B10123055
theorem B3996251 : Blo 1776089 3996251 := bstep (se 1 (by rfl) ⟨2997188, by rfl⟩ : syracuseStep 3996251 = 5994377) B5994377
theorem B1776219 : Blo 1776089 1776219 := bstep (se 1 (by rfl) ⟨1332164, by rfl⟩ : syracuseStep 1776219 = 2664329) B2664329
theorem B1776287 : Blo 1776089 1776287 := bstep (se 1 (by rfl) ⟨1332215, by rfl⟩ : syracuseStep 1776287 = 2664431) B2664431
theorem B3996395 : Blo 1776089 3996395 := bstep (se 1 (by rfl) ⟨2997296, by rfl⟩ : syracuseStep 3996395 = 5994593) B5994593
theorem B1776455 : Blo 1776089 1776455 := bstep (se 1 (by rfl) ⟨1332341, by rfl⟩ : syracuseStep 1776455 = 2664683) B2664683
theorem B1776495 : Blo 1776089 1776495 := bstep (se 1 (by rfl) ⟨1332371, by rfl⟩ : syracuseStep 1776495 = 2664743) B2664743
theorem B233798561 : Blo 1776089 233798561 := bstep (se 2 (by rfl) ⟨87674460, by rfl⟩ : syracuseStep 233798561 = 175348921) B175348921
theorem B1776551 : Blo 1776089 1776551 := bstep (se 1 (by rfl) ⟨1332413, by rfl⟩ : syracuseStep 1776551 = 2664827) B2664827
theorem B4496431 : Blo 1776089 4496431 := bstep (se 1 (by rfl) ⟨3372323, by rfl⟩ : syracuseStep 4496431 = 6744647) B6744647
theorem B129719353 : Blo 1776089 129719353 := bstep (se 2 (by rfl) ⟨48644757, by rfl⟩ : syracuseStep 129719353 = 97289515) B97289515
theorem B6077531 : Blo 1776089 6077531 := bstep (se 1 (by rfl) ⟨4558148, by rfl⟩ : syracuseStep 6077531 = 9116297) B9116297
theorem B1776731 : Blo 1776089 1776731 := bstep (se 1 (by rfl) ⟨1332548, by rfl⟩ : syracuseStep 1776731 = 2665097) B2665097
theorem B1776847 : Blo 1776089 1776847 := bstep (se 1 (by rfl) ⟨1332635, by rfl⟩ : syracuseStep 1776847 = 2665271) B2665271
theorem B2997479 : Blo 1776089 2997479 := bstep (se 1 (by rfl) ⟨2248109, by rfl⟩ : syracuseStep 2997479 = 4496219) B4496219
theorem B1776871 : Blo 1776089 1776871 := bstep (se 1 (by rfl) ⟨1332653, by rfl⟩ : syracuseStep 1776871 = 2665307) B2665307
theorem B1598692625 : Blo 1776089 1598692625 := bstep (se 2 (by rfl) ⟨599509734, by rfl⟩ : syracuseStep 1598692625 = 1199019469) B1199019469
theorem B1776967 : Blo 1776089 1776967 := bstep (se 1 (by rfl) ⟨1332725, by rfl⟩ : syracuseStep 1776967 = 2665451) B2665451
theorem B3997007 : Blo 1776089 3997007 := bstep (se 1 (by rfl) ⟨2997755, by rfl⟩ : syracuseStep 3997007 = 5995511) B5995511
theorem B4054379 : Blo 1776089 4054379 := bstep (se 1 (by rfl) ⟨3040784, by rfl⟩ : syracuseStep 4054379 = 6081569) B6081569
theorem B5127547 : Blo 1776089 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B3997097 : Blo 1776089 3997097 := bstep (se 2 (by rfl) ⟨1498911, by rfl⟩ : syracuseStep 3997097 = 2997823) B2997823
theorem B1777103 : Blo 1776089 1777103 := bstep (se 1 (by rfl) ⟨1332827, by rfl⟩ : syracuseStep 1777103 = 2665655) B2665655
theorem B5996051 : Blo 1776089 5996051 := bstep (se 1 (by rfl) ⟨4497038, by rfl⟩ : syracuseStep 5996051 = 8994077) B8994077
theorem B3997295 : Blo 1776089 3997295 := bstep (se 1 (by rfl) ⟨2997971, by rfl⟩ : syracuseStep 3997295 = 5995943) B5995943
theorem B1777263 : Blo 1776089 1777263 := bstep (se 1 (by rfl) ⟨1332947, by rfl⟩ : syracuseStep 1777263 = 2665895) B2665895
theorem B1777319 : Blo 1776089 1777319 := bstep (se 1 (by rfl) ⟨1332989, by rfl⟩ : syracuseStep 1777319 = 2665979) B2665979
theorem B1777383 : Blo 1776089 1777383 := bstep (se 1 (by rfl) ⟨1333037, by rfl⟩ : syracuseStep 1777383 = 2666075) B2666075
theorem B1777439 : Blo 1776089 1777439 := bstep (se 1 (by rfl) ⟨1333079, by rfl⟩ : syracuseStep 1777439 = 2666159) B2666159
theorem B1777519 : Blo 1776089 1777519 := bstep (se 1 (by rfl) ⟨1333139, by rfl⟩ : syracuseStep 1777519 = 2666279) B2666279
theorem B3997583 : Blo 1776089 3997583 := bstep (se 1 (by rfl) ⟨2998187, by rfl⟩ : syracuseStep 3997583 = 5996375) B5996375
theorem B1777575 : Blo 1776089 1777575 := bstep (se 1 (by rfl) ⟨1333181, by rfl⟩ : syracuseStep 1777575 = 2666363) B2666363
theorem B15179831 : Blo 1776089 15179831 := bstep (se 1 (by rfl) ⟨11384873, by rfl⟩ : syracuseStep 15179831 = 22769747) B22769747
theorem B1777819 : Blo 1776089 1777819 := bstep (se 1 (by rfl) ⟨1333364, by rfl⟩ : syracuseStep 1777819 = 2666729) B2666729
theorem B2998505 : Blo 1776089 2998505 := bstep (se 2 (by rfl) ⟨1124439, by rfl⟩ : syracuseStep 2998505 = 2248879) B2248879
theorem B1777903 : Blo 1776089 1777903 := bstep (se 1 (by rfl) ⟨1333427, by rfl⟩ : syracuseStep 1777903 = 2666855) B2666855
theorem B65757521 : Blo 1776089 65757521 := bstep (se 2 (by rfl) ⟨24659070, by rfl⟩ : syracuseStep 65757521 = 49318141) B49318141
theorem B20242871 : Blo 1776089 20242871 := bstep (se 1 (by rfl) ⟨15182153, by rfl⟩ : syracuseStep 20242871 = 30364307) B30364307
theorem B369484355 : Blo 1776089 369484355 := bstep (se 1 (by rfl) ⟨277113266, by rfl⟩ : syracuseStep 369484355 = 554226533) B554226533
theorem B3998519 : Blo 1776089 3998519 := bstep (se 1 (by rfl) ⟨2998889, by rfl⟩ : syracuseStep 3998519 = 5997779) B5997779
theorem B1999687 : Blo 1776089 1999687 := bstep (se 1 (by rfl) ⟨1499765, by rfl⟩ : syracuseStep 1999687 = 2999531) B2999531
theorem B4498375 : Blo 1776089 4498375 := bstep (se 1 (by rfl) ⟨3373781, by rfl⟩ : syracuseStep 4498375 = 6747563) B6747563
theorem B3998699 : Blo 1776089 3998699 := bstep (se 1 (by rfl) ⟨2999024, by rfl⟩ : syracuseStep 3998699 = 5998049) B5998049
theorem B43246709 : Blo 1776089 43246709 := bstep (se 5 (by rfl) ⟨2027189, by rfl⟩ : syracuseStep 43246709 = 4054379) B4054379
theorem B11379851 : Blo 1776089 11379851 := bstep (se 1 (by rfl) ⟨8534888, by rfl⟩ : syracuseStep 11379851 = 17069777) B17069777
theorem B43828559 : Blo 1776089 43828559 := bstep (se 1 (by rfl) ⟨32871419, by rfl⟩ : syracuseStep 43828559 = 65742839) B65742839
theorem B172959137 : Blo 1776089 172959137 := bstep (se 2 (by rfl) ⟨64859676, by rfl⟩ : syracuseStep 172959137 = 129719353) B129719353
theorem B9119251 : Blo 1776089 9119251 := bstep (se 1 (by rfl) ⟨6839438, by rfl⟩ : syracuseStep 9119251 = 13678877) B13678877
theorem B10118681 : Blo 1776089 10118681 := bstep (se 2 (by rfl) ⟨3794505, by rfl⟩ : syracuseStep 10118681 = 7589011) B7589011
theorem B4269743 : Blo 1776089 4269743 := bstep (se 1 (by rfl) ⟨3202307, by rfl⟩ : syracuseStep 4269743 = 6404615) B6404615
theorem B4499135 : Blo 1776089 4499135 := bstep (se 1 (by rfl) ⟨3374351, by rfl⟩ : syracuseStep 4499135 = 6748703) B6748703
theorem B2664167 : Blo 1776089 2664167 := bstep (se 1 (by rfl) ⟨1998125, by rfl⟩ : syracuseStep 2664167 = 3996251) B3996251
theorem B172984045 : Blo 1776089 172984045 := bstep (se 3 (by rfl) ⟨32434508, by rfl⟩ : syracuseStep 172984045 = 64869017) B64869017
theorem B5998319 : Blo 1776089 5998319 := bstep (se 1 (by rfl) ⟨4498739, by rfl⟩ : syracuseStep 5998319 = 8997479) B8997479
theorem B2664263 : Blo 1776089 2664263 := bstep (se 1 (by rfl) ⟨1998197, by rfl⟩ : syracuseStep 2664263 = 3996395) B3996395
theorem B3999599 : Blo 1776089 3999599 := bstep (se 1 (by rfl) ⟨2999699, by rfl⟩ : syracuseStep 3999599 = 5999399) B5999399
theorem B3999707 : Blo 1776089 3999707 := bstep (se 1 (by rfl) ⟨2999780, by rfl⟩ : syracuseStep 3999707 = 5999561) B5999561
theorem B3000287 : Blo 1776089 3000287 := bstep (se 1 (by rfl) ⟨2250215, by rfl⟩ : syracuseStep 3000287 = 4500431) B4500431
theorem B24307721 : Blo 1776089 24307721 := bstep (se 2 (by rfl) ⟨9115395, by rfl⟩ : syracuseStep 24307721 = 18230791) B18230791
theorem B3999815 : Blo 1776089 3999815 := bstep (se 1 (by rfl) ⟨2999861, by rfl⟩ : syracuseStep 3999815 = 5999723) B5999723
theorem B3999887 : Blo 1776089 3999887 := bstep (se 1 (by rfl) ⟨2999915, by rfl⟩ : syracuseStep 3999887 = 5999831) B5999831
theorem B3000503 : Blo 1776089 3000503 := bstep (se 1 (by rfl) ⟨2250377, by rfl⟩ : syracuseStep 3000503 = 4500755) B4500755
theorem B2664671 : Blo 1776089 2664671 := bstep (se 1 (by rfl) ⟨1998503, by rfl⟩ : syracuseStep 2664671 = 3997007) B3997007
theorem B3999977 : Blo 1776089 3999977 := bstep (se 2 (by rfl) ⟨1499991, by rfl⟩ : syracuseStep 3999977 = 2999983) B2999983
theorem B3999995 : Blo 1776089 3999995 := bstep (se 1 (by rfl) ⟨2999996, by rfl⟩ : syracuseStep 3999995 = 5999993) B5999993
theorem B2664731 : Blo 1776089 2664731 := bstep (se 1 (by rfl) ⟨1998548, by rfl⟩ : syracuseStep 2664731 = 3997097) B3997097
theorem B2664863 : Blo 1776089 2664863 := bstep (se 1 (by rfl) ⟨1998647, by rfl⟩ : syracuseStep 2664863 = 3997295) B3997295
theorem B5401081 : Blo 1776089 5401081 := bstep (se 2 (by rfl) ⟨2025405, by rfl⟩ : syracuseStep 5401081 = 4050811) B4050811
theorem B4000247 : Blo 1776089 4000247 := bstep (se 1 (by rfl) ⟨3000185, by rfl⟩ : syracuseStep 4000247 = 6000371) B6000371
theorem B2665055 : Blo 1776089 2665055 := bstep (se 1 (by rfl) ⟨1998791, by rfl⟩ : syracuseStep 2665055 = 3997583) B3997583
theorem B5696281 : Blo 1776089 5696281 := bstep (se 2 (by rfl) ⟨2136105, by rfl⟩ : syracuseStep 5696281 = 4272211) B4272211
theorem B16206749 : Blo 1776089 16206749 := bstep (se 3 (by rfl) ⟨3038765, by rfl⟩ : syracuseStep 16206749 = 6077531) B6077531
theorem B2665385 : Blo 1776089 2665385 := bstep (se 2 (by rfl) ⟨999519, by rfl⟩ : syracuseStep 2665385 = 1999039) B1999039
theorem B2665415 : Blo 1776089 2665415 := bstep (se 1 (by rfl) ⟨1999061, by rfl⟩ : syracuseStep 2665415 = 3998123) B3998123
theorem B115256267 : Blo 1776089 115256267 := bstep (se 1 (by rfl) ⟨86442200, by rfl⟩ : syracuseStep 115256267 = 172884401) B172884401
theorem B2665535 : Blo 1776089 2665535 := bstep (se 1 (by rfl) ⟨1999151, by rfl⟩ : syracuseStep 2665535 = 3998303) B3998303
theorem B2665775 : Blo 1776089 2665775 := bstep (se 1 (by rfl) ⟨1999331, by rfl⟩ : syracuseStep 2665775 = 3998663) B3998663
theorem B4271519 : Blo 1776089 4271519 := bstep (se 1 (by rfl) ⟨3203639, by rfl⟩ : syracuseStep 4271519 = 6407279) B6407279
theorem B2665961 : Blo 1776089 2665961 := bstep (se 2 (by rfl) ⟨999735, by rfl⟩ : syracuseStep 2665961 = 1999471) B1999471
theorem B2666015 : Blo 1776089 2666015 := bstep (se 1 (by rfl) ⟨1999511, by rfl⟩ : syracuseStep 2666015 = 3999023) B3999023
theorem B2666105 : Blo 1776089 2666105 := bstep (se 2 (by rfl) ⟨999789, by rfl⟩ : syracuseStep 2666105 = 1999579) B1999579
theorem B2666351 : Blo 1776089 2666351 := bstep (se 1 (by rfl) ⟨1999763, by rfl⟩ : syracuseStep 2666351 = 3999527) B3999527
theorem B8540099 : Blo 1776089 8540099 := bstep (se 1 (by rfl) ⟨6405074, by rfl⟩ : syracuseStep 8540099 = 12810149) B12810149
theorem B14413787 : Blo 1776089 14413787 := bstep (se 1 (by rfl) ⟨10810340, by rfl⟩ : syracuseStep 14413787 = 21620681) B21620681
theorem B6000695 : Blo 1776089 6000695 := bstep (se 1 (by rfl) ⟨4500521, by rfl⟩ : syracuseStep 6000695 = 9001043) B9001043
theorem B2666603 : Blo 1776089 2666603 := bstep (se 1 (by rfl) ⟨1999952, by rfl⟩ : syracuseStep 2666603 = 3999905) B3999905
theorem B15175835 : Blo 1776089 15175835 := bstep (se 1 (by rfl) ⟨11381876, by rfl⟩ : syracuseStep 15175835 = 22763753) B22763753
theorem B6746287 : Blo 1776089 6746287 := bstep (se 1 (by rfl) ⟨5059715, by rfl⟩ : syracuseStep 6746287 = 10119431) B10119431
theorem B6836729 : Blo 1776089 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B2667035 : Blo 1776089 2667035 := bstep (se 1 (by rfl) ⟨2000276, by rfl⟩ : syracuseStep 2667035 = 4000553) B4000553
theorem B155865707 : Blo 1776089 155865707 := bstep (se 1 (by rfl) ⟨116899280, by rfl⟩ : syracuseStep 155865707 = 233798561) B233798561
theorem B3372187 : Blo 1776089 3372187 := bstep (se 1 (by rfl) ⟨2529140, by rfl⟩ : syracuseStep 3372187 = 5058281) B5058281
theorem B11384155 : Blo 1776089 11384155 := bstep (se 1 (by rfl) ⟨8538116, by rfl⟩ : syracuseStep 11384155 = 17076233) B17076233
theorem B8107391 : Blo 1776089 8107391 := bstep (se 1 (by rfl) ⟨6080543, by rfl⟩ : syracuseStep 8107391 = 12161087) B12161087
theorem B18494999 : Blo 1776089 18494999 := bstep (se 1 (by rfl) ⟨13871249, by rfl⟩ : syracuseStep 18494999 = 27742499) B27742499
theorem B41055767 : Blo 1776089 41055767 := bstep (se 1 (by rfl) ⟨30791825, by rfl⟩ : syracuseStep 41055767 = 61583651) B61583651
theorem B2250271 : Blo 1776089 2250271 := bstep (se 1 (by rfl) ⟨1687703, by rfl⟩ : syracuseStep 2250271 = 3375407) B3375407
theorem B20239955 : Blo 1776089 20239955 := bstep (se 1 (by rfl) ⟨15179966, by rfl⟩ : syracuseStep 20239955 = 30359933) B30359933
theorem B12982123 : Blo 1776089 12982123 := bstep (se 1 (by rfl) ⟨9736592, by rfl⟩ : syracuseStep 12982123 = 19473185) B19473185
theorem B2529311 : Blo 1776089 2529311 := bstep (se 1 (by rfl) ⟨1896983, by rfl⟩ : syracuseStep 2529311 = 3793967) B3793967
theorem B6748231 : Blo 1776089 6748231 := bstep (se 1 (by rfl) ⟨5061173, by rfl⟩ : syracuseStep 6748231 = 10122347) B10122347
theorem B7305383 : Blo 1776089 7305383 := bstep (se 1 (by rfl) ⟨5479037, by rfl⟩ : syracuseStep 7305383 = 10958075) B10958075
theorem B1777659 : Blo 1776089 1777659 := bstep (se 1 (by rfl) ⟨1333244, by rfl⟩ : syracuseStep 1777659 = 2666489) B2666489
theorem B1776231 : Blo 1776089 1776231 := bstep (se 1 (by rfl) ⟨1332173, by rfl⟩ : syracuseStep 1776231 = 2664347) B2664347
theorem B1776255 : Blo 1776089 1776255 := bstep (se 1 (by rfl) ⟨1332191, by rfl⟩ : syracuseStep 1776255 = 2664383) B2664383
theorem B5995241 : Blo 1776089 5995241 := bstep (se 2 (by rfl) ⟨2248215, by rfl⟩ : syracuseStep 5995241 = 4496431) B4496431
theorem B4496107 : Blo 1776089 4496107 := bstep (se 1 (by rfl) ⟨3372080, by rfl⟩ : syracuseStep 4496107 = 6744161) B6744161
theorem B1776379 : Blo 1776089 1776379 := bstep (se 1 (by rfl) ⟨1332284, by rfl⟩ : syracuseStep 1776379 = 2664569) B2664569
theorem B11385643 : Blo 1776089 11385643 := bstep (se 1 (by rfl) ⟨8539232, by rfl⟩ : syracuseStep 11385643 = 17078465) B17078465
theorem B5692207 : Blo 1776089 5692207 := bstep (se 1 (by rfl) ⟨4269155, by rfl⟩ : syracuseStep 5692207 = 8538311) B8538311
theorem B5692283 : Blo 1776089 5692283 := bstep (se 1 (by rfl) ⟨4269212, by rfl⟩ : syracuseStep 5692283 = 8538425) B8538425
theorem B7691219 : Blo 1776089 7691219 := bstep (se 1 (by rfl) ⟨5768414, by rfl⟩ : syracuseStep 7691219 = 11536829) B11536829
theorem B1776635 : Blo 1776089 1776635 := bstep (se 1 (by rfl) ⟨1332476, by rfl⟩ : syracuseStep 1776635 = 2664953) B2664953
theorem B1776671 : Blo 1776089 1776671 := bstep (se 1 (by rfl) ⟨1332503, by rfl⟩ : syracuseStep 1776671 = 2665007) B2665007
theorem B11386001 : Blo 1776089 11386001 := bstep (se 2 (by rfl) ⟨4269750, by rfl⟩ : syracuseStep 11386001 = 8539501) B8539501
theorem B1776959 : Blo 1776089 1776959 := bstep (se 1 (by rfl) ⟨1332719, by rfl⟩ : syracuseStep 1776959 = 2665439) B2665439
theorem B1998319 : Blo 1776089 1998319 := bstep (se 1 (by rfl) ⟨1498739, by rfl⟩ : syracuseStep 1998319 = 2997479) B2997479
theorem B1065795083 : Blo 1776089 1065795083 := bstep (se 1 (by rfl) ⟨799346312, by rfl⟩ : syracuseStep 1065795083 = 1598692625) B1598692625
theorem B10116697 : Blo 1776089 10116697 := bstep (se 2 (by rfl) ⟨3793761, by rfl⟩ : syracuseStep 10116697 = 7587523) B7587523
theorem B1777255 : Blo 1776089 1777255 := bstep (se 1 (by rfl) ⟨1332941, by rfl⟩ : syracuseStep 1777255 = 2665883) B2665883
theorem B3997367 : Blo 1776089 3997367 := bstep (se 1 (by rfl) ⟨2998025, by rfl⟩ : syracuseStep 3997367 = 5996051) B5996051
theorem B1777535 : Blo 1776089 1777535 := bstep (se 1 (by rfl) ⟨1333151, by rfl⟩ : syracuseStep 1777535 = 2666303) B2666303
theorem B4497383 : Blo 1776089 4497383 := bstep (se 1 (by rfl) ⟨3373037, by rfl⟩ : syracuseStep 4497383 = 6746075) B6746075
theorem B4497403 : Blo 1776089 4497403 := bstep (se 1 (by rfl) ⟨3373052, by rfl⟩ : syracuseStep 4497403 = 6746105) B6746105
theorem B1777735 : Blo 1776089 1777735 := bstep (se 1 (by rfl) ⟨1333301, by rfl⟩ : syracuseStep 1777735 = 2666603) B2666603
theorem B10117223 : Blo 1776089 10117223 := bstep (se 1 (by rfl) ⟨7587917, by rfl⟩ : syracuseStep 10117223 = 15175835) B15175835
theorem B1999003 : Blo 1776089 1999003 := bstep (se 1 (by rfl) ⟨1499252, by rfl⟩ : syracuseStep 1999003 = 2998505) B2998505
theorem B8995049 : Blo 1776089 8995049 := bstep (se 2 (by rfl) ⟨3373143, by rfl⟩ : syracuseStep 8995049 = 6746287) B6746287
theorem B1778023 : Blo 1776089 1778023 := bstep (se 1 (by rfl) ⟨1333517, by rfl⟩ : syracuseStep 1778023 = 2667035) B2667035
theorem B7201441 : Blo 1776089 7201441 := bstep (se 2 (by rfl) ⟨2700540, by rfl⟩ : syracuseStep 7201441 = 5401081) B5401081
theorem B7586567 : Blo 1776089 7586567 := bstep (se 1 (by rfl) ⟨5689925, by rfl⟩ : syracuseStep 7586567 = 11379851) B11379851
theorem B12329999 : Blo 1776089 12329999 := bstep (se 1 (by rfl) ⟨9247499, by rfl⟩ : syracuseStep 12329999 = 18494999) B18494999
theorem B27370511 : Blo 1776089 27370511 := bstep (se 1 (by rfl) ⟨20527883, by rfl⟩ : syracuseStep 27370511 = 41055767) B41055767
theorem B7595041 : Blo 1776089 7595041 := bstep (se 2 (by rfl) ⟨2848140, by rfl⟩ : syracuseStep 7595041 = 5696281) B5696281
theorem B13493303 : Blo 1776089 13493303 := bstep (se 1 (by rfl) ⟨10119977, by rfl⟩ : syracuseStep 13493303 = 20239955) B20239955
theorem B15180857 : Blo 1776089 15180857 := bstep (se 2 (by rfl) ⟨5692821, by rfl⟩ : syracuseStep 15180857 = 11385643) B11385643
theorem B2999423 : Blo 1776089 2999423 := bstep (se 1 (by rfl) ⟨2249567, by rfl⟩ : syracuseStep 2999423 = 4499135) B4499135
theorem B3998879 : Blo 1776089 3998879 := bstep (se 1 (by rfl) ⟨2999159, by rfl⟩ : syracuseStep 3998879 = 5998319) B5998319
theorem B5997833 : Blo 1776089 5997833 := bstep (se 2 (by rfl) ⟨2249187, by rfl⟩ : syracuseStep 5997833 = 4498375) B4498375
theorem B2000191 : Blo 1776089 2000191 := bstep (se 1 (by rfl) ⟨1500143, by rfl⟩ : syracuseStep 2000191 = 3000287) B3000287
theorem B16205147 : Blo 1776089 16205147 := bstep (se 1 (by rfl) ⟨12153860, by rfl⟩ : syracuseStep 16205147 = 24307721) B24307721
theorem B2000335 : Blo 1776089 2000335 := bstep (se 1 (by rfl) ⟨1500251, by rfl⟩ : syracuseStep 2000335 = 3000503) B3000503
theorem B3794855 : Blo 1776089 3794855 := bstep (se 1 (by rfl) ⟨2846141, by rfl⟩ : syracuseStep 3794855 = 5692283) B5692283
theorem B2664425 : Blo 1776089 2664425 := bstep (se 2 (by rfl) ⟨999159, by rfl⟩ : syracuseStep 2664425 = 1998319) B1998319
theorem B12159001 : Blo 1776089 12159001 := bstep (se 2 (by rfl) ⟨4559625, by rfl⟩ : syracuseStep 12159001 = 9119251) B9119251
theorem B3000361 : Blo 1776089 3000361 := bstep (se 2 (by rfl) ⟨1125135, by rfl⟩ : syracuseStep 3000361 = 2250271) B2250271
theorem B2664911 : Blo 1776089 2664911 := bstep (se 1 (by rfl) ⟨1998683, by rfl⟩ : syracuseStep 2664911 = 3997367) B3997367
theorem B10119887 : Blo 1776089 10119887 := bstep (se 1 (by rfl) ⟨7589915, by rfl⟩ : syracuseStep 10119887 = 15179831) B15179831
theorem B4000463 : Blo 1776089 4000463 := bstep (se 1 (by rfl) ⟨3000347, by rfl⟩ : syracuseStep 4000463 = 6000695) B6000695
theorem B6744829 : Blo 1776089 6744829 := bstep (se 3 (by rfl) ⟨1264655, by rfl⟩ : syracuseStep 6744829 = 2529311) B2529311
theorem B8997641 : Blo 1776089 8997641 := bstep (se 2 (by rfl) ⟨3374115, by rfl⟩ : syracuseStep 8997641 = 6748231) B6748231
theorem B43838347 : Blo 1776089 43838347 := bstep (se 1 (by rfl) ⟨32878760, by rfl⟩ : syracuseStep 43838347 = 65757521) B65757521
theorem B13495247 : Blo 1776089 13495247 := bstep (se 1 (by rfl) ⟨10121435, by rfl⟩ : syracuseStep 13495247 = 20242871) B20242871
theorem B103910471 : Blo 1776089 103910471 := bstep (se 1 (by rfl) ⟨77932853, by rfl⟩ : syracuseStep 103910471 = 155865707) B155865707
theorem B2665679 : Blo 1776089 2665679 := bstep (se 1 (by rfl) ⟨1999259, by rfl⟩ : syracuseStep 2665679 = 3998519) B3998519
theorem B2665799 : Blo 1776089 2665799 := bstep (se 1 (by rfl) ⟨1999349, by rfl⟩ : syracuseStep 2665799 = 3998699) B3998699
theorem B28831139 : Blo 1776089 28831139 := bstep (se 1 (by rfl) ⟨21623354, by rfl⟩ : syracuseStep 28831139 = 43246709) B43246709
theorem B115306091 : Blo 1776089 115306091 := bstep (se 1 (by rfl) ⟨86479568, by rfl⟩ : syracuseStep 115306091 = 172959137) B172959137
theorem B6745787 : Blo 1776089 6745787 := bstep (se 1 (by rfl) ⟨5059340, by rfl⟩ : syracuseStep 6745787 = 10118681) B10118681
theorem B7589609 : Blo 1776089 7589609 := bstep (se 2 (by rfl) ⟨2846103, by rfl⟩ : syracuseStep 7589609 = 5692207) B5692207
theorem B2666249 : Blo 1776089 2666249 := bstep (se 2 (by rfl) ⟨999843, by rfl⟩ : syracuseStep 2666249 = 1999687) B1999687
theorem B2846495 : Blo 1776089 2846495 := bstep (se 1 (by rfl) ⟨2134871, by rfl⟩ : syracuseStep 2846495 = 4269743) B4269743
theorem B2666399 : Blo 1776089 2666399 := bstep (se 1 (by rfl) ⟨1999799, by rfl⟩ : syracuseStep 2666399 = 3999599) B3999599
theorem B2666471 : Blo 1776089 2666471 := bstep (se 1 (by rfl) ⟨1999853, by rfl⟩ : syracuseStep 2666471 = 3999707) B3999707
theorem B18231277 : Blo 1776089 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B2666543 : Blo 1776089 2666543 := bstep (se 1 (by rfl) ⟨1999907, by rfl⟩ : syracuseStep 2666543 = 3999815) B3999815
theorem B2666591 : Blo 1776089 2666591 := bstep (se 1 (by rfl) ⟨1999943, by rfl⟩ : syracuseStep 2666591 = 3999887) B3999887
theorem B4870255 : Blo 1776089 4870255 := bstep (se 1 (by rfl) ⟨3652691, by rfl⟩ : syracuseStep 4870255 = 7305383) B7305383
theorem B2666651 : Blo 1776089 2666651 := bstep (se 1 (by rfl) ⟨1999988, by rfl⟩ : syracuseStep 2666651 = 3999977) B3999977
theorem B2666663 : Blo 1776089 2666663 := bstep (se 1 (by rfl) ⟨1999997, by rfl⟩ : syracuseStep 2666663 = 3999995) B3999995
theorem B2666831 : Blo 1776089 2666831 := bstep (se 1 (by rfl) ⟨2000123, by rfl⟩ : syracuseStep 2666831 = 4000247) B4000247
theorem B76837511 : Blo 1776089 76837511 := bstep (se 1 (by rfl) ⟨57628133, by rfl⟩ : syracuseStep 76837511 = 115256267) B115256267
theorem B7590667 : Blo 1776089 7590667 := bstep (se 1 (by rfl) ⟨5693000, by rfl⟩ : syracuseStep 7590667 = 11386001) B11386001
theorem B13488929 : Blo 1776089 13488929 := bstep (se 2 (by rfl) ⟨5058348, by rfl⟩ : syracuseStep 13488929 = 10116697) B10116697
theorem B2847679 : Blo 1776089 2847679 := bstep (se 1 (by rfl) ⟨2135759, by rfl⟩ : syracuseStep 2847679 = 4271519) B4271519
theorem B710530055 : Blo 1776089 710530055 := bstep (se 1 (by rfl) ⟨532897541, by rfl⟩ : syracuseStep 710530055 = 1065795083) B1065795083
theorem B29219039 : Blo 1776089 29219039 := bstep (se 1 (by rfl) ⟨21914279, by rfl⟩ : syracuseStep 29219039 = 43828559) B43828559
theorem B5404927 : Blo 1776089 5404927 := bstep (se 1 (by rfl) ⟨4053695, by rfl⟩ : syracuseStep 5404927 = 8107391) B8107391
theorem B5994809 : Blo 1776089 5994809 := bstep (se 2 (by rfl) ⟨2248053, by rfl⟩ : syracuseStep 5994809 = 4496107) B4496107
theorem B1776111 : Blo 1776089 1776111 := bstep (se 1 (by rfl) ⟨1332083, by rfl⟩ : syracuseStep 1776111 = 2664167) B2664167
theorem B1776175 : Blo 1776089 1776175 := bstep (se 1 (by rfl) ⟨1332131, by rfl⟩ : syracuseStep 1776175 = 2664263) B2664263
theorem B1776447 : Blo 1776089 1776447 := bstep (se 1 (by rfl) ⟨1332335, by rfl⟩ : syracuseStep 1776447 = 2664671) B2664671
theorem B985291613 : Blo 1776089 985291613 := bstep (se 3 (by rfl) ⟨184742177, by rfl⟩ : syracuseStep 985291613 = 369484355) B369484355
theorem B1776487 : Blo 1776089 1776487 := bstep (se 1 (by rfl) ⟨1332365, by rfl⟩ : syracuseStep 1776487 = 2664731) B2664731
theorem B4496249 : Blo 1776089 4496249 := bstep (se 2 (by rfl) ⟨1686093, by rfl⟩ : syracuseStep 4496249 = 3372187) B3372187
theorem B1776575 : Blo 1776089 1776575 := bstep (se 1 (by rfl) ⟨1332431, by rfl⟩ : syracuseStep 1776575 = 2664863) B2664863
theorem B1776703 : Blo 1776089 1776703 := bstep (se 1 (by rfl) ⟨1332527, by rfl⟩ : syracuseStep 1776703 = 2665055) B2665055
theorem B15178873 : Blo 1776089 15178873 := bstep (se 2 (by rfl) ⟨5692077, by rfl⟩ : syracuseStep 15178873 = 11384155) B11384155
theorem B3996827 : Blo 1776089 3996827 := bstep (se 1 (by rfl) ⟨2997620, by rfl⟩ : syracuseStep 3996827 = 5995241) B5995241
theorem B10804499 : Blo 1776089 10804499 := bstep (se 1 (by rfl) ⟨8103374, by rfl⟩ : syracuseStep 10804499 = 16206749) B16206749
theorem B1776923 : Blo 1776089 1776923 := bstep (se 1 (by rfl) ⟨1332692, by rfl⟩ : syracuseStep 1776923 = 2665385) B2665385
theorem B1776943 : Blo 1776089 1776943 := bstep (se 1 (by rfl) ⟨1332707, by rfl⟩ : syracuseStep 1776943 = 2665415) B2665415
theorem B5127479 : Blo 1776089 5127479 := bstep (se 1 (by rfl) ⟨3845609, by rfl⟩ : syracuseStep 5127479 = 7691219) B7691219
theorem B1777023 : Blo 1776089 1777023 := bstep (se 1 (by rfl) ⟨1332767, by rfl⟩ : syracuseStep 1777023 = 2665535) B2665535
theorem B1777183 : Blo 1776089 1777183 := bstep (se 1 (by rfl) ⟨1332887, by rfl⟩ : syracuseStep 1777183 = 2665775) B2665775
theorem B230645393 : Blo 1776089 230645393 := bstep (se 2 (by rfl) ⟨86492022, by rfl⟩ : syracuseStep 230645393 = 172984045) B172984045
theorem B1777307 : Blo 1776089 1777307 := bstep (se 1 (by rfl) ⟨1332980, by rfl⟩ : syracuseStep 1777307 = 2665961) B2665961
theorem B1777343 : Blo 1776089 1777343 := bstep (se 1 (by rfl) ⟨1333007, by rfl⟩ : syracuseStep 1777343 = 2666015) B2666015
theorem B1777403 : Blo 1776089 1777403 := bstep (se 1 (by rfl) ⟨1333052, by rfl⟩ : syracuseStep 1777403 = 2666105) B2666105
theorem B17309497 : Blo 1776089 17309497 := bstep (se 2 (by rfl) ⟨6491061, by rfl⟩ : syracuseStep 17309497 = 12982123) B12982123
theorem B1777567 : Blo 1776089 1777567 := bstep (se 1 (by rfl) ⟨1333175, by rfl⟩ : syracuseStep 1777567 = 2666351) B2666351
theorem B5693399 : Blo 1776089 5693399 := bstep (se 1 (by rfl) ⟨4270049, by rfl⟩ : syracuseStep 5693399 = 8540099) B8540099
theorem B9609191 : Blo 1776089 9609191 := bstep (se 1 (by rfl) ⟨7206893, by rfl⟩ : syracuseStep 9609191 = 14413787) B14413787
theorem B2998255 : Blo 1776089 2998255 := bstep (se 1 (by rfl) ⟨2248691, by rfl⟩ : syracuseStep 2998255 = 4497383) B4497383
theorem B5996537 : Blo 1776089 5996537 := bstep (se 2 (by rfl) ⟨2248701, by rfl⟩ : syracuseStep 5996537 = 4497403) B4497403
theorem B1777695 : Blo 1776089 1777695 := bstep (se 1 (by rfl) ⟨1333271, by rfl⟩ : syracuseStep 1777695 = 2666543) B2666543
theorem B16212001 : Blo 1776089 16212001 := bstep (se 2 (by rfl) ⟨6079500, by rfl⟩ : syracuseStep 16212001 = 12159001) B12159001
theorem B1777727 : Blo 1776089 1777727 := bstep (se 1 (by rfl) ⟨1333295, by rfl⟩ : syracuseStep 1777727 = 2666591) B2666591
theorem B1777767 : Blo 1776089 1777767 := bstep (se 1 (by rfl) ⟨1333325, by rfl⟩ : syracuseStep 1777767 = 2666651) B2666651
theorem B1777775 : Blo 1776089 1777775 := bstep (se 1 (by rfl) ⟨1333331, by rfl⟩ : syracuseStep 1777775 = 2666663) B2666663
theorem B5996699 : Blo 1776089 5996699 := bstep (se 1 (by rfl) ⟨4497524, by rfl⟩ : syracuseStep 5996699 = 8995049) B8995049
theorem B1777887 : Blo 1776089 1777887 := bstep (se 1 (by rfl) ⟨1333415, by rfl⟩ : syracuseStep 1777887 = 2666831) B2666831
theorem B51225007 : Blo 1776089 51225007 := bstep (se 1 (by rfl) ⟨38418755, by rfl⟩ : syracuseStep 51225007 = 76837511) B76837511
theorem B473686703 : Blo 1776089 473686703 := bstep (se 1 (by rfl) ⟨355265027, by rfl⟩ : syracuseStep 473686703 = 710530055) B710530055
theorem B8995535 : Blo 1776089 8995535 := bstep (se 1 (by rfl) ⟨6746651, by rfl⟩ : syracuseStep 8995535 = 13493303) B13493303
theorem B1999615 : Blo 1776089 1999615 := bstep (se 1 (by rfl) ⟨1499711, by rfl⟩ : syracuseStep 1999615 = 2999423) B2999423
theorem B3998555 : Blo 1776089 3998555 := bstep (se 1 (by rfl) ⟨2998916, by rfl⟩ : syracuseStep 3998555 = 5997833) B5997833
theorem B9601921 : Blo 1776089 9601921 := bstep (se 2 (by rfl) ⟨3600720, by rfl⟩ : syracuseStep 9601921 = 7201441) B7201441
theorem B58451129 : Blo 1776089 58451129 := bstep (se 2 (by rfl) ⟨21919173, by rfl⟩ : syracuseStep 58451129 = 43838347) B43838347
theorem B10126721 : Blo 1776089 10126721 := bstep (se 2 (by rfl) ⟨3797520, by rfl⟩ : syracuseStep 10126721 = 7595041) B7595041
theorem B5998427 : Blo 1776089 5998427 := bstep (se 1 (by rfl) ⟨4498820, by rfl⟩ : syracuseStep 5998427 = 8997641) B8997641
theorem B656861075 : Blo 1776089 656861075 := bstep (se 1 (by rfl) ⟨492645806, by rfl⟩ : syracuseStep 656861075 = 985291613) B985291613
theorem B8996831 : Blo 1776089 8996831 := bstep (se 1 (by rfl) ⟨6747623, by rfl⟩ : syracuseStep 8996831 = 13495247) B13495247
theorem B3997691 : Blo 1776089 3997691 := bstep (se 1 (by rfl) ⟨2998268, by rfl⟩ : syracuseStep 3997691 = 5996537) B5996537
theorem B69273647 : Blo 1776089 69273647 := bstep (se 1 (by rfl) ⟨51955235, by rfl⟩ : syracuseStep 69273647 = 103910471) B103910471
theorem B2664551 : Blo 1776089 2664551 := bstep (se 1 (by rfl) ⟨1998413, by rfl⟩ : syracuseStep 2664551 = 3996827) B3996827
theorem B7202999 : Blo 1776089 7202999 := bstep (se 1 (by rfl) ⟨5402249, by rfl⟩ : syracuseStep 7202999 = 10804499) B10804499
theorem B3418319 : Blo 1776089 3418319 := bstep (se 1 (by rfl) ⟨2563739, by rfl⟩ : syracuseStep 3418319 = 5127479) B5127479
theorem B19220759 : Blo 1776089 19220759 := bstep (se 1 (by rfl) ⟨14415569, by rfl⟩ : syracuseStep 19220759 = 28831139) B28831139
theorem B23079329 : Blo 1776089 23079329 := bstep (se 2 (by rfl) ⟨8654748, by rfl⟩ : syracuseStep 23079329 = 17309497) B17309497
theorem B10119613 : Blo 1776089 10119613 := bstep (se 3 (by rfl) ⟨1897427, by rfl⟩ : syracuseStep 10119613 = 3794855) B3794855
theorem B3795599 : Blo 1776089 3795599 := bstep (se 1 (by rfl) ⟨2846699, by rfl⟩ : syracuseStep 3795599 = 5693399) B5693399
theorem B24308369 : Blo 1776089 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B4000481 : Blo 1776089 4000481 := bstep (se 2 (by rfl) ⟨1500180, by rfl⟩ : syracuseStep 4000481 = 3000361) B3000361
theorem B6744815 : Blo 1776089 6744815 := bstep (se 1 (by rfl) ⟨5058611, by rfl⟩ : syracuseStep 6744815 = 10117223) B10117223
theorem B2665337 : Blo 1776089 2665337 := bstep (se 2 (by rfl) ⟨999501, by rfl⟩ : syracuseStep 2665337 = 1999003) B1999003
theorem B5057711 : Blo 1776089 5057711 := bstep (se 1 (by rfl) ⟨3793283, by rfl⟩ : syracuseStep 5057711 = 7586567) B7586567
theorem B8219999 : Blo 1776089 8219999 := bstep (se 1 (by rfl) ⟨6164999, by rfl⟩ : syracuseStep 8219999 = 12329999) B12329999
theorem B18247007 : Blo 1776089 18247007 := bstep (se 1 (by rfl) ⟨13685255, by rfl⟩ : syracuseStep 18247007 = 27370511) B27370511
theorem B10120571 : Blo 1776089 10120571 := bstep (se 1 (by rfl) ⟨7590428, by rfl⟩ : syracuseStep 10120571 = 15180857) B15180857
theorem B2665919 : Blo 1776089 2665919 := bstep (se 1 (by rfl) ⟨1999439, by rfl⟩ : syracuseStep 2665919 = 3998879) B3998879
theorem B10120889 : Blo 1776089 10120889 := bstep (se 2 (by rfl) ⟨3795333, by rfl⟩ : syracuseStep 10120889 = 7590667) B7590667
theorem B20238497 : Blo 1776089 20238497 := bstep (se 2 (by rfl) ⟨7589436, by rfl⟩ : syracuseStep 20238497 = 15178873) B15178873
theorem B2666921 : Blo 1776089 2666921 := bstep (se 2 (by rfl) ⟨1000095, by rfl⟩ : syracuseStep 2666921 = 2000191) B2000191
theorem B6746591 : Blo 1776089 6746591 := bstep (se 1 (by rfl) ⟨5059943, by rfl⟩ : syracuseStep 6746591 = 10119887) B10119887
theorem B2666975 : Blo 1776089 2666975 := bstep (se 1 (by rfl) ⟨2000231, by rfl⟩ : syracuseStep 2666975 = 4000463) B4000463
theorem B2667113 : Blo 1776089 2667113 := bstep (se 2 (by rfl) ⟨1000167, by rfl⟩ : syracuseStep 2667113 = 2000335) B2000335
theorem B76870727 : Blo 1776089 76870727 := bstep (se 1 (by rfl) ⟨57653045, by rfl⟩ : syracuseStep 76870727 = 115306091) B115306091
theorem B5059739 : Blo 1776089 5059739 := bstep (se 1 (by rfl) ⟨3794804, by rfl⟩ : syracuseStep 5059739 = 7589609) B7589609
theorem B1897663 : Blo 1776089 1897663 := bstep (se 1 (by rfl) ⟨1423247, by rfl⟩ : syracuseStep 1897663 = 2846495) B2846495
theorem B6493673 : Blo 1776089 6493673 := bstep (se 2 (by rfl) ⟨2435127, by rfl⟩ : syracuseStep 6493673 = 4870255) B4870255
theorem B7206569 : Blo 1776089 7206569 := bstep (se 2 (by rfl) ⟨2702463, by rfl⟩ : syracuseStep 7206569 = 5404927) B5404927
theorem B8992619 : Blo 1776089 8992619 := bstep (se 1 (by rfl) ⟨6744464, by rfl⟩ : syracuseStep 8992619 = 13488929) B13488929
theorem B10803431 : Blo 1776089 10803431 := bstep (se 1 (by rfl) ⟨8102573, by rfl⟩ : syracuseStep 10803431 = 16205147) B16205147
theorem B8993105 : Blo 1776089 8993105 := bstep (se 2 (by rfl) ⟨3372414, by rfl⟩ : syracuseStep 8993105 = 6744829) B6744829
theorem B1776283 : Blo 1776089 1776283 := bstep (se 1 (by rfl) ⟨1332212, by rfl⟩ : syracuseStep 1776283 = 2664425) B2664425
theorem B19479359 : Blo 1776089 19479359 := bstep (se 1 (by rfl) ⟨14609519, by rfl⟩ : syracuseStep 19479359 = 29219039) B29219039
theorem B3996539 : Blo 1776089 3996539 := bstep (se 1 (by rfl) ⟨2997404, by rfl⟩ : syracuseStep 3996539 = 5994809) B5994809
theorem B1776607 : Blo 1776089 1776607 := bstep (se 1 (by rfl) ⟨1332455, by rfl⟩ : syracuseStep 1776607 = 2664911) B2664911
theorem B2997499 : Blo 1776089 2997499 := bstep (se 1 (by rfl) ⟨2248124, by rfl⟩ : syracuseStep 2997499 = 4496249) B4496249
theorem B1777119 : Blo 1776089 1777119 := bstep (se 1 (by rfl) ⟨1332839, by rfl⟩ : syracuseStep 1777119 = 2665679) B2665679
theorem B1777199 : Blo 1776089 1777199 := bstep (se 1 (by rfl) ⟨1332899, by rfl⟩ : syracuseStep 1777199 = 2665799) B2665799
theorem B15187621 : Blo 1776089 15187621 := bstep (se 4 (by rfl) ⟨1423839, by rfl⟩ : syracuseStep 15187621 = 2847679) B2847679
theorem B153763595 : Blo 1776089 153763595 := bstep (se 1 (by rfl) ⟨115322696, by rfl⟩ : syracuseStep 153763595 = 230645393) B230645393
theorem B4497191 : Blo 1776089 4497191 := bstep (se 1 (by rfl) ⟨3372893, by rfl⟩ : syracuseStep 4497191 = 6745787) B6745787
theorem B1777499 : Blo 1776089 1777499 := bstep (se 1 (by rfl) ⟨1333124, by rfl⟩ : syracuseStep 1777499 = 2666249) B2666249
theorem B1777599 : Blo 1776089 1777599 := bstep (se 1 (by rfl) ⟨1333199, by rfl⟩ : syracuseStep 1777599 = 2666399) B2666399
theorem B3997673 : Blo 1776089 3997673 := bstep (se 2 (by rfl) ⟨1499127, by rfl⟩ : syracuseStep 3997673 = 2998255) B2998255
theorem B6406127 : Blo 1776089 6406127 := bstep (se 1 (by rfl) ⟨4804595, by rfl⟩ : syracuseStep 6406127 = 9609191) B9609191
theorem B1777647 : Blo 1776089 1777647 := bstep (se 1 (by rfl) ⟨1333235, by rfl⟩ : syracuseStep 1777647 = 2666471) B2666471
theorem B3997799 : Blo 1776089 3997799 := bstep (se 1 (by rfl) ⟨2998349, by rfl⟩ : syracuseStep 3997799 = 5996699) B5996699
theorem B13492331 : Blo 1776089 13492331 := bstep (se 1 (by rfl) ⟨10119248, by rfl⟩ : syracuseStep 13492331 = 20238497) B20238497
theorem B1777947 : Blo 1776089 1777947 := bstep (se 1 (by rfl) ⟨1333460, by rfl⟩ : syracuseStep 1777947 = 2666921) B2666921
theorem B4497727 : Blo 1776089 4497727 := bstep (se 1 (by rfl) ⟨3373295, by rfl⟩ : syracuseStep 4497727 = 6746591) B6746591
theorem B1777983 : Blo 1776089 1777983 := bstep (se 1 (by rfl) ⟨1333487, by rfl⟩ : syracuseStep 1777983 = 2666975) B2666975
theorem B1778075 : Blo 1776089 1778075 := bstep (se 1 (by rfl) ⟨1333556, by rfl⟩ : syracuseStep 1778075 = 2667113) B2667113
theorem B5997023 : Blo 1776089 5997023 := bstep (se 1 (by rfl) ⟨4497767, by rfl⟩ : syracuseStep 5997023 = 8995535) B8995535
theorem B13492817 : Blo 1776089 13492817 := bstep (se 2 (by rfl) ⟨5059806, by rfl⟩ : syracuseStep 13492817 = 10119613) B10119613
theorem B6751147 : Blo 1776089 6751147 := bstep (se 1 (by rfl) ⟨5063360, by rfl⟩ : syracuseStep 6751147 = 10126721) B10126721
theorem B3998951 : Blo 1776089 3998951 := bstep (se 1 (by rfl) ⟨2999213, by rfl⟩ : syracuseStep 3998951 = 5998427) B5998427
theorem B5997887 : Blo 1776089 5997887 := bstep (se 1 (by rfl) ⟨4498415, by rfl⟩ : syracuseStep 5997887 = 8996831) B8996831
theorem B4801999 : Blo 1776089 4801999 := bstep (se 1 (by rfl) ⟨3601499, by rfl⟩ : syracuseStep 4801999 = 7202999) B7202999
theorem B7202287 : Blo 1776089 7202287 := bstep (se 1 (by rfl) ⟨5401715, by rfl⟩ : syracuseStep 7202287 = 10803431) B10803431
theorem B12813839 : Blo 1776089 12813839 := bstep (se 1 (by rfl) ⟨9610379, by rfl⟩ : syracuseStep 12813839 = 19220759) B19220759
theorem B15386219 : Blo 1776089 15386219 := bstep (se 1 (by rfl) ⟨11539664, by rfl⟩ : syracuseStep 15386219 = 23079329) B23079329
theorem B16205579 : Blo 1776089 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B12986239 : Blo 1776089 12986239 := bstep (se 1 (by rfl) ⟨9739679, by rfl⟩ : syracuseStep 12986239 = 19479359) B19479359
theorem B2664359 : Blo 1776089 2664359 := bstep (se 1 (by rfl) ⟨1998269, by rfl⟩ : syracuseStep 2664359 = 3996539) B3996539
theorem B51210245 : Blo 1776089 51210245 := bstep (se 4 (by rfl) ⟨4800960, by rfl⟩ : syracuseStep 51210245 = 9601921) B9601921
theorem B102509063 : Blo 1776089 102509063 := bstep (se 1 (by rfl) ⟨76881797, by rfl⟩ : syracuseStep 102509063 = 153763595) B153763595
theorem B2665115 : Blo 1776089 2665115 := bstep (se 1 (by rfl) ⟨1998836, by rfl⟩ : syracuseStep 2665115 = 3997673) B3997673
theorem B4270751 : Blo 1776089 4270751 := bstep (se 1 (by rfl) ⟨3203063, by rfl⟩ : syracuseStep 4270751 = 6406127) B6406127
theorem B2665127 : Blo 1776089 2665127 := bstep (se 1 (by rfl) ⟨1998845, by rfl⟩ : syracuseStep 2665127 = 3997691) B3997691
theorem B2665703 : Blo 1776089 2665703 := bstep (se 1 (by rfl) ⟨1999277, by rfl⟩ : syracuseStep 2665703 = 3998555) B3998555
theorem B68300009 : Blo 1776089 68300009 := bstep (se 2 (by rfl) ⟨25612503, by rfl⟩ : syracuseStep 68300009 = 51225007) B51225007
theorem B2666153 : Blo 1776089 2666153 := bstep (se 2 (by rfl) ⟨999807, by rfl⟩ : syracuseStep 2666153 = 1999615) B1999615
theorem B4804379 : Blo 1776089 4804379 := bstep (se 1 (by rfl) ⟨3603284, by rfl⟩ : syracuseStep 4804379 = 7206569) B7206569
theorem B437907383 : Blo 1776089 437907383 := bstep (se 1 (by rfl) ⟨328430537, by rfl⟩ : syracuseStep 437907383 = 656861075) B656861075
theorem B46182431 : Blo 1776089 46182431 := bstep (se 1 (by rfl) ⟨34636823, by rfl⟩ : syracuseStep 46182431 = 69273647) B69273647
theorem B10121597 : Blo 1776089 10121597 := bstep (se 3 (by rfl) ⟨1897799, by rfl⟩ : syracuseStep 10121597 = 3795599) B3795599
theorem B2666987 : Blo 1776089 2666987 := bstep (se 1 (by rfl) ⟨2000240, by rfl⟩ : syracuseStep 2666987 = 4000481) B4000481
theorem B3371807 : Blo 1776089 3371807 := bstep (se 1 (by rfl) ⟨2528855, by rfl⟩ : syracuseStep 3371807 = 5057711) B5057711
theorem B6747047 : Blo 1776089 6747047 := bstep (se 1 (by rfl) ⟨5060285, by rfl⟩ : syracuseStep 6747047 = 10120571) B10120571
theorem B6747259 : Blo 1776089 6747259 := bstep (se 1 (by rfl) ⟨5060444, by rfl⟩ : syracuseStep 6747259 = 10120889) B10120889
theorem B21616001 : Blo 1776089 21616001 := bstep (se 2 (by rfl) ⟨8106000, by rfl⟩ : syracuseStep 21616001 = 16212001) B16212001
theorem B315791135 : Blo 1776089 315791135 := bstep (se 1 (by rfl) ⟨236843351, by rfl⟩ : syracuseStep 315791135 = 473686703) B473686703
theorem B9115517 : Blo 1776089 9115517 := bstep (se 3 (by rfl) ⟨1709159, by rfl⟩ : syracuseStep 9115517 = 3418319) B3418319
theorem B51247151 : Blo 1776089 51247151 := bstep (se 1 (by rfl) ⟨38435363, by rfl⟩ : syracuseStep 51247151 = 76870727) B76870727
theorem B3373159 : Blo 1776089 3373159 := bstep (se 1 (by rfl) ⟨2529869, by rfl⟩ : syracuseStep 3373159 = 5059739) B5059739
theorem B38967419 : Blo 1776089 38967419 := bstep (se 1 (by rfl) ⟨29225564, by rfl⟩ : syracuseStep 38967419 = 58451129) B58451129
theorem B21919997 : Blo 1776089 21919997 := bstep (se 3 (by rfl) ⟨4109999, by rfl⟩ : syracuseStep 21919997 = 8219999) B8219999
theorem B5995079 : Blo 1776089 5995079 := bstep (se 1 (by rfl) ⟨4496309, by rfl⟩ : syracuseStep 5995079 = 8992619) B8992619
theorem B17316461 : Blo 1776089 17316461 := bstep (se 3 (by rfl) ⟨3246836, by rfl⟩ : syracuseStep 17316461 = 6493673) B6493673
theorem B1776367 : Blo 1776089 1776367 := bstep (se 1 (by rfl) ⟨1332275, by rfl⟩ : syracuseStep 1776367 = 2664551) B2664551
theorem B5995403 : Blo 1776089 5995403 := bstep (se 1 (by rfl) ⟨4496552, by rfl⟩ : syracuseStep 5995403 = 8993105) B8993105
theorem B2530217 : Blo 1776089 2530217 := bstep (se 2 (by rfl) ⟨948831, by rfl⟩ : syracuseStep 2530217 = 1897663) B1897663
theorem B3996665 : Blo 1776089 3996665 := bstep (se 2 (by rfl) ⟨1498749, by rfl⟩ : syracuseStep 3996665 = 2997499) B2997499
theorem B4496543 : Blo 1776089 4496543 := bstep (se 1 (by rfl) ⟨3372407, by rfl⟩ : syracuseStep 4496543 = 6744815) B6744815
theorem B1776891 : Blo 1776089 1776891 := bstep (se 1 (by rfl) ⟨1332668, by rfl⟩ : syracuseStep 1776891 = 2665337) B2665337
theorem B20250161 : Blo 1776089 20250161 := bstep (se 2 (by rfl) ⟨7593810, by rfl⟩ : syracuseStep 20250161 = 15187621) B15187621
theorem B12164671 : Blo 1776089 12164671 := bstep (se 1 (by rfl) ⟨9123503, by rfl⟩ : syracuseStep 12164671 = 18247007) B18247007
theorem B1777279 : Blo 1776089 1777279 := bstep (se 1 (by rfl) ⟨1332959, by rfl⟩ : syracuseStep 1777279 = 2665919) B2665919
theorem B2998127 : Blo 1776089 2998127 := bstep (se 1 (by rfl) ⟨2248595, by rfl⟩ : syracuseStep 2998127 = 4497191) B4497191
theorem B8994887 : Blo 1776089 8994887 := bstep (se 1 (by rfl) ⟨6746165, by rfl⟩ : syracuseStep 8994887 = 13492331) B13492331
theorem B4497545 : Blo 1776089 4497545 := bstep (se 2 (by rfl) ⟨1686579, by rfl⟩ : syracuseStep 4497545 = 3373159) B3373159
theorem B3998015 : Blo 1776089 3998015 := bstep (se 1 (by rfl) ⟨2998511, by rfl⟩ : syracuseStep 3998015 = 5997023) B5997023
theorem B1777991 : Blo 1776089 1777991 := bstep (se 1 (by rfl) ⟨1333493, by rfl⟩ : syracuseStep 1777991 = 2666987) B2666987
theorem B8995211 : Blo 1776089 8995211 := bstep (se 1 (by rfl) ⟨6746408, by rfl⟩ : syracuseStep 8995211 = 13492817) B13492817
theorem B5996969 : Blo 1776089 5996969 := bstep (se 2 (by rfl) ⟨2248863, by rfl⟩ : syracuseStep 5996969 = 4497727) B4497727
theorem B4498031 : Blo 1776089 4498031 := bstep (se 1 (by rfl) ⟨3373523, by rfl⟩ : syracuseStep 4498031 = 6747047) B6747047
theorem B3998591 : Blo 1776089 3998591 := bstep (se 1 (by rfl) ⟨2998943, by rfl⟩ : syracuseStep 3998591 = 5997887) B5997887
theorem B14410667 : Blo 1776089 14410667 := bstep (se 1 (by rfl) ⟨10808000, by rfl⟩ : syracuseStep 14410667 = 21616001) B21616001
theorem B10257479 : Blo 1776089 10257479 := bstep (se 1 (by rfl) ⟨7693109, by rfl⟩ : syracuseStep 10257479 = 15386219) B15386219
theorem B210527423 : Blo 1776089 210527423 := bstep (se 1 (by rfl) ⟨157895567, by rfl⟩ : syracuseStep 210527423 = 315791135) B315791135
theorem B25978279 : Blo 1776089 25978279 := bstep (se 1 (by rfl) ⟨19483709, by rfl⟩ : syracuseStep 25978279 = 38967419) B38967419
theorem B8996345 : Blo 1776089 8996345 := bstep (se 2 (by rfl) ⟨3373629, by rfl⟩ : syracuseStep 8996345 = 6747259) B6747259
theorem B68339375 : Blo 1776089 68339375 := bstep (se 1 (by rfl) ⟨51254531, by rfl⟩ : syracuseStep 68339375 = 102509063) B102509063
theorem B9603049 : Blo 1776089 9603049 := bstep (se 2 (by rfl) ⟨3601143, by rfl⟩ : syracuseStep 9603049 = 7202287) B7202287
theorem B2664443 : Blo 1776089 2664443 := bstep (se 1 (by rfl) ⟨1998332, by rfl⟩ : syracuseStep 2664443 = 3996665) B3996665
theorem B45533339 : Blo 1776089 45533339 := bstep (se 1 (by rfl) ⟨34150004, by rfl⟩ : syracuseStep 45533339 = 68300009) B68300009
theorem B24308045 : Blo 1776089 24308045 := bstep (se 3 (by rfl) ⟨4557758, by rfl⟩ : syracuseStep 24308045 = 9115517) B9115517
theorem B2665199 : Blo 1776089 2665199 := bstep (se 1 (by rfl) ⟨1998899, by rfl⟩ : syracuseStep 2665199 = 3997799) B3997799
theorem B123153149 : Blo 1776089 123153149 := bstep (se 3 (by rfl) ⟨23091215, by rfl⟩ : syracuseStep 123153149 = 46182431) B46182431
theorem B58453325 : Blo 1776089 58453325 := bstep (se 3 (by rfl) ⟨10959998, by rfl⟩ : syracuseStep 58453325 = 21919997) B21919997
theorem B2665967 : Blo 1776089 2665967 := bstep (se 1 (by rfl) ⟨1999475, by rfl⟩ : syracuseStep 2665967 = 3998951) B3998951
theorem B34140163 : Blo 1776089 34140163 := bstep (se 1 (by rfl) ⟨25605122, by rfl⟩ : syracuseStep 34140163 = 51210245) B51210245
theorem B34164767 : Blo 1776089 34164767 := bstep (se 1 (by rfl) ⟨25623575, by rfl⟩ : syracuseStep 34164767 = 51247151) B51247151
theorem B2847167 : Blo 1776089 2847167 := bstep (se 1 (by rfl) ⟨2135375, by rfl⟩ : syracuseStep 2847167 = 4270751) B4270751
theorem B6402665 : Blo 1776089 6402665 := bstep (se 2 (by rfl) ⟨2400999, by rfl⟩ : syracuseStep 6402665 = 4801999) B4801999
theorem B8991485 : Blo 1776089 8991485 := bstep (se 3 (by rfl) ⟨1685903, by rfl⟩ : syracuseStep 8991485 = 3371807) B3371807
theorem B6747245 : Blo 1776089 6747245 := bstep (se 3 (by rfl) ⟨1265108, by rfl⟩ : syracuseStep 6747245 = 2530217) B2530217
theorem B17314985 : Blo 1776089 17314985 := bstep (se 2 (by rfl) ⟨6493119, by rfl⟩ : syracuseStep 17314985 = 12986239) B12986239
theorem B6747731 : Blo 1776089 6747731 := bstep (se 1 (by rfl) ⟨5060798, by rfl⟩ : syracuseStep 6747731 = 10121597) B10121597
theorem B64878245 : Blo 1776089 64878245 := bstep (se 4 (by rfl) ⟨6082335, by rfl⟩ : syracuseStep 64878245 = 12164671) B12164671
theorem B8542559 : Blo 1776089 8542559 := bstep (se 1 (by rfl) ⟨6406919, by rfl⟩ : syracuseStep 8542559 = 12813839) B12813839
theorem B10803719 : Blo 1776089 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B9001529 : Blo 1776089 9001529 := bstep (se 2 (by rfl) ⟨3375573, by rfl⟩ : syracuseStep 9001529 = 6751147) B6751147
theorem B1776239 : Blo 1776089 1776239 := bstep (se 1 (by rfl) ⟨1332179, by rfl⟩ : syracuseStep 1776239 = 2664359) B2664359
theorem B46177229 : Blo 1776089 46177229 := bstep (se 3 (by rfl) ⟨8658230, by rfl⟩ : syracuseStep 46177229 = 17316461) B17316461
theorem B3996719 : Blo 1776089 3996719 := bstep (se 1 (by rfl) ⟨2997539, by rfl⟩ : syracuseStep 3996719 = 5995079) B5995079
theorem B1776743 : Blo 1776089 1776743 := bstep (se 1 (by rfl) ⟨1332557, by rfl⟩ : syracuseStep 1776743 = 2665115) B2665115
theorem B1776751 : Blo 1776089 1776751 := bstep (se 1 (by rfl) ⟨1332563, by rfl⟩ : syracuseStep 1776751 = 2665127) B2665127
theorem B3996935 : Blo 1776089 3996935 := bstep (se 1 (by rfl) ⟨2997701, by rfl⟩ : syracuseStep 3996935 = 5995403) B5995403
theorem B2997695 : Blo 1776089 2997695 := bstep (se 1 (by rfl) ⟨2248271, by rfl⟩ : syracuseStep 2997695 = 4496543) B4496543
theorem B1777135 : Blo 1776089 1777135 := bstep (se 1 (by rfl) ⟨1332851, by rfl⟩ : syracuseStep 1777135 = 2665703) B2665703
theorem B13500107 : Blo 1776089 13500107 := bstep (se 1 (by rfl) ⟨10125080, by rfl⟩ : syracuseStep 13500107 = 20250161) B20250161
theorem B1777435 : Blo 1776089 1777435 := bstep (se 1 (by rfl) ⟨1333076, by rfl⟩ : syracuseStep 1777435 = 2666153) B2666153
theorem B3202919 : Blo 1776089 3202919 := bstep (se 1 (by rfl) ⟨2402189, by rfl⟩ : syracuseStep 3202919 = 4804379) B4804379
theorem B1998751 : Blo 1776089 1998751 := bstep (se 1 (by rfl) ⟨1499063, by rfl⟩ : syracuseStep 1998751 = 2998127) B2998127
theorem B291938255 : Blo 1776089 291938255 := bstep (se 1 (by rfl) ⟨218953691, by rfl⟩ : syracuseStep 291938255 = 437907383) B437907383
theorem B5996591 : Blo 1776089 5996591 := bstep (se 1 (by rfl) ⟨4497443, by rfl⟩ : syracuseStep 5996591 = 8994887) B8994887
theorem B2998363 : Blo 1776089 2998363 := bstep (se 1 (by rfl) ⟨2248772, by rfl⟩ : syracuseStep 2998363 = 4497545) B4497545
theorem B5996807 : Blo 1776089 5996807 := bstep (se 1 (by rfl) ⟨4497605, by rfl⟩ : syracuseStep 5996807 = 8995211) B8995211
theorem B3997979 : Blo 1776089 3997979 := bstep (se 1 (by rfl) ⟨2998484, by rfl⟩ : syracuseStep 3997979 = 5996969) B5996969
theorem B2998687 : Blo 1776089 2998687 := bstep (se 1 (by rfl) ⟨2249015, by rfl⟩ : syracuseStep 2998687 = 4498031) B4498031
theorem B4498163 : Blo 1776089 4498163 := bstep (se 1 (by rfl) ⟨3373622, by rfl⟩ : syracuseStep 4498163 = 6747245) B6747245
theorem B11543323 : Blo 1776089 11543323 := bstep (se 1 (by rfl) ⟨8657492, by rfl⟩ : syracuseStep 11543323 = 17314985) B17314985
theorem B5997563 : Blo 1776089 5997563 := bstep (se 1 (by rfl) ⟨4498172, by rfl⟩ : syracuseStep 5997563 = 8996345) B8996345
theorem B4498487 : Blo 1776089 4498487 := bstep (se 1 (by rfl) ⟨3373865, by rfl⟩ : syracuseStep 4498487 = 6747731) B6747731
theorem B16205363 : Blo 1776089 16205363 := bstep (se 1 (by rfl) ⟨12154022, by rfl⟩ : syracuseStep 16205363 = 24308045) B24308045
theorem B5695039 : Blo 1776089 5695039 := bstep (se 1 (by rfl) ⟨4271279, by rfl⟩ : syracuseStep 5695039 = 8542559) B8542559
theorem B17073773 : Blo 1776089 17073773 := bstep (se 3 (by rfl) ⟨3201332, by rfl⟩ : syracuseStep 17073773 = 6402665) B6402665
theorem B82102099 : Blo 1776089 82102099 := bstep (se 1 (by rfl) ⟨61576574, by rfl⟩ : syracuseStep 82102099 = 123153149) B123153149
theorem B34637705 : Blo 1776089 34637705 := bstep (se 2 (by rfl) ⟨12989139, by rfl⟩ : syracuseStep 34637705 = 25978279) B25978279
theorem B2664479 : Blo 1776089 2664479 := bstep (se 1 (by rfl) ⟨1998359, by rfl⟩ : syracuseStep 2664479 = 3996719) B3996719
theorem B2664623 : Blo 1776089 2664623 := bstep (se 1 (by rfl) ⟨1998467, by rfl⟩ : syracuseStep 2664623 = 3996935) B3996935
theorem B2665001 : Blo 1776089 2665001 := bstep (se 2 (by rfl) ⟨999375, by rfl⟩ : syracuseStep 2665001 = 1998751) B1998751
theorem B22776511 : Blo 1776089 22776511 := bstep (se 1 (by rfl) ⟨17082383, by rfl⟩ : syracuseStep 22776511 = 34164767) B34164767
theorem B2665343 : Blo 1776089 2665343 := bstep (se 1 (by rfl) ⟨1999007, by rfl⟩ : syracuseStep 2665343 = 3998015) B3998015
theorem B2665727 : Blo 1776089 2665727 := bstep (se 1 (by rfl) ⟨1999295, by rfl⟩ : syracuseStep 2665727 = 3998591) B3998591
theorem B45559583 : Blo 1776089 45559583 := bstep (se 1 (by rfl) ⟨34169687, by rfl⟩ : syracuseStep 45559583 = 68339375) B68339375
theorem B30355559 : Blo 1776089 30355559 := bstep (se 1 (by rfl) ⟨22766669, by rfl⟩ : syracuseStep 30355559 = 45533339) B45533339
theorem B6001019 : Blo 1776089 6001019 := bstep (se 1 (by rfl) ⟨4500764, by rfl⟩ : syracuseStep 6001019 = 9001529) B9001529
theorem B9000071 : Blo 1776089 9000071 := bstep (se 1 (by rfl) ⟨6750053, by rfl⟩ : syracuseStep 9000071 = 13500107) B13500107
theorem B123139277 : Blo 1776089 123139277 := bstep (se 3 (by rfl) ⟨23088614, by rfl⟩ : syracuseStep 123139277 = 46177229) B46177229
theorem B2135279 : Blo 1776089 2135279 := bstep (se 1 (by rfl) ⟨1601459, by rfl⟩ : syracuseStep 2135279 = 3202919) B3202919
theorem B45520217 : Blo 1776089 45520217 := bstep (se 2 (by rfl) ⟨17070081, by rfl⟩ : syracuseStep 45520217 = 34140163) B34140163
theorem B1898111 : Blo 1776089 1898111 := bstep (se 1 (by rfl) ⟨1423583, by rfl⟩ : syracuseStep 1898111 = 2847167) B2847167
theorem B5994323 : Blo 1776089 5994323 := bstep (se 1 (by rfl) ⟨4495742, by rfl⟩ : syracuseStep 5994323 = 8991485) B8991485
theorem B6838319 : Blo 1776089 6838319 := bstep (se 1 (by rfl) ⟨5128739, by rfl⟩ : syracuseStep 6838319 = 10257479) B10257479
theorem B140351615 : Blo 1776089 140351615 := bstep (se 1 (by rfl) ⟨105263711, by rfl⟩ : syracuseStep 140351615 = 210527423) B210527423
theorem B43252163 : Blo 1776089 43252163 := bstep (se 1 (by rfl) ⟨32439122, by rfl⟩ : syracuseStep 43252163 = 64878245) B64878245
theorem B1776295 : Blo 1776089 1776295 := bstep (se 1 (by rfl) ⟨1332221, by rfl⟩ : syracuseStep 1776295 = 2664443) B2664443
theorem B28809917 : Blo 1776089 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B1776799 : Blo 1776089 1776799 := bstep (se 1 (by rfl) ⟨1332599, by rfl⟩ : syracuseStep 1776799 = 2665199) B2665199
theorem B38968883 : Blo 1776089 38968883 := bstep (se 1 (by rfl) ⟨29226662, by rfl⟩ : syracuseStep 38968883 = 58453325) B58453325
theorem B1998463 : Blo 1776089 1998463 := bstep (se 1 (by rfl) ⟨1498847, by rfl⟩ : syracuseStep 1998463 = 2997695) B2997695
theorem B1777311 : Blo 1776089 1777311 := bstep (se 1 (by rfl) ⟨1332983, by rfl⟩ : syracuseStep 1777311 = 2665967) B2665967
theorem B38428445 : Blo 1776089 38428445 := bstep (se 3 (by rfl) ⟨7205333, by rfl⟩ : syracuseStep 38428445 = 14410667) B14410667
theorem B12804065 : Blo 1776089 12804065 := bstep (se 2 (by rfl) ⟨4801524, by rfl⟩ : syracuseStep 12804065 = 9603049) B9603049
theorem B194625503 : Blo 1776089 194625503 := bstep (se 1 (by rfl) ⟨145969127, by rfl⟩ : syracuseStep 194625503 = 291938255) B291938255
theorem B3997727 : Blo 1776089 3997727 := bstep (se 1 (by rfl) ⟨2998295, by rfl⟩ : syracuseStep 3997727 = 5996591) B5996591
theorem B3997817 : Blo 1776089 3997817 := bstep (se 2 (by rfl) ⟨1499181, by rfl⟩ : syracuseStep 3997817 = 2998363) B2998363
theorem B3997871 : Blo 1776089 3997871 := bstep (se 1 (by rfl) ⟨2998403, by rfl⟩ : syracuseStep 3997871 = 5996807) B5996807
theorem B2998775 : Blo 1776089 2998775 := bstep (se 1 (by rfl) ⟨2249081, by rfl⟩ : syracuseStep 2998775 = 4498163) B4498163
theorem B3998249 : Blo 1776089 3998249 := bstep (se 2 (by rfl) ⟨1499343, by rfl⟩ : syracuseStep 3998249 = 2998687) B2998687
theorem B5694077 : Blo 1776089 5694077 := bstep (se 3 (by rfl) ⟨1067639, by rfl⟩ : syracuseStep 5694077 = 2135279) B2135279
theorem B3998375 : Blo 1776089 3998375 := bstep (se 1 (by rfl) ⟨2998781, by rfl⟩ : syracuseStep 3998375 = 5997563) B5997563
theorem B2998991 : Blo 1776089 2998991 := bstep (se 1 (by rfl) ⟨2249243, by rfl⟩ : syracuseStep 2998991 = 4498487) B4498487
theorem B82092851 : Blo 1776089 82092851 := bstep (se 1 (by rfl) ⟨61569638, by rfl⟩ : syracuseStep 82092851 = 123139277) B123139277
theorem B30368681 : Blo 1776089 30368681 := bstep (se 2 (by rfl) ⟨11388255, by rfl⟩ : syracuseStep 30368681 = 22776511) B22776511
theorem B2664617 : Blo 1776089 2664617 := bstep (se 2 (by rfl) ⟨999231, by rfl⟩ : syracuseStep 2664617 = 1998463) B1998463
theorem B25979255 : Blo 1776089 25979255 := bstep (se 1 (by rfl) ⟨19484441, by rfl⟩ : syracuseStep 25979255 = 38968883) B38968883
theorem B25618963 : Blo 1776089 25618963 := bstep (se 1 (by rfl) ⟨19214222, by rfl⟩ : syracuseStep 25618963 = 38428445) B38428445
theorem B20237039 : Blo 1776089 20237039 := bstep (se 1 (by rfl) ⟨15177779, by rfl⟩ : syracuseStep 20237039 = 30355559) B30355559
theorem B2665319 : Blo 1776089 2665319 := bstep (se 1 (by rfl) ⟨1998989, by rfl⟩ : syracuseStep 2665319 = 3997979) B3997979
theorem B4000679 : Blo 1776089 4000679 := bstep (se 1 (by rfl) ⟨3000509, by rfl⟩ : syracuseStep 4000679 = 6001019) B6001019
theorem B6000047 : Blo 1776089 6000047 := bstep (se 1 (by rfl) ⟨4500035, by rfl⟩ : syracuseStep 6000047 = 9000071) B9000071
theorem B30346811 : Blo 1776089 30346811 := bstep (se 1 (by rfl) ⟨22760108, by rfl⟩ : syracuseStep 30346811 = 45520217) B45520217
theorem B11382515 : Blo 1776089 11382515 := bstep (se 1 (by rfl) ⟨8536886, by rfl⟩ : syracuseStep 11382515 = 17073773) B17073773
theorem B4558879 : Blo 1776089 4558879 := bstep (se 1 (by rfl) ⟨3419159, by rfl⟩ : syracuseStep 4558879 = 6838319) B6838319
theorem B19206611 : Blo 1776089 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B30373055 : Blo 1776089 30373055 := bstep (se 1 (by rfl) ⟨22779791, by rfl⟩ : syracuseStep 30373055 = 45559583) B45559583
theorem B129750335 : Blo 1776089 129750335 := bstep (se 1 (by rfl) ⟨97312751, by rfl⟩ : syracuseStep 129750335 = 194625503) B194625503
theorem B10803575 : Blo 1776089 10803575 := bstep (se 1 (by rfl) ⟨8102681, by rfl⟩ : syracuseStep 10803575 = 16205363) B16205363
theorem B15391097 : Blo 1776089 15391097 := bstep (se 2 (by rfl) ⟨5771661, by rfl⟩ : syracuseStep 15391097 = 11543323) B11543323
theorem B3996215 : Blo 1776089 3996215 := bstep (se 1 (by rfl) ⟨2997161, by rfl⟩ : syracuseStep 3996215 = 5994323) B5994323
theorem B23091803 : Blo 1776089 23091803 := bstep (se 1 (by rfl) ⟨17318852, by rfl⟩ : syracuseStep 23091803 = 34637705) B34637705
theorem B1776319 : Blo 1776089 1776319 := bstep (se 1 (by rfl) ⟨1332239, by rfl⟩ : syracuseStep 1776319 = 2664479) B2664479
theorem B93567743 : Blo 1776089 93567743 := bstep (se 1 (by rfl) ⟨70175807, by rfl⟩ : syracuseStep 93567743 = 140351615) B140351615
theorem B1776415 : Blo 1776089 1776415 := bstep (se 1 (by rfl) ⟨1332311, by rfl⟩ : syracuseStep 1776415 = 2664623) B2664623
theorem B28834775 : Blo 1776089 28834775 := bstep (se 1 (by rfl) ⟨21626081, by rfl⟩ : syracuseStep 28834775 = 43252163) B43252163
theorem B5061629 : Blo 1776089 5061629 := bstep (se 3 (by rfl) ⟨949055, by rfl⟩ : syracuseStep 5061629 = 1898111) B1898111
theorem B1776667 : Blo 1776089 1776667 := bstep (se 1 (by rfl) ⟨1332500, by rfl⟩ : syracuseStep 1776667 = 2665001) B2665001
theorem B1776895 : Blo 1776089 1776895 := bstep (se 1 (by rfl) ⟨1332671, by rfl⟩ : syracuseStep 1776895 = 2665343) B2665343
theorem B7593385 : Blo 1776089 7593385 := bstep (se 2 (by rfl) ⟨2847519, by rfl⟩ : syracuseStep 7593385 = 5695039) B5695039
theorem B1777151 : Blo 1776089 1777151 := bstep (se 1 (by rfl) ⟨1332863, by rfl⟩ : syracuseStep 1777151 = 2665727) B2665727
theorem B109469465 : Blo 1776089 109469465 := bstep (se 2 (by rfl) ⟨41051049, by rfl⟩ : syracuseStep 109469465 = 82102099) B82102099
theorem B8536043 : Blo 1776089 8536043 := bstep (se 1 (by rfl) ⟨6402032, by rfl⟩ : syracuseStep 8536043 = 12804065) B12804065
theorem B6078505 : Blo 1776089 6078505 := bstep (se 2 (by rfl) ⟨2279439, by rfl⟩ : syracuseStep 6078505 = 4558879) B4558879
theorem B12804407 : Blo 1776089 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B1999183 : Blo 1776089 1999183 := bstep (se 1 (by rfl) ⟨1499387, by rfl⟩ : syracuseStep 1999183 = 2998775) B2998775
theorem B1999327 : Blo 1776089 1999327 := bstep (se 1 (by rfl) ⟨1499495, by rfl⟩ : syracuseStep 1999327 = 2998991) B2998991
theorem B86500223 : Blo 1776089 86500223 := bstep (se 1 (by rfl) ⟨64875167, by rfl⟩ : syracuseStep 86500223 = 129750335) B129750335
theorem B17319503 : Blo 1776089 17319503 := bstep (se 1 (by rfl) ⟨12989627, by rfl⟩ : syracuseStep 17319503 = 25979255) B25979255
theorem B2664143 : Blo 1776089 2664143 := bstep (se 1 (by rfl) ⟨1998107, by rfl⟩ : syracuseStep 2664143 = 3996215) B3996215
theorem B15394535 : Blo 1776089 15394535 := bstep (se 1 (by rfl) ⟨11545901, by rfl⟩ : syracuseStep 15394535 = 23091803) B23091803
theorem B4000031 : Blo 1776089 4000031 := bstep (se 1 (by rfl) ⟨3000023, by rfl⟩ : syracuseStep 4000031 = 6000047) B6000047
theorem B7588343 : Blo 1776089 7588343 := bstep (se 1 (by rfl) ⟨5691257, by rfl⟩ : syracuseStep 7588343 = 11382515) B11382515
theorem B2665151 : Blo 1776089 2665151 := bstep (se 1 (by rfl) ⟨1998863, by rfl⟩ : syracuseStep 2665151 = 3997727) B3997727
theorem B2665211 : Blo 1776089 2665211 := bstep (se 1 (by rfl) ⟨1998908, by rfl⟩ : syracuseStep 2665211 = 3997817) B3997817
theorem B2665247 : Blo 1776089 2665247 := bstep (se 1 (by rfl) ⟨1998935, by rfl⟩ : syracuseStep 2665247 = 3997871) B3997871
theorem B2665499 : Blo 1776089 2665499 := bstep (se 1 (by rfl) ⟨1999124, by rfl⟩ : syracuseStep 2665499 = 3998249) B3998249
theorem B2665583 : Blo 1776089 2665583 := bstep (se 1 (by rfl) ⟨1999187, by rfl⟩ : syracuseStep 2665583 = 3998375) B3998375
theorem B20245787 : Blo 1776089 20245787 := bstep (se 1 (by rfl) ⟨15184340, by rfl⟩ : syracuseStep 20245787 = 30368681) B30368681
theorem B10260731 : Blo 1776089 10260731 := bstep (se 1 (by rfl) ⟨7695548, by rfl⟩ : syracuseStep 10260731 = 15391097) B15391097
theorem B15184205 : Blo 1776089 15184205 := bstep (se 3 (by rfl) ⟨2847038, by rfl⟩ : syracuseStep 15184205 = 5694077) B5694077
theorem B62378495 : Blo 1776089 62378495 := bstep (se 1 (by rfl) ⟨46783871, by rfl⟩ : syracuseStep 62378495 = 93567743) B93567743
theorem B2667119 : Blo 1776089 2667119 := bstep (se 1 (by rfl) ⟨2000339, by rfl⟩ : syracuseStep 2667119 = 4000679) B4000679
theorem B19223183 : Blo 1776089 19223183 := bstep (se 1 (by rfl) ⟨14417387, by rfl⟩ : syracuseStep 19223183 = 28834775) B28834775
theorem B20231207 : Blo 1776089 20231207 := bstep (se 1 (by rfl) ⟨15173405, by rfl⟩ : syracuseStep 20231207 = 30346811) B30346811
theorem B72979643 : Blo 1776089 72979643 := bstep (se 1 (by rfl) ⟨54734732, by rfl⟩ : syracuseStep 72979643 = 109469465) B109469465
theorem B5690695 : Blo 1776089 5690695 := bstep (se 1 (by rfl) ⟨4268021, by rfl⟩ : syracuseStep 5690695 = 8536043) B8536043
theorem B13497677 : Blo 1776089 13497677 := bstep (se 3 (by rfl) ⟨2530814, by rfl⟩ : syracuseStep 13497677 = 5061629) B5061629
theorem B54728567 : Blo 1776089 54728567 := bstep (se 1 (by rfl) ⟨41046425, by rfl⟩ : syracuseStep 54728567 = 82092851) B82092851
theorem B34158617 : Blo 1776089 34158617 := bstep (se 2 (by rfl) ⟨12809481, by rfl⟩ : syracuseStep 34158617 = 25618963) B25618963
theorem B20248703 : Blo 1776089 20248703 := bstep (se 1 (by rfl) ⟨15186527, by rfl⟩ : syracuseStep 20248703 = 30373055) B30373055
theorem B28809533 : Blo 1776089 28809533 := bstep (se 3 (by rfl) ⟨5401787, by rfl⟩ : syracuseStep 28809533 = 10803575) B10803575
theorem B1776411 : Blo 1776089 1776411 := bstep (se 1 (by rfl) ⟨1332308, by rfl⟩ : syracuseStep 1776411 = 2664617) B2664617
theorem B13491359 : Blo 1776089 13491359 := bstep (se 1 (by rfl) ⟨10118519, by rfl⟩ : syracuseStep 13491359 = 20237039) B20237039
theorem B10124513 : Blo 1776089 10124513 := bstep (se 2 (by rfl) ⟨3796692, by rfl⟩ : syracuseStep 10124513 = 7593385) B7593385
theorem B1776879 : Blo 1776089 1776879 := bstep (se 1 (by rfl) ⟨1332659, by rfl⟩ : syracuseStep 1776879 = 2665319) B2665319
theorem B6840487 : Blo 1776089 6840487 := bstep (se 1 (by rfl) ⟨5130365, by rfl⟩ : syracuseStep 6840487 = 10260731) B10260731
theorem B8536271 : Blo 1776089 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B1778079 : Blo 1776089 1778079 := bstep (se 1 (by rfl) ⟨1333559, by rfl⟩ : syracuseStep 1778079 = 2667119) B2667119
theorem B48653095 : Blo 1776089 48653095 := bstep (se 1 (by rfl) ⟨36489821, by rfl⟩ : syracuseStep 48653095 = 72979643) B72979643
theorem B20235581 : Blo 1776089 20235581 := bstep (se 3 (by rfl) ⟨3794171, by rfl⟩ : syracuseStep 20235581 = 7588343) B7588343
theorem B7587593 : Blo 1776089 7587593 := bstep (se 2 (by rfl) ⟨2845347, by rfl⟩ : syracuseStep 7587593 = 5690695) B5690695
theorem B8104673 : Blo 1776089 8104673 := bstep (se 2 (by rfl) ⟨3039252, by rfl⟩ : syracuseStep 8104673 = 6078505) B6078505
theorem B41585663 : Blo 1776089 41585663 := bstep (se 1 (by rfl) ⟨31189247, by rfl⟩ : syracuseStep 41585663 = 62378495) B62378495
theorem B12815455 : Blo 1776089 12815455 := bstep (se 1 (by rfl) ⟨9611591, by rfl⟩ : syracuseStep 12815455 = 19223183) B19223183
theorem B2665577 : Blo 1776089 2665577 := bstep (se 2 (by rfl) ⟨999591, by rfl⟩ : syracuseStep 2665577 = 1999183) B1999183
theorem B57666815 : Blo 1776089 57666815 := bstep (se 1 (by rfl) ⟨43250111, by rfl⟩ : syracuseStep 57666815 = 86500223) B86500223
theorem B2665769 : Blo 1776089 2665769 := bstep (se 2 (by rfl) ⟨999663, by rfl⟩ : syracuseStep 2665769 = 1999327) B1999327
theorem B13487471 : Blo 1776089 13487471 := bstep (se 1 (by rfl) ⟨10115603, by rfl⟩ : syracuseStep 13487471 = 20231207) B20231207
theorem B8998451 : Blo 1776089 8998451 := bstep (se 1 (by rfl) ⟨6748838, by rfl⟩ : syracuseStep 8998451 = 13497677) B13497677
theorem B11546335 : Blo 1776089 11546335 := bstep (se 1 (by rfl) ⟨8659751, by rfl⟩ : syracuseStep 11546335 = 17319503) B17319503
theorem B2666687 : Blo 1776089 2666687 := bstep (se 1 (by rfl) ⟨2000015, by rfl⟩ : syracuseStep 2666687 = 4000031) B4000031
theorem B19206355 : Blo 1776089 19206355 := bstep (se 1 (by rfl) ⟨14404766, by rfl⟩ : syracuseStep 19206355 = 28809533) B28809533
theorem B13497191 : Blo 1776089 13497191 := bstep (se 1 (by rfl) ⟨10122893, by rfl⟩ : syracuseStep 13497191 = 20245787) B20245787
theorem B10122803 : Blo 1776089 10122803 := bstep (se 1 (by rfl) ⟨7592102, by rfl⟩ : syracuseStep 10122803 = 15184205) B15184205
theorem B1776095 : Blo 1776089 1776095 := bstep (se 1 (by rfl) ⟨1332071, by rfl⟩ : syracuseStep 1776095 = 2664143) B2664143
theorem B10263023 : Blo 1776089 10263023 := bstep (se 1 (by rfl) ⟨7697267, by rfl⟩ : syracuseStep 10263023 = 15394535) B15394535
theorem B36485711 : Blo 1776089 36485711 := bstep (se 1 (by rfl) ⟨27364283, by rfl⟩ : syracuseStep 36485711 = 54728567) B54728567
theorem B22772411 : Blo 1776089 22772411 := bstep (se 1 (by rfl) ⟨17079308, by rfl⟩ : syracuseStep 22772411 = 34158617) B34158617
theorem B13499135 : Blo 1776089 13499135 := bstep (se 1 (by rfl) ⟨10124351, by rfl⟩ : syracuseStep 13499135 = 20248703) B20248703
theorem B1776767 : Blo 1776089 1776767 := bstep (se 1 (by rfl) ⟨1332575, by rfl⟩ : syracuseStep 1776767 = 2665151) B2665151
theorem B1776807 : Blo 1776089 1776807 := bstep (se 1 (by rfl) ⟨1332605, by rfl⟩ : syracuseStep 1776807 = 2665211) B2665211
theorem B1776831 : Blo 1776089 1776831 := bstep (se 1 (by rfl) ⟨1332623, by rfl⟩ : syracuseStep 1776831 = 2665247) B2665247
theorem B1776999 : Blo 1776089 1776999 := bstep (se 1 (by rfl) ⟨1332749, by rfl⟩ : syracuseStep 1776999 = 2665499) B2665499
theorem B1777055 : Blo 1776089 1777055 := bstep (se 1 (by rfl) ⟨1332791, by rfl⟩ : syracuseStep 1777055 = 2665583) B2665583
theorem B8994239 : Blo 1776089 8994239 := bstep (se 1 (by rfl) ⟨6745679, by rfl⟩ : syracuseStep 8994239 = 13491359) B13491359
theorem B6749675 : Blo 1776089 6749675 := bstep (se 1 (by rfl) ⟨5062256, by rfl⟩ : syracuseStep 6749675 = 10124513) B10124513
theorem B1777791 : Blo 1776089 1777791 := bstep (se 1 (by rfl) ⟨1333343, by rfl⟩ : syracuseStep 1777791 = 2666687) B2666687
theorem B25608473 : Blo 1776089 25608473 := bstep (se 2 (by rfl) ⟨9603177, by rfl⟩ : syracuseStep 25608473 = 19206355) B19206355
theorem B6842015 : Blo 1776089 6842015 := bstep (se 1 (by rfl) ⟨5131511, by rfl⟩ : syracuseStep 6842015 = 10263023) B10263023
theorem B24323807 : Blo 1776089 24323807 := bstep (se 1 (by rfl) ⟨18242855, by rfl⟩ : syracuseStep 24323807 = 36485711) B36485711
theorem B15181607 : Blo 1776089 15181607 := bstep (se 1 (by rfl) ⟨11386205, by rfl⟩ : syracuseStep 15181607 = 22772411) B22772411
theorem B15395113 : Blo 1776089 15395113 := bstep (se 2 (by rfl) ⟨5773167, by rfl⟩ : syracuseStep 15395113 = 11546335) B11546335
theorem B4499783 : Blo 1776089 4499783 := bstep (se 1 (by rfl) ⟨3374837, by rfl⟩ : syracuseStep 4499783 = 6749675) B6749675
theorem B5998967 : Blo 1776089 5998967 := bstep (se 1 (by rfl) ⟨4499225, by rfl⟩ : syracuseStep 5998967 = 8998451) B8998451
theorem B9120649 : Blo 1776089 9120649 := bstep (se 2 (by rfl) ⟨3420243, by rfl⟩ : syracuseStep 9120649 = 6840487) B6840487
theorem B8998127 : Blo 1776089 8998127 := bstep (se 1 (by rfl) ⟨6748595, by rfl⟩ : syracuseStep 8998127 = 13497191) B13497191
theorem B5058395 : Blo 1776089 5058395 := bstep (se 1 (by rfl) ⟨3793796, by rfl⟩ : syracuseStep 5058395 = 7587593) B7587593
theorem B5403115 : Blo 1776089 5403115 := bstep (se 1 (by rfl) ⟨4052336, by rfl⟩ : syracuseStep 5403115 = 8104673) B8104673
theorem B8999423 : Blo 1776089 8999423 := bstep (se 1 (by rfl) ⟨6749567, by rfl⟩ : syracuseStep 8999423 = 13499135) B13499135
theorem B8991647 : Blo 1776089 8991647 := bstep (se 1 (by rfl) ⟨6743735, by rfl⟩ : syracuseStep 8991647 = 13487471) B13487471
theorem B22763389 : Blo 1776089 22763389 := bstep (se 3 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 22763389 = 8536271) B8536271
theorem B13490387 : Blo 1776089 13490387 := bstep (se 1 (by rfl) ⟨10117790, by rfl⟩ : syracuseStep 13490387 = 20235581) B20235581
theorem B6748535 : Blo 1776089 6748535 := bstep (se 1 (by rfl) ⟨5061401, by rfl⟩ : syracuseStep 6748535 = 10122803) B10122803
theorem B64870793 : Blo 1776089 64870793 := bstep (se 2 (by rfl) ⟨24326547, by rfl⟩ : syracuseStep 64870793 = 48653095) B48653095
theorem B17087273 : Blo 1776089 17087273 := bstep (se 2 (by rfl) ⟨6407727, by rfl⟩ : syracuseStep 17087273 = 12815455) B12815455
theorem B1777051 : Blo 1776089 1777051 := bstep (se 1 (by rfl) ⟨1332788, by rfl⟩ : syracuseStep 1777051 = 2665577) B2665577
theorem B38444543 : Blo 1776089 38444543 := bstep (se 1 (by rfl) ⟨28833407, by rfl⟩ : syracuseStep 38444543 = 57666815) B57666815
theorem B1777179 : Blo 1776089 1777179 := bstep (se 1 (by rfl) ⟨1332884, by rfl⟩ : syracuseStep 1777179 = 2665769) B2665769
theorem B5996159 : Blo 1776089 5996159 := bstep (se 1 (by rfl) ⟨4497119, by rfl⟩ : syracuseStep 5996159 = 8994239) B8994239
theorem B110895101 : Blo 1776089 110895101 := bstep (se 3 (by rfl) ⟨20792831, by rfl⟩ : syracuseStep 110895101 = 41585663) B41585663
theorem B17072315 : Blo 1776089 17072315 := bstep (se 1 (by rfl) ⟨12804236, by rfl⟩ : syracuseStep 17072315 = 25608473) B25608473
theorem B2999855 : Blo 1776089 2999855 := bstep (se 1 (by rfl) ⟨2249891, by rfl⟩ : syracuseStep 2999855 = 4499783) B4499783
theorem B4499023 : Blo 1776089 4499023 := bstep (se 1 (by rfl) ⟨3374267, by rfl⟩ : syracuseStep 4499023 = 6748535) B6748535
theorem B3999311 : Blo 1776089 3999311 := bstep (se 1 (by rfl) ⟨2999483, by rfl⟩ : syracuseStep 3999311 = 5998967) B5998967
theorem B43247195 : Blo 1776089 43247195 := bstep (se 1 (by rfl) ⟨32435396, by rfl⟩ : syracuseStep 43247195 = 64870793) B64870793
theorem B5998751 : Blo 1776089 5998751 := bstep (se 1 (by rfl) ⟨4499063, by rfl⟩ : syracuseStep 5998751 = 8998127) B8998127
theorem B5999615 : Blo 1776089 5999615 := bstep (se 1 (by rfl) ⟨4499711, by rfl⟩ : syracuseStep 5999615 = 8999423) B8999423
theorem B7204153 : Blo 1776089 7204153 := bstep (se 2 (by rfl) ⟨2701557, by rfl⟩ : syracuseStep 7204153 = 5403115) B5403115
theorem B16215871 : Blo 1776089 16215871 := bstep (se 1 (by rfl) ⟨12161903, by rfl⟩ : syracuseStep 16215871 = 24323807) B24323807
theorem B12160865 : Blo 1776089 12160865 := bstep (se 2 (by rfl) ⟨4560324, by rfl⟩ : syracuseStep 12160865 = 9120649) B9120649
theorem B10121071 : Blo 1776089 10121071 := bstep (se 1 (by rfl) ⟨7590803, by rfl⟩ : syracuseStep 10121071 = 15181607) B15181607
theorem B11391515 : Blo 1776089 11391515 := bstep (se 1 (by rfl) ⟨8543636, by rfl⟩ : syracuseStep 11391515 = 17087273) B17087273
theorem B25629695 : Blo 1776089 25629695 := bstep (se 1 (by rfl) ⟨19222271, by rfl⟩ : syracuseStep 25629695 = 38444543) B38444543
theorem B3372263 : Blo 1776089 3372263 := bstep (se 1 (by rfl) ⟨2529197, by rfl⟩ : syracuseStep 3372263 = 5058395) B5058395
theorem B73930067 : Blo 1776089 73930067 := bstep (se 1 (by rfl) ⟨55447550, by rfl⟩ : syracuseStep 73930067 = 110895101) B110895101
theorem B20526817 : Blo 1776089 20526817 := bstep (se 2 (by rfl) ⟨7697556, by rfl⟩ : syracuseStep 20526817 = 15395113) B15395113
theorem B5994431 : Blo 1776089 5994431 := bstep (se 1 (by rfl) ⟨4495823, by rfl⟩ : syracuseStep 5994431 = 8991647) B8991647
theorem B4561343 : Blo 1776089 4561343 := bstep (se 1 (by rfl) ⟨3421007, by rfl⟩ : syracuseStep 4561343 = 6842015) B6842015
theorem B8993591 : Blo 1776089 8993591 := bstep (se 1 (by rfl) ⟨6745193, by rfl⟩ : syracuseStep 8993591 = 13490387) B13490387
theorem B3997439 : Blo 1776089 3997439 := bstep (se 1 (by rfl) ⟨2998079, by rfl⟩ : syracuseStep 3997439 = 5996159) B5996159
theorem B30351185 : Blo 1776089 30351185 := bstep (se 2 (by rfl) ⟨11381694, by rfl⟩ : syracuseStep 30351185 = 22763389) B22763389
theorem B7594343 : Blo 1776089 7594343 := bstep (se 1 (by rfl) ⟨5695757, by rfl⟩ : syracuseStep 7594343 = 11391515) B11391515
theorem B1999903 : Blo 1776089 1999903 := bstep (se 1 (by rfl) ⟨1499927, by rfl⟩ : syracuseStep 1999903 = 2999855) B2999855
theorem B3999167 : Blo 1776089 3999167 := bstep (se 1 (by rfl) ⟨2999375, by rfl⟩ : syracuseStep 3999167 = 5998751) B5998751
theorem B3040895 : Blo 1776089 3040895 := bstep (se 1 (by rfl) ⟨2280671, by rfl⟩ : syracuseStep 3040895 = 4561343) B4561343
theorem B3999743 : Blo 1776089 3999743 := bstep (se 1 (by rfl) ⟨2999807, by rfl⟩ : syracuseStep 3999743 = 5999615) B5999615
theorem B5998697 : Blo 1776089 5998697 := bstep (se 2 (by rfl) ⟨2249511, by rfl⟩ : syracuseStep 5998697 = 4499023) B4499023
theorem B21621161 : Blo 1776089 21621161 := bstep (se 2 (by rfl) ⟨8107935, by rfl⟩ : syracuseStep 21621161 = 16215871) B16215871
theorem B13494761 : Blo 1776089 13494761 := bstep (se 2 (by rfl) ⟨5060535, by rfl⟩ : syracuseStep 13494761 = 10121071) B10121071
theorem B2664959 : Blo 1776089 2664959 := bstep (se 1 (by rfl) ⟨1998719, by rfl⟩ : syracuseStep 2664959 = 3997439) B3997439
theorem B11381543 : Blo 1776089 11381543 := bstep (se 1 (by rfl) ⟨8536157, by rfl⟩ : syracuseStep 11381543 = 17072315) B17072315
theorem B2248175 : Blo 1776089 2248175 := bstep (se 1 (by rfl) ⟨1686131, by rfl⟩ : syracuseStep 2248175 = 3372263) B3372263
theorem B49286711 : Blo 1776089 49286711 := bstep (se 1 (by rfl) ⟨36965033, by rfl⟩ : syracuseStep 49286711 = 73930067) B73930067
theorem B2666207 : Blo 1776089 2666207 := bstep (se 1 (by rfl) ⟨1999655, by rfl⟩ : syracuseStep 2666207 = 3999311) B3999311
theorem B28831463 : Blo 1776089 28831463 := bstep (se 1 (by rfl) ⟨21623597, by rfl⟩ : syracuseStep 28831463 = 43247195) B43247195
theorem B9605537 : Blo 1776089 9605537 := bstep (se 2 (by rfl) ⟨3602076, by rfl⟩ : syracuseStep 9605537 = 7204153) B7204153
theorem B32428973 : Blo 1776089 32428973 := bstep (se 3 (by rfl) ⟨6080432, by rfl⟩ : syracuseStep 32428973 = 12160865) B12160865
theorem B17086463 : Blo 1776089 17086463 := bstep (se 1 (by rfl) ⟨12814847, by rfl⟩ : syracuseStep 17086463 = 25629695) B25629695
theorem B3996287 : Blo 1776089 3996287 := bstep (se 1 (by rfl) ⟨2997215, by rfl⟩ : syracuseStep 3996287 = 5994431) B5994431
theorem B5995727 : Blo 1776089 5995727 := bstep (se 1 (by rfl) ⟨4496795, by rfl⟩ : syracuseStep 5995727 = 8993591) B8993591
theorem B27369089 : Blo 1776089 27369089 := bstep (se 2 (by rfl) ⟨10263408, by rfl⟩ : syracuseStep 27369089 = 20526817) B20526817
theorem B20234123 : Blo 1776089 20234123 := bstep (se 1 (by rfl) ⟨15175592, by rfl⟩ : syracuseStep 20234123 = 30351185) B30351185
theorem B5062895 : Blo 1776089 5062895 := bstep (se 1 (by rfl) ⟨3797171, by rfl⟩ : syracuseStep 5062895 = 7594343) B7594343
theorem B21619315 : Blo 1776089 21619315 := bstep (se 1 (by rfl) ⟨16214486, by rfl⟩ : syracuseStep 21619315 = 32428973) B32428973
theorem B3999131 : Blo 1776089 3999131 := bstep (se 1 (by rfl) ⟨2999348, by rfl⟩ : syracuseStep 3999131 = 5998697) B5998697
theorem B8996507 : Blo 1776089 8996507 := bstep (se 1 (by rfl) ⟨6747380, by rfl⟩ : syracuseStep 8996507 = 13494761) B13494761
theorem B2664191 : Blo 1776089 2664191 := bstep (se 1 (by rfl) ⟨1998143, by rfl⟩ : syracuseStep 2664191 = 3996287) B3996287
theorem B7587695 : Blo 1776089 7587695 := bstep (se 1 (by rfl) ⟨5690771, by rfl⟩ : syracuseStep 7587695 = 11381543) B11381543
theorem B18246059 : Blo 1776089 18246059 := bstep (se 1 (by rfl) ⟨13684544, by rfl⟩ : syracuseStep 18246059 = 27369089) B27369089
theorem B19220975 : Blo 1776089 19220975 := bstep (se 1 (by rfl) ⟨14415731, by rfl⟩ : syracuseStep 19220975 = 28831463) B28831463
theorem B2666111 : Blo 1776089 2666111 := bstep (se 1 (by rfl) ⟨1999583, by rfl⟩ : syracuseStep 2666111 = 3999167) B3999167
theorem B2027263 : Blo 1776089 2027263 := bstep (se 1 (by rfl) ⟨1520447, by rfl⟩ : syracuseStep 2027263 = 3040895) B3040895
theorem B2666495 : Blo 1776089 2666495 := bstep (se 1 (by rfl) ⟨1999871, by rfl⟩ : syracuseStep 2666495 = 3999743) B3999743
theorem B11390975 : Blo 1776089 11390975 := bstep (se 1 (by rfl) ⟨8543231, by rfl⟩ : syracuseStep 11390975 = 17086463) B17086463
theorem B2666537 : Blo 1776089 2666537 := bstep (se 2 (by rfl) ⟨999951, by rfl⟩ : syracuseStep 2666537 = 1999903) B1999903
theorem B14414107 : Blo 1776089 14414107 := bstep (se 1 (by rfl) ⟨10810580, by rfl⟩ : syracuseStep 14414107 = 21621161) B21621161
theorem B13489415 : Blo 1776089 13489415 := bstep (se 1 (by rfl) ⟨10117061, by rfl⟩ : syracuseStep 13489415 = 20234123) B20234123
theorem B6403691 : Blo 1776089 6403691 := bstep (se 1 (by rfl) ⟨4802768, by rfl⟩ : syracuseStep 6403691 = 9605537) B9605537
theorem B5995133 : Blo 1776089 5995133 := bstep (se 3 (by rfl) ⟨1124087, by rfl⟩ : syracuseStep 5995133 = 2248175) B2248175
theorem B1776639 : Blo 1776089 1776639 := bstep (se 1 (by rfl) ⟨1332479, by rfl⟩ : syracuseStep 1776639 = 2664959) B2664959
theorem B3997151 : Blo 1776089 3997151 := bstep (se 1 (by rfl) ⟨2997863, by rfl⟩ : syracuseStep 3997151 = 5995727) B5995727
theorem B32857807 : Blo 1776089 32857807 := bstep (se 1 (by rfl) ⟨24643355, by rfl⟩ : syracuseStep 32857807 = 49286711) B49286711
theorem B1777471 : Blo 1776089 1777471 := bstep (se 1 (by rfl) ⟨1333103, by rfl⟩ : syracuseStep 1777471 = 2666207) B2666207
theorem B1777691 : Blo 1776089 1777691 := bstep (se 1 (by rfl) ⟨1333268, by rfl⟩ : syracuseStep 1777691 = 2666537) B2666537
theorem B3375263 : Blo 1776089 3375263 := bstep (se 1 (by rfl) ⟨2531447, by rfl⟩ : syracuseStep 3375263 = 5062895) B5062895
theorem B19218809 : Blo 1776089 19218809 := bstep (se 2 (by rfl) ⟨7207053, by rfl⟩ : syracuseStep 19218809 = 14414107) B14414107
theorem B4269127 : Blo 1776089 4269127 := bstep (se 1 (by rfl) ⟨3201845, by rfl⟩ : syracuseStep 4269127 = 6403691) B6403691
theorem B5997671 : Blo 1776089 5997671 := bstep (se 1 (by rfl) ⟨4498253, by rfl⟩ : syracuseStep 5997671 = 8996507) B8996507
theorem B12813983 : Blo 1776089 12813983 := bstep (se 1 (by rfl) ⟨9610487, by rfl⟩ : syracuseStep 12813983 = 19220975) B19220975
theorem B2664767 : Blo 1776089 2664767 := bstep (se 1 (by rfl) ⟨1998575, by rfl⟩ : syracuseStep 2664767 = 3997151) B3997151
theorem B2666087 : Blo 1776089 2666087 := bstep (se 1 (by rfl) ⟨1999565, by rfl⟩ : syracuseStep 2666087 = 3999131) B3999131
theorem B5058463 : Blo 1776089 5058463 := bstep (se 1 (by rfl) ⟨3793847, by rfl⟩ : syracuseStep 5058463 = 7587695) B7587695
theorem B28825753 : Blo 1776089 28825753 := bstep (se 2 (by rfl) ⟨10809657, by rfl⟩ : syracuseStep 28825753 = 21619315) B21619315
theorem B8992943 : Blo 1776089 8992943 := bstep (se 1 (by rfl) ⟨6744707, by rfl⟩ : syracuseStep 8992943 = 13489415) B13489415
theorem B1776127 : Blo 1776089 1776127 := bstep (se 1 (by rfl) ⟨1332095, by rfl⟩ : syracuseStep 1776127 = 2664191) B2664191
theorem B12164039 : Blo 1776089 12164039 := bstep (se 1 (by rfl) ⟨9123029, by rfl⟩ : syracuseStep 12164039 = 18246059) B18246059
theorem B3996755 : Blo 1776089 3996755 := bstep (se 1 (by rfl) ⟨2997566, by rfl⟩ : syracuseStep 3996755 = 5995133) B5995133
theorem B43810409 : Blo 1776089 43810409 := bstep (se 2 (by rfl) ⟨16428903, by rfl⟩ : syracuseStep 43810409 = 32857807) B32857807
theorem B2703017 : Blo 1776089 2703017 := bstep (se 2 (by rfl) ⟨1013631, by rfl⟩ : syracuseStep 2703017 = 2027263) B2027263
theorem B7593983 : Blo 1776089 7593983 := bstep (se 1 (by rfl) ⟨5695487, by rfl⟩ : syracuseStep 7593983 = 11390975) B11390975
theorem B1777407 : Blo 1776089 1777407 := bstep (se 1 (by rfl) ⟨1333055, by rfl⟩ : syracuseStep 1777407 = 2666111) B2666111
theorem B1777663 : Blo 1776089 1777663 := bstep (se 1 (by rfl) ⟨1333247, by rfl⟩ : syracuseStep 1777663 = 2666495) B2666495
theorem B3998447 : Blo 1776089 3998447 := bstep (se 1 (by rfl) ⟨2998835, by rfl⟩ : syracuseStep 3998447 = 5997671) B5997671
theorem B51250157 : Blo 1776089 51250157 := bstep (se 3 (by rfl) ⟨9609404, by rfl⟩ : syracuseStep 51250157 = 19218809) B19218809
theorem B116827757 : Blo 1776089 116827757 := bstep (se 3 (by rfl) ⟨21905204, by rfl⟩ : syracuseStep 116827757 = 43810409) B43810409
theorem B2664503 : Blo 1776089 2664503 := bstep (se 1 (by rfl) ⟨1998377, by rfl⟩ : syracuseStep 2664503 = 3996755) B3996755
theorem B5062655 : Blo 1776089 5062655 := bstep (se 1 (by rfl) ⟨3796991, by rfl⟩ : syracuseStep 5062655 = 7593983) B7593983
theorem B6744617 : Blo 1776089 6744617 := bstep (se 2 (by rfl) ⟨2529231, by rfl⟩ : syracuseStep 6744617 = 5058463) B5058463
theorem B2250175 : Blo 1776089 2250175 := bstep (se 1 (by rfl) ⟨1687631, by rfl⟩ : syracuseStep 2250175 = 3375263) B3375263
theorem B38434337 : Blo 1776089 38434337 := bstep (se 2 (by rfl) ⟨14412876, by rfl⟩ : syracuseStep 38434337 = 28825753) B28825753
theorem B8542655 : Blo 1776089 8542655 := bstep (se 1 (by rfl) ⟨6406991, by rfl⟩ : syracuseStep 8542655 = 12813983) B12813983
theorem B5692169 : Blo 1776089 5692169 := bstep (se 2 (by rfl) ⟨2134563, by rfl⟩ : syracuseStep 5692169 = 4269127) B4269127
theorem B5995295 : Blo 1776089 5995295 := bstep (se 1 (by rfl) ⟨4496471, by rfl⟩ : syracuseStep 5995295 = 8992943) B8992943
theorem B1776511 : Blo 1776089 1776511 := bstep (se 1 (by rfl) ⟨1332383, by rfl⟩ : syracuseStep 1776511 = 2664767) B2664767
theorem B7208045 : Blo 1776089 7208045 := bstep (se 3 (by rfl) ⟨1351508, by rfl⟩ : syracuseStep 7208045 = 2703017) B2703017
theorem B8109359 : Blo 1776089 8109359 := bstep (se 1 (by rfl) ⟨6082019, by rfl⟩ : syracuseStep 8109359 = 12164039) B12164039
theorem B1777391 : Blo 1776089 1777391 := bstep (se 1 (by rfl) ⟨1333043, by rfl⟩ : syracuseStep 1777391 = 2666087) B2666087
theorem B5695103 : Blo 1776089 5695103 := bstep (se 1 (by rfl) ⟨4271327, by rfl⟩ : syracuseStep 5695103 = 8542655) B8542655
theorem B3794779 : Blo 1776089 3794779 := bstep (se 1 (by rfl) ⟨2846084, by rfl⟩ : syracuseStep 3794779 = 5692169) B5692169
theorem B3000233 : Blo 1776089 3000233 := bstep (se 2 (by rfl) ⟨1125087, by rfl⟩ : syracuseStep 3000233 = 2250175) B2250175
theorem B2665631 : Blo 1776089 2665631 := bstep (se 1 (by rfl) ⟨1999223, by rfl⟩ : syracuseStep 2665631 = 3998447) B3998447
theorem B77885171 : Blo 1776089 77885171 := bstep (se 1 (by rfl) ⟨58413878, by rfl⟩ : syracuseStep 77885171 = 116827757) B116827757
theorem B4805363 : Blo 1776089 4805363 := bstep (se 1 (by rfl) ⟨3604022, by rfl⟩ : syracuseStep 4805363 = 7208045) B7208045
theorem B34166771 : Blo 1776089 34166771 := bstep (se 1 (by rfl) ⟨25625078, by rfl⟩ : syracuseStep 34166771 = 51250157) B51250157
theorem B25622891 : Blo 1776089 25622891 := bstep (se 1 (by rfl) ⟨19217168, by rfl⟩ : syracuseStep 25622891 = 38434337) B38434337
theorem B1776335 : Blo 1776089 1776335 := bstep (se 1 (by rfl) ⟨1332251, by rfl⟩ : syracuseStep 1776335 = 2664503) B2664503
theorem B3375103 : Blo 1776089 3375103 := bstep (se 1 (by rfl) ⟨2531327, by rfl⟩ : syracuseStep 3375103 = 5062655) B5062655
theorem B4496411 : Blo 1776089 4496411 := bstep (se 1 (by rfl) ⟨3372308, by rfl⟩ : syracuseStep 4496411 = 6744617) B6744617
theorem B3996863 : Blo 1776089 3996863 := bstep (se 1 (by rfl) ⟨2997647, by rfl⟩ : syracuseStep 3996863 = 5995295) B5995295
theorem B5406239 : Blo 1776089 5406239 := bstep (se 1 (by rfl) ⟨4054679, by rfl⟩ : syracuseStep 5406239 = 8109359) B8109359
theorem B2000155 : Blo 1776089 2000155 := bstep (se 1 (by rfl) ⟨1500116, by rfl⟩ : syracuseStep 2000155 = 3000233) B3000233
theorem B17081927 : Blo 1776089 17081927 := bstep (se 1 (by rfl) ⟨12811445, by rfl⟩ : syracuseStep 17081927 = 25622891) B25622891
theorem B12814301 : Blo 1776089 12814301 := bstep (se 3 (by rfl) ⟨2402681, by rfl⟩ : syracuseStep 12814301 = 4805363) B4805363
theorem B2664575 : Blo 1776089 2664575 := bstep (se 1 (by rfl) ⟨1998431, by rfl⟩ : syracuseStep 2664575 = 3996863) B3996863
theorem B51923447 : Blo 1776089 51923447 := bstep (se 1 (by rfl) ⟨38942585, by rfl⟩ : syracuseStep 51923447 = 77885171) B77885171
theorem B4500137 : Blo 1776089 4500137 := bstep (se 2 (by rfl) ⟨1687551, by rfl⟩ : syracuseStep 4500137 = 3375103) B3375103
theorem B3796735 : Blo 1776089 3796735 := bstep (se 1 (by rfl) ⟨2847551, by rfl⟩ : syracuseStep 3796735 = 5695103) B5695103
theorem B22777847 : Blo 1776089 22777847 := bstep (se 1 (by rfl) ⟨17083385, by rfl⟩ : syracuseStep 22777847 = 34166771) B34166771
theorem B5059705 : Blo 1776089 5059705 := bstep (se 2 (by rfl) ⟨1897389, by rfl⟩ : syracuseStep 5059705 = 3794779) B3794779
theorem B2997607 : Blo 1776089 2997607 := bstep (se 1 (by rfl) ⟨2248205, by rfl⟩ : syracuseStep 2997607 = 4496411) B4496411
theorem B1777087 : Blo 1776089 1777087 := bstep (se 1 (by rfl) ⟨1332815, by rfl⟩ : syracuseStep 1777087 = 2665631) B2665631
theorem B3604159 : Blo 1776089 3604159 := bstep (se 1 (by rfl) ⟨2703119, by rfl⟩ : syracuseStep 3604159 = 5406239) B5406239
theorem B11387951 : Blo 1776089 11387951 := bstep (se 1 (by rfl) ⟨8540963, by rfl⟩ : syracuseStep 11387951 = 17081927) B17081927
theorem B3000091 : Blo 1776089 3000091 := bstep (se 1 (by rfl) ⟨2250068, by rfl⟩ : syracuseStep 3000091 = 4500137) B4500137
theorem B19222181 : Blo 1776089 19222181 := bstep (se 4 (by rfl) ⟨1802079, by rfl⟩ : syracuseStep 19222181 = 3604159) B3604159
theorem B6746273 : Blo 1776089 6746273 := bstep (se 2 (by rfl) ⟨2529852, by rfl⟩ : syracuseStep 6746273 = 5059705) B5059705
theorem B34615631 : Blo 1776089 34615631 := bstep (se 1 (by rfl) ⟨25961723, by rfl⟩ : syracuseStep 34615631 = 51923447) B51923447
theorem B2666873 : Blo 1776089 2666873 := bstep (se 2 (by rfl) ⟨1000077, by rfl⟩ : syracuseStep 2666873 = 2000155) B2000155
theorem B15185231 : Blo 1776089 15185231 := bstep (se 1 (by rfl) ⟨11388923, by rfl⟩ : syracuseStep 15185231 = 22777847) B22777847
theorem B8542867 : Blo 1776089 8542867 := bstep (se 1 (by rfl) ⟨6407150, by rfl⟩ : syracuseStep 8542867 = 12814301) B12814301
theorem B1776383 : Blo 1776089 1776383 := bstep (se 1 (by rfl) ⟨1332287, by rfl⟩ : syracuseStep 1776383 = 2664575) B2664575
theorem B3996809 : Blo 1776089 3996809 := bstep (se 2 (by rfl) ⟨1498803, by rfl⟩ : syracuseStep 3996809 = 2997607) B2997607
theorem B5062313 : Blo 1776089 5062313 := bstep (se 2 (by rfl) ⟨1898367, by rfl⟩ : syracuseStep 5062313 = 3796735) B3796735
theorem B4497515 : Blo 1776089 4497515 := bstep (se 1 (by rfl) ⟨3373136, by rfl⟩ : syracuseStep 4497515 = 6746273) B6746273
theorem B1777915 : Blo 1776089 1777915 := bstep (se 1 (by rfl) ⟨1333436, by rfl⟩ : syracuseStep 1777915 = 2666873) B2666873
theorem B92308349 : Blo 1776089 92308349 := bstep (se 3 (by rfl) ⟨17307815, by rfl⟩ : syracuseStep 92308349 = 34615631) B34615631
theorem B2664539 : Blo 1776089 2664539 := bstep (se 1 (by rfl) ⟨1998404, by rfl⟩ : syracuseStep 2664539 = 3996809) B3996809
theorem B4000121 : Blo 1776089 4000121 := bstep (se 2 (by rfl) ⟨1500045, by rfl⟩ : syracuseStep 4000121 = 3000091) B3000091
theorem B12814787 : Blo 1776089 12814787 := bstep (se 1 (by rfl) ⟨9611090, by rfl⟩ : syracuseStep 12814787 = 19222181) B19222181
theorem B11390489 : Blo 1776089 11390489 := bstep (se 2 (by rfl) ⟨4271433, by rfl⟩ : syracuseStep 11390489 = 8542867) B8542867
theorem B7591967 : Blo 1776089 7591967 := bstep (se 1 (by rfl) ⟨5693975, by rfl⟩ : syracuseStep 7591967 = 11387951) B11387951
theorem B10123487 : Blo 1776089 10123487 := bstep (se 1 (by rfl) ⟨7592615, by rfl⟩ : syracuseStep 10123487 = 15185231) B15185231
theorem B3374875 : Blo 1776089 3374875 := bstep (se 1 (by rfl) ⟨2531156, by rfl⟩ : syracuseStep 3374875 = 5062313) B5062313
theorem B2998343 : Blo 1776089 2998343 := bstep (se 1 (by rfl) ⟨2248757, by rfl⟩ : syracuseStep 2998343 = 4497515) B4497515
theorem B61538899 : Blo 1776089 61538899 := bstep (se 1 (by rfl) ⟨46154174, by rfl⟩ : syracuseStep 61538899 = 92308349) B92308349
theorem B4499833 : Blo 1776089 4499833 := bstep (se 2 (by rfl) ⟨1687437, by rfl⟩ : syracuseStep 4499833 = 3374875) B3374875
theorem B34172765 : Blo 1776089 34172765 := bstep (se 3 (by rfl) ⟨6407393, by rfl⟩ : syracuseStep 34172765 = 12814787) B12814787
theorem B2666747 : Blo 1776089 2666747 := bstep (se 1 (by rfl) ⟨2000060, by rfl⟩ : syracuseStep 2666747 = 4000121) B4000121
theorem B5061311 : Blo 1776089 5061311 := bstep (se 1 (by rfl) ⟨3795983, by rfl⟩ : syracuseStep 5061311 = 7591967) B7591967
theorem B1776359 : Blo 1776089 1776359 := bstep (se 1 (by rfl) ⟨1332269, by rfl⟩ : syracuseStep 1776359 = 2664539) B2664539
theorem B6748991 : Blo 1776089 6748991 := bstep (se 1 (by rfl) ⟨5061743, by rfl⟩ : syracuseStep 6748991 = 10123487) B10123487
theorem B7593659 : Blo 1776089 7593659 := bstep (se 1 (by rfl) ⟨5695244, by rfl⟩ : syracuseStep 7593659 = 11390489) B11390489
theorem B1998895 : Blo 1776089 1998895 := bstep (se 1 (by rfl) ⟨1499171, by rfl⟩ : syracuseStep 1998895 = 2998343) B2998343
theorem B1777831 : Blo 1776089 1777831 := bstep (se 1 (by rfl) ⟨1333373, by rfl⟩ : syracuseStep 1777831 = 2666747) B2666747
theorem B82051865 : Blo 1776089 82051865 := bstep (se 2 (by rfl) ⟨30769449, by rfl⟩ : syracuseStep 82051865 = 61538899) B61538899
theorem B4499327 : Blo 1776089 4499327 := bstep (se 1 (by rfl) ⟨3374495, by rfl⟩ : syracuseStep 4499327 = 6748991) B6748991
theorem B5999777 : Blo 1776089 5999777 := bstep (se 2 (by rfl) ⟨2249916, by rfl⟩ : syracuseStep 5999777 = 4499833) B4499833
theorem B3374207 : Blo 1776089 3374207 := bstep (se 1 (by rfl) ⟨2530655, by rfl⟩ : syracuseStep 3374207 = 5061311) B5061311
theorem B5062439 : Blo 1776089 5062439 := bstep (se 1 (by rfl) ⟨3796829, by rfl⟩ : syracuseStep 5062439 = 7593659) B7593659
theorem B22781843 : Blo 1776089 22781843 := bstep (se 1 (by rfl) ⟨17086382, by rfl⟩ : syracuseStep 22781843 = 34172765) B34172765
theorem B2999551 : Blo 1776089 2999551 := bstep (se 1 (by rfl) ⟨2249663, by rfl⟩ : syracuseStep 2999551 = 4499327) B4499327
theorem B3999851 : Blo 1776089 3999851 := bstep (se 1 (by rfl) ⟨2999888, by rfl⟩ : syracuseStep 3999851 = 5999777) B5999777
theorem B2665193 : Blo 1776089 2665193 := bstep (se 2 (by rfl) ⟨999447, by rfl⟩ : syracuseStep 2665193 = 1998895) B1998895
theorem B54701243 : Blo 1776089 54701243 := bstep (se 1 (by rfl) ⟨41025932, by rfl⟩ : syracuseStep 54701243 = 82051865) B82051865
theorem B2249471 : Blo 1776089 2249471 := bstep (se 1 (by rfl) ⟨1687103, by rfl⟩ : syracuseStep 2249471 = 3374207) B3374207
theorem B3374959 : Blo 1776089 3374959 := bstep (se 1 (by rfl) ⟨2531219, by rfl⟩ : syracuseStep 3374959 = 5062439) B5062439
theorem B15187895 : Blo 1776089 15187895 := bstep (se 1 (by rfl) ⟨11390921, by rfl⟩ : syracuseStep 15187895 = 22781843) B22781843
theorem B3999401 : Blo 1776089 3999401 := bstep (se 2 (by rfl) ⟨1499775, by rfl⟩ : syracuseStep 3999401 = 2999551) B2999551
theorem B5998589 : Blo 1776089 5998589 := bstep (se 3 (by rfl) ⟨1124735, by rfl⟩ : syracuseStep 5998589 = 2249471) B2249471
theorem B4499945 : Blo 1776089 4499945 := bstep (se 2 (by rfl) ⟨1687479, by rfl⟩ : syracuseStep 4499945 = 3374959) B3374959
theorem B2666567 : Blo 1776089 2666567 := bstep (se 1 (by rfl) ⟨1999925, by rfl⟩ : syracuseStep 2666567 = 3999851) B3999851
theorem B36467495 : Blo 1776089 36467495 := bstep (se 1 (by rfl) ⟨27350621, by rfl⟩ : syracuseStep 36467495 = 54701243) B54701243
theorem B1776795 : Blo 1776089 1776795 := bstep (se 1 (by rfl) ⟨1332596, by rfl⟩ : syracuseStep 1776795 = 2665193) B2665193
theorem B10125263 : Blo 1776089 10125263 := bstep (se 1 (by rfl) ⟨7593947, by rfl⟩ : syracuseStep 10125263 = 15187895) B15187895
theorem B1777711 : Blo 1776089 1777711 := bstep (se 1 (by rfl) ⟨1333283, by rfl⟩ : syracuseStep 1777711 = 2666567) B2666567
theorem B3999059 : Blo 1776089 3999059 := bstep (se 1 (by rfl) ⟨2999294, by rfl⟩ : syracuseStep 3999059 = 5998589) B5998589
theorem B2999963 : Blo 1776089 2999963 := bstep (se 1 (by rfl) ⟨2249972, by rfl⟩ : syracuseStep 2999963 = 4499945) B4499945
theorem B2666267 : Blo 1776089 2666267 := bstep (se 1 (by rfl) ⟨1999700, by rfl⟩ : syracuseStep 2666267 = 3999401) B3999401
theorem B24311663 : Blo 1776089 24311663 := bstep (se 1 (by rfl) ⟨18233747, by rfl⟩ : syracuseStep 24311663 = 36467495) B36467495
theorem B6750175 : Blo 1776089 6750175 := bstep (se 1 (by rfl) ⟨5062631, by rfl⟩ : syracuseStep 6750175 = 10125263) B10125263
theorem B1999975 : Blo 1776089 1999975 := bstep (se 1 (by rfl) ⟨1499981, by rfl⟩ : syracuseStep 1999975 = 2999963) B2999963
theorem B2666039 : Blo 1776089 2666039 := bstep (se 1 (by rfl) ⟨1999529, by rfl⟩ : syracuseStep 2666039 = 3999059) B3999059
theorem B16207775 : Blo 1776089 16207775 := bstep (se 1 (by rfl) ⟨12155831, by rfl⟩ : syracuseStep 16207775 = 24311663) B24311663
theorem B9000233 : Blo 1776089 9000233 := bstep (se 2 (by rfl) ⟨3375087, by rfl⟩ : syracuseStep 9000233 = 6750175) B6750175
theorem B1777511 : Blo 1776089 1777511 := bstep (se 1 (by rfl) ⟨1333133, by rfl⟩ : syracuseStep 1777511 = 2666267) B2666267
theorem B6000155 : Blo 1776089 6000155 := bstep (se 1 (by rfl) ⟨4500116, by rfl⟩ : syracuseStep 6000155 = 9000233) B9000233
theorem B2666633 : Blo 1776089 2666633 := bstep (se 2 (by rfl) ⟨999987, by rfl⟩ : syracuseStep 2666633 = 1999975) B1999975
theorem B1777359 : Blo 1776089 1777359 := bstep (se 1 (by rfl) ⟨1333019, by rfl⟩ : syracuseStep 1777359 = 2666039) B2666039
theorem B10805183 : Blo 1776089 10805183 := bstep (se 1 (by rfl) ⟨8103887, by rfl⟩ : syracuseStep 10805183 = 16207775) B16207775
theorem B1777755 : Blo 1776089 1777755 := bstep (se 1 (by rfl) ⟨1333316, by rfl⟩ : syracuseStep 1777755 = 2666633) B2666633
theorem B4000103 : Blo 1776089 4000103 := bstep (se 1 (by rfl) ⟨3000077, by rfl⟩ : syracuseStep 4000103 = 6000155) B6000155
theorem B7203455 : Blo 1776089 7203455 := bstep (se 1 (by rfl) ⟨5402591, by rfl⟩ : syracuseStep 7203455 = 10805183) B10805183
theorem B4802303 : Blo 1776089 4802303 := bstep (se 1 (by rfl) ⟨3601727, by rfl⟩ : syracuseStep 4802303 = 7203455) B7203455
theorem B2666735 : Blo 1776089 2666735 := bstep (se 1 (by rfl) ⟨2000051, by rfl⟩ : syracuseStep 2666735 = 4000103) B4000103
theorem B1777823 : Blo 1776089 1777823 := bstep (se 1 (by rfl) ⟨1333367, by rfl⟩ : syracuseStep 1777823 = 2666735) B2666735
theorem B3201535 : Blo 1776089 3201535 := bstep (se 1 (by rfl) ⟨2401151, by rfl⟩ : syracuseStep 3201535 = 4802303) B4802303
theorem B4268713 : Blo 1776089 4268713 := bstep (se 2 (by rfl) ⟨1600767, by rfl⟩ : syracuseStep 4268713 = 3201535) B3201535
theorem B5691617 : Blo 1776089 5691617 := bstep (se 2 (by rfl) ⟨2134356, by rfl⟩ : syracuseStep 5691617 = 4268713) B4268713
theorem B3794411 : Blo 1776089 3794411 := bstep (se 1 (by rfl) ⟨2845808, by rfl⟩ : syracuseStep 3794411 = 5691617) B5691617
theorem B10118429 : Blo 1776089 10118429 := bstep (se 3 (by rfl) ⟨1897205, by rfl⟩ : syracuseStep 10118429 = 3794411) B3794411
theorem B6745619 : Blo 1776089 6745619 := bstep (se 1 (by rfl) ⟨5059214, by rfl⟩ : syracuseStep 6745619 = 10118429) B10118429
theorem B4497079 : Blo 1776089 4497079 := bstep (se 1 (by rfl) ⟨3372809, by rfl⟩ : syracuseStep 4497079 = 6745619) B6745619
theorem B5996105 : Blo 1776089 5996105 := bstep (se 2 (by rfl) ⟨2248539, by rfl⟩ : syracuseStep 5996105 = 4497079) B4497079
theorem B3997403 : Blo 1776089 3997403 := bstep (se 1 (by rfl) ⟨2998052, by rfl⟩ : syracuseStep 3997403 = 5996105) B5996105
theorem B2664935 : Blo 1776089 2664935 := bstep (se 1 (by rfl) ⟨1998701, by rfl⟩ : syracuseStep 2664935 = 3997403) B3997403
theorem B1776623 : Blo 1776089 1776623 := bstep (se 1 (by rfl) ⟨1332467, by rfl⟩ : syracuseStep 1776623 = 2664935) B2664935

theorem C0 (j : ℕ) (h1 : 444022 ≤ j) (h2 : j ≤ 444521) : Blo 1776089 (4 * j + 3) := by
  interval_cases j
  · exact B1776091
  · exact B1776095
  · exact B1776099
  · exact B1776103
  · exact B1776107
  · exact B1776111
  · exact B1776115
  · exact B1776119
  · exact B1776123
  · exact B1776127
  · exact B1776131
  · exact B1776135
  · exact B1776139
  · exact B1776143
  · exact B1776147
  · exact B1776151
  · exact B1776155
  · exact B1776159
  · exact B1776163
  · exact B1776167
  · exact B1776171
  · exact B1776175
  · exact B1776179
  · exact B1776183
  · exact B1776187
  · exact B1776191
  · exact B1776195
  · exact B1776199
  · exact B1776203
  · exact B1776207
  · exact B1776211
  · exact B1776215
  · exact B1776219
  · exact B1776223
  · exact B1776227
  · exact B1776231
  · exact B1776235
  · exact B1776239
  · exact B1776243
  · exact B1776247
  · exact B1776251
  · exact B1776255
  · exact B1776259
  · exact B1776263
  · exact B1776267
  · exact B1776271
  · exact B1776275
  · exact B1776279
  · exact B1776283
  · exact B1776287
  · exact B1776291
  · exact B1776295
  · exact B1776299
  · exact B1776303
  · exact B1776307
  · exact B1776311
  · exact B1776315
  · exact B1776319
  · exact B1776323
  · exact B1776327
  · exact B1776331
  · exact B1776335
  · exact B1776339
  · exact B1776343
  · exact B1776347
  · exact B1776351
  · exact B1776355
  · exact B1776359
  · exact B1776363
  · exact B1776367
  · exact B1776371
  · exact B1776375
  · exact B1776379
  · exact B1776383
  · exact B1776387
  · exact B1776391
  · exact B1776395
  · exact B1776399
  · exact B1776403
  · exact B1776407
  · exact B1776411
  · exact B1776415
  · exact B1776419
  · exact B1776423
  · exact B1776427
  · exact B1776431
  · exact B1776435
  · exact B1776439
  · exact B1776443
  · exact B1776447
  · exact B1776451
  · exact B1776455
  · exact B1776459
  · exact B1776463
  · exact B1776467
  · exact B1776471
  · exact B1776475
  · exact B1776479
  · exact B1776483
  · exact B1776487
  · exact B1776491
  · exact B1776495
  · exact B1776499
  · exact B1776503
  · exact B1776507
  · exact B1776511
  · exact B1776515
  · exact B1776519
  · exact B1776523
  · exact B1776527
  · exact B1776531
  · exact B1776535
  · exact B1776539
  · exact B1776543
  · exact B1776547
  · exact B1776551
  · exact B1776555
  · exact B1776559
  · exact B1776563
  · exact B1776567
  · exact B1776571
  · exact B1776575
  · exact B1776579
  · exact B1776583
  · exact B1776587
  · exact B1776591
  · exact B1776595
  · exact B1776599
  · exact B1776603
  · exact B1776607
  · exact B1776611
  · exact B1776615
  · exact B1776619
  · exact B1776623
  · exact B1776627
  · exact B1776631
  · exact B1776635
  · exact B1776639
  · exact B1776643
  · exact B1776647
  · exact B1776651
  · exact B1776655
  · exact B1776659
  · exact B1776663
  · exact B1776667
  · exact B1776671
  · exact B1776675
  · exact B1776679
  · exact B1776683
  · exact B1776687
  · exact B1776691
  · exact B1776695
  · exact B1776699
  · exact B1776703
  · exact B1776707
  · exact B1776711
  · exact B1776715
  · exact B1776719
  · exact B1776723
  · exact B1776727
  · exact B1776731
  · exact B1776735
  · exact B1776739
  · exact B1776743
  · exact B1776747
  · exact B1776751
  · exact B1776755
  · exact B1776759
  · exact B1776763
  · exact B1776767
  · exact B1776771
  · exact B1776775
  · exact B1776779
  · exact B1776783
  · exact B1776787
  · exact B1776791
  · exact B1776795
  · exact B1776799
  · exact B1776803
  · exact B1776807
  · exact B1776811
  · exact B1776815
  · exact B1776819
  · exact B1776823
  · exact B1776827
  · exact B1776831
  · exact B1776835
  · exact B1776839
  · exact B1776843
  · exact B1776847
  · exact B1776851
  · exact B1776855
  · exact B1776859
  · exact B1776863
  · exact B1776867
  · exact B1776871
  · exact B1776875
  · exact B1776879
  · exact B1776883
  · exact B1776887
  · exact B1776891
  · exact B1776895
  · exact B1776899
  · exact B1776903
  · exact B1776907
  · exact B1776911
  · exact B1776915
  · exact B1776919
  · exact B1776923
  · exact B1776927
  · exact B1776931
  · exact B1776935
  · exact B1776939
  · exact B1776943
  · exact B1776947
  · exact B1776951
  · exact B1776955
  · exact B1776959
  · exact B1776963
  · exact B1776967
  · exact B1776971
  · exact B1776975
  · exact B1776979
  · exact B1776983
  · exact B1776987
  · exact B1776991
  · exact B1776995
  · exact B1776999
  · exact B1777003
  · exact B1777007
  · exact B1777011
  · exact B1777015
  · exact B1777019
  · exact B1777023
  · exact B1777027
  · exact B1777031
  · exact B1777035
  · exact B1777039
  · exact B1777043
  · exact B1777047
  · exact B1777051
  · exact B1777055
  · exact B1777059
  · exact B1777063
  · exact B1777067
  · exact B1777071
  · exact B1777075
  · exact B1777079
  · exact B1777083
  · exact B1777087
  · exact B1777091
  · exact B1777095
  · exact B1777099
  · exact B1777103
  · exact B1777107
  · exact B1777111
  · exact B1777115
  · exact B1777119
  · exact B1777123
  · exact B1777127
  · exact B1777131
  · exact B1777135
  · exact B1777139
  · exact B1777143
  · exact B1777147
  · exact B1777151
  · exact B1777155
  · exact B1777159
  · exact B1777163
  · exact B1777167
  · exact B1777171
  · exact B1777175
  · exact B1777179
  · exact B1777183
  · exact B1777187
  · exact B1777191
  · exact B1777195
  · exact B1777199
  · exact B1777203
  · exact B1777207
  · exact B1777211
  · exact B1777215
  · exact B1777219
  · exact B1777223
  · exact B1777227
  · exact B1777231
  · exact B1777235
  · exact B1777239
  · exact B1777243
  · exact B1777247
  · exact B1777251
  · exact B1777255
  · exact B1777259
  · exact B1777263
  · exact B1777267
  · exact B1777271
  · exact B1777275
  · exact B1777279
  · exact B1777283
  · exact B1777287
  · exact B1777291
  · exact B1777295
  · exact B1777299
  · exact B1777303
  · exact B1777307
  · exact B1777311
  · exact B1777315
  · exact B1777319
  · exact B1777323
  · exact B1777327
  · exact B1777331
  · exact B1777335
  · exact B1777339
  · exact B1777343
  · exact B1777347
  · exact B1777351
  · exact B1777355
  · exact B1777359
  · exact B1777363
  · exact B1777367
  · exact B1777371
  · exact B1777375
  · exact B1777379
  · exact B1777383
  · exact B1777387
  · exact B1777391
  · exact B1777395
  · exact B1777399
  · exact B1777403
  · exact B1777407
  · exact B1777411
  · exact B1777415
  · exact B1777419
  · exact B1777423
  · exact B1777427
  · exact B1777431
  · exact B1777435
  · exact B1777439
  · exact B1777443
  · exact B1777447
  · exact B1777451
  · exact B1777455
  · exact B1777459
  · exact B1777463
  · exact B1777467
  · exact B1777471
  · exact B1777475
  · exact B1777479
  · exact B1777483
  · exact B1777487
  · exact B1777491
  · exact B1777495
  · exact B1777499
  · exact B1777503
  · exact B1777507
  · exact B1777511
  · exact B1777515
  · exact B1777519
  · exact B1777523
  · exact B1777527
  · exact B1777531
  · exact B1777535
  · exact B1777539
  · exact B1777543
  · exact B1777547
  · exact B1777551
  · exact B1777555
  · exact B1777559
  · exact B1777563
  · exact B1777567
  · exact B1777571
  · exact B1777575
  · exact B1777579
  · exact B1777583
  · exact B1777587
  · exact B1777591
  · exact B1777595
  · exact B1777599
  · exact B1777603
  · exact B1777607
  · exact B1777611
  · exact B1777615
  · exact B1777619
  · exact B1777623
  · exact B1777627
  · exact B1777631
  · exact B1777635
  · exact B1777639
  · exact B1777643
  · exact B1777647
  · exact B1777651
  · exact B1777655
  · exact B1777659
  · exact B1777663
  · exact B1777667
  · exact B1777671
  · exact B1777675
  · exact B1777679
  · exact B1777683
  · exact B1777687
  · exact B1777691
  · exact B1777695
  · exact B1777699
  · exact B1777703
  · exact B1777707
  · exact B1777711
  · exact B1777715
  · exact B1777719
  · exact B1777723
  · exact B1777727
  · exact B1777731
  · exact B1777735
  · exact B1777739
  · exact B1777743
  · exact B1777747
  · exact B1777751
  · exact B1777755
  · exact B1777759
  · exact B1777763
  · exact B1777767
  · exact B1777771
  · exact B1777775
  · exact B1777779
  · exact B1777783
  · exact B1777787
  · exact B1777791
  · exact B1777795
  · exact B1777799
  · exact B1777803
  · exact B1777807
  · exact B1777811
  · exact B1777815
  · exact B1777819
  · exact B1777823
  · exact B1777827
  · exact B1777831
  · exact B1777835
  · exact B1777839
  · exact B1777843
  · exact B1777847
  · exact B1777851
  · exact B1777855
  · exact B1777859
  · exact B1777863
  · exact B1777867
  · exact B1777871
  · exact B1777875
  · exact B1777879
  · exact B1777883
  · exact B1777887
  · exact B1777891
  · exact B1777895
  · exact B1777899
  · exact B1777903
  · exact B1777907
  · exact B1777911
  · exact B1777915
  · exact B1777919
  · exact B1777923
  · exact B1777927
  · exact B1777931
  · exact B1777935
  · exact B1777939
  · exact B1777943
  · exact B1777947
  · exact B1777951
  · exact B1777955
  · exact B1777959
  · exact B1777963
  · exact B1777967
  · exact B1777971
  · exact B1777975
  · exact B1777979
  · exact B1777983
  · exact B1777987
  · exact B1777991
  · exact B1777995
  · exact B1777999
  · exact B1778003
  · exact B1778007
  · exact B1778011
  · exact B1778015
  · exact B1778019
  · exact B1778023
  · exact B1778027
  · exact B1778031
  · exact B1778035
  · exact B1778039
  · exact B1778043
  · exact B1778047
  · exact B1778051
  · exact B1778055
  · exact B1778059
  · exact B1778063
  · exact B1778067
  · exact B1778071
  · exact B1778075
  · exact B1778079
  · exact B1778083
  · exact B1778087

theorem solution (m : ℕ) (hlo : 1776089 ≤ m) (hhi : m ≤ 1778089) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 444022 ≤ j := by omega
    have hj2 : j ≤ 444521 := by omega
    have hb : Blo 1776089 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
