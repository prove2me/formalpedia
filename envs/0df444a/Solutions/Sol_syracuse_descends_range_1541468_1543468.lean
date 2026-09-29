-- Prove2me | solution 1 for syracuse_descends_range_1541468_1543468
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:05:13.529989+00:00
-- url     : https://prove2.me/submissions/26e2a199-91b6-4ba0-99b9-e65710e9b06e

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


theorem B6021125 : Blo 1541468 6021125 := bbase (se 4 (by rfl) ⟨564480, by rfl⟩ : syracuseStep 6021125 = 1128961) (by norm_num)
theorem B4390949 : Blo 1541468 4390949 := bbase (se 4 (by rfl) ⟨411651, by rfl⟩ : syracuseStep 4390949 = 823303) (by norm_num)
theorem B6250661 : Blo 1541468 6250661 := bbase (se 4 (by rfl) ⟨585999, by rfl⟩ : syracuseStep 6250661 = 1171999) (by norm_num)
theorem B1646777 : Blo 1541468 1646777 := bbase (se 2 (by rfl) ⟨617541, by rfl⟩ : syracuseStep 1646777 = 1235083) (by norm_num)
theorem B4939973 : Blo 1541468 4939973 := bbase (se 4 (by rfl) ⟨463122, by rfl⟩ : syracuseStep 4939973 = 926245) (by norm_num)
theorem B2113997 : Blo 1541468 2113997 := bbase (se 3 (by rfl) ⟨396374, by rfl⟩ : syracuseStep 2113997 = 792749) (by norm_num)
theorem B11715029 : Blo 1541468 11715029 := bbase (se 7 (by rfl) ⟨137285, by rfl⟩ : syracuseStep 11715029 = 274571) (by norm_num)
theorem B1851865 : Blo 1541468 1851865 := bbase (se 2 (by rfl) ⟨694449, by rfl⟩ : syracuseStep 1851865 = 1388899) (by norm_num)
theorem B3957221 : Blo 1541468 3957221 := bbase (se 4 (by rfl) ⟨370989, by rfl⟩ : syracuseStep 3957221 = 741979) (by norm_num)
theorem B3006973 : Blo 1541468 3006973 := bbase (se 3 (by rfl) ⟨563807, by rfl⟩ : syracuseStep 3006973 = 1127615) (by norm_num)
theorem B3957245 : Blo 1541468 3957245 := bbase (se 3 (by rfl) ⟨741983, by rfl⟩ : syracuseStep 3957245 = 1483967) (by norm_num)
theorem B3293725 : Blo 1541468 3293725 := bbase (se 3 (by rfl) ⟨617573, by rfl⟩ : syracuseStep 3293725 = 1235147) (by norm_num)
theorem B7414325 : Blo 1541468 7414325 := bbase (se 5 (by rfl) ⟨347546, by rfl⟩ : syracuseStep 7414325 = 695093) (by norm_num)
theorem B7807589 : Blo 1541468 7807589 := bbase (se 4 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 7807589 = 1463923) (by norm_num)
theorem B1647221 : Blo 1541468 1647221 := bbase (se 5 (by rfl) ⟨77213, by rfl⟩ : syracuseStep 1647221 = 154427) (by norm_num)
theorem B5202629 : Blo 1541468 5202629 := bbase (se 4 (by rfl) ⟨487746, by rfl⟩ : syracuseStep 5202629 = 975493) (by norm_num)
theorem B2196181 : Blo 1541468 2196181 := bbase (se 7 (by rfl) ⟨25736, by rfl⟩ : syracuseStep 2196181 = 51473) (by norm_num)
theorem B1647469 : Blo 1541468 1647469 := bbase (se 3 (by rfl) ⟨308900, by rfl⟩ : syracuseStep 1647469 = 617801) (by norm_num)
theorem B11707253 : Blo 1541468 11707253 := bbase (se 5 (by rfl) ⟨548777, by rfl⟩ : syracuseStep 11707253 = 1097555) (by norm_num)
theorem B4752245 : Blo 1541468 4752245 := bbase (se 5 (by rfl) ⟨222761, by rfl⟩ : syracuseStep 4752245 = 445523) (by norm_num)
theorem B3294101 : Blo 1541468 3294101 := bbase (se 6 (by rfl) ⟨77205, by rfl⟩ : syracuseStep 3294101 = 154411) (by norm_num)
theorem B3957653 : Blo 1541468 3957653 := bbase (se 6 (by rfl) ⟨92757, by rfl⟩ : syracuseStep 3957653 = 185515) (by norm_num)
theorem B6587365 : Blo 1541468 6587365 := bbase (se 4 (by rfl) ⟨617565, by rfl⟩ : syracuseStep 6587365 = 1235131) (by norm_num)
theorem B6587381 : Blo 1541468 6587381 := bbase (se 5 (by rfl) ⟨308783, by rfl⟩ : syracuseStep 6587381 = 617567) (by norm_num)
theorem B4391941 : Blo 1541468 4391941 := bbase (se 4 (by rfl) ⟨411744, by rfl⟩ : syracuseStep 4391941 = 823489) (by norm_num)
theorem B8782901 : Blo 1541468 8782901 := bbase (se 5 (by rfl) ⟨411698, by rfl⟩ : syracuseStep 8782901 = 823397) (by norm_num)
theorem B5203061 : Blo 1541468 5203061 := bbase (se 5 (by rfl) ⟨243893, by rfl⟩ : syracuseStep 5203061 = 487787) (by norm_num)
theorem B3703981 : Blo 1541468 3703981 := bbase (se 3 (by rfl) ⟨694496, by rfl⟩ : syracuseStep 3703981 = 1388993) (by norm_num)
theorem B13173941 : Blo 1541468 13173941 := bbase (se 5 (by rfl) ⟨617528, by rfl⟩ : syracuseStep 13173941 = 1235057) (by norm_num)
theorem B2344157 : Blo 1541468 2344157 := bbase (se 3 (by rfl) ⟨439529, by rfl⟩ : syracuseStep 2344157 = 879059) (by norm_num)
theorem B1950961 : Blo 1541468 1950961 := bbase (se 2 (by rfl) ⟨731610, by rfl⟩ : syracuseStep 1950961 = 1463221) (by norm_num)
theorem B1647901 : Blo 1541468 1647901 := bbase (se 3 (by rfl) ⟨308981, by rfl⟩ : syracuseStep 1647901 = 617963) (by norm_num)
theorem B5276981 : Blo 1541468 5276981 := bbase (se 5 (by rfl) ⟨247358, by rfl⟩ : syracuseStep 5276981 = 494717) (by norm_num)
theorem B1951057 : Blo 1541468 1951057 := bbase (se 2 (by rfl) ⟨731646, by rfl⟩ : syracuseStep 1951057 = 1463293) (by norm_num)
theorem B2966869 : Blo 1541468 2966869 := bbase (se 12 (by rfl) ⟨1086, by rfl⟩ : syracuseStep 2966869 = 2173) (by norm_num)
theorem B1647973 : Blo 1541468 1647973 := bbase (se 4 (by rfl) ⟨154497, by rfl⟩ : syracuseStep 1647973 = 308995) (by norm_num)
theorem B4941253 : Blo 1541468 4941253 := bbase (se 4 (by rfl) ⟨463242, by rfl⟩ : syracuseStep 4941253 = 926485) (by norm_num)
theorem B2196973 : Blo 1541468 2196973 := bbase (se 3 (by rfl) ⟨411932, by rfl⟩ : syracuseStep 2196973 = 823865) (by norm_num)
theorem B1852913 : Blo 1541468 1852913 := bbase (se 2 (by rfl) ⟨694842, by rfl⟩ : syracuseStep 1852913 = 1389685) (by norm_num)
theorem B1951229 : Blo 1541468 1951229 := bbase (se 3 (by rfl) ⟨365855, by rfl⟩ : syracuseStep 1951229 = 731711) (by norm_num)
theorem B5858837 : Blo 1541468 5858837 := bbase (se 6 (by rfl) ⟨137316, by rfl⟩ : syracuseStep 5858837 = 274633) (by norm_num)
theorem B5203493 : Blo 1541468 5203493 := bbase (se 4 (by rfl) ⟨487827, by rfl⟩ : syracuseStep 5203493 = 975655) (by norm_num)
theorem B1951285 : Blo 1541468 1951285 := bbase (se 5 (by rfl) ⟨91466, by rfl⟩ : syracuseStep 1951285 = 182933) (by norm_num)
theorem B5860309 : Blo 1541468 5860309 := bbase (se 7 (by rfl) ⟨68675, by rfl⟩ : syracuseStep 5860309 = 137351) (by norm_num)
theorem B1951381 : Blo 1541468 1951381 := bbase (se 6 (by rfl) ⟨45735, by rfl⟩ : syracuseStep 1951381 = 91471) (by norm_num)
theorem B25011989 : Blo 1541468 25011989 := bbase (se 6 (by rfl) ⟨586218, by rfl⟩ : syracuseStep 25011989 = 1172437) (by norm_num)
theorem B1853221 : Blo 1541468 1853221 := bbase (se 4 (by rfl) ⟨173739, by rfl⟩ : syracuseStep 1853221 = 347479) (by norm_num)
theorem B5859125 : Blo 1541468 5859125 := bbase (se 5 (by rfl) ⟨274646, by rfl⟩ : syracuseStep 5859125 = 549293) (by norm_num)
theorem B2197309 : Blo 1541468 2197309 := bbase (se 3 (by rfl) ⟨411995, by rfl⟩ : syracuseStep 2197309 = 823991) (by norm_num)
theorem B1951553 : Blo 1541468 1951553 := bbase (se 2 (by rfl) ⟨731832, by rfl⟩ : syracuseStep 1951553 = 1463665) (by norm_num)
theorem B3704653 : Blo 1541468 3704653 := bbase (se 3 (by rfl) ⟨694622, by rfl⟩ : syracuseStep 3704653 = 1389245) (by norm_num)
theorem B7808885 : Blo 1541468 7808885 := bbase (se 5 (by rfl) ⟨366041, by rfl⟩ : syracuseStep 7808885 = 732083) (by norm_num)
theorem B1951609 : Blo 1541468 1951609 := bbase (se 2 (by rfl) ⟨731853, by rfl⟩ : syracuseStep 1951609 = 1463707) (by norm_num)
theorem B2926525 : Blo 1541468 2926525 := bbase (se 3 (by rfl) ⟨548723, by rfl⟩ : syracuseStep 2926525 = 1097447) (by norm_num)
theorem B1853389 : Blo 1541468 1853389 := bbase (se 3 (by rfl) ⟨347510, by rfl⟩ : syracuseStep 1853389 = 695021) (by norm_num)
theorem B5203925 : Blo 1541468 5203925 := bbase (se 7 (by rfl) ⟨60983, by rfl⟩ : syracuseStep 5203925 = 121967) (by norm_num)
theorem B1951705 : Blo 1541468 1951705 := bbase (se 2 (by rfl) ⟨731889, by rfl⟩ : syracuseStep 1951705 = 1463779) (by norm_num)
theorem B2312213 : Blo 1541468 2312213 := bbase (se 6 (by rfl) ⟨54192, by rfl⟩ : syracuseStep 2312213 = 108385) (by norm_num)
theorem B2197525 : Blo 1541468 2197525 := bbase (se 6 (by rfl) ⟨51504, by rfl⟩ : syracuseStep 2197525 = 103009) (by norm_num)
theorem B2312237 : Blo 1541468 2312237 := bbase (se 3 (by rfl) ⟨433544, by rfl⟩ : syracuseStep 2312237 = 867089) (by norm_num)
theorem B3704885 : Blo 1541468 3704885 := bbase (se 5 (by rfl) ⟨173666, by rfl⟩ : syracuseStep 3704885 = 347333) (by norm_num)
theorem B2312261 : Blo 1541468 2312261 := bbase (se 4 (by rfl) ⟨216774, by rfl⟩ : syracuseStep 2312261 = 433549) (by norm_num)
theorem B4393045 : Blo 1541468 4393045 := bbase (se 8 (by rfl) ⟨25740, by rfl⟩ : syracuseStep 4393045 = 51481) (by norm_num)
theorem B2312285 : Blo 1541468 2312285 := bbase (se 3 (by rfl) ⟨433553, by rfl⟩ : syracuseStep 2312285 = 867107) (by norm_num)
theorem B2926685 : Blo 1541468 2926685 := bbase (se 3 (by rfl) ⟨548753, by rfl⟩ : syracuseStep 2926685 = 1097507) (by norm_num)
theorem B3704933 : Blo 1541468 3704933 := bbase (se 4 (by rfl) ⟨347337, by rfl⟩ : syracuseStep 3704933 = 694675) (by norm_num)
theorem B2312309 : Blo 1541468 2312309 := bbase (se 5 (by rfl) ⟨108389, by rfl⟩ : syracuseStep 2312309 = 216779) (by norm_num)
theorem B1951877 : Blo 1541468 1951877 := bbase (se 4 (by rfl) ⟨182988, by rfl⟩ : syracuseStep 1951877 = 365977) (by norm_num)
theorem B2312333 : Blo 1541468 2312333 := bbase (se 3 (by rfl) ⟨433562, by rfl⟩ : syracuseStep 2312333 = 867125) (by norm_num)
theorem B1853585 : Blo 1541468 1853585 := bbase (se 2 (by rfl) ⟨695094, by rfl⟩ : syracuseStep 1853585 = 1390189) (by norm_num)
theorem B2312357 : Blo 1541468 2312357 := bbase (se 4 (by rfl) ⟨216783, by rfl⟩ : syracuseStep 2312357 = 433567) (by norm_num)
theorem B3516581 : Blo 1541468 3516581 := bbase (se 4 (by rfl) ⟨329679, by rfl⟩ : syracuseStep 3516581 = 659359) (by norm_num)
theorem B2312381 : Blo 1541468 2312381 := bbase (se 3 (by rfl) ⟨433571, by rfl⟩ : syracuseStep 2312381 = 867143) (by norm_num)
theorem B1951933 : Blo 1541468 1951933 := bbase (se 3 (by rfl) ⟨365987, by rfl⟩ : syracuseStep 1951933 = 731975) (by norm_num)
theorem B2312405 : Blo 1541468 2312405 := bbase (se 7 (by rfl) ⟨27098, by rfl⟩ : syracuseStep 2312405 = 54197) (by norm_num)
theorem B8784085 : Blo 1541468 8784085 := bbase (se 7 (by rfl) ⟨102938, by rfl⟩ : syracuseStep 8784085 = 205877) (by norm_num)
theorem B2312429 : Blo 1541468 2312429 := bbase (se 3 (by rfl) ⟨433580, by rfl⟩ : syracuseStep 2312429 = 867161) (by norm_num)
theorem B2926829 : Blo 1541468 2926829 := bbase (se 3 (by rfl) ⟨548780, by rfl⟩ : syracuseStep 2926829 = 1097561) (by norm_num)
theorem B2312453 : Blo 1541468 2312453 := bbase (se 4 (by rfl) ⟨216792, by rfl⟩ : syracuseStep 2312453 = 433585) (by norm_num)
theorem B2312477 : Blo 1541468 2312477 := bbase (se 3 (by rfl) ⟨433589, by rfl⟩ : syracuseStep 2312477 = 867179) (by norm_num)
theorem B1952029 : Blo 1541468 1952029 := bbase (se 3 (by rfl) ⟨366005, by rfl⟩ : syracuseStep 1952029 = 732011) (by norm_num)
theorem B2312501 : Blo 1541468 2312501 := bbase (se 5 (by rfl) ⟨108398, by rfl⟩ : syracuseStep 2312501 = 216797) (by norm_num)
theorem B2312525 : Blo 1541468 2312525 := bbase (se 3 (by rfl) ⟨433598, by rfl⟩ : syracuseStep 2312525 = 867197) (by norm_num)
theorem B2312549 : Blo 1541468 2312549 := bbase (se 4 (by rfl) ⟨216801, by rfl⟩ : syracuseStep 2312549 = 433603) (by norm_num)
theorem B2312573 : Blo 1541468 2312573 := bbase (se 3 (by rfl) ⟨433607, by rfl⟩ : syracuseStep 2312573 = 867215) (by norm_num)
theorem B5204357 : Blo 1541468 5204357 := bbase (se 4 (by rfl) ⟨487908, by rfl⟩ : syracuseStep 5204357 = 975817) (by norm_num)
theorem B2312597 : Blo 1541468 2312597 := bbase (se 6 (by rfl) ⟨54201, by rfl⟩ : syracuseStep 2312597 = 108403) (by norm_num)
theorem B7408037 : Blo 1541468 7408037 := bbase (se 4 (by rfl) ⟨694503, by rfl⟩ : syracuseStep 7408037 = 1389007) (by norm_num)
theorem B2312621 : Blo 1541468 2312621 := bbase (se 3 (by rfl) ⟨433616, by rfl⟩ : syracuseStep 2312621 = 867233) (by norm_num)
theorem B2312645 : Blo 1541468 2312645 := bbase (se 4 (by rfl) ⟨216810, by rfl⟩ : syracuseStep 2312645 = 433621) (by norm_num)
theorem B1952201 : Blo 1541468 1952201 := bbase (se 2 (by rfl) ⟨732075, by rfl⟩ : syracuseStep 1952201 = 1464151) (by norm_num)
theorem B2312669 : Blo 1541468 2312669 := bbase (se 3 (by rfl) ⟨433625, by rfl⟩ : syracuseStep 2312669 = 867251) (by norm_num)
theorem B2312693 : Blo 1541468 2312693 := bbase (se 5 (by rfl) ⟨108407, by rfl⟩ : syracuseStep 2312693 = 216815) (by norm_num)
theorem B3295741 : Blo 1541468 3295741 := bbase (se 3 (by rfl) ⟨617951, by rfl⟩ : syracuseStep 3295741 = 1235903) (by norm_num)
theorem B1952257 : Blo 1541468 1952257 := bbase (se 2 (by rfl) ⟨732096, by rfl⟩ : syracuseStep 1952257 = 1464193) (by norm_num)
theorem B2312717 : Blo 1541468 2312717 := bbase (se 3 (by rfl) ⟨433634, by rfl⟩ : syracuseStep 2312717 = 867269) (by norm_num)
theorem B2927117 : Blo 1541468 2927117 := bbase (se 3 (by rfl) ⟨548834, by rfl⟩ : syracuseStep 2927117 = 1097669) (by norm_num)
theorem B17132053 : Blo 1541468 17132053 := bbase (se 6 (by rfl) ⟨401532, by rfl⟩ : syracuseStep 17132053 = 803065) (by norm_num)
theorem B2312741 : Blo 1541468 2312741 := bbase (se 4 (by rfl) ⟨216819, by rfl⟩ : syracuseStep 2312741 = 433639) (by norm_num)
theorem B2312765 : Blo 1541468 2312765 := bbase (se 3 (by rfl) ⟨433643, by rfl⟩ : syracuseStep 2312765 = 867287) (by norm_num)
theorem B2312789 : Blo 1541468 2312789 := bbase (se 8 (by rfl) ⟨13551, by rfl⟩ : syracuseStep 2312789 = 27103) (by norm_num)
theorem B1952353 : Blo 1541468 1952353 := bbase (se 2 (by rfl) ⟨732132, by rfl⟩ : syracuseStep 1952353 = 1464265) (by norm_num)
theorem B3902053 : Blo 1541468 3902053 := bbase (se 4 (by rfl) ⟨365817, by rfl⟩ : syracuseStep 3902053 = 731635) (by norm_num)
theorem B2312813 : Blo 1541468 2312813 := bbase (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) (by norm_num)
theorem B2312837 : Blo 1541468 2312837 := bbase (se 4 (by rfl) ⟨216828, by rfl⟩ : syracuseStep 2312837 = 433657) (by norm_num)
theorem B2312861 : Blo 1541468 2312861 := bbase (se 3 (by rfl) ⟨433661, by rfl⟩ : syracuseStep 2312861 = 867323) (by norm_num)
theorem B2927269 : Blo 1541468 2927269 := bbase (se 4 (by rfl) ⟨274431, by rfl⟩ : syracuseStep 2927269 = 548863) (by norm_num)
theorem B2312885 : Blo 1541468 2312885 := bbase (se 5 (by rfl) ⟨108416, by rfl⟩ : syracuseStep 2312885 = 216833) (by norm_num)
theorem B2312909 : Blo 1541468 2312909 := bbase (se 3 (by rfl) ⟨433670, by rfl⟩ : syracuseStep 2312909 = 867341) (by norm_num)
theorem B3902165 : Blo 1541468 3902165 := bbase (se 7 (by rfl) ⟨45728, by rfl⟩ : syracuseStep 3902165 = 91457) (by norm_num)
theorem B2312933 : Blo 1541468 2312933 := bbase (se 4 (by rfl) ⟨216837, by rfl⟩ : syracuseStep 2312933 = 433675) (by norm_num)
theorem B2312957 : Blo 1541468 2312957 := bbase (se 3 (by rfl) ⟨433679, by rfl⟩ : syracuseStep 2312957 = 867359) (by norm_num)
theorem B1952525 : Blo 1541468 1952525 := bbase (se 3 (by rfl) ⟨366098, by rfl⟩ : syracuseStep 1952525 = 732197) (by norm_num)
theorem B2312981 : Blo 1541468 2312981 := bbase (se 6 (by rfl) ⟨54210, by rfl⟩ : syracuseStep 2312981 = 108421) (by norm_num)
theorem B4942613 : Blo 1541468 4942613 := bbase (se 6 (by rfl) ⟨115842, by rfl⟩ : syracuseStep 4942613 = 231685) (by norm_num)
theorem B2313005 : Blo 1541468 2313005 := bbase (se 3 (by rfl) ⟨433688, by rfl⟩ : syracuseStep 2313005 = 867377) (by norm_num)
theorem B5204789 : Blo 1541468 5204789 := bbase (se 5 (by rfl) ⟨243974, by rfl⟩ : syracuseStep 5204789 = 487949) (by norm_num)
theorem B2313029 : Blo 1541468 2313029 := bbase (se 4 (by rfl) ⟨216846, by rfl⟩ : syracuseStep 2313029 = 433693) (by norm_num)
theorem B1952581 : Blo 1541468 1952581 := bbase (se 4 (by rfl) ⟨183054, by rfl⟩ : syracuseStep 1952581 = 366109) (by norm_num)
theorem B2313053 : Blo 1541468 2313053 := bbase (se 3 (by rfl) ⟨433697, by rfl⟩ : syracuseStep 2313053 = 867395) (by norm_num)
theorem B2313077 : Blo 1541468 2313077 := bbase (se 5 (by rfl) ⟨108425, by rfl⟩ : syracuseStep 2313077 = 216851) (by norm_num)
theorem B9882485 : Blo 1541468 9882485 := bbase (se 5 (by rfl) ⟨463241, by rfl⟩ : syracuseStep 9882485 = 926483) (by norm_num)
theorem B2313101 : Blo 1541468 2313101 := bbase (se 3 (by rfl) ⟨433706, by rfl⟩ : syracuseStep 2313101 = 867413) (by norm_num)
theorem B3902357 : Blo 1541468 3902357 := bbase (se 6 (by rfl) ⟨91461, by rfl⟩ : syracuseStep 3902357 = 182923) (by norm_num)
theorem B4942741 : Blo 1541468 4942741 := bbase (se 6 (by rfl) ⟨115845, by rfl⟩ : syracuseStep 4942741 = 231691) (by norm_num)
theorem B13732757 : Blo 1541468 13732757 := bbase (se 6 (by rfl) ⟨321861, by rfl⟩ : syracuseStep 13732757 = 643723) (by norm_num)
theorem B2313125 : Blo 1541468 2313125 := bbase (se 4 (by rfl) ⟨216855, by rfl⟩ : syracuseStep 2313125 = 433711) (by norm_num)
theorem B1952677 : Blo 1541468 1952677 := bbase (se 4 (by rfl) ⟨183063, by rfl⟩ : syracuseStep 1952677 = 366127) (by norm_num)
theorem B1878953 : Blo 1541468 1878953 := bbase (se 2 (by rfl) ⟨704607, by rfl⟩ : syracuseStep 1878953 = 1409215) (by norm_num)
theorem B2313149 : Blo 1541468 2313149 := bbase (se 3 (by rfl) ⟨433715, by rfl⟩ : syracuseStep 2313149 = 867431) (by norm_num)
theorem B18754517 : Blo 1541468 18754517 := bbase (se 7 (by rfl) ⟨219779, by rfl⟩ : syracuseStep 18754517 = 439559) (by norm_num)
theorem B2927573 : Blo 1541468 2927573 := bbase (se 7 (by rfl) ⟨34307, by rfl⟩ : syracuseStep 2927573 = 68615) (by norm_num)
theorem B2313173 : Blo 1541468 2313173 := bbase (se 7 (by rfl) ⟨27107, by rfl⟩ : syracuseStep 2313173 = 54215) (by norm_num)
theorem B2313197 : Blo 1541468 2313197 := bbase (se 3 (by rfl) ⟨433724, by rfl⟩ : syracuseStep 2313197 = 867449) (by norm_num)
theorem B2313221 : Blo 1541468 2313221 := bbase (se 4 (by rfl) ⟨216864, by rfl⟩ : syracuseStep 2313221 = 433729) (by norm_num)
theorem B2313245 : Blo 1541468 2313245 := bbase (se 3 (by rfl) ⟨433733, by rfl⟩ : syracuseStep 2313245 = 867467) (by norm_num)
theorem B2313269 : Blo 1541468 2313269 := bbase (se 5 (by rfl) ⟨108434, by rfl⟩ : syracuseStep 2313269 = 216869) (by norm_num)
theorem B3468365 : Blo 1541468 3468365 := bbase (se 3 (by rfl) ⟨650318, by rfl⟩ : syracuseStep 3468365 = 1300637) (by norm_num)
theorem B2313293 : Blo 1541468 2313293 := bbase (se 3 (by rfl) ⟨433742, by rfl⟩ : syracuseStep 2313293 = 867485) (by norm_num)
theorem B1952849 : Blo 1541468 1952849 := bbase (se 2 (by rfl) ⟨732318, by rfl⟩ : syracuseStep 1952849 = 1464637) (by norm_num)
theorem B20024405 : Blo 1541468 20024405 := bbase (se 8 (by rfl) ⟨117330, by rfl⟩ : syracuseStep 20024405 = 234661) (by norm_num)
theorem B2313317 : Blo 1541468 2313317 := bbase (se 4 (by rfl) ⟨216873, by rfl⟩ : syracuseStep 2313317 = 433747) (by norm_num)
theorem B2313341 : Blo 1541468 2313341 := bbase (se 3 (by rfl) ⟨433751, by rfl⟩ : syracuseStep 2313341 = 867503) (by norm_num)
theorem B7810181 : Blo 1541468 7810181 := bbase (se 4 (by rfl) ⟨732204, by rfl⟩ : syracuseStep 7810181 = 1464409) (by norm_num)
theorem B1952905 : Blo 1541468 1952905 := bbase (se 2 (by rfl) ⟨732339, by rfl⟩ : syracuseStep 1952905 = 1464679) (by norm_num)
theorem B3468437 : Blo 1541468 3468437 := bbase (se 6 (by rfl) ⟨81291, by rfl⟩ : syracuseStep 3468437 = 162583) (by norm_num)
theorem B2313365 : Blo 1541468 2313365 := bbase (se 6 (by rfl) ⟨54219, by rfl⟩ : syracuseStep 2313365 = 108439) (by norm_num)
theorem B4942997 : Blo 1541468 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B2313389 : Blo 1541468 2313389 := bbase (se 3 (by rfl) ⟨433760, by rfl⟩ : syracuseStep 2313389 = 867521) (by norm_num)
theorem B2313413 : Blo 1541468 2313413 := bbase (se 4 (by rfl) ⟨216882, by rfl⟩ : syracuseStep 2313413 = 433765) (by norm_num)
theorem B6589637 : Blo 1541468 6589637 := bbase (se 4 (by rfl) ⟨617778, by rfl⟩ : syracuseStep 6589637 = 1235557) (by norm_num)
theorem B3468509 : Blo 1541468 3468509 := bbase (se 3 (by rfl) ⟨650345, by rfl⟩ : syracuseStep 3468509 = 1300691) (by norm_num)
theorem B2313437 : Blo 1541468 2313437 := bbase (se 3 (by rfl) ⟨433769, by rfl⟩ : syracuseStep 2313437 = 867539) (by norm_num)
theorem B5205221 : Blo 1541468 5205221 := bbase (se 4 (by rfl) ⟨487989, by rfl⟩ : syracuseStep 5205221 = 975979) (by norm_num)
theorem B1953001 : Blo 1541468 1953001 := bbase (se 2 (by rfl) ⟨732375, by rfl⟩ : syracuseStep 1953001 = 1464751) (by norm_num)
theorem B3902701 : Blo 1541468 3902701 := bbase (se 3 (by rfl) ⟨731756, by rfl⟩ : syracuseStep 3902701 = 1463513) (by norm_num)
theorem B2313461 : Blo 1541468 2313461 := bbase (se 5 (by rfl) ⟨108443, by rfl⟩ : syracuseStep 2313461 = 216887) (by norm_num)
theorem B2313485 : Blo 1541468 2313485 := bbase (se 3 (by rfl) ⟨433778, by rfl⟩ : syracuseStep 2313485 = 867557) (by norm_num)
theorem B3468581 : Blo 1541468 3468581 := bbase (se 4 (by rfl) ⟨325179, by rfl⟩ : syracuseStep 3468581 = 650359) (by norm_num)
theorem B2313509 : Blo 1541468 2313509 := bbase (se 4 (by rfl) ⟨216891, by rfl⟩ : syracuseStep 2313509 = 433783) (by norm_num)
theorem B2313533 : Blo 1541468 2313533 := bbase (se 3 (by rfl) ⟨433787, by rfl⟩ : syracuseStep 2313533 = 867575) (by norm_num)
theorem B2313557 : Blo 1541468 2313557 := bbase (se 11 (by rfl) ⟨1694, by rfl⟩ : syracuseStep 2313557 = 3389) (by norm_num)
theorem B3902813 : Blo 1541468 3902813 := bbase (se 3 (by rfl) ⟨731777, by rfl⟩ : syracuseStep 3902813 = 1463555) (by norm_num)
theorem B2780509 : Blo 1541468 2780509 := bbase (se 3 (by rfl) ⟨521345, by rfl⟩ : syracuseStep 2780509 = 1042691) (by norm_num)
theorem B3468653 : Blo 1541468 3468653 := bbase (se 3 (by rfl) ⟨650372, by rfl⟩ : syracuseStep 3468653 = 1300745) (by norm_num)
theorem B2313581 : Blo 1541468 2313581 := bbase (se 3 (by rfl) ⟨433796, by rfl⟩ : syracuseStep 2313581 = 867593) (by norm_num)
theorem B2313605 : Blo 1541468 2313605 := bbase (se 4 (by rfl) ⟨216900, by rfl⟩ : syracuseStep 2313605 = 433801) (by norm_num)
theorem B1953173 : Blo 1541468 1953173 := bbase (se 6 (by rfl) ⟨45777, by rfl⟩ : syracuseStep 1953173 = 91555) (by norm_num)
theorem B2313629 : Blo 1541468 2313629 := bbase (se 3 (by rfl) ⟨433805, by rfl⟩ : syracuseStep 2313629 = 867611) (by norm_num)
theorem B2780581 : Blo 1541468 2780581 := bbase (se 4 (by rfl) ⟨260679, by rfl⟩ : syracuseStep 2780581 = 521359) (by norm_num)
theorem B3468725 : Blo 1541468 3468725 := bbase (se 5 (by rfl) ⟨162596, by rfl⟩ : syracuseStep 3468725 = 325193) (by norm_num)
theorem B2313653 : Blo 1541468 2313653 := bbase (se 5 (by rfl) ⟨108452, by rfl⟩ : syracuseStep 2313653 = 216905) (by norm_num)
theorem B2313677 : Blo 1541468 2313677 := bbase (se 3 (by rfl) ⟨433814, by rfl⟩ : syracuseStep 2313677 = 867629) (by norm_num)
theorem B1953229 : Blo 1541468 1953229 := bbase (se 3 (by rfl) ⟨366230, by rfl⟩ : syracuseStep 1953229 = 732461) (by norm_num)
theorem B3706325 : Blo 1541468 3706325 := bbase (se 7 (by rfl) ⟨43433, by rfl⟩ : syracuseStep 3706325 = 86867) (by norm_num)
theorem B2313701 : Blo 1541468 2313701 := bbase (se 4 (by rfl) ⟨216909, by rfl⟩ : syracuseStep 2313701 = 433819) (by norm_num)
theorem B3468797 : Blo 1541468 3468797 := bbase (se 3 (by rfl) ⟨650399, by rfl⟩ : syracuseStep 3468797 = 1300799) (by norm_num)
theorem B2313725 : Blo 1541468 2313725 := bbase (se 3 (by rfl) ⟨433823, by rfl⟩ : syracuseStep 2313725 = 867647) (by norm_num)
theorem B2313749 : Blo 1541468 2313749 := bbase (se 6 (by rfl) ⟨54228, by rfl⟩ : syracuseStep 2313749 = 108457) (by norm_num)
theorem B3903005 : Blo 1541468 3903005 := bbase (se 3 (by rfl) ⟨731813, by rfl⟩ : syracuseStep 3903005 = 1463627) (by norm_num)
theorem B2313773 : Blo 1541468 2313773 := bbase (se 3 (by rfl) ⟨433832, by rfl⟩ : syracuseStep 2313773 = 867665) (by norm_num)
theorem B1953325 : Blo 1541468 1953325 := bbase (se 3 (by rfl) ⟨366248, by rfl⟩ : syracuseStep 1953325 = 732497) (by norm_num)
theorem B4394549 : Blo 1541468 4394549 := bbase (se 5 (by rfl) ⟨205994, by rfl⟩ : syracuseStep 4394549 = 411989) (by norm_num)
theorem B3468869 : Blo 1541468 3468869 := bbase (se 4 (by rfl) ⟨325206, by rfl⟩ : syracuseStep 3468869 = 650413) (by norm_num)
theorem B2313797 : Blo 1541468 2313797 := bbase (se 4 (by rfl) ⟨216918, by rfl⟩ : syracuseStep 2313797 = 433837) (by norm_num)
theorem B8343125 : Blo 1541468 8343125 := bbase (se 8 (by rfl) ⟨48885, by rfl⟩ : syracuseStep 8343125 = 97771) (by norm_num)
theorem B2313821 : Blo 1541468 2313821 := bbase (se 3 (by rfl) ⟨433841, by rfl⟩ : syracuseStep 2313821 = 867683) (by norm_num)
theorem B2313845 : Blo 1541468 2313845 := bbase (se 5 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 2313845 = 216923) (by norm_num)
theorem B3468941 : Blo 1541468 3468941 := bbase (se 3 (by rfl) ⟨650426, by rfl⟩ : syracuseStep 3468941 = 1300853) (by norm_num)
theorem B2313869 : Blo 1541468 2313869 := bbase (se 3 (by rfl) ⟨433850, by rfl⟩ : syracuseStep 2313869 = 867701) (by norm_num)
theorem B5205653 : Blo 1541468 5205653 := bbase (se 6 (by rfl) ⟨122007, by rfl⟩ : syracuseStep 5205653 = 244015) (by norm_num)
theorem B3706517 : Blo 1541468 3706517 := bbase (se 6 (by rfl) ⟨86871, by rfl⟩ : syracuseStep 3706517 = 173743) (by norm_num)
theorem B5852837 : Blo 1541468 5852837 := bbase (se 4 (by rfl) ⟨548703, by rfl⟩ : syracuseStep 5852837 = 1097407) (by norm_num)
theorem B2313893 : Blo 1541468 2313893 := bbase (se 4 (by rfl) ⟨216927, by rfl⟩ : syracuseStep 2313893 = 433855) (by norm_num)
theorem B2313917 : Blo 1541468 2313917 := bbase (se 3 (by rfl) ⟨433859, by rfl⟩ : syracuseStep 2313917 = 867719) (by norm_num)
theorem B2928325 : Blo 1541468 2928325 := bbase (se 4 (by rfl) ⟨274530, by rfl⟩ : syracuseStep 2928325 = 549061) (by norm_num)
theorem B3469013 : Blo 1541468 3469013 := bbase (se 7 (by rfl) ⟨40652, by rfl⟩ : syracuseStep 3469013 = 81305) (by norm_num)
theorem B8335061 : Blo 1541468 8335061 := bbase (se 7 (by rfl) ⟨97676, by rfl⟩ : syracuseStep 8335061 = 195353) (by norm_num)
theorem B2313941 : Blo 1541468 2313941 := bbase (se 7 (by rfl) ⟨27116, by rfl⟩ : syracuseStep 2313941 = 54233) (by norm_num)
theorem B2313965 : Blo 1541468 2313965 := bbase (se 3 (by rfl) ⟨433868, by rfl⟩ : syracuseStep 2313965 = 867737) (by norm_num)
theorem B2313989 : Blo 1541468 2313989 := bbase (se 4 (by rfl) ⟨216936, by rfl⟩ : syracuseStep 2313989 = 433873) (by norm_num)
theorem B3469085 : Blo 1541468 3469085 := bbase (se 3 (by rfl) ⟨650453, by rfl⟩ : syracuseStep 3469085 = 1300907) (by norm_num)
theorem B2314013 : Blo 1541468 2314013 := bbase (se 3 (by rfl) ⟨433877, by rfl⟩ : syracuseStep 2314013 = 867755) (by norm_num)
theorem B2314037 : Blo 1541468 2314037 := bbase (se 5 (by rfl) ⟨108470, by rfl⟩ : syracuseStep 2314037 = 216941) (by norm_num)
theorem B2314061 : Blo 1541468 2314061 := bbase (se 3 (by rfl) ⟨433886, by rfl⟩ : syracuseStep 2314061 = 867773) (by norm_num)
theorem B2928469 : Blo 1541468 2928469 := bbase (se 9 (by rfl) ⟨8579, by rfl⟩ : syracuseStep 2928469 = 17159) (by norm_num)
theorem B3469157 : Blo 1541468 3469157 := bbase (se 4 (by rfl) ⟨325233, by rfl⟩ : syracuseStep 3469157 = 650467) (by norm_num)
theorem B2314085 : Blo 1541468 2314085 := bbase (se 4 (by rfl) ⟨216945, by rfl⟩ : syracuseStep 2314085 = 433891) (by norm_num)
theorem B3903349 : Blo 1541468 3903349 := bbase (se 5 (by rfl) ⟨182969, by rfl⟩ : syracuseStep 3903349 = 365939) (by norm_num)
theorem B2314109 : Blo 1541468 2314109 := bbase (se 3 (by rfl) ⟨433895, by rfl⟩ : syracuseStep 2314109 = 867791) (by norm_num)
theorem B2469781 : Blo 1541468 2469781 := bbase (se 6 (by rfl) ⟨57885, by rfl⟩ : syracuseStep 2469781 = 115771) (by norm_num)
theorem B2314133 : Blo 1541468 2314133 := bbase (se 6 (by rfl) ⟨54237, by rfl⟩ : syracuseStep 2314133 = 108475) (by norm_num)
theorem B3469229 : Blo 1541468 3469229 := bbase (se 3 (by rfl) ⟨650480, by rfl⟩ : syracuseStep 3469229 = 1300961) (by norm_num)
theorem B2314157 : Blo 1541468 2314157 := bbase (se 3 (by rfl) ⟨433904, by rfl⟩ : syracuseStep 2314157 = 867809) (by norm_num)
theorem B2314181 : Blo 1541468 2314181 := bbase (se 4 (by rfl) ⟨216954, by rfl⟩ : syracuseStep 2314181 = 433909) (by norm_num)
theorem B2314205 : Blo 1541468 2314205 := bbase (se 3 (by rfl) ⟨433913, by rfl⟩ : syracuseStep 2314205 = 867827) (by norm_num)
theorem B3903461 : Blo 1541468 3903461 := bbase (se 4 (by rfl) ⟨365949, by rfl⟩ : syracuseStep 3903461 = 731899) (by norm_num)
theorem B3469301 : Blo 1541468 3469301 := bbase (se 5 (by rfl) ⟨162623, by rfl⟩ : syracuseStep 3469301 = 325247) (by norm_num)
theorem B2928629 : Blo 1541468 2928629 := bbase (se 5 (by rfl) ⟨137279, by rfl⟩ : syracuseStep 2928629 = 274559) (by norm_num)
theorem B2314229 : Blo 1541468 2314229 := bbase (se 5 (by rfl) ⟨108479, by rfl⟩ : syracuseStep 2314229 = 216959) (by norm_num)
theorem B2314253 : Blo 1541468 2314253 := bbase (se 3 (by rfl) ⟨433922, by rfl⟩ : syracuseStep 2314253 = 867845) (by norm_num)
theorem B2314277 : Blo 1541468 2314277 := bbase (se 4 (by rfl) ⟨216963, by rfl⟩ : syracuseStep 2314277 = 433927) (by norm_num)
theorem B5279797 : Blo 1541468 5279797 := bbase (se 5 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 5279797 = 494981) (by norm_num)
theorem B3469373 : Blo 1541468 3469373 := bbase (se 3 (by rfl) ⟨650507, by rfl⟩ : syracuseStep 3469373 = 1301015) (by norm_num)
theorem B2314301 : Blo 1541468 2314301 := bbase (se 3 (by rfl) ⟨433931, by rfl⟩ : syracuseStep 2314301 = 867863) (by norm_num)
theorem B5206085 : Blo 1541468 5206085 := bbase (se 4 (by rfl) ⟨488070, by rfl⟩ : syracuseStep 5206085 = 976141) (by norm_num)
theorem B13176917 : Blo 1541468 13176917 := bbase (se 8 (by rfl) ⟨77208, by rfl⟩ : syracuseStep 13176917 = 154417) (by norm_num)
theorem B2314325 : Blo 1541468 2314325 := bbase (se 8 (by rfl) ⟨13560, by rfl⟩ : syracuseStep 2314325 = 27121) (by norm_num)
theorem B3756133 : Blo 1541468 3756133 := bbase (se 4 (by rfl) ⟨352137, by rfl⟩ : syracuseStep 3756133 = 704275) (by norm_num)
theorem B2314349 : Blo 1541468 2314349 := bbase (se 3 (by rfl) ⟨433940, by rfl⟩ : syracuseStep 2314349 = 867881) (by norm_num)
theorem B3469445 : Blo 1541468 3469445 := bbase (se 4 (by rfl) ⟨325260, by rfl⟩ : syracuseStep 3469445 = 650521) (by norm_num)
theorem B2928773 : Blo 1541468 2928773 := bbase (se 4 (by rfl) ⟨274572, by rfl⟩ : syracuseStep 2928773 = 549145) (by norm_num)
theorem B2314373 : Blo 1541468 2314373 := bbase (se 4 (by rfl) ⟨216972, by rfl⟩ : syracuseStep 2314373 = 433945) (by norm_num)
theorem B8786069 : Blo 1541468 8786069 := bbase (se 6 (by rfl) ⟨205923, by rfl⟩ : syracuseStep 8786069 = 411847) (by norm_num)
theorem B2314397 : Blo 1541468 2314397 := bbase (se 3 (by rfl) ⟨433949, by rfl⟩ : syracuseStep 2314397 = 867899) (by norm_num)
theorem B3903653 : Blo 1541468 3903653 := bbase (se 4 (by rfl) ⟨365967, by rfl⟩ : syracuseStep 3903653 = 731935) (by norm_num)
theorem B15225013 : Blo 1541468 15225013 := bbase (se 5 (by rfl) ⟨713672, by rfl⟩ : syracuseStep 15225013 = 1427345) (by norm_num)
theorem B2314421 : Blo 1541468 2314421 := bbase (se 5 (by rfl) ⟨108488, by rfl⟩ : syracuseStep 2314421 = 216977) (by norm_num)
theorem B3469517 : Blo 1541468 3469517 := bbase (se 3 (by rfl) ⟨650534, by rfl⟩ : syracuseStep 3469517 = 1301069) (by norm_num)
theorem B2314445 : Blo 1541468 2314445 := bbase (se 3 (by rfl) ⟨433958, by rfl⟩ : syracuseStep 2314445 = 867917) (by norm_num)
theorem B2314469 : Blo 1541468 2314469 := bbase (se 4 (by rfl) ⟨216981, by rfl⟩ : syracuseStep 2314469 = 433963) (by norm_num)
theorem B2314493 : Blo 1541468 2314493 := bbase (se 3 (by rfl) ⟨433967, by rfl⟩ : syracuseStep 2314493 = 867935) (by norm_num)
theorem B3469589 : Blo 1541468 3469589 := bbase (se 6 (by rfl) ⟨81318, by rfl⟩ : syracuseStep 3469589 = 162637) (by norm_num)
theorem B2314517 : Blo 1541468 2314517 := bbase (se 6 (by rfl) ⟨54246, by rfl⟩ : syracuseStep 2314517 = 108493) (by norm_num)
theorem B2085149 : Blo 1541468 2085149 := bbase (se 3 (by rfl) ⟨390965, by rfl⟩ : syracuseStep 2085149 = 781931) (by norm_num)
theorem B2314541 : Blo 1541468 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B2314565 : Blo 1541468 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B2085197 : Blo 1541468 2085197 := bbase (se 3 (by rfl) ⟨390974, by rfl⟩ : syracuseStep 2085197 = 781949) (by norm_num)
theorem B2601301 : Blo 1541468 2601301 := bbase (se 10 (by rfl) ⟨3810, by rfl⟩ : syracuseStep 2601301 = 7621) (by norm_num)
theorem B3469661 : Blo 1541468 3469661 := bbase (se 3 (by rfl) ⟨650561, by rfl⟩ : syracuseStep 3469661 = 1301123) (by norm_num)
theorem B2314589 : Blo 1541468 2314589 := bbase (se 3 (by rfl) ⟨433985, by rfl⟩ : syracuseStep 2314589 = 867971) (by norm_num)
theorem B2314613 : Blo 1541468 2314613 := bbase (se 5 (by rfl) ⟨108497, by rfl⟩ : syracuseStep 2314613 = 216995) (by norm_num)
theorem B2314637 : Blo 1541468 2314637 := bbase (se 3 (by rfl) ⟨433994, by rfl⟩ : syracuseStep 2314637 = 867989) (by norm_num)
theorem B7811477 : Blo 1541468 7811477 := bbase (se 6 (by rfl) ⟨183081, by rfl⟩ : syracuseStep 7811477 = 366163) (by norm_num)
theorem B3469733 : Blo 1541468 3469733 := bbase (se 4 (by rfl) ⟨325287, by rfl⟩ : syracuseStep 3469733 = 650575) (by norm_num)
theorem B2929061 : Blo 1541468 2929061 := bbase (se 4 (by rfl) ⟨274599, by rfl⟩ : syracuseStep 2929061 = 549199) (by norm_num)
theorem B2314661 : Blo 1541468 2314661 := bbase (se 4 (by rfl) ⟨216999, by rfl⟩ : syracuseStep 2314661 = 433999) (by norm_num)
theorem B2601389 : Blo 1541468 2601389 := bbase (se 3 (by rfl) ⟨487760, by rfl⟩ : syracuseStep 2601389 = 975521) (by norm_num)
theorem B2470333 : Blo 1541468 2470333 := bbase (se 3 (by rfl) ⟨463187, by rfl⟩ : syracuseStep 2470333 = 926375) (by norm_num)
theorem B2314685 : Blo 1541468 2314685 := bbase (se 3 (by rfl) ⟨434003, by rfl⟩ : syracuseStep 2314685 = 868007) (by norm_num)
theorem B2314709 : Blo 1541468 2314709 := bbase (se 7 (by rfl) ⟨27125, by rfl⟩ : syracuseStep 2314709 = 54251) (by norm_num)
theorem B3469805 : Blo 1541468 3469805 := bbase (se 3 (by rfl) ⟨650588, by rfl⟩ : syracuseStep 3469805 = 1301177) (by norm_num)
theorem B2314733 : Blo 1541468 2314733 := bbase (se 3 (by rfl) ⟨434012, by rfl⟩ : syracuseStep 2314733 = 868025) (by norm_num)
theorem B5206517 : Blo 1541468 5206517 := bbase (se 5 (by rfl) ⟨244055, by rfl⟩ : syracuseStep 5206517 = 488111) (by norm_num)
theorem B3903997 : Blo 1541468 3903997 := bbase (se 3 (by rfl) ⟨731999, by rfl⟩ : syracuseStep 3903997 = 1463999) (by norm_num)
theorem B3518981 : Blo 1541468 3518981 := bbase (se 4 (by rfl) ⟨329904, by rfl⟩ : syracuseStep 3518981 = 659809) (by norm_num)
theorem B2314757 : Blo 1541468 2314757 := bbase (se 4 (by rfl) ⟨217008, by rfl⟩ : syracuseStep 2314757 = 434017) (by norm_num)
theorem B2314781 : Blo 1541468 2314781 := bbase (se 3 (by rfl) ⟨434021, by rfl⟩ : syracuseStep 2314781 = 868043) (by norm_num)
theorem B2601517 : Blo 1541468 2601517 := bbase (se 3 (by rfl) ⟨487784, by rfl⟩ : syracuseStep 2601517 = 975569) (by norm_num)
theorem B3469877 : Blo 1541468 3469877 := bbase (se 5 (by rfl) ⟨162650, by rfl⟩ : syracuseStep 3469877 = 325301) (by norm_num)
theorem B2314805 : Blo 1541468 2314805 := bbase (se 5 (by rfl) ⟨108506, by rfl⟩ : syracuseStep 2314805 = 217013) (by norm_num)
theorem B2929213 : Blo 1541468 2929213 := bbase (se 3 (by rfl) ⟨549227, by rfl⟩ : syracuseStep 2929213 = 1098455) (by norm_num)
theorem B2314829 : Blo 1541468 2314829 := bbase (se 3 (by rfl) ⟨434030, by rfl⟩ : syracuseStep 2314829 = 868061) (by norm_num)
theorem B2314853 : Blo 1541468 2314853 := bbase (se 4 (by rfl) ⟨217017, by rfl⟩ : syracuseStep 2314853 = 434035) (by norm_num)
theorem B3904109 : Blo 1541468 3904109 := bbase (se 3 (by rfl) ⟨732020, by rfl⟩ : syracuseStep 3904109 = 1464041) (by norm_num)
theorem B3469949 : Blo 1541468 3469949 := bbase (se 3 (by rfl) ⟨650615, by rfl⟩ : syracuseStep 3469949 = 1301231) (by norm_num)
theorem B2314877 : Blo 1541468 2314877 := bbase (se 3 (by rfl) ⟨434039, by rfl⟩ : syracuseStep 2314877 = 868079) (by norm_num)
theorem B2601605 : Blo 1541468 2601605 := bbase (se 4 (by rfl) ⟨243900, by rfl⟩ : syracuseStep 2601605 = 487801) (by norm_num)
theorem B2314901 : Blo 1541468 2314901 := bbase (se 6 (by rfl) ⟨54255, by rfl⟩ : syracuseStep 2314901 = 108511) (by norm_num)
theorem B7508645 : Blo 1541468 7508645 := bbase (se 4 (by rfl) ⟨703935, by rfl⟩ : syracuseStep 7508645 = 1407871) (by norm_num)
theorem B6255269 : Blo 1541468 6255269 := bbase (se 4 (by rfl) ⟨586431, by rfl⟩ : syracuseStep 6255269 = 1172863) (by norm_num)
theorem B2314925 : Blo 1541468 2314925 := bbase (se 3 (by rfl) ⟨434048, by rfl⟩ : syracuseStep 2314925 = 868097) (by norm_num)
theorem B2470589 : Blo 1541468 2470589 := bbase (se 3 (by rfl) ⟨463235, by rfl⟩ : syracuseStep 2470589 = 926471) (by norm_num)
theorem B3470021 : Blo 1541468 3470021 := bbase (se 4 (by rfl) ⟨325314, by rfl⟩ : syracuseStep 3470021 = 650629) (by norm_num)
theorem B2314949 : Blo 1541468 2314949 := bbase (se 4 (by rfl) ⟨217026, by rfl⟩ : syracuseStep 2314949 = 434053) (by norm_num)
theorem B2314973 : Blo 1541468 2314973 := bbase (se 3 (by rfl) ⟨434057, by rfl⟩ : syracuseStep 2314973 = 868115) (by norm_num)
theorem B2314997 : Blo 1541468 2314997 := bbase (se 5 (by rfl) ⟨108515, by rfl⟩ : syracuseStep 2314997 = 217031) (by norm_num)
theorem B2601733 : Blo 1541468 2601733 := bbase (se 4 (by rfl) ⟨243912, by rfl⟩ : syracuseStep 2601733 = 487825) (by norm_num)
theorem B3470093 : Blo 1541468 3470093 := bbase (se 3 (by rfl) ⟨650642, by rfl⟩ : syracuseStep 3470093 = 1301285) (by norm_num)
theorem B2315021 : Blo 1541468 2315021 := bbase (se 3 (by rfl) ⟨434066, by rfl⟩ : syracuseStep 2315021 = 868133) (by norm_num)
theorem B1757981 : Blo 1541468 1757981 := bbase (se 3 (by rfl) ⟨329621, by rfl⟩ : syracuseStep 1757981 = 659243) (by norm_num)
theorem B2315045 : Blo 1541468 2315045 := bbase (se 4 (by rfl) ⟨217035, by rfl⟩ : syracuseStep 2315045 = 434071) (by norm_num)
theorem B3904301 : Blo 1541468 3904301 := bbase (se 3 (by rfl) ⟨732056, by rfl⟩ : syracuseStep 3904301 = 1464113) (by norm_num)
theorem B7803701 : Blo 1541468 7803701 := bbase (se 5 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 7803701 = 731597) (by norm_num)
theorem B2315069 : Blo 1541468 2315069 := bbase (se 3 (by rfl) ⟨434075, by rfl⟩ : syracuseStep 2315069 = 868151) (by norm_num)
theorem B3470165 : Blo 1541468 3470165 := bbase (se 9 (by rfl) ⟨10166, by rfl⟩ : syracuseStep 3470165 = 20333) (by norm_num)
theorem B2315093 : Blo 1541468 2315093 := bbase (se 9 (by rfl) ⟨6782, by rfl⟩ : syracuseStep 2315093 = 13565) (by norm_num)
theorem B2601821 : Blo 1541468 2601821 := bbase (se 3 (by rfl) ⟨487841, by rfl⟩ : syracuseStep 2601821 = 975683) (by norm_num)
theorem B3126109 : Blo 1541468 3126109 := bbase (se 3 (by rfl) ⟨586145, by rfl⟩ : syracuseStep 3126109 = 1172291) (by norm_num)
theorem B2929517 : Blo 1541468 2929517 := bbase (se 3 (by rfl) ⟨549284, by rfl⟩ : syracuseStep 2929517 = 1098569) (by norm_num)
theorem B2315117 : Blo 1541468 2315117 := bbase (se 3 (by rfl) ⟨434084, by rfl⟩ : syracuseStep 2315117 = 868169) (by norm_num)
theorem B2315141 : Blo 1541468 2315141 := bbase (se 4 (by rfl) ⟨217044, by rfl⟩ : syracuseStep 2315141 = 434089) (by norm_num)
theorem B1930133 : Blo 1541468 1930133 := bbase (se 6 (by rfl) ⟨45237, by rfl⟩ : syracuseStep 1930133 = 90475) (by norm_num)
theorem B3470237 : Blo 1541468 3470237 := bbase (se 3 (by rfl) ⟨650669, by rfl⟩ : syracuseStep 3470237 = 1301339) (by norm_num)
theorem B2315165 : Blo 1541468 2315165 := bbase (se 3 (by rfl) ⟨434093, by rfl⟩ : syracuseStep 2315165 = 868187) (by norm_num)
theorem B5206949 : Blo 1541468 5206949 := bbase (se 4 (by rfl) ⟨488151, by rfl⟩ : syracuseStep 5206949 = 976303) (by norm_num)
theorem B2315189 : Blo 1541468 2315189 := bbase (se 5 (by rfl) ⟨108524, by rfl⟩ : syracuseStep 2315189 = 217049) (by norm_num)
theorem B2601949 : Blo 1541468 2601949 := bbase (se 3 (by rfl) ⟨487865, by rfl⟩ : syracuseStep 2601949 = 975731) (by norm_num)
theorem B3470309 : Blo 1541468 3470309 := bbase (se 4 (by rfl) ⟨325341, by rfl⟩ : syracuseStep 3470309 = 650683) (by norm_num)
theorem B3470381 : Blo 1541468 3470381 := bbase (se 3 (by rfl) ⟨650696, by rfl⟩ : syracuseStep 3470381 = 1301393) (by norm_num)
theorem B2602037 : Blo 1541468 2602037 := bbase (se 5 (by rfl) ⟨121970, by rfl⟩ : syracuseStep 2602037 = 243941) (by norm_num)
theorem B1782853 : Blo 1541468 1782853 := bbase (se 4 (by rfl) ⟨167142, by rfl⟩ : syracuseStep 1782853 = 334285) (by norm_num)
theorem B3470453 : Blo 1541468 3470453 := bbase (se 5 (by rfl) ⟨162677, by rfl⟩ : syracuseStep 3470453 = 325355) (by norm_num)
theorem B8909941 : Blo 1541468 8909941 := bbase (se 5 (by rfl) ⟨417653, by rfl⟩ : syracuseStep 8909941 = 835307) (by norm_num)
theorem B3904645 : Blo 1541468 3904645 := bbase (se 4 (by rfl) ⟨366060, by rfl⟩ : syracuseStep 3904645 = 732121) (by norm_num)
theorem B2602165 : Blo 1541468 2602165 := bbase (se 5 (by rfl) ⟨121976, by rfl⟩ : syracuseStep 2602165 = 243953) (by norm_num)
theorem B3470525 : Blo 1541468 3470525 := bbase (se 3 (by rfl) ⟨650723, by rfl⟩ : syracuseStep 3470525 = 1301447) (by norm_num)
theorem B1758409 : Blo 1541468 1758409 := bbase (se 2 (by rfl) ⟨659403, by rfl⟩ : syracuseStep 1758409 = 1318807) (by norm_num)
theorem B3904757 : Blo 1541468 3904757 := bbase (se 5 (by rfl) ⟨183035, by rfl⟩ : syracuseStep 3904757 = 366071) (by norm_num)
theorem B3470597 : Blo 1541468 3470597 := bbase (se 4 (by rfl) ⟨325368, by rfl⟩ : syracuseStep 3470597 = 650737) (by norm_num)
theorem B2602253 : Blo 1541468 2602253 := bbase (se 3 (by rfl) ⟨487922, by rfl⟩ : syracuseStep 2602253 = 975845) (by norm_num)
theorem B9385237 : Blo 1541468 9385237 := bbase (se 6 (by rfl) ⟨219966, by rfl⟩ : syracuseStep 9385237 = 439933) (by norm_num)
theorem B3470669 : Blo 1541468 3470669 := bbase (se 3 (by rfl) ⟨650750, by rfl⟩ : syracuseStep 3470669 = 1301501) (by norm_num)
theorem B5207381 : Blo 1541468 5207381 := bbase (se 13 (by rfl) ⟨953, by rfl⟩ : syracuseStep 5207381 = 1907) (by norm_num)
theorem B2471293 : Blo 1541468 2471293 := bbase (se 3 (by rfl) ⟨463367, by rfl⟩ : syracuseStep 2471293 = 926735) (by norm_num)
theorem B2602381 : Blo 1541468 2602381 := bbase (se 3 (by rfl) ⟨487946, by rfl⟩ : syracuseStep 2602381 = 975893) (by norm_num)
theorem B3470741 : Blo 1541468 3470741 := bbase (se 6 (by rfl) ⟨81345, by rfl⟩ : syracuseStep 3470741 = 162691) (by norm_num)
theorem B3904949 : Blo 1541468 3904949 := bbase (se 5 (by rfl) ⟨183044, by rfl⟩ : syracuseStep 3904949 = 366089) (by norm_num)
theorem B5559749 : Blo 1541468 5559749 := bbase (se 4 (by rfl) ⟨521226, by rfl⟩ : syracuseStep 5559749 = 1042453) (by norm_num)
theorem B7919045 : Blo 1541468 7919045 := bbase (se 4 (by rfl) ⟨742410, by rfl⟩ : syracuseStep 7919045 = 1484821) (by norm_num)
theorem B3470813 : Blo 1541468 3470813 := bbase (se 3 (by rfl) ⟨650777, by rfl⟩ : syracuseStep 3470813 = 1301555) (by norm_num)
theorem B2602469 : Blo 1541468 2602469 := bbase (se 4 (by rfl) ⟨243981, by rfl⟩ : syracuseStep 2602469 = 487963) (by norm_num)
theorem B7411189 : Blo 1541468 7411189 := bbase (se 5 (by rfl) ⟨347399, by rfl⟩ : syracuseStep 7411189 = 694799) (by norm_num)
theorem B1734169 : Blo 1541468 1734169 := bbase (se 2 (by rfl) ⟨650313, by rfl⟩ : syracuseStep 1734169 = 1300627) (by norm_num)
theorem B3470885 : Blo 1541468 3470885 := bbase (se 4 (by rfl) ⟨325395, by rfl⟩ : syracuseStep 3470885 = 650791) (by norm_num)
theorem B1734205 : Blo 1541468 1734205 := bbase (se 3 (by rfl) ⟨325163, by rfl⟩ : syracuseStep 1734205 = 650327) (by norm_num)
theorem B1734241 : Blo 1541468 1734241 := bbase (se 2 (by rfl) ⟨650340, by rfl⟩ : syracuseStep 1734241 = 1300681) (by norm_num)
theorem B2602597 : Blo 1541468 2602597 := bbase (se 4 (by rfl) ⟨243993, by rfl⟩ : syracuseStep 2602597 = 487987) (by norm_num)
theorem B3470957 : Blo 1541468 3470957 := bbase (se 3 (by rfl) ⟨650804, by rfl⟩ : syracuseStep 3470957 = 1301609) (by norm_num)
theorem B1734277 : Blo 1541468 1734277 := bbase (se 4 (by rfl) ⟨162588, by rfl⟩ : syracuseStep 1734277 = 325177) (by norm_num)
theorem B7812773 : Blo 1541468 7812773 := bbase (se 4 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 7812773 = 1464895) (by norm_num)
theorem B1734313 : Blo 1541468 1734313 := bbase (se 2 (by rfl) ⟨650367, by rfl⟩ : syracuseStep 1734313 = 1300735) (by norm_num)
theorem B3471029 : Blo 1541468 3471029 := bbase (se 5 (by rfl) ⟨162704, by rfl⟩ : syracuseStep 3471029 = 325409) (by norm_num)
theorem B2602685 : Blo 1541468 2602685 := bbase (se 3 (by rfl) ⟨488003, by rfl⟩ : syracuseStep 2602685 = 976007) (by norm_num)
theorem B1734349 : Blo 1541468 1734349 := bbase (se 3 (by rfl) ⟨325190, by rfl⟩ : syracuseStep 1734349 = 650381) (by norm_num)
theorem B5854949 : Blo 1541468 5854949 := bbase (se 4 (by rfl) ⟨548901, by rfl⟩ : syracuseStep 5854949 = 1097803) (by norm_num)
theorem B1734385 : Blo 1541468 1734385 := bbase (se 2 (by rfl) ⟨650394, by rfl⟩ : syracuseStep 1734385 = 1300789) (by norm_num)
theorem B3471101 : Blo 1541468 3471101 := bbase (se 3 (by rfl) ⟨650831, by rfl⟩ : syracuseStep 3471101 = 1301663) (by norm_num)
theorem B5207813 : Blo 1541468 5207813 := bbase (se 4 (by rfl) ⟨488232, by rfl⟩ : syracuseStep 5207813 = 976465) (by norm_num)
theorem B3905293 : Blo 1541468 3905293 := bbase (se 3 (by rfl) ⟨732242, by rfl⟩ : syracuseStep 3905293 = 1464485) (by norm_num)
theorem B1734421 : Blo 1541468 1734421 := bbase (se 6 (by rfl) ⟨40650, by rfl⟩ : syracuseStep 1734421 = 81301) (by norm_num)
theorem B2471717 : Blo 1541468 2471717 := bbase (se 4 (by rfl) ⟨231723, by rfl⟩ : syracuseStep 2471717 = 463447) (by norm_num)
theorem B1734457 : Blo 1541468 1734457 := bbase (se 2 (by rfl) ⟨650421, by rfl⟩ : syracuseStep 1734457 = 1300843) (by norm_num)
theorem B2602813 : Blo 1541468 2602813 := bbase (se 3 (by rfl) ⟨488027, by rfl⟩ : syracuseStep 2602813 = 976055) (by norm_num)
theorem B3471173 : Blo 1541468 3471173 := bbase (se 4 (by rfl) ⟨325422, by rfl⟩ : syracuseStep 3471173 = 650845) (by norm_num)
theorem B1734493 : Blo 1541468 1734493 := bbase (se 3 (by rfl) ⟨325217, by rfl⟩ : syracuseStep 1734493 = 650435) (by norm_num)
theorem B3905405 : Blo 1541468 3905405 := bbase (se 3 (by rfl) ⟨732263, by rfl⟩ : syracuseStep 3905405 = 1464527) (by norm_num)
theorem B1734529 : Blo 1541468 1734529 := bbase (se 2 (by rfl) ⟨650448, by rfl⟩ : syracuseStep 1734529 = 1300897) (by norm_num)
theorem B3471245 : Blo 1541468 3471245 := bbase (se 3 (by rfl) ⟨650858, by rfl⟩ : syracuseStep 3471245 = 1301717) (by norm_num)
theorem B2602901 : Blo 1541468 2602901 := bbase (se 6 (by rfl) ⟨61005, by rfl⟩ : syracuseStep 2602901 = 122011) (by norm_num)
theorem B1734565 : Blo 1541468 1734565 := bbase (se 4 (by rfl) ⟨162615, by rfl⟩ : syracuseStep 1734565 = 325231) (by norm_num)
theorem B3127205 : Blo 1541468 3127205 := bbase (se 4 (by rfl) ⟨293175, by rfl⟩ : syracuseStep 3127205 = 586351) (by norm_num)
theorem B1669033 : Blo 1541468 1669033 := bbase (se 2 (by rfl) ⟨625887, by rfl⟩ : syracuseStep 1669033 = 1251775) (by norm_num)
theorem B1734601 : Blo 1541468 1734601 := bbase (se 2 (by rfl) ⟨650475, by rfl⟩ : syracuseStep 1734601 = 1300951) (by norm_num)
theorem B3471317 : Blo 1541468 3471317 := bbase (se 7 (by rfl) ⟨40679, by rfl⟩ : syracuseStep 3471317 = 81359) (by norm_num)
theorem B6772709 : Blo 1541468 6772709 := bbase (se 4 (by rfl) ⟨634941, by rfl⟩ : syracuseStep 6772709 = 1269883) (by norm_num)
theorem B1734637 : Blo 1541468 1734637 := bbase (se 3 (by rfl) ⟨325244, by rfl⟩ : syracuseStep 1734637 = 650489) (by norm_num)
theorem B3127277 : Blo 1541468 3127277 := bbase (se 3 (by rfl) ⟨586364, by rfl⟩ : syracuseStep 3127277 = 1172729) (by norm_num)
theorem B9885685 : Blo 1541468 9885685 := bbase (se 5 (by rfl) ⟨463391, by rfl⟩ : syracuseStep 9885685 = 926783) (by norm_num)
theorem B5855237 : Blo 1541468 5855237 := bbase (se 4 (by rfl) ⟨548928, by rfl⟩ : syracuseStep 5855237 = 1097857) (by norm_num)
theorem B1734673 : Blo 1541468 1734673 := bbase (se 2 (by rfl) ⟨650502, by rfl⟩ : syracuseStep 1734673 = 1301005) (by norm_num)
theorem B2603029 : Blo 1541468 2603029 := bbase (se 6 (by rfl) ⟨61008, by rfl⟩ : syracuseStep 2603029 = 122017) (by norm_num)
theorem B3471389 : Blo 1541468 3471389 := bbase (se 3 (by rfl) ⟨650885, by rfl⟩ : syracuseStep 3471389 = 1301771) (by norm_num)
theorem B6674485 : Blo 1541468 6674485 := bbase (se 5 (by rfl) ⟨312866, by rfl⟩ : syracuseStep 6674485 = 625733) (by norm_num)
theorem B1734709 : Blo 1541468 1734709 := bbase (se 5 (by rfl) ⟨81314, by rfl⟩ : syracuseStep 1734709 = 162629) (by norm_num)
theorem B1669177 : Blo 1541468 1669177 := bbase (se 2 (by rfl) ⟨625941, by rfl⟩ : syracuseStep 1669177 = 1251883) (by norm_num)
theorem B3905597 : Blo 1541468 3905597 := bbase (se 3 (by rfl) ⟨732299, by rfl⟩ : syracuseStep 3905597 = 1464599) (by norm_num)
theorem B7804997 : Blo 1541468 7804997 := bbase (se 4 (by rfl) ⟨731718, by rfl⟩ : syracuseStep 7804997 = 1463437) (by norm_num)
theorem B2472005 : Blo 1541468 2472005 := bbase (se 4 (by rfl) ⟨231750, by rfl⟩ : syracuseStep 2472005 = 463501) (by norm_num)
theorem B1734745 : Blo 1541468 1734745 := bbase (se 2 (by rfl) ⟨650529, by rfl⟩ : syracuseStep 1734745 = 1301059) (by norm_num)
theorem B3471461 : Blo 1541468 3471461 := bbase (se 4 (by rfl) ⟨325449, by rfl⟩ : syracuseStep 3471461 = 650899) (by norm_num)
theorem B2603117 : Blo 1541468 2603117 := bbase (se 3 (by rfl) ⟨488084, by rfl⟩ : syracuseStep 2603117 = 976169) (by norm_num)
theorem B1734781 : Blo 1541468 1734781 := bbase (se 3 (by rfl) ⟨325271, by rfl⟩ : syracuseStep 1734781 = 650543) (by norm_num)
theorem B1734817 : Blo 1541468 1734817 := bbase (se 2 (by rfl) ⟨650556, by rfl⟩ : syracuseStep 1734817 = 1301113) (by norm_num)
theorem B3471533 : Blo 1541468 3471533 := bbase (se 3 (by rfl) ⟨650912, by rfl⟩ : syracuseStep 3471533 = 1301825) (by norm_num)
theorem B5208245 : Blo 1541468 5208245 := bbase (se 5 (by rfl) ⟨244136, by rfl⟩ : syracuseStep 5208245 = 488273) (by norm_num)
theorem B1734853 : Blo 1541468 1734853 := bbase (se 4 (by rfl) ⟨162642, by rfl⟩ : syracuseStep 1734853 = 325285) (by norm_num)
theorem B1734889 : Blo 1541468 1734889 := bbase (se 2 (by rfl) ⟨650583, by rfl⟩ : syracuseStep 1734889 = 1301167) (by norm_num)
theorem B2603245 : Blo 1541468 2603245 := bbase (se 3 (by rfl) ⟨488108, by rfl⟩ : syracuseStep 2603245 = 976217) (by norm_num)
theorem B3471605 : Blo 1541468 3471605 := bbase (se 5 (by rfl) ⟨162731, by rfl⟩ : syracuseStep 3471605 = 325463) (by norm_num)
theorem B1734925 : Blo 1541468 1734925 := bbase (se 3 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 1734925 = 650597) (by norm_num)
theorem B16668949 : Blo 1541468 16668949 := bbase (se 6 (by rfl) ⟨390678, by rfl⟩ : syracuseStep 16668949 = 781357) (by norm_num)
theorem B2472229 : Blo 1541468 2472229 := bbase (se 4 (by rfl) ⟨231771, by rfl⟩ : syracuseStep 2472229 = 463543) (by norm_num)
theorem B1734961 : Blo 1541468 1734961 := bbase (se 2 (by rfl) ⟨650610, by rfl⟩ : syracuseStep 1734961 = 1301221) (by norm_num)
theorem B4692277 : Blo 1541468 4692277 := bbase (se 5 (by rfl) ⟨219950, by rfl⟩ : syracuseStep 4692277 = 439901) (by norm_num)
theorem B8788277 : Blo 1541468 8788277 := bbase (se 5 (by rfl) ⟨411950, by rfl⟩ : syracuseStep 8788277 = 823901) (by norm_num)
theorem B3471677 : Blo 1541468 3471677 := bbase (se 3 (by rfl) ⟨650939, by rfl⟩ : syracuseStep 3471677 = 1301879) (by norm_num)
theorem B2603333 : Blo 1541468 2603333 := bbase (se 4 (by rfl) ⟨244062, by rfl⟩ : syracuseStep 2603333 = 488125) (by norm_num)
theorem B1734997 : Blo 1541468 1734997 := bbase (se 10 (by rfl) ⟨2541, by rfl⟩ : syracuseStep 1734997 = 5083) (by norm_num)
theorem B1759577 : Blo 1541468 1759577 := bbase (se 2 (by rfl) ⟨659841, by rfl⟩ : syracuseStep 1759577 = 1319683) (by norm_num)
theorem B1735033 : Blo 1541468 1735033 := bbase (se 2 (by rfl) ⟨650637, by rfl⟩ : syracuseStep 1735033 = 1301275) (by norm_num)
theorem B3471749 : Blo 1541468 3471749 := bbase (se 4 (by rfl) ⟨325476, by rfl⟩ : syracuseStep 3471749 = 650953) (by norm_num)
theorem B3905941 : Blo 1541468 3905941 := bbase (se 6 (by rfl) ⟨91545, by rfl⟩ : syracuseStep 3905941 = 183091) (by norm_num)
theorem B1735069 : Blo 1541468 1735069 := bbase (se 3 (by rfl) ⟨325325, by rfl⟩ : syracuseStep 1735069 = 650651) (by norm_num)
theorem B1735105 : Blo 1541468 1735105 := bbase (se 2 (by rfl) ⟨650664, by rfl⟩ : syracuseStep 1735105 = 1301329) (by norm_num)
theorem B2603461 : Blo 1541468 2603461 := bbase (se 4 (by rfl) ⟨244074, by rfl⟩ : syracuseStep 2603461 = 488149) (by norm_num)
theorem B3471821 : Blo 1541468 3471821 := bbase (se 3 (by rfl) ⟨650966, by rfl⟩ : syracuseStep 3471821 = 1301933) (by norm_num)
theorem B1735141 : Blo 1541468 1735141 := bbase (se 4 (by rfl) ⟨162669, by rfl⟩ : syracuseStep 1735141 = 325339) (by norm_num)
theorem B3906053 : Blo 1541468 3906053 := bbase (se 4 (by rfl) ⟨366192, by rfl⟩ : syracuseStep 3906053 = 732385) (by norm_num)
theorem B1735177 : Blo 1541468 1735177 := bbase (se 2 (by rfl) ⟨650691, by rfl⟩ : syracuseStep 1735177 = 1301383) (by norm_num)
theorem B3471893 : Blo 1541468 3471893 := bbase (se 6 (by rfl) ⟨81372, by rfl⟩ : syracuseStep 3471893 = 162745) (by norm_num)
theorem B2603549 : Blo 1541468 2603549 := bbase (se 3 (by rfl) ⟨488165, by rfl⟩ : syracuseStep 2603549 = 976331) (by norm_num)
theorem B1563181 : Blo 1541468 1563181 := bbase (se 3 (by rfl) ⟨293096, by rfl⟩ : syracuseStep 1563181 = 586193) (by norm_num)
theorem B1735213 : Blo 1541468 1735213 := bbase (se 3 (by rfl) ⟨325352, by rfl⟩ : syracuseStep 1735213 = 650705) (by norm_num)
theorem B1735249 : Blo 1541468 1735249 := bbase (se 2 (by rfl) ⟨650718, by rfl⟩ : syracuseStep 1735249 = 1301437) (by norm_num)
theorem B2226781 : Blo 1541468 2226781 := bbase (se 3 (by rfl) ⟨417521, by rfl⟩ : syracuseStep 2226781 = 835043) (by norm_num)
theorem B3471965 : Blo 1541468 3471965 := bbase (se 3 (by rfl) ⟨650993, by rfl⟩ : syracuseStep 3471965 = 1301987) (by norm_num)
theorem B5208677 : Blo 1541468 5208677 := bbase (se 4 (by rfl) ⟨488313, by rfl⟩ : syracuseStep 5208677 = 976627) (by norm_num)
theorem B1735285 : Blo 1541468 1735285 := bbase (se 5 (by rfl) ⟨81341, by rfl⟩ : syracuseStep 1735285 = 162683) (by norm_num)
theorem B1735321 : Blo 1541468 1735321 := bbase (se 2 (by rfl) ⟨650745, by rfl⟩ : syracuseStep 1735321 = 1301491) (by norm_num)
theorem B2603677 : Blo 1541468 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B3472037 : Blo 1541468 3472037 := bbase (se 4 (by rfl) ⟨325503, by rfl⟩ : syracuseStep 3472037 = 651007) (by norm_num)
theorem B1735357 : Blo 1541468 1735357 := bbase (se 3 (by rfl) ⟨325379, by rfl⟩ : syracuseStep 1735357 = 650759) (by norm_num)
theorem B3906245 : Blo 1541468 3906245 := bbase (se 4 (by rfl) ⟨366210, by rfl⟩ : syracuseStep 3906245 = 732421) (by norm_num)
theorem B1735393 : Blo 1541468 1735393 := bbase (se 2 (by rfl) ⟨650772, by rfl⟩ : syracuseStep 1735393 = 1301545) (by norm_num)
theorem B3472109 : Blo 1541468 3472109 := bbase (se 3 (by rfl) ⟨651020, by rfl⟩ : syracuseStep 3472109 = 1302041) (by norm_num)
theorem B2603765 : Blo 1541468 2603765 := bbase (se 5 (by rfl) ⟨122051, by rfl⟩ : syracuseStep 2603765 = 244103) (by norm_num)
theorem B1735429 : Blo 1541468 1735429 := bbase (se 4 (by rfl) ⟨162696, by rfl⟩ : syracuseStep 1735429 = 325393) (by norm_num)
theorem B1735465 : Blo 1541468 1735465 := bbase (se 2 (by rfl) ⟨650799, by rfl⟩ : syracuseStep 1735465 = 1301599) (by norm_num)
theorem B3472181 : Blo 1541468 3472181 := bbase (se 5 (by rfl) ⟨162758, by rfl⟩ : syracuseStep 3472181 = 325517) (by norm_num)
theorem B1735501 : Blo 1541468 1735501 := bbase (se 3 (by rfl) ⟨325406, by rfl⟩ : syracuseStep 1735501 = 650813) (by norm_num)
theorem B31652693 : Blo 1541468 31652693 := bbase (se 9 (by rfl) ⟨92732, by rfl⟩ : syracuseStep 31652693 = 185465) (by norm_num)
theorem B1735537 : Blo 1541468 1735537 := bbase (se 2 (by rfl) ⟨650826, by rfl⟩ : syracuseStep 1735537 = 1301653) (by norm_num)
theorem B1563509 : Blo 1541468 1563509 := bbase (se 5 (by rfl) ⟨73289, by rfl⟩ : syracuseStep 1563509 = 146579) (by norm_num)
theorem B2603893 : Blo 1541468 2603893 := bbase (se 5 (by rfl) ⟨122057, by rfl⟩ : syracuseStep 2603893 = 244115) (by norm_num)
theorem B3472253 : Blo 1541468 3472253 := bbase (se 3 (by rfl) ⟨651047, by rfl⟩ : syracuseStep 3472253 = 1302095) (by norm_num)
theorem B1735573 : Blo 1541468 1735573 := bbase (se 6 (by rfl) ⟨40677, by rfl⟩ : syracuseStep 1735573 = 81355) (by norm_num)
theorem B2505629 : Blo 1541468 2505629 := bbase (se 3 (by rfl) ⟨469805, by rfl⟩ : syracuseStep 2505629 = 939611) (by norm_num)
theorem B6257573 : Blo 1541468 6257573 := bbase (se 4 (by rfl) ⟨586647, by rfl⟩ : syracuseStep 6257573 = 1173295) (by norm_num)
theorem B1735609 : Blo 1541468 1735609 := bbase (se 2 (by rfl) ⟨650853, by rfl⟩ : syracuseStep 1735609 = 1301707) (by norm_num)
theorem B3472325 : Blo 1541468 3472325 := bbase (se 4 (by rfl) ⟨325530, by rfl⟩ : syracuseStep 3472325 = 651061) (by norm_num)
theorem B2603981 : Blo 1541468 2603981 := bbase (se 3 (by rfl) ⟨488246, by rfl⟩ : syracuseStep 2603981 = 976493) (by norm_num)
theorem B1735645 : Blo 1541468 1735645 := bbase (se 3 (by rfl) ⟨325433, by rfl⟩ : syracuseStep 1735645 = 650867) (by norm_num)
theorem B1735681 : Blo 1541468 1735681 := bbase (se 2 (by rfl) ⟨650880, by rfl⟩ : syracuseStep 1735681 = 1301761) (by norm_num)
theorem B3472397 : Blo 1541468 3472397 := bbase (se 3 (by rfl) ⟨651074, by rfl⟩ : syracuseStep 3472397 = 1302149) (by norm_num)
theorem B5209109 : Blo 1541468 5209109 := bbase (se 6 (by rfl) ⟨122088, by rfl⟩ : syracuseStep 5209109 = 244177) (by norm_num)
theorem B3906589 : Blo 1541468 3906589 := bbase (se 3 (by rfl) ⟨732485, by rfl⟩ : syracuseStep 3906589 = 1464971) (by norm_num)
theorem B4168741 : Blo 1541468 4168741 := bbase (se 4 (by rfl) ⟨390819, by rfl⟩ : syracuseStep 4168741 = 781639) (by norm_num)
theorem B1735717 : Blo 1541468 1735717 := bbase (se 4 (by rfl) ⟨162723, by rfl⟩ : syracuseStep 1735717 = 325447) (by norm_num)
theorem B1735753 : Blo 1541468 1735753 := bbase (se 2 (by rfl) ⟨650907, by rfl⟩ : syracuseStep 1735753 = 1301815) (by norm_num)
theorem B2604109 : Blo 1541468 2604109 := bbase (se 3 (by rfl) ⟨488270, by rfl⟩ : syracuseStep 2604109 = 976541) (by norm_num)
theorem B3472469 : Blo 1541468 3472469 := bbase (se 8 (by rfl) ⟨20346, by rfl⟩ : syracuseStep 3472469 = 40693) (by norm_num)
theorem B1735789 : Blo 1541468 1735789 := bbase (se 3 (by rfl) ⟨325460, by rfl⟩ : syracuseStep 1735789 = 650921) (by norm_num)
theorem B4168837 : Blo 1541468 4168837 := bbase (se 4 (by rfl) ⟨390828, by rfl⟩ : syracuseStep 4168837 = 781657) (by norm_num)
theorem B3906701 : Blo 1541468 3906701 := bbase (se 3 (by rfl) ⟨732506, by rfl⟩ : syracuseStep 3906701 = 1465013) (by norm_num)
theorem B1735825 : Blo 1541468 1735825 := bbase (se 2 (by rfl) ⟨650934, by rfl⟩ : syracuseStep 1735825 = 1301869) (by norm_num)
theorem B3472541 : Blo 1541468 3472541 := bbase (se 3 (by rfl) ⟨651101, by rfl⟩ : syracuseStep 3472541 = 1302203) (by norm_num)
theorem B5856421 : Blo 1541468 5856421 := bbase (se 4 (by rfl) ⟨549039, by rfl⟩ : syracuseStep 5856421 = 1098079) (by norm_num)
theorem B2604197 : Blo 1541468 2604197 := bbase (se 4 (by rfl) ⟨244143, by rfl⟩ : syracuseStep 2604197 = 488287) (by norm_num)
theorem B1735861 : Blo 1541468 1735861 := bbase (se 5 (by rfl) ⟨81368, by rfl⟩ : syracuseStep 1735861 = 162737) (by norm_num)
theorem B1563833 : Blo 1541468 1563833 := bbase (se 2 (by rfl) ⟨586437, by rfl⟩ : syracuseStep 1563833 = 1172875) (by norm_num)
theorem B1735897 : Blo 1541468 1735897 := bbase (se 2 (by rfl) ⟨650961, by rfl⟩ : syracuseStep 1735897 = 1301923) (by norm_num)
theorem B3472613 : Blo 1541468 3472613 := bbase (se 4 (by rfl) ⟨325557, by rfl⟩ : syracuseStep 3472613 = 651115) (by norm_num)
theorem B1735933 : Blo 1541468 1735933 := bbase (se 3 (by rfl) ⟨325487, by rfl⟩ : syracuseStep 1735933 = 650975) (by norm_num)
theorem B1735969 : Blo 1541468 1735969 := bbase (se 2 (by rfl) ⟨650988, by rfl⟩ : syracuseStep 1735969 = 1301977) (by norm_num)
theorem B2604325 : Blo 1541468 2604325 := bbase (se 4 (by rfl) ⟨244155, by rfl⟩ : syracuseStep 2604325 = 488311) (by norm_num)
theorem B3472685 : Blo 1541468 3472685 := bbase (se 3 (by rfl) ⟨651128, by rfl⟩ : syracuseStep 3472685 = 1302257) (by norm_num)
theorem B1736005 : Blo 1541468 1736005 := bbase (se 4 (by rfl) ⟨162750, by rfl⟩ : syracuseStep 1736005 = 325501) (by norm_num)
theorem B3906893 : Blo 1541468 3906893 := bbase (se 3 (by rfl) ⟨732542, by rfl⟩ : syracuseStep 3906893 = 1465085) (by norm_num)
theorem B7806293 : Blo 1541468 7806293 := bbase (se 11 (by rfl) ⟨5717, by rfl⟩ : syracuseStep 7806293 = 11435) (by norm_num)
theorem B1670501 : Blo 1541468 1670501 := bbase (se 4 (by rfl) ⟨156609, by rfl⟩ : syracuseStep 1670501 = 313219) (by norm_num)
theorem B1736041 : Blo 1541468 1736041 := bbase (se 2 (by rfl) ⟨651015, by rfl⟩ : syracuseStep 1736041 = 1302031) (by norm_num)
theorem B3472757 : Blo 1541468 3472757 := bbase (se 5 (by rfl) ⟨162785, by rfl⟩ : syracuseStep 3472757 = 325571) (by norm_num)
theorem B2604413 : Blo 1541468 2604413 := bbase (se 3 (by rfl) ⟨488327, by rfl⟩ : syracuseStep 2604413 = 976655) (by norm_num)
theorem B1736077 : Blo 1541468 1736077 := bbase (se 3 (by rfl) ⟨325514, by rfl⟩ : syracuseStep 1736077 = 651029) (by norm_num)
theorem B3292589 : Blo 1541468 3292589 := bbase (se 3 (by rfl) ⟨617360, by rfl⟩ : syracuseStep 3292589 = 1234721) (by norm_num)
theorem B1736113 : Blo 1541468 1736113 := bbase (se 2 (by rfl) ⟨651042, by rfl⟩ : syracuseStep 1736113 = 1302085) (by norm_num)
theorem B3292597 : Blo 1541468 3292597 := bbase (se 5 (by rfl) ⟨154340, by rfl⟩ : syracuseStep 3292597 = 308681) (by norm_num)
theorem B2194877 : Blo 1541468 2194877 := bbase (se 3 (by rfl) ⟨411539, by rfl⟩ : syracuseStep 2194877 = 823079) (by norm_num)
theorem B4693445 : Blo 1541468 4693445 := bbase (se 4 (by rfl) ⟨440010, by rfl⟩ : syracuseStep 4693445 = 880021) (by norm_num)
theorem B4390357 : Blo 1541468 4390357 := bbase (se 7 (by rfl) ⟨51449, by rfl⟩ : syracuseStep 4390357 = 102899) (by norm_num)
theorem B5856725 : Blo 1541468 5856725 := bbase (se 7 (by rfl) ⟨68633, by rfl⟩ : syracuseStep 5856725 = 137267) (by norm_num)
theorem B1736149 : Blo 1541468 1736149 := bbase (se 7 (by rfl) ⟨20345, by rfl⟩ : syracuseStep 1736149 = 40691) (by norm_num)
theorem B7232981 : Blo 1541468 7232981 := bbase (se 7 (by rfl) ⟨84761, by rfl⟩ : syracuseStep 7232981 = 169523) (by norm_num)
theorem B1736185 : Blo 1541468 1736185 := bbase (se 2 (by rfl) ⟨651069, by rfl⟩ : syracuseStep 1736185 = 1302139) (by norm_num)
theorem B2604541 : Blo 1541468 2604541 := bbase (se 3 (by rfl) ⟨488351, by rfl⟩ : syracuseStep 2604541 = 976703) (by norm_num)
theorem B6585877 : Blo 1541468 6585877 := bbase (se 6 (by rfl) ⟨154356, by rfl⟩ : syracuseStep 6585877 = 308713) (by norm_num)
theorem B1736221 : Blo 1541468 1736221 := bbase (se 3 (by rfl) ⟨325541, by rfl⟩ : syracuseStep 1736221 = 651083) (by norm_num)
theorem B1736257 : Blo 1541468 1736257 := bbase (se 2 (by rfl) ⟨651096, by rfl⟩ : syracuseStep 1736257 = 1302193) (by norm_num)
theorem B1736293 : Blo 1541468 1736293 := bbase (se 4 (by rfl) ⟨162777, by rfl⟩ : syracuseStep 1736293 = 325555) (by norm_num)
theorem B4390517 : Blo 1541468 4390517 := bbase (se 5 (by rfl) ⟨205805, by rfl⟩ : syracuseStep 4390517 = 411611) (by norm_num)
theorem B3128957 : Blo 1541468 3128957 := bbase (se 3 (by rfl) ⟨586679, by rfl⟩ : syracuseStep 3128957 = 1173359) (by norm_num)
theorem B1736329 : Blo 1541468 1736329 := bbase (se 2 (by rfl) ⟨651123, by rfl⟩ : syracuseStep 1736329 = 1302247) (by norm_num)
theorem B1736365 : Blo 1541468 1736365 := bbase (se 3 (by rfl) ⟨325568, by rfl⟩ : syracuseStep 1736365 = 651137) (by norm_num)
theorem B1736401 : Blo 1541468 1736401 := bbase (se 2 (by rfl) ⟨651150, by rfl⟩ : syracuseStep 1736401 = 1302301) (by norm_num)
theorem B1564381 : Blo 1541468 1564381 := bbase (se 3 (by rfl) ⟨293321, by rfl⟩ : syracuseStep 1564381 = 586643) (by norm_num)
theorem B1564417 : Blo 1541468 1564417 := bbase (se 2 (by rfl) ⟨586656, by rfl⟩ : syracuseStep 1564417 = 1173313) (by norm_num)
theorem B2817845 : Blo 1541468 2817845 := bbase (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) (by norm_num)
theorem B4390757 : Blo 1541468 4390757 := bbase (se 4 (by rfl) ⟨411633, by rfl⟩ : syracuseStep 4390757 = 823267) (by norm_num)
theorem B2195429 : Blo 1541468 2195429 := bbase (se 4 (by rfl) ⟨205821, by rfl⟩ : syracuseStep 2195429 = 411643) (by norm_num)
theorem B4014083 : Blo 1541468 4014083 := bstep (se 1 (by rfl) ⟨3010562, by rfl⟩ : syracuseStep 4014083 = 6021125) B6021125
theorem B5857379 : Blo 1541468 5857379 := bstep (se 1 (by rfl) ⟨4393034, by rfl⟩ : syracuseStep 5857379 = 8786069) B8786069
theorem B5857393 : Blo 1541468 5857393 := bstep (se 2 (by rfl) ⟨2196522, by rfl⟩ : syracuseStep 5857393 = 4393045) B4393045
theorem B3293315 : Blo 1541468 3293315 := bstep (se 1 (by rfl) ⟨2469986, by rfl⟩ : syracuseStep 3293315 = 4939973) B4939973
theorem B20300017 : Blo 1541468 20300017 := bstep (se 2 (by rfl) ⟨7612506, by rfl⟩ : syracuseStep 20300017 = 15225013) B15225013
theorem B2638147 : Blo 1541468 2638147 := bstep (se 1 (by rfl) ⟨1978610, by rfl⟩ : syracuseStep 2638147 = 3957221) B3957221
theorem B2638163 : Blo 1541468 2638163 := bstep (se 1 (by rfl) ⟨1978622, by rfl⟩ : syracuseStep 2638163 = 3957245) B3957245
theorem B22225265 : Blo 1541468 22225265 := bstep (se 2 (by rfl) ⟨8334474, by rfl⟩ : syracuseStep 22225265 = 16668949) B16668949
theorem B5005763 : Blo 1541468 5005763 := bstep (se 1 (by rfl) ⟨3754322, by rfl⟩ : syracuseStep 5005763 = 7508645) B7508645
theorem B4170179 : Blo 1541468 4170179 := bstep (se 1 (by rfl) ⟨3127634, by rfl⟩ : syracuseStep 4170179 = 6255269) B6255269
theorem B1647059 : Blo 1541468 1647059 := bstep (se 1 (by rfl) ⟨1235294, by rfl⟩ : syracuseStep 1647059 = 2470589) B2470589
theorem B4391405 : Blo 1541468 4391405 := bstep (se 3 (by rfl) ⟨823388, by rfl⟩ : syracuseStep 4391405 = 1646777) B1646777
theorem B4170221 : Blo 1541468 4170221 := bstep (se 3 (by rfl) ⟨781916, by rfl⟩ : syracuseStep 4170221 = 1563833) B1563833
theorem B5202467 : Blo 1541468 5202467 := bstep (se 1 (by rfl) ⟨3901850, by rfl⟩ : syracuseStep 5202467 = 7803701) B7803701
theorem B3293777 : Blo 1541468 3293777 := bstep (se 2 (by rfl) ⟨1235166, by rfl⟩ : syracuseStep 3293777 = 2470333) B2470333
theorem B2196067 : Blo 1541468 2196067 := bstep (se 1 (by rfl) ⟨1647050, by rfl⟩ : syracuseStep 2196067 = 3294101) B3294101
theorem B4391587 : Blo 1541468 4391587 := bstep (se 1 (by rfl) ⟨3293690, by rfl⟩ : syracuseStep 4391587 = 6587381) B6587381
theorem B4391633 : Blo 1541468 4391633 := bstep (se 2 (by rfl) ⟨1646862, by rfl⟩ : syracuseStep 4391633 = 3293725) B3293725
theorem B8782627 : Blo 1541468 8782627 := bstep (se 1 (by rfl) ⟨6586970, by rfl⟩ : syracuseStep 8782627 = 13173941) B13173941
theorem B5202737 : Blo 1541468 5202737 := bstep (se 2 (by rfl) ⟨1951026, by rfl⟩ : syracuseStep 5202737 = 3902053) B3902053
theorem B1647811 : Blo 1541468 1647811 := bstep (se 1 (by rfl) ⟨1235858, by rfl⟩ : syracuseStep 1647811 = 2471717) B2471717
theorem B5637325 : Blo 1541468 5637325 := bstep (se 3 (by rfl) ⟨1056998, by rfl⟩ : syracuseStep 5637325 = 2113997) B2113997
theorem B4941101 : Blo 1541468 4941101 := bstep (se 3 (by rfl) ⟨926456, by rfl⟩ : syracuseStep 4941101 = 1852913) B1852913
theorem B8783153 : Blo 1541468 8783153 := bstep (se 2 (by rfl) ⟨3293682, by rfl⟩ : syracuseStep 8783153 = 6587365) B6587365
theorem B4515139 : Blo 1541468 4515139 := bstep (se 1 (by rfl) ⟨3386354, by rfl⟩ : syracuseStep 4515139 = 6772709) B6772709
theorem B5203277 : Blo 1541468 5203277 := bstep (se 3 (by rfl) ⟨975614, by rfl⟩ : syracuseStep 5203277 = 1951229) B1951229
theorem B1541475 : Blo 1541468 1541475 := bstep (se 1 (by rfl) ⟨1156106, by rfl⟩ : syracuseStep 1541475 = 2312213) B2312213
theorem B1541491 : Blo 1541468 1541491 := bstep (se 1 (by rfl) ⟨1156118, by rfl⟩ : syracuseStep 1541491 = 2312237) B2312237
theorem B1541507 : Blo 1541468 1541507 := bstep (se 1 (by rfl) ⟨1156130, by rfl⟩ : syracuseStep 1541507 = 2312261) B2312261
theorem B5203331 : Blo 1541468 5203331 := bstep (se 1 (by rfl) ⟨3902498, by rfl⟩ : syracuseStep 5203331 = 7804997) B7804997
theorem B1541523 : Blo 1541468 1541523 := bstep (se 1 (by rfl) ⟨1156142, by rfl⟩ : syracuseStep 1541523 = 2312285) B2312285
theorem B1951123 : Blo 1541468 1951123 := bstep (se 1 (by rfl) ⟨1463342, by rfl⟩ : syracuseStep 1951123 = 2926685) B2926685
theorem B1541539 : Blo 1541468 1541539 := bstep (se 1 (by rfl) ⟨1156154, by rfl⟩ : syracuseStep 1541539 = 2312309) B2312309
theorem B1541555 : Blo 1541468 1541555 := bstep (se 1 (by rfl) ⟨1156166, by rfl⟩ : syracuseStep 1541555 = 2312333) B2312333
theorem B1541571 : Blo 1541468 1541571 := bstep (se 1 (by rfl) ⟨1156178, by rfl⟩ : syracuseStep 1541571 = 2312357) B2312357
theorem B2344387 : Blo 1541468 2344387 := bstep (se 1 (by rfl) ⟨1758290, by rfl⟩ : syracuseStep 2344387 = 3516581) B3516581
theorem B1541587 : Blo 1541468 1541587 := bstep (se 1 (by rfl) ⟨1156190, by rfl⟩ : syracuseStep 1541587 = 2312381) B2312381
theorem B1541603 : Blo 1541468 1541603 := bstep (se 1 (by rfl) ⟨1156202, by rfl⟩ : syracuseStep 1541603 = 2312405) B2312405
theorem B1541619 : Blo 1541468 1541619 := bstep (se 1 (by rfl) ⟨1156214, by rfl⟩ : syracuseStep 1541619 = 2312429) B2312429
theorem B1951219 : Blo 1541468 1951219 := bstep (se 1 (by rfl) ⟨1463414, by rfl⟩ : syracuseStep 1951219 = 2926829) B2926829
theorem B11879921 : Blo 1541468 11879921 := bstep (se 2 (by rfl) ⟨4454970, by rfl⟩ : syracuseStep 11879921 = 8909941) B8909941
theorem B1541635 : Blo 1541468 1541635 := bstep (se 1 (by rfl) ⟨1156226, by rfl⟩ : syracuseStep 1541635 = 2312453) B2312453
theorem B1541651 : Blo 1541468 1541651 := bstep (se 1 (by rfl) ⟨1156238, by rfl⟩ : syracuseStep 1541651 = 2312477) B2312477
theorem B1541667 : Blo 1541468 1541667 := bstep (se 1 (by rfl) ⟨1156250, by rfl⟩ : syracuseStep 1541667 = 2312501) B2312501
theorem B5858851 : Blo 1541468 5858851 := bstep (se 1 (by rfl) ⟨4394138, by rfl⟩ : syracuseStep 5858851 = 8788277) B8788277
theorem B7808561 : Blo 1541468 7808561 := bstep (se 2 (by rfl) ⟨2928210, by rfl⟩ : syracuseStep 7808561 = 5856421) B5856421
theorem B1541683 : Blo 1541468 1541683 := bstep (se 1 (by rfl) ⟨1156262, by rfl⟩ : syracuseStep 1541683 = 2312525) B2312525
theorem B1541699 : Blo 1541468 1541699 := bstep (se 1 (by rfl) ⟨1156274, by rfl⟩ : syracuseStep 1541699 = 2312549) B2312549
theorem B1541715 : Blo 1541468 1541715 := bstep (se 1 (by rfl) ⟨1156286, by rfl⟩ : syracuseStep 1541715 = 2312573) B2312573
theorem B1541731 : Blo 1541468 1541731 := bstep (se 1 (by rfl) ⟨1156298, by rfl⟩ : syracuseStep 1541731 = 2312597) B2312597
theorem B1541747 : Blo 1541468 1541747 := bstep (se 1 (by rfl) ⟨1156310, by rfl⟩ : syracuseStep 1541747 = 2312621) B2312621
theorem B1541763 : Blo 1541468 1541763 := bstep (se 1 (by rfl) ⟨1156322, by rfl⟩ : syracuseStep 1541763 = 2312645) B2312645
theorem B5203601 : Blo 1541468 5203601 := bstep (se 2 (by rfl) ⟨1951350, by rfl⟩ : syracuseStep 5203601 = 3902701) B3902701
theorem B1541779 : Blo 1541468 1541779 := bstep (se 1 (by rfl) ⟨1156334, by rfl⟩ : syracuseStep 1541779 = 2312669) B2312669
theorem B1541795 : Blo 1541468 1541795 := bstep (se 1 (by rfl) ⟨1156346, by rfl⟩ : syracuseStep 1541795 = 2312693) B2312693
theorem B1541811 : Blo 1541468 1541811 := bstep (se 1 (by rfl) ⟨1156358, by rfl⟩ : syracuseStep 1541811 = 2312717) B2312717
theorem B1541827 : Blo 1541468 1541827 := bstep (se 1 (by rfl) ⟨1156370, by rfl⟩ : syracuseStep 1541827 = 2312741) B2312741
theorem B2197201 : Blo 1541468 2197201 := bstep (se 2 (by rfl) ⟨823950, by rfl⟩ : syracuseStep 2197201 = 1647901) B1647901
theorem B1541843 : Blo 1541468 1541843 := bstep (se 1 (by rfl) ⟨1156382, by rfl⟩ : syracuseStep 1541843 = 2312765) B2312765
theorem B1541859 : Blo 1541468 1541859 := bstep (se 1 (by rfl) ⟨1156394, by rfl⟩ : syracuseStep 1541859 = 2312789) B2312789
theorem B1541875 : Blo 1541468 1541875 := bstep (se 1 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 1541875 = 2312813) B2312813
theorem B1541891 : Blo 1541468 1541891 := bstep (se 1 (by rfl) ⟨1156418, by rfl⟩ : syracuseStep 1541891 = 2312837) B2312837
theorem B1541907 : Blo 1541468 1541907 := bstep (se 1 (by rfl) ⟨1156430, by rfl⟩ : syracuseStep 1541907 = 2312861) B2312861
theorem B1541923 : Blo 1541468 1541923 := bstep (se 1 (by rfl) ⟨1156442, by rfl⟩ : syracuseStep 1541923 = 2312885) B2312885
theorem B2197297 : Blo 1541468 2197297 := bstep (se 2 (by rfl) ⟨823986, by rfl⟩ : syracuseStep 2197297 = 1647973) B1647973
theorem B1541939 : Blo 1541468 1541939 := bstep (se 1 (by rfl) ⟨1156454, by rfl⟩ : syracuseStep 1541939 = 2312909) B2312909
theorem B1541955 : Blo 1541468 1541955 := bstep (se 1 (by rfl) ⟨1156466, by rfl⟩ : syracuseStep 1541955 = 2312933) B2312933
theorem B1541971 : Blo 1541468 1541971 := bstep (se 1 (by rfl) ⟨1156478, by rfl⟩ : syracuseStep 1541971 = 2312957) B2312957
theorem B1541987 : Blo 1541468 1541987 := bstep (se 1 (by rfl) ⟨1156490, by rfl⟩ : syracuseStep 1541987 = 2312981) B2312981
theorem B3295075 : Blo 1541468 3295075 := bstep (se 1 (by rfl) ⟨2471306, by rfl⟩ : syracuseStep 3295075 = 4942613) B4942613
theorem B1542003 : Blo 1541468 1542003 := bstep (se 1 (by rfl) ⟨1156502, by rfl⟩ : syracuseStep 1542003 = 2313005) B2313005
theorem B1542019 : Blo 1541468 1542019 := bstep (se 1 (by rfl) ⟨1156514, by rfl⟩ : syracuseStep 1542019 = 2313029) B2313029
theorem B1542035 : Blo 1541468 1542035 := bstep (se 1 (by rfl) ⟨1156526, by rfl⟩ : syracuseStep 1542035 = 2313053) B2313053
theorem B1542051 : Blo 1541468 1542051 := bstep (se 1 (by rfl) ⟨1156538, by rfl⟩ : syracuseStep 1542051 = 2313077) B2313077
theorem B6588323 : Blo 1541468 6588323 := bstep (se 1 (by rfl) ⟨4941242, by rfl⟩ : syracuseStep 6588323 = 9882485) B9882485
theorem B1542067 : Blo 1541468 1542067 := bstep (se 1 (by rfl) ⟨1156550, by rfl⟩ : syracuseStep 1542067 = 2313101) B2313101
theorem B1542083 : Blo 1541468 1542083 := bstep (se 1 (by rfl) ⟨1156562, by rfl⟩ : syracuseStep 1542083 = 2313125) B2313125
theorem B4171715 : Blo 1541468 4171715 := bstep (se 1 (by rfl) ⟨3128786, by rfl⟩ : syracuseStep 4171715 = 6257573) B6257573
theorem B1542099 : Blo 1541468 1542099 := bstep (se 1 (by rfl) ⟨1156574, by rfl⟩ : syracuseStep 1542099 = 2313149) B2313149
theorem B12503011 : Blo 1541468 12503011 := bstep (se 1 (by rfl) ⟨9377258, by rfl⟩ : syracuseStep 12503011 = 18754517) B18754517
theorem B1951715 : Blo 1541468 1951715 := bstep (se 1 (by rfl) ⟨1463786, by rfl⟩ : syracuseStep 1951715 = 2927573) B2927573
theorem B1542115 : Blo 1541468 1542115 := bstep (se 1 (by rfl) ⟨1156586, by rfl⟩ : syracuseStep 1542115 = 2313173) B2313173
theorem B9881585 : Blo 1541468 9881585 := bstep (se 2 (by rfl) ⟨3705594, by rfl⟩ : syracuseStep 9881585 = 7411189) B7411189
theorem B1542131 : Blo 1541468 1542131 := bstep (se 1 (by rfl) ⟨1156598, by rfl⟩ : syracuseStep 1542131 = 2313197) B2313197
theorem B1542147 : Blo 1541468 1542147 := bstep (se 1 (by rfl) ⟨1156610, by rfl⟩ : syracuseStep 1542147 = 2313221) B2313221
theorem B1542163 : Blo 1541468 1542163 := bstep (se 1 (by rfl) ⟨1156622, by rfl⟩ : syracuseStep 1542163 = 2313245) B2313245
theorem B2312225 : Blo 1541468 2312225 := bstep (se 2 (by rfl) ⟨867084, by rfl⟩ : syracuseStep 2312225 = 1734169) B1734169
theorem B1542179 : Blo 1541468 1542179 := bstep (se 1 (by rfl) ⟨1156634, by rfl⟩ : syracuseStep 1542179 = 2313269) B2313269
theorem B2312243 : Blo 1541468 2312243 := bstep (se 1 (by rfl) ⟨1734182, by rfl⟩ : syracuseStep 2312243 = 3468365) B3468365
theorem B1542195 : Blo 1541468 1542195 := bstep (se 1 (by rfl) ⟨1156646, by rfl⟩ : syracuseStep 1542195 = 2313293) B2313293
theorem B1542211 : Blo 1541468 1542211 := bstep (se 1 (by rfl) ⟨1156658, by rfl⟩ : syracuseStep 1542211 = 2313317) B2313317
theorem B4687949 : Blo 1541468 4687949 := bstep (se 3 (by rfl) ⟨878990, by rfl⟩ : syracuseStep 4687949 = 1757981) B1757981
theorem B2312273 : Blo 1541468 2312273 := bstep (se 2 (by rfl) ⟨867102, by rfl⟩ : syracuseStep 2312273 = 1734205) B1734205
theorem B1542227 : Blo 1541468 1542227 := bstep (se 1 (by rfl) ⟨1156670, by rfl⟩ : syracuseStep 1542227 = 2313341) B2313341
theorem B2312291 : Blo 1541468 2312291 := bstep (se 1 (by rfl) ⟨1734218, by rfl⟩ : syracuseStep 2312291 = 3468437) B3468437
theorem B1542243 : Blo 1541468 1542243 := bstep (se 1 (by rfl) ⟨1156682, by rfl⟩ : syracuseStep 1542243 = 2313365) B2313365
theorem B3295331 : Blo 1541468 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B1542259 : Blo 1541468 1542259 := bstep (se 1 (by rfl) ⟨1156694, by rfl⟩ : syracuseStep 1542259 = 2313389) B2313389
theorem B2312321 : Blo 1541468 2312321 := bstep (se 2 (by rfl) ⟨867120, by rfl⟩ : syracuseStep 2312321 = 1734241) B1734241
theorem B1542275 : Blo 1541468 1542275 := bstep (se 1 (by rfl) ⟨1156706, by rfl⟩ : syracuseStep 1542275 = 2313413) B2313413
theorem B4393091 : Blo 1541468 4393091 := bstep (se 1 (by rfl) ⟨3294818, by rfl⟩ : syracuseStep 4393091 = 6589637) B6589637
theorem B2312339 : Blo 1541468 2312339 := bstep (se 1 (by rfl) ⟨1734254, by rfl⟩ : syracuseStep 2312339 = 3468509) B3468509
theorem B1542291 : Blo 1541468 1542291 := bstep (se 1 (by rfl) ⟨1156718, by rfl⟩ : syracuseStep 1542291 = 2313437) B2313437
theorem B1542307 : Blo 1541468 1542307 := bstep (se 1 (by rfl) ⟨1156730, by rfl⟩ : syracuseStep 1542307 = 2313461) B2313461
theorem B5204141 : Blo 1541468 5204141 := bstep (se 3 (by rfl) ⟨975776, by rfl⟩ : syracuseStep 5204141 = 1951553) B1951553
theorem B2312369 : Blo 1541468 2312369 := bstep (se 2 (by rfl) ⟨867138, by rfl⟩ : syracuseStep 2312369 = 1734277) B1734277
theorem B1542323 : Blo 1541468 1542323 := bstep (se 1 (by rfl) ⟨1156742, by rfl⟩ : syracuseStep 1542323 = 2313485) B2313485
theorem B2312387 : Blo 1541468 2312387 := bstep (se 1 (by rfl) ⟨1734290, by rfl⟩ : syracuseStep 2312387 = 3468581) B3468581
theorem B1542339 : Blo 1541468 1542339 := bstep (se 1 (by rfl) ⟨1156754, by rfl⟩ : syracuseStep 1542339 = 2313509) B2313509
theorem B1542355 : Blo 1541468 1542355 := bstep (se 1 (by rfl) ⟨1156766, by rfl⟩ : syracuseStep 1542355 = 2313533) B2313533
theorem B2312417 : Blo 1541468 2312417 := bstep (se 2 (by rfl) ⟨867156, by rfl⟩ : syracuseStep 2312417 = 1734313) B1734313
theorem B5204195 : Blo 1541468 5204195 := bstep (se 1 (by rfl) ⟨3903146, by rfl⟩ : syracuseStep 5204195 = 7806293) B7806293
theorem B1542371 : Blo 1541468 1542371 := bstep (se 1 (by rfl) ⟨1156778, by rfl⟩ : syracuseStep 1542371 = 2313557) B2313557
theorem B2312435 : Blo 1541468 2312435 := bstep (se 1 (by rfl) ⟨1734326, by rfl⟩ : syracuseStep 2312435 = 3468653) B3468653
theorem B1542387 : Blo 1541468 1542387 := bstep (se 1 (by rfl) ⟨1156790, by rfl⟩ : syracuseStep 1542387 = 2313581) B2313581
theorem B1542403 : Blo 1541468 1542403 := bstep (se 1 (by rfl) ⟨1156802, by rfl⟩ : syracuseStep 1542403 = 2313605) B2313605
theorem B2312465 : Blo 1541468 2312465 := bstep (se 2 (by rfl) ⟨867174, by rfl⟩ : syracuseStep 2312465 = 1734349) B1734349
theorem B1542419 : Blo 1541468 1542419 := bstep (se 1 (by rfl) ⟨1156814, by rfl⟩ : syracuseStep 1542419 = 2313629) B2313629
theorem B2312483 : Blo 1541468 2312483 := bstep (se 1 (by rfl) ⟨1734362, by rfl⟩ : syracuseStep 2312483 = 3468725) B3468725
theorem B1542435 : Blo 1541468 1542435 := bstep (se 1 (by rfl) ⟨1156826, by rfl⟩ : syracuseStep 1542435 = 2313653) B2313653
theorem B1542451 : Blo 1541468 1542451 := bstep (se 1 (by rfl) ⟨1156838, by rfl⟩ : syracuseStep 1542451 = 2313677) B2313677
theorem B2312513 : Blo 1541468 2312513 := bstep (se 2 (by rfl) ⟨867192, by rfl⟩ : syracuseStep 2312513 = 1734385) B1734385
theorem B1542467 : Blo 1541468 1542467 := bstep (se 1 (by rfl) ⟨1156850, by rfl⟩ : syracuseStep 1542467 = 2313701) B2313701
theorem B2312531 : Blo 1541468 2312531 := bstep (se 1 (by rfl) ⟨1734398, by rfl⟩ : syracuseStep 2312531 = 3468797) B3468797
theorem B1542483 : Blo 1541468 1542483 := bstep (se 1 (by rfl) ⟨1156862, by rfl⟩ : syracuseStep 1542483 = 2313725) B2313725
theorem B1542499 : Blo 1541468 1542499 := bstep (se 1 (by rfl) ⟨1156874, by rfl⟩ : syracuseStep 1542499 = 2313749) B2313749
theorem B2312561 : Blo 1541468 2312561 := bstep (se 2 (by rfl) ⟨867210, by rfl⟩ : syracuseStep 2312561 = 1734421) B1734421
theorem B1542515 : Blo 1541468 1542515 := bstep (se 1 (by rfl) ⟨1156886, by rfl⟩ : syracuseStep 1542515 = 2313773) B2313773
theorem B2312579 : Blo 1541468 2312579 := bstep (se 1 (by rfl) ⟨1734434, by rfl⟩ : syracuseStep 2312579 = 3468869) B3468869
theorem B1542531 : Blo 1541468 1542531 := bstep (se 1 (by rfl) ⟨1156898, by rfl⟩ : syracuseStep 1542531 = 2313797) B2313797
theorem B10553741 : Blo 1541468 10553741 := bstep (se 3 (by rfl) ⟨1978826, by rfl⟩ : syracuseStep 10553741 = 3957653) B3957653
theorem B5147021 : Blo 1541468 5147021 := bstep (se 3 (by rfl) ⟨965066, by rfl⟩ : syracuseStep 5147021 = 1930133) B1930133
theorem B1542547 : Blo 1541468 1542547 := bstep (se 1 (by rfl) ⟨1156910, by rfl⟩ : syracuseStep 1542547 = 2313821) B2313821
theorem B2312609 : Blo 1541468 2312609 := bstep (se 2 (by rfl) ⟨867228, by rfl⟩ : syracuseStep 2312609 = 1734457) B1734457
theorem B2927011 : Blo 1541468 2927011 := bstep (se 1 (by rfl) ⟨2195258, by rfl⟩ : syracuseStep 2927011 = 4390517) B4390517
theorem B1542563 : Blo 1541468 1542563 := bstep (se 1 (by rfl) ⟨1156922, by rfl⟩ : syracuseStep 1542563 = 2313845) B2313845
theorem B2312627 : Blo 1541468 2312627 := bstep (se 1 (by rfl) ⟨1734470, by rfl⟩ : syracuseStep 2312627 = 3468941) B3468941
theorem B1542579 : Blo 1541468 1542579 := bstep (se 1 (by rfl) ⟨1156934, by rfl⟩ : syracuseStep 1542579 = 2313869) B2313869
theorem B3901891 : Blo 1541468 3901891 := bstep (se 1 (by rfl) ⟨2926418, by rfl⟩ : syracuseStep 3901891 = 5852837) B5852837
theorem B1542595 : Blo 1541468 1542595 := bstep (se 1 (by rfl) ⟨1156946, by rfl⟩ : syracuseStep 1542595 = 2313893) B2313893
theorem B2312657 : Blo 1541468 2312657 := bstep (se 2 (by rfl) ⟨867246, by rfl⟩ : syracuseStep 2312657 = 1734493) B1734493
theorem B1542611 : Blo 1541468 1542611 := bstep (se 1 (by rfl) ⟨1156958, by rfl⟩ : syracuseStep 1542611 = 2313917) B2313917
theorem B2312675 : Blo 1541468 2312675 := bstep (se 1 (by rfl) ⟨1734506, by rfl⟩ : syracuseStep 2312675 = 3469013) B3469013
theorem B5556707 : Blo 1541468 5556707 := bstep (se 1 (by rfl) ⟨4167530, by rfl⟩ : syracuseStep 5556707 = 8335061) B8335061
theorem B1542627 : Blo 1541468 1542627 := bstep (se 1 (by rfl) ⟨1156970, by rfl⟩ : syracuseStep 1542627 = 2313941) B2313941
theorem B5204465 : Blo 1541468 5204465 := bstep (se 2 (by rfl) ⟨1951674, by rfl⟩ : syracuseStep 5204465 = 3903349) B3903349
theorem B1542643 : Blo 1541468 1542643 := bstep (se 1 (by rfl) ⟨1156982, by rfl⟩ : syracuseStep 1542643 = 2313965) B2313965
theorem B2312705 : Blo 1541468 2312705 := bstep (se 2 (by rfl) ⟨867264, by rfl⟩ : syracuseStep 2312705 = 1734529) B1734529
theorem B1542659 : Blo 1541468 1542659 := bstep (se 1 (by rfl) ⟨1156994, by rfl⟩ : syracuseStep 1542659 = 2313989) B2313989
theorem B2312723 : Blo 1541468 2312723 := bstep (se 1 (by rfl) ⟨1734542, by rfl⟩ : syracuseStep 2312723 = 3469085) B3469085
theorem B1542675 : Blo 1541468 1542675 := bstep (se 1 (by rfl) ⟨1157006, by rfl⟩ : syracuseStep 1542675 = 2314013) B2314013
theorem B1878563 : Blo 1541468 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1542691 : Blo 1541468 1542691 := bstep (se 1 (by rfl) ⟨1157018, by rfl⟩ : syracuseStep 1542691 = 2314037) B2314037
theorem B2312753 : Blo 1541468 2312753 := bstep (se 2 (by rfl) ⟨867282, by rfl⟩ : syracuseStep 2312753 = 1734565) B1734565
theorem B1542707 : Blo 1541468 1542707 := bstep (se 1 (by rfl) ⟨1157030, by rfl⟩ : syracuseStep 1542707 = 2314061) B2314061
theorem B2312771 : Blo 1541468 2312771 := bstep (se 1 (by rfl) ⟨1734578, by rfl⟩ : syracuseStep 2312771 = 3469157) B3469157
theorem B2927171 : Blo 1541468 2927171 := bstep (se 1 (by rfl) ⟨2195378, by rfl⟩ : syracuseStep 2927171 = 4390757) B4390757
theorem B1542723 : Blo 1541468 1542723 := bstep (se 1 (by rfl) ⟨1157042, by rfl⟩ : syracuseStep 1542723 = 2314085) B2314085
theorem B3902033 : Blo 1541468 3902033 := bstep (se 2 (by rfl) ⟨1463262, by rfl⟩ : syracuseStep 3902033 = 2926525) B2926525
theorem B1542739 : Blo 1541468 1542739 := bstep (se 1 (by rfl) ⟨1157054, by rfl⟩ : syracuseStep 1542739 = 2314109) B2314109
theorem B2312801 : Blo 1541468 2312801 := bstep (se 2 (by rfl) ⟨867300, by rfl⟩ : syracuseStep 2312801 = 1734601) B1734601
theorem B1542755 : Blo 1541468 1542755 := bstep (se 1 (by rfl) ⟨1157066, by rfl⟩ : syracuseStep 1542755 = 2314133) B2314133
theorem B2312819 : Blo 1541468 2312819 := bstep (se 1 (by rfl) ⟨1734614, by rfl⟩ : syracuseStep 2312819 = 3469229) B3469229
theorem B1542771 : Blo 1541468 1542771 := bstep (se 1 (by rfl) ⟨1157078, by rfl⟩ : syracuseStep 1542771 = 2314157) B2314157
theorem B1542787 : Blo 1541468 1542787 := bstep (se 1 (by rfl) ⟨1157090, by rfl⟩ : syracuseStep 1542787 = 2314181) B2314181
theorem B2312849 : Blo 1541468 2312849 := bstep (se 2 (by rfl) ⟨867318, by rfl⟩ : syracuseStep 2312849 = 1734637) B1734637
theorem B1542803 : Blo 1541468 1542803 := bstep (se 1 (by rfl) ⟨1157102, by rfl⟩ : syracuseStep 1542803 = 2314205) B2314205
theorem B2312867 : Blo 1541468 2312867 := bstep (se 1 (by rfl) ⟨1734650, by rfl⟩ : syracuseStep 2312867 = 3469301) B3469301
theorem B1952419 : Blo 1541468 1952419 := bstep (se 1 (by rfl) ⟨1464314, by rfl⟩ : syracuseStep 1952419 = 2928629) B2928629
theorem B1542819 : Blo 1541468 1542819 := bstep (se 1 (by rfl) ⟨1157114, by rfl⟩ : syracuseStep 1542819 = 2314229) B2314229
theorem B1542835 : Blo 1541468 1542835 := bstep (se 1 (by rfl) ⟨1157126, by rfl⟩ : syracuseStep 1542835 = 2314253) B2314253
theorem B2312897 : Blo 1541468 2312897 := bstep (se 2 (by rfl) ⟨867336, by rfl⟩ : syracuseStep 2312897 = 1734673) B1734673
theorem B1542851 : Blo 1541468 1542851 := bstep (se 1 (by rfl) ⟨1157138, by rfl⟩ : syracuseStep 1542851 = 2314277) B2314277
theorem B2312915 : Blo 1541468 2312915 := bstep (se 1 (by rfl) ⟨1734686, by rfl⟩ : syracuseStep 2312915 = 3469373) B3469373
theorem B1542867 : Blo 1541468 1542867 := bstep (se 1 (by rfl) ⟨1157150, by rfl⟩ : syracuseStep 1542867 = 2314301) B2314301
theorem B8784611 : Blo 1541468 8784611 := bstep (se 1 (by rfl) ⟨6588458, by rfl⟩ : syracuseStep 8784611 = 13176917) B13176917
theorem B1542883 : Blo 1541468 1542883 := bstep (se 1 (by rfl) ⟨1157162, by rfl⟩ : syracuseStep 1542883 = 2314325) B2314325
theorem B8899313 : Blo 1541468 8899313 := bstep (se 2 (by rfl) ⟨3337242, by rfl⟩ : syracuseStep 8899313 = 6674485) B6674485
theorem B2312945 : Blo 1541468 2312945 := bstep (se 2 (by rfl) ⟨867354, by rfl⟩ : syracuseStep 2312945 = 1734709) B1734709
theorem B1542899 : Blo 1541468 1542899 := bstep (se 1 (by rfl) ⟨1157174, by rfl⟩ : syracuseStep 1542899 = 2314349) B2314349
theorem B7039729 : Blo 1541468 7039729 := bstep (se 2 (by rfl) ⟨2639898, by rfl⟩ : syracuseStep 7039729 = 5279797) B5279797
theorem B2312963 : Blo 1541468 2312963 := bstep (se 1 (by rfl) ⟨1734722, by rfl⟩ : syracuseStep 2312963 = 3469445) B3469445
theorem B1952515 : Blo 1541468 1952515 := bstep (se 1 (by rfl) ⟨1464386, by rfl⟩ : syracuseStep 1952515 = 2928773) B2928773
theorem B1542915 : Blo 1541468 1542915 := bstep (se 1 (by rfl) ⟨1157186, by rfl⟩ : syracuseStep 1542915 = 2314373) B2314373
theorem B11709197 : Blo 1541468 11709197 := bstep (se 3 (by rfl) ⟨2195474, by rfl⟩ : syracuseStep 11709197 = 4390949) B4390949
theorem B1542931 : Blo 1541468 1542931 := bstep (se 1 (by rfl) ⟨1157198, by rfl⟩ : syracuseStep 1542931 = 2314397) B2314397
theorem B2312993 : Blo 1541468 2312993 := bstep (se 2 (by rfl) ⟨867372, by rfl⟩ : syracuseStep 2312993 = 1734745) B1734745
theorem B1542947 : Blo 1541468 1542947 := bstep (se 1 (by rfl) ⟨1157210, by rfl⟩ : syracuseStep 1542947 = 2314421) B2314421
theorem B5008177 : Blo 1541468 5008177 := bstep (se 2 (by rfl) ⟨1878066, by rfl⟩ : syracuseStep 5008177 = 3756133) B3756133
theorem B2313011 : Blo 1541468 2313011 := bstep (se 1 (by rfl) ⟨1734758, by rfl⟩ : syracuseStep 2313011 = 3469517) B3469517
theorem B1542963 : Blo 1541468 1542963 := bstep (se 1 (by rfl) ⟨1157222, by rfl⟩ : syracuseStep 1542963 = 2314445) B2314445
theorem B1542979 : Blo 1541468 1542979 := bstep (se 1 (by rfl) ⟨1157234, by rfl⟩ : syracuseStep 1542979 = 2314469) B2314469
theorem B2313041 : Blo 1541468 2313041 := bstep (se 2 (by rfl) ⟨867390, by rfl⟩ : syracuseStep 2313041 = 1734781) B1734781
theorem B1542995 : Blo 1541468 1542995 := bstep (se 1 (by rfl) ⟨1157246, by rfl⟩ : syracuseStep 1542995 = 2314493) B2314493
theorem B2313059 : Blo 1541468 2313059 := bstep (se 1 (by rfl) ⟨1734794, by rfl⟩ : syracuseStep 2313059 = 3469589) B3469589
theorem B1543011 : Blo 1541468 1543011 := bstep (se 1 (by rfl) ⟨1157258, by rfl⟩ : syracuseStep 1543011 = 2314517) B2314517
theorem B1543027 : Blo 1541468 1543027 := bstep (se 1 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 1543027 = 2314541) B2314541
theorem B2313089 : Blo 1541468 2313089 := bstep (se 2 (by rfl) ⟨867408, by rfl⟩ : syracuseStep 2313089 = 1734817) B1734817
theorem B1543043 : Blo 1541468 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B2313107 : Blo 1541468 2313107 := bstep (se 1 (by rfl) ⟨1734830, by rfl⟩ : syracuseStep 2313107 = 3469661) B3469661
theorem B1543059 : Blo 1541468 1543059 := bstep (se 1 (by rfl) ⟨1157294, by rfl⟩ : syracuseStep 1543059 = 2314589) B2314589
theorem B1543075 : Blo 1541468 1543075 := bstep (se 1 (by rfl) ⟨1157306, by rfl⟩ : syracuseStep 1543075 = 2314613) B2314613
theorem B2313137 : Blo 1541468 2313137 := bstep (se 2 (by rfl) ⟨867426, by rfl⟩ : syracuseStep 2313137 = 1734853) B1734853
theorem B1543091 : Blo 1541468 1543091 := bstep (se 1 (by rfl) ⟨1157318, by rfl⟩ : syracuseStep 1543091 = 2314637) B2314637
theorem B2313155 : Blo 1541468 2313155 := bstep (se 1 (by rfl) ⟨1734866, by rfl⟩ : syracuseStep 2313155 = 3469733) B3469733
theorem B1543107 : Blo 1541468 1543107 := bstep (se 1 (by rfl) ⟨1157330, by rfl⟩ : syracuseStep 1543107 = 2314661) B2314661
theorem B1543123 : Blo 1541468 1543123 := bstep (se 1 (by rfl) ⟨1157342, by rfl⟩ : syracuseStep 1543123 = 2314685) B2314685
theorem B2313185 : Blo 1541468 2313185 := bstep (se 2 (by rfl) ⟨867444, by rfl⟩ : syracuseStep 2313185 = 1734889) B1734889
theorem B7810019 : Blo 1541468 7810019 := bstep (se 1 (by rfl) ⟨5857514, by rfl⟩ : syracuseStep 7810019 = 11715029) B11715029
theorem B1543139 : Blo 1541468 1543139 := bstep (se 1 (by rfl) ⟨1157354, by rfl⟩ : syracuseStep 1543139 = 2314709) B2314709
theorem B2313203 : Blo 1541468 2313203 := bstep (se 1 (by rfl) ⟨1734902, by rfl⟩ : syracuseStep 2313203 = 3469805) B3469805
theorem B1543155 : Blo 1541468 1543155 := bstep (se 1 (by rfl) ⟨1157366, by rfl⟩ : syracuseStep 1543155 = 2314733) B2314733
theorem B2345987 : Blo 1541468 2345987 := bstep (se 1 (by rfl) ⟨1759490, by rfl⟩ : syracuseStep 2345987 = 3518981) B3518981
theorem B1543171 : Blo 1541468 1543171 := bstep (se 1 (by rfl) ⟨1157378, by rfl⟩ : syracuseStep 1543171 = 2314757) B2314757
theorem B5205005 : Blo 1541468 5205005 := bstep (se 3 (by rfl) ⟨975938, by rfl⟩ : syracuseStep 5205005 = 1951877) B1951877
theorem B2313233 : Blo 1541468 2313233 := bstep (se 2 (by rfl) ⟨867462, by rfl⟩ : syracuseStep 2313233 = 1734925) B1734925
theorem B1543187 : Blo 1541468 1543187 := bstep (se 1 (by rfl) ⟨1157390, by rfl⟩ : syracuseStep 1543187 = 2314781) B2314781
theorem B2313251 : Blo 1541468 2313251 := bstep (se 1 (by rfl) ⟨1734938, by rfl⟩ : syracuseStep 2313251 = 3469877) B3469877
theorem B4942883 : Blo 1541468 4942883 := bstep (se 1 (by rfl) ⟨3707162, by rfl⟩ : syracuseStep 4942883 = 7414325) B7414325
theorem B1543203 : Blo 1541468 1543203 := bstep (se 1 (by rfl) ⟨1157402, by rfl⟩ : syracuseStep 1543203 = 2314805) B2314805
theorem B3296305 : Blo 1541468 3296305 := bstep (se 2 (by rfl) ⟨1236114, by rfl⟩ : syracuseStep 3296305 = 2472229) B2472229
theorem B1543219 : Blo 1541468 1543219 := bstep (se 1 (by rfl) ⟨1157414, by rfl⟩ : syracuseStep 1543219 = 2314829) B2314829
theorem B2313281 : Blo 1541468 2313281 := bstep (se 2 (by rfl) ⟨867480, by rfl⟩ : syracuseStep 2313281 = 1734961) B1734961
theorem B5205059 : Blo 1541468 5205059 := bstep (se 1 (by rfl) ⟨3903794, by rfl⟩ : syracuseStep 5205059 = 7807589) B7807589
theorem B1543235 : Blo 1541468 1543235 := bstep (se 1 (by rfl) ⟨1157426, by rfl⟩ : syracuseStep 1543235 = 2314853) B2314853
theorem B2313299 : Blo 1541468 2313299 := bstep (se 1 (by rfl) ⟨1734974, by rfl⟩ : syracuseStep 2313299 = 3469949) B3469949
theorem B1543251 : Blo 1541468 1543251 := bstep (se 1 (by rfl) ⟨1157438, by rfl⟩ : syracuseStep 1543251 = 2314877) B2314877
theorem B1543267 : Blo 1541468 1543267 := bstep (se 1 (by rfl) ⟨1157450, by rfl⟩ : syracuseStep 1543267 = 2314901) B2314901
theorem B3468401 : Blo 1541468 3468401 := bstep (se 2 (by rfl) ⟨1300650, by rfl⟩ : syracuseStep 3468401 = 2601301) B2601301
theorem B2313329 : Blo 1541468 2313329 := bstep (se 2 (by rfl) ⟨867498, by rfl⟩ : syracuseStep 2313329 = 1734997) B1734997
theorem B1543283 : Blo 1541468 1543283 := bstep (se 1 (by rfl) ⟨1157462, by rfl⟩ : syracuseStep 1543283 = 2314925) B2314925
theorem B3468419 : Blo 1541468 3468419 := bstep (se 1 (by rfl) ⟨2601314, by rfl⟩ : syracuseStep 3468419 = 5202629) B5202629
theorem B2313347 : Blo 1541468 2313347 := bstep (se 1 (by rfl) ⟨1735010, by rfl⟩ : syracuseStep 2313347 = 3470021) B3470021
theorem B1543299 : Blo 1541468 1543299 := bstep (se 1 (by rfl) ⟨1157474, by rfl⟩ : syracuseStep 1543299 = 2314949) B2314949
theorem B1543315 : Blo 1541468 1543315 := bstep (se 1 (by rfl) ⟨1157486, by rfl⟩ : syracuseStep 1543315 = 2314973) B2314973
theorem B2313377 : Blo 1541468 2313377 := bstep (se 2 (by rfl) ⟨867516, by rfl⟩ : syracuseStep 2313377 = 1735033) B1735033
theorem B1543331 : Blo 1541468 1543331 := bstep (se 1 (by rfl) ⟨1157498, by rfl⟩ : syracuseStep 1543331 = 2314997) B2314997
theorem B2313395 : Blo 1541468 2313395 := bstep (se 1 (by rfl) ⟨1735046, by rfl⟩ : syracuseStep 2313395 = 3470093) B3470093
theorem B1543347 : Blo 1541468 1543347 := bstep (se 1 (by rfl) ⟨1157510, by rfl⟩ : syracuseStep 1543347 = 2315021) B2315021
theorem B1543363 : Blo 1541468 1543363 := bstep (se 1 (by rfl) ⟨1157522, by rfl⟩ : syracuseStep 1543363 = 2315045) B2315045
theorem B2313425 : Blo 1541468 2313425 := bstep (se 2 (by rfl) ⟨867534, by rfl⟩ : syracuseStep 2313425 = 1735069) B1735069
theorem B1543379 : Blo 1541468 1543379 := bstep (se 1 (by rfl) ⟨1157534, by rfl⟩ : syracuseStep 1543379 = 2315069) B2315069
theorem B2313443 : Blo 1541468 2313443 := bstep (se 1 (by rfl) ⟨1735082, by rfl⟩ : syracuseStep 2313443 = 3470165) B3470165
theorem B1543395 : Blo 1541468 1543395 := bstep (se 1 (by rfl) ⟨1157546, by rfl⟩ : syracuseStep 1543395 = 2315093) B2315093
theorem B1953011 : Blo 1541468 1953011 := bstep (se 1 (by rfl) ⟨1464758, by rfl⟩ : syracuseStep 1953011 = 2929517) B2929517
theorem B1543411 : Blo 1541468 1543411 := bstep (se 1 (by rfl) ⟨1157558, by rfl⟩ : syracuseStep 1543411 = 2315117) B2315117
theorem B2313473 : Blo 1541468 2313473 := bstep (se 2 (by rfl) ⟨867552, by rfl⟩ : syracuseStep 2313473 = 1735105) B1735105
theorem B1543427 : Blo 1541468 1543427 := bstep (se 1 (by rfl) ⟨1157570, by rfl⟩ : syracuseStep 1543427 = 2315141) B2315141
theorem B2313491 : Blo 1541468 2313491 := bstep (se 1 (by rfl) ⟨1735118, by rfl⟩ : syracuseStep 2313491 = 3470237) B3470237
theorem B1543443 : Blo 1541468 1543443 := bstep (se 1 (by rfl) ⟨1157582, by rfl⟩ : syracuseStep 1543443 = 2315165) B2315165
theorem B1543459 : Blo 1541468 1543459 := bstep (se 1 (by rfl) ⟨1157594, by rfl⟩ : syracuseStep 1543459 = 2315189) B2315189
theorem B2313521 : Blo 1541468 2313521 := bstep (se 2 (by rfl) ⟨867570, by rfl⟩ : syracuseStep 2313521 = 1735141) B1735141
theorem B2313539 : Blo 1541468 2313539 := bstep (se 1 (by rfl) ⟨1735154, by rfl⟩ : syracuseStep 2313539 = 3470309) B3470309
theorem B5205329 : Blo 1541468 5205329 := bstep (se 2 (by rfl) ⟨1951998, by rfl⟩ : syracuseStep 5205329 = 3903997) B3903997
theorem B4394321 : Blo 1541468 4394321 := bstep (se 2 (by rfl) ⟨1647870, by rfl⟩ : syracuseStep 4394321 = 3295741) B3295741
theorem B2313569 : Blo 1541468 2313569 := bstep (se 2 (by rfl) ⟨867588, by rfl⟩ : syracuseStep 2313569 = 1735177) B1735177
theorem B22842737 : Blo 1541468 22842737 := bstep (se 2 (by rfl) ⟨8566026, by rfl⟩ : syracuseStep 22842737 = 17132053) B17132053
theorem B2313587 : Blo 1541468 2313587 := bstep (se 1 (by rfl) ⟨1735190, by rfl⟩ : syracuseStep 2313587 = 3470381) B3470381
theorem B3468689 : Blo 1541468 3468689 := bstep (se 2 (by rfl) ⟨1300758, by rfl⟩ : syracuseStep 3468689 = 2601517) B2601517
theorem B2313617 : Blo 1541468 2313617 := bstep (se 2 (by rfl) ⟨867606, by rfl⟩ : syracuseStep 2313617 = 1735213) B1735213
theorem B3468707 : Blo 1541468 3468707 := bstep (se 1 (by rfl) ⟨2601530, by rfl⟩ : syracuseStep 3468707 = 5203061) B5203061
theorem B2313635 : Blo 1541468 2313635 := bstep (se 1 (by rfl) ⟨1735226, by rfl⟩ : syracuseStep 2313635 = 3470453) B3470453
theorem B2313665 : Blo 1541468 2313665 := bstep (se 2 (by rfl) ⟨867624, by rfl⟩ : syracuseStep 2313665 = 1735249) B1735249
theorem B2969041 : Blo 1541468 2969041 := bstep (se 2 (by rfl) ⟨1113390, by rfl⟩ : syracuseStep 2969041 = 2226781) B2226781
theorem B2313683 : Blo 1541468 2313683 := bstep (se 1 (by rfl) ⟨1735262, by rfl⟩ : syracuseStep 2313683 = 3470525) B3470525
theorem B2313713 : Blo 1541468 2313713 := bstep (se 2 (by rfl) ⟨867642, by rfl⟩ : syracuseStep 2313713 = 1735285) B1735285
theorem B2313731 : Blo 1541468 2313731 := bstep (se 1 (by rfl) ⟨1735298, by rfl⟩ : syracuseStep 2313731 = 3470597) B3470597
theorem B2313761 : Blo 1541468 2313761 := bstep (se 2 (by rfl) ⟨867660, by rfl⟩ : syracuseStep 2313761 = 1735321) B1735321
theorem B3517987 : Blo 1541468 3517987 := bstep (se 1 (by rfl) ⟨2638490, by rfl⟩ : syracuseStep 3517987 = 5276981) B5276981
theorem B3903025 : Blo 1541468 3903025 := bstep (se 2 (by rfl) ⟨1463634, by rfl⟩ : syracuseStep 3903025 = 2927269) B2927269
theorem B2313779 : Blo 1541468 2313779 := bstep (se 1 (by rfl) ⟨1735334, by rfl⟩ : syracuseStep 2313779 = 3470669) B3470669
theorem B2313809 : Blo 1541468 2313809 := bstep (se 2 (by rfl) ⟨867678, by rfl⟩ : syracuseStep 2313809 = 1735357) B1735357
theorem B2313827 : Blo 1541468 2313827 := bstep (se 1 (by rfl) ⟨1735370, by rfl⟩ : syracuseStep 2313827 = 3470741) B3470741
theorem B2928241 : Blo 1541468 2928241 := bstep (se 2 (by rfl) ⟨1098090, by rfl⟩ : syracuseStep 2928241 = 2196181) B2196181
theorem B2313857 : Blo 1541468 2313857 := bstep (se 2 (by rfl) ⟨867696, by rfl⟩ : syracuseStep 2313857 = 1735393) B1735393
theorem B3706499 : Blo 1541468 3706499 := bstep (se 1 (by rfl) ⟨2779874, by rfl⟩ : syracuseStep 3706499 = 5559749) B5559749
theorem B5279363 : Blo 1541468 5279363 := bstep (se 1 (by rfl) ⟨3959522, by rfl⟩ : syracuseStep 5279363 = 7919045) B7919045
theorem B2313875 : Blo 1541468 2313875 := bstep (se 1 (by rfl) ⟨1735406, by rfl⟩ : syracuseStep 2313875 = 3470813) B3470813
theorem B3468977 : Blo 1541468 3468977 := bstep (se 2 (by rfl) ⟨1300866, by rfl⟩ : syracuseStep 3468977 = 2601733) B2601733
theorem B2313905 : Blo 1541468 2313905 := bstep (se 2 (by rfl) ⟨867714, by rfl⟩ : syracuseStep 2313905 = 1735429) B1735429
theorem B3468995 : Blo 1541468 3468995 := bstep (se 1 (by rfl) ⟨2601746, by rfl⟩ : syracuseStep 3468995 = 5203493) B5203493
theorem B2313923 : Blo 1541468 2313923 := bstep (se 1 (by rfl) ⟨1735442, by rfl⟩ : syracuseStep 2313923 = 3470885) B3470885
theorem B2313953 : Blo 1541468 2313953 := bstep (se 2 (by rfl) ⟨867732, by rfl⟩ : syracuseStep 2313953 = 1735465) B1735465
theorem B2313971 : Blo 1541468 2313971 := bstep (se 1 (by rfl) ⟨1735478, by rfl⟩ : syracuseStep 2313971 = 3470957) B3470957
theorem B7810829 : Blo 1541468 7810829 := bstep (se 3 (by rfl) ⟨1464530, by rfl⟩ : syracuseStep 7810829 = 2929061) B2929061
theorem B2314001 : Blo 1541468 2314001 := bstep (se 2 (by rfl) ⟨867750, by rfl⟩ : syracuseStep 2314001 = 1735501) B1735501
theorem B2314019 : Blo 1541468 2314019 := bstep (se 1 (by rfl) ⟨1735514, by rfl⟩ : syracuseStep 2314019 = 3471029) B3471029
theorem B2314049 : Blo 1541468 2314049 := bstep (se 2 (by rfl) ⟨867768, by rfl⟩ : syracuseStep 2314049 = 1735537) B1735537
theorem B3903299 : Blo 1541468 3903299 := bstep (se 1 (by rfl) ⟨2927474, by rfl⟩ : syracuseStep 3903299 = 5854949) B5854949
theorem B5853005 : Blo 1541468 5853005 := bstep (se 3 (by rfl) ⟨1097438, by rfl⟩ : syracuseStep 5853005 = 2194877) B2194877
theorem B2314067 : Blo 1541468 2314067 := bstep (se 1 (by rfl) ⟨1735550, by rfl⟩ : syracuseStep 2314067 = 3471101) B3471101
theorem B16674659 : Blo 1541468 16674659 := bstep (se 1 (by rfl) ⟨12505994, by rfl⟩ : syracuseStep 16674659 = 25011989) B25011989
theorem B5205869 : Blo 1541468 5205869 := bstep (se 3 (by rfl) ⟨976100, by rfl⟩ : syracuseStep 5205869 = 1952201) B1952201
theorem B2314097 : Blo 1541468 2314097 := bstep (se 2 (by rfl) ⟨867786, by rfl⟩ : syracuseStep 2314097 = 1735573) B1735573
theorem B6590321 : Blo 1541468 6590321 := bstep (se 2 (by rfl) ⟨2471370, by rfl⟩ : syracuseStep 6590321 = 4942741) B4942741
theorem B2314115 : Blo 1541468 2314115 := bstep (se 1 (by rfl) ⟨1735586, by rfl⟩ : syracuseStep 2314115 = 3471173) B3471173
theorem B2314145 : Blo 1541468 2314145 := bstep (se 2 (by rfl) ⟨867804, by rfl⟩ : syracuseStep 2314145 = 1735609) B1735609
theorem B5205923 : Blo 1541468 5205923 := bstep (se 1 (by rfl) ⟨3904442, by rfl⟩ : syracuseStep 5205923 = 7808885) B7808885
theorem B2314163 : Blo 1541468 2314163 := bstep (se 1 (by rfl) ⟨1735622, by rfl⟩ : syracuseStep 2314163 = 3471245) B3471245
theorem B3469265 : Blo 1541468 3469265 := bstep (se 2 (by rfl) ⟨1300974, by rfl⟩ : syracuseStep 3469265 = 2601949) B2601949
theorem B2314193 : Blo 1541468 2314193 := bstep (se 2 (by rfl) ⟨867822, by rfl⟩ : syracuseStep 2314193 = 1735645) B1735645
theorem B3469283 : Blo 1541468 3469283 := bstep (se 1 (by rfl) ⟨2601962, by rfl⟩ : syracuseStep 3469283 = 5203925) B5203925
theorem B2314211 : Blo 1541468 2314211 := bstep (se 1 (by rfl) ⟨1735658, by rfl⟩ : syracuseStep 2314211 = 3471317) B3471317
theorem B2084851 : Blo 1541468 2084851 := bstep (se 1 (by rfl) ⟨1563638, by rfl⟩ : syracuseStep 2084851 = 3127277) B3127277
theorem B2314241 : Blo 1541468 2314241 := bstep (se 2 (by rfl) ⟨867840, by rfl⟩ : syracuseStep 2314241 = 1735681) B1735681
theorem B3903491 : Blo 1541468 3903491 := bstep (se 1 (by rfl) ⟨2927618, by rfl⟩ : syracuseStep 3903491 = 5855237) B5855237
theorem B8343557 : Blo 1541468 8343557 := bstep (se 4 (by rfl) ⟨782208, by rfl⟩ : syracuseStep 8343557 = 1564417) B1564417
theorem B2314259 : Blo 1541468 2314259 := bstep (se 1 (by rfl) ⟨1735694, by rfl⟩ : syracuseStep 2314259 = 3471389) B3471389
theorem B2469923 : Blo 1541468 2469923 := bstep (se 1 (by rfl) ⟨1852442, by rfl⟩ : syracuseStep 2469923 = 3704885) B3704885
theorem B5558321 : Blo 1541468 5558321 := bstep (se 2 (by rfl) ⟨2084370, by rfl⟩ : syracuseStep 5558321 = 4168741) B4168741
theorem B2314289 : Blo 1541468 2314289 := bstep (se 2 (by rfl) ⟨867858, by rfl⟩ : syracuseStep 2314289 = 1735717) B1735717
theorem B2469955 : Blo 1541468 2469955 := bstep (se 1 (by rfl) ⟨1852466, by rfl⟩ : syracuseStep 2469955 = 3704933) B3704933
theorem B2314307 : Blo 1541468 2314307 := bstep (se 1 (by rfl) ⟨1735730, by rfl⟩ : syracuseStep 2314307 = 3471461) B3471461
theorem B2314337 : Blo 1541468 2314337 := bstep (se 2 (by rfl) ⟨867876, by rfl⟩ : syracuseStep 2314337 = 1735753) B1735753
theorem B2314355 : Blo 1541468 2314355 := bstep (se 1 (by rfl) ⟨1735766, by rfl⟩ : syracuseStep 2314355 = 3471533) B3471533
theorem B2314385 : Blo 1541468 2314385 := bstep (se 2 (by rfl) ⟨867894, by rfl⟩ : syracuseStep 2314385 = 1735789) B1735789
theorem B2314403 : Blo 1541468 2314403 := bstep (se 1 (by rfl) ⟨1735802, by rfl⟩ : syracuseStep 2314403 = 3471605) B3471605
theorem B5558449 : Blo 1541468 5558449 := bstep (se 2 (by rfl) ⟨2084418, by rfl⟩ : syracuseStep 5558449 = 4168837) B4168837
theorem B5206193 : Blo 1541468 5206193 := bstep (se 2 (by rfl) ⟨1952322, by rfl⟩ : syracuseStep 5206193 = 3904645) B3904645
theorem B19771573 : Blo 1541468 19771573 := bstep (se 5 (by rfl) ⟨926792, by rfl⟩ : syracuseStep 19771573 = 1853585) B1853585
theorem B2314433 : Blo 1541468 2314433 := bstep (se 2 (by rfl) ⟨867912, by rfl⟩ : syracuseStep 2314433 = 1735825) B1735825
theorem B2314451 : Blo 1541468 2314451 := bstep (se 1 (by rfl) ⟨1735838, by rfl⟩ : syracuseStep 2314451 = 3471677) B3471677
theorem B3469553 : Blo 1541468 3469553 := bstep (se 2 (by rfl) ⟨1301082, by rfl⟩ : syracuseStep 3469553 = 2602165) B2602165
theorem B2314481 : Blo 1541468 2314481 := bstep (se 2 (by rfl) ⟨867930, by rfl⟩ : syracuseStep 2314481 = 1735861) B1735861
theorem B3469571 : Blo 1541468 3469571 := bstep (se 1 (by rfl) ⟨2602178, by rfl⟩ : syracuseStep 3469571 = 5204357) B5204357
theorem B2314499 : Blo 1541468 2314499 := bstep (se 1 (by rfl) ⟨1735874, by rfl⟩ : syracuseStep 2314499 = 3471749) B3471749
theorem B2314529 : Blo 1541468 2314529 := bstep (se 2 (by rfl) ⟨867948, by rfl⟩ : syracuseStep 2314529 = 1735897) B1735897
theorem B2314547 : Blo 1541468 2314547 := bstep (se 1 (by rfl) ⟨1735910, by rfl⟩ : syracuseStep 2314547 = 3471821) B3471821
theorem B2601281 : Blo 1541468 2601281 := bstep (se 2 (by rfl) ⟨975480, by rfl⟩ : syracuseStep 2601281 = 1950961) B1950961
theorem B2314577 : Blo 1541468 2314577 := bstep (se 2 (by rfl) ⟨867966, by rfl⟩ : syracuseStep 2314577 = 1735933) B1735933
theorem B2314595 : Blo 1541468 2314595 := bstep (se 1 (by rfl) ⟨1735946, by rfl⟩ : syracuseStep 2314595 = 3471893) B3471893
theorem B12513649 : Blo 1541468 12513649 := bstep (se 2 (by rfl) ⟨4692618, by rfl⟩ : syracuseStep 12513649 = 9385237) B9385237
theorem B2314625 : Blo 1541468 2314625 := bstep (se 2 (by rfl) ⟨867984, by rfl⟩ : syracuseStep 2314625 = 1735969) B1735969
theorem B9884045 : Blo 1541468 9884045 := bstep (se 3 (by rfl) ⟨1853258, by rfl⟩ : syracuseStep 9884045 = 3706517) B3706517
theorem B2314643 : Blo 1541468 2314643 := bstep (se 1 (by rfl) ⟨1735982, by rfl⟩ : syracuseStep 2314643 = 3471965) B3471965
theorem B2314673 : Blo 1541468 2314673 := bstep (se 2 (by rfl) ⟨868002, by rfl⟩ : syracuseStep 2314673 = 1736005) B1736005
theorem B2601409 : Blo 1541468 2601409 := bstep (se 2 (by rfl) ⟨975528, by rfl⟩ : syracuseStep 2601409 = 1951057) B1951057
theorem B2314691 : Blo 1541468 2314691 := bstep (se 1 (by rfl) ⟨1736018, by rfl⟩ : syracuseStep 2314691 = 3472037) B3472037
theorem B3707345 : Blo 1541468 3707345 := bstep (se 2 (by rfl) ⟨1390254, by rfl⟩ : syracuseStep 3707345 = 2780509) B2780509
theorem B2314721 : Blo 1541468 2314721 := bstep (se 2 (by rfl) ⟨868020, by rfl⟩ : syracuseStep 2314721 = 1736041) B1736041
theorem B2601443 : Blo 1541468 2601443 := bstep (se 1 (by rfl) ⟨1951082, by rfl⟩ : syracuseStep 2601443 = 3902165) B3902165
theorem B2314739 : Blo 1541468 2314739 := bstep (se 1 (by rfl) ⟨1736054, by rfl⟩ : syracuseStep 2314739 = 3472109) B3472109
theorem B3469841 : Blo 1541468 3469841 := bstep (se 2 (by rfl) ⟨1301190, by rfl⟩ : syracuseStep 3469841 = 2602381) B2602381
theorem B2314769 : Blo 1541468 2314769 := bstep (se 2 (by rfl) ⟨868038, by rfl⟩ : syracuseStep 2314769 = 1736077) B1736077
theorem B3469859 : Blo 1541468 3469859 := bstep (se 1 (by rfl) ⟨2602394, by rfl⟩ : syracuseStep 3469859 = 5204789) B5204789
theorem B2314787 : Blo 1541468 2314787 := bstep (se 1 (by rfl) ⟨1736090, by rfl⟩ : syracuseStep 2314787 = 3472181) B3472181
theorem B3707441 : Blo 1541468 3707441 := bstep (se 2 (by rfl) ⟨1390290, by rfl⟩ : syracuseStep 3707441 = 2780581) B2780581
theorem B2314817 : Blo 1541468 2314817 := bstep (se 2 (by rfl) ⟨868056, by rfl⟩ : syracuseStep 2314817 = 1736113) B1736113
theorem B8786501 : Blo 1541468 8786501 := bstep (se 4 (by rfl) ⟨823734, by rfl⟩ : syracuseStep 8786501 = 1647469) B1647469
theorem B2314835 : Blo 1541468 2314835 := bstep (se 1 (by rfl) ⟨1736126, by rfl⟩ : syracuseStep 2314835 = 3472253) B3472253
theorem B2601571 : Blo 1541468 2601571 := bstep (se 1 (by rfl) ⟨1951178, by rfl⟩ : syracuseStep 2601571 = 3902357) B3902357
theorem B9155171 : Blo 1541468 9155171 := bstep (se 1 (by rfl) ⟨6866378, by rfl⟩ : syracuseStep 9155171 = 13732757) B13732757
theorem B5853809 : Blo 1541468 5853809 := bstep (se 2 (by rfl) ⟨2195178, by rfl⟩ : syracuseStep 5853809 = 4390357) B4390357
theorem B2314865 : Blo 1541468 2314865 := bstep (se 2 (by rfl) ⟨868074, by rfl⟩ : syracuseStep 2314865 = 1736149) B1736149
theorem B2314883 : Blo 1541468 2314883 := bstep (se 1 (by rfl) ⟨1736162, by rfl⟩ : syracuseStep 2314883 = 3472325) B3472325
theorem B2929297 : Blo 1541468 2929297 := bstep (se 2 (by rfl) ⟨1098486, by rfl⟩ : syracuseStep 2929297 = 2196973) B2196973
theorem B2314913 : Blo 1541468 2314913 := bstep (se 2 (by rfl) ⟨868092, by rfl⟩ : syracuseStep 2314913 = 1736185) B1736185
theorem B2314931 : Blo 1541468 2314931 := bstep (se 1 (by rfl) ⟨1736198, by rfl⟩ : syracuseStep 2314931 = 3472397) B3472397
theorem B5206733 : Blo 1541468 5206733 := bstep (se 3 (by rfl) ⟨976262, by rfl⟩ : syracuseStep 5206733 = 1952525) B1952525
theorem B2314961 : Blo 1541468 2314961 := bstep (se 2 (by rfl) ⟨868110, by rfl⟩ : syracuseStep 2314961 = 1736221) B1736221
theorem B13349603 : Blo 1541468 13349603 := bstep (se 1 (by rfl) ⟨10012202, by rfl⟩ : syracuseStep 13349603 = 20024405) B20024405
theorem B2314979 : Blo 1541468 2314979 := bstep (se 1 (by rfl) ⟨1736234, by rfl⟩ : syracuseStep 2314979 = 3472469) B3472469
theorem B2601713 : Blo 1541468 2601713 := bstep (se 2 (by rfl) ⟨975642, by rfl⟩ : syracuseStep 2601713 = 1951285) B1951285
theorem B2315009 : Blo 1541468 2315009 := bstep (se 2 (by rfl) ⟨868128, by rfl⟩ : syracuseStep 2315009 = 1736257) B1736257
theorem B5206787 : Blo 1541468 5206787 := bstep (se 1 (by rfl) ⟨3905090, by rfl⟩ : syracuseStep 5206787 = 7810181) B7810181
theorem B2315027 : Blo 1541468 2315027 := bstep (se 1 (by rfl) ⟨1736270, by rfl⟩ : syracuseStep 2315027 = 3472541) B3472541
theorem B3470129 : Blo 1541468 3470129 := bstep (se 2 (by rfl) ⟨1301298, by rfl⟩ : syracuseStep 3470129 = 2602597) B2602597
theorem B2315057 : Blo 1541468 2315057 := bstep (se 2 (by rfl) ⟨868146, by rfl⟩ : syracuseStep 2315057 = 1736293) B1736293
theorem B3470147 : Blo 1541468 3470147 := bstep (se 1 (by rfl) ⟨2602610, by rfl⟩ : syracuseStep 3470147 = 5205221) B5205221
theorem B2315075 : Blo 1541468 2315075 := bstep (se 1 (by rfl) ⟨1736306, by rfl⟩ : syracuseStep 2315075 = 3472613) B3472613
theorem B2315105 : Blo 1541468 2315105 := bstep (se 2 (by rfl) ⟨868164, by rfl⟩ : syracuseStep 2315105 = 1736329) B1736329
theorem B2601841 : Blo 1541468 2601841 := bstep (se 2 (by rfl) ⟨975690, by rfl⟩ : syracuseStep 2601841 = 1951381) B1951381
theorem B2315123 : Blo 1541468 2315123 := bstep (se 1 (by rfl) ⟨1736342, by rfl⟩ : syracuseStep 2315123 = 3472685) B3472685
theorem B2315153 : Blo 1541468 2315153 := bstep (se 2 (by rfl) ⟨868182, by rfl⟩ : syracuseStep 2315153 = 1736365) B1736365
theorem B2601875 : Blo 1541468 2601875 := bstep (se 1 (by rfl) ⟨1951406, by rfl⟩ : syracuseStep 2601875 = 3902813) B3902813
theorem B2315171 : Blo 1541468 2315171 := bstep (se 1 (by rfl) ⟨1736378, by rfl⟩ : syracuseStep 2315171 = 3472757) B3472757
theorem B3904433 : Blo 1541468 3904433 := bstep (se 2 (by rfl) ⟨1464162, by rfl⟩ : syracuseStep 3904433 = 2928325) B2928325
theorem B2315201 : Blo 1541468 2315201 := bstep (se 2 (by rfl) ⟨868200, by rfl⟩ : syracuseStep 2315201 = 1736401) B1736401
theorem B2085841 : Blo 1541468 2085841 := bstep (se 2 (by rfl) ⟨782190, by rfl⟩ : syracuseStep 2085841 = 1564381) B1564381
theorem B3904483 : Blo 1541468 3904483 := bstep (se 1 (by rfl) ⟨2928362, by rfl⟩ : syracuseStep 3904483 = 5856725) B5856725
theorem B2470883 : Blo 1541468 2470883 := bstep (se 1 (by rfl) ⟨1853162, by rfl⟩ : syracuseStep 2470883 = 3706325) B3706325
theorem B5207057 : Blo 1541468 5207057 := bstep (se 2 (by rfl) ⟨1952646, by rfl⟩ : syracuseStep 5207057 = 3905293) B3905293
theorem B2602003 : Blo 1541468 2602003 := bstep (se 1 (by rfl) ⟨1951502, by rfl⟩ : syracuseStep 2602003 = 3903005) B3903005
theorem B2929699 : Blo 1541468 2929699 := bstep (se 1 (by rfl) ⟨2197274, by rfl⟩ : syracuseStep 2929699 = 4394549) B4394549
theorem B2470961 : Blo 1541468 2470961 := bstep (se 2 (by rfl) ⟨926610, by rfl⟩ : syracuseStep 2470961 = 1853221) B1853221
theorem B3470417 : Blo 1541468 3470417 := bstep (se 2 (by rfl) ⟨1301406, by rfl⟩ : syracuseStep 3470417 = 2602813) B2602813
theorem B2929745 : Blo 1541468 2929745 := bstep (se 2 (by rfl) ⟨1098654, by rfl⟩ : syracuseStep 2929745 = 2197309) B2197309
theorem B2085971 : Blo 1541468 2085971 := bstep (se 1 (by rfl) ⟨1564478, by rfl⟩ : syracuseStep 2085971 = 3128957) B3128957
theorem B3470435 : Blo 1541468 3470435 := bstep (se 1 (by rfl) ⟨2602826, by rfl⟩ : syracuseStep 3470435 = 5205653) B5205653
theorem B5010541 : Blo 1541468 5010541 := bstep (se 3 (by rfl) ⟨939476, by rfl⟩ : syracuseStep 5010541 = 1878953) B1878953
theorem B3904625 : Blo 1541468 3904625 := bstep (se 2 (by rfl) ⟨1464234, by rfl⟩ : syracuseStep 3904625 = 2928469) B2928469
theorem B9876613 : Blo 1541468 9876613 := bstep (se 4 (by rfl) ⟨925932, by rfl⟩ : syracuseStep 9876613 = 1851865) B1851865
theorem B2602145 : Blo 1541468 2602145 := bstep (se 2 (by rfl) ⟨975804, by rfl⟩ : syracuseStep 2602145 = 1951609) B1951609
theorem B2225377 : Blo 1541468 2225377 := bstep (se 2 (by rfl) ⟨834516, by rfl⟩ : syracuseStep 2225377 = 1669033) B1669033
theorem B5854477 : Blo 1541468 5854477 := bstep (se 3 (by rfl) ⟨1097714, by rfl⟩ : syracuseStep 5854477 = 2195429) B2195429
theorem B2471185 : Blo 1541468 2471185 := bstep (se 2 (by rfl) ⟨926694, by rfl⟩ : syracuseStep 2471185 = 1853389) B1853389
theorem B2602273 : Blo 1541468 2602273 := bstep (se 2 (by rfl) ⟨975852, by rfl⟩ : syracuseStep 2602273 = 1951705) B1951705
theorem B2602307 : Blo 1541468 2602307 := bstep (se 1 (by rfl) ⟨1951730, by rfl⟩ : syracuseStep 2602307 = 3903461) B3903461
theorem B16037189 : Blo 1541468 16037189 := bstep (se 4 (by rfl) ⟨1503486, by rfl⟩ : syracuseStep 16037189 = 3006973) B3006973
theorem B3470705 : Blo 1541468 3470705 := bstep (se 2 (by rfl) ⟨1301514, by rfl⟩ : syracuseStep 3470705 = 2603029) B2603029
theorem B2930033 : Blo 1541468 2930033 := bstep (se 2 (by rfl) ⟨1098762, by rfl⟩ : syracuseStep 2930033 = 2197525) B2197525
theorem B3470723 : Blo 1541468 3470723 := bstep (se 1 (by rfl) ⟨2603042, by rfl⟩ : syracuseStep 3470723 = 5206085) B5206085
theorem B2225569 : Blo 1541468 2225569 := bstep (se 2 (by rfl) ⟨834588, by rfl⟩ : syracuseStep 2225569 = 1669177) B1669177
theorem B2602435 : Blo 1541468 2602435 := bstep (se 1 (by rfl) ⟨1951826, by rfl⟩ : syracuseStep 2602435 = 3903653) B3903653
theorem B4167107 : Blo 1541468 4167107 := bstep (se 1 (by rfl) ⟨3125330, by rfl⟩ : syracuseStep 4167107 = 6250661) B6250661
theorem B6592013 : Blo 1541468 6592013 := bstep (se 3 (by rfl) ⟨1236002, by rfl⟩ : syracuseStep 6592013 = 2472005) B2472005
theorem B5207597 : Blo 1541468 5207597 := bstep (se 3 (by rfl) ⟨976424, by rfl⟩ : syracuseStep 5207597 = 1952849) B1952849
theorem B8336965 : Blo 1541468 8336965 := bstep (se 4 (by rfl) ⟨781590, by rfl⟩ : syracuseStep 8336965 = 1563181) B1563181
theorem B2602577 : Blo 1541468 2602577 := bstep (se 2 (by rfl) ⟨975966, by rfl⟩ : syracuseStep 2602577 = 1951933) B1951933
theorem B5207651 : Blo 1541468 5207651 := bstep (se 1 (by rfl) ⟨3905738, by rfl⟩ : syracuseStep 5207651 = 7811477) B7811477
theorem B11712113 : Blo 1541468 11712113 := bstep (se 2 (by rfl) ⟨4392042, by rfl⟩ : syracuseStep 11712113 = 8784085) B8784085
theorem B1734259 : Blo 1541468 1734259 := bstep (se 1 (by rfl) ⟨1300694, by rfl⟩ : syracuseStep 1734259 = 2601389) B2601389
theorem B3470993 : Blo 1541468 3470993 := bstep (se 2 (by rfl) ⟨1301622, by rfl⟩ : syracuseStep 3470993 = 2603245) B2603245
theorem B3471011 : Blo 1541468 3471011 := bstep (se 1 (by rfl) ⟨2603258, by rfl⟩ : syracuseStep 3471011 = 5206517) B5206517
theorem B9508549 : Blo 1541468 9508549 := bstep (se 4 (by rfl) ⟨891426, by rfl⟩ : syracuseStep 9508549 = 1782853) B1782853
theorem B2602705 : Blo 1541468 2602705 := bstep (se 2 (by rfl) ⟨976014, by rfl⟩ : syracuseStep 2602705 = 1952029) B1952029
theorem B6256369 : Blo 1541468 6256369 := bstep (se 2 (by rfl) ⟨2346138, by rfl⟩ : syracuseStep 6256369 = 4692277) B4692277
theorem B2602739 : Blo 1541468 2602739 := bstep (se 1 (by rfl) ⟨1952054, by rfl⟩ : syracuseStep 2602739 = 3904109) B3904109
theorem B1734403 : Blo 1541468 1734403 := bstep (se 1 (by rfl) ⟨1300802, by rfl⟩ : syracuseStep 1734403 = 2601605) B2601605
theorem B5207921 : Blo 1541468 5207921 := bstep (se 2 (by rfl) ⟨1952970, by rfl⟩ : syracuseStep 5207921 = 3905941) B3905941
theorem B2602867 : Blo 1541468 2602867 := bstep (se 1 (by rfl) ⟨1952150, by rfl⟩ : syracuseStep 2602867 = 3904301) B3904301
theorem B1734547 : Blo 1541468 1734547 := bstep (se 1 (by rfl) ⟨1300910, by rfl⟩ : syracuseStep 1734547 = 2601821) B2601821
theorem B7804835 : Blo 1541468 7804835 := bstep (se 1 (by rfl) ⟨5853626, by rfl⟩ : syracuseStep 7804835 = 11707253) B11707253
theorem B3168163 : Blo 1541468 3168163 := bstep (se 1 (by rfl) ⟨2376122, by rfl⟩ : syracuseStep 3168163 = 4752245) B4752245
theorem B3471281 : Blo 1541468 3471281 := bstep (se 2 (by rfl) ⟨1301730, by rfl⟩ : syracuseStep 3471281 = 2603461) B2603461
theorem B3471299 : Blo 1541468 3471299 := bstep (se 1 (by rfl) ⟨2603474, by rfl⟩ : syracuseStep 3471299 = 5206949) B5206949
theorem B2603009 : Blo 1541468 2603009 := bstep (se 2 (by rfl) ⟨976128, by rfl⟩ : syracuseStep 2603009 = 1952257) B1952257
theorem B1734691 : Blo 1541468 1734691 := bstep (se 1 (by rfl) ⟨1301018, by rfl⟩ : syracuseStep 1734691 = 2602037) B2602037
theorem B5855267 : Blo 1541468 5855267 := bstep (se 1 (by rfl) ⟨4391450, by rfl⟩ : syracuseStep 5855267 = 8782901) B8782901
theorem B5560397 : Blo 1541468 5560397 := bstep (se 3 (by rfl) ⟨1042574, by rfl⟩ : syracuseStep 5560397 = 2085149) B2085149
theorem B3905617 : Blo 1541468 3905617 := bstep (se 2 (by rfl) ⟨1464606, by rfl⟩ : syracuseStep 3905617 = 2929213) B2929213
theorem B2603137 : Blo 1541468 2603137 := bstep (se 2 (by rfl) ⟨976176, by rfl⟩ : syracuseStep 2603137 = 1952353) B1952353
theorem B1562771 : Blo 1541468 1562771 := bstep (se 1 (by rfl) ⟨1172078, by rfl⟩ : syracuseStep 1562771 = 2344157) B2344157
theorem B2603171 : Blo 1541468 2603171 := bstep (se 1 (by rfl) ⟨1952378, by rfl⟩ : syracuseStep 2603171 = 3904757) B3904757
theorem B1734835 : Blo 1541468 1734835 := bstep (se 1 (by rfl) ⟨1301126, by rfl⟩ : syracuseStep 1734835 = 2602253) B2602253
theorem B5560525 : Blo 1541468 5560525 := bstep (se 3 (by rfl) ⟨1042598, by rfl⟩ : syracuseStep 5560525 = 2085197) B2085197
theorem B3471569 : Blo 1541468 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B3471587 : Blo 1541468 3471587 := bstep (se 1 (by rfl) ⟨2603690, by rfl⟩ : syracuseStep 3471587 = 5207381) B5207381
theorem B4692205 : Blo 1541468 4692205 := bstep (se 3 (by rfl) ⟨879788, by rfl⟩ : syracuseStep 4692205 = 1759577) B1759577
theorem B4454669 : Blo 1541468 4454669 := bstep (se 3 (by rfl) ⟨835250, by rfl⟩ : syracuseStep 4454669 = 1670501) B1670501
theorem B2603299 : Blo 1541468 2603299 := bstep (se 1 (by rfl) ⟨1952474, by rfl⟩ : syracuseStep 2603299 = 3904949) B3904949
theorem B1734979 : Blo 1541468 1734979 := bstep (se 1 (by rfl) ⟨1301234, by rfl⟩ : syracuseStep 1734979 = 2602469) B2602469
theorem B3905891 : Blo 1541468 3905891 := bstep (se 1 (by rfl) ⟨2929418, by rfl⟩ : syracuseStep 3905891 = 5858837) B5858837
theorem B9378181 : Blo 1541468 9378181 := bstep (se 4 (by rfl) ⟨879204, by rfl⟩ : syracuseStep 9378181 = 1758409) B1758409
theorem B5208461 : Blo 1541468 5208461 := bstep (se 3 (by rfl) ⟨976586, by rfl⟩ : syracuseStep 5208461 = 1953173) B1953173
theorem B2603441 : Blo 1541468 2603441 := bstep (se 2 (by rfl) ⟨976290, by rfl⟩ : syracuseStep 2603441 = 1952581) B1952581
theorem B5208515 : Blo 1541468 5208515 := bstep (se 1 (by rfl) ⟨3906386, by rfl⟩ : syracuseStep 5208515 = 7812773) B7812773
theorem B8780237 : Blo 1541468 8780237 := bstep (se 3 (by rfl) ⟨1646294, by rfl⟩ : syracuseStep 8780237 = 3292589) B3292589
theorem B4168145 : Blo 1541468 4168145 := bstep (se 2 (by rfl) ⟨1563054, by rfl⟩ : syracuseStep 4168145 = 3126109) B3126109
theorem B1735123 : Blo 1541468 1735123 := bstep (se 1 (by rfl) ⟨1301342, by rfl⟩ : syracuseStep 1735123 = 2602685) B2602685
theorem B3471857 : Blo 1541468 3471857 := bstep (se 2 (by rfl) ⟨1301946, by rfl⟩ : syracuseStep 3471857 = 2603893) B2603893
theorem B3471875 : Blo 1541468 3471875 := bstep (se 1 (by rfl) ⟨2603906, by rfl⟩ : syracuseStep 3471875 = 5207813) B5207813
theorem B3906083 : Blo 1541468 3906083 := bstep (se 1 (by rfl) ⟨2929562, by rfl⟩ : syracuseStep 3906083 = 5859125) B5859125
theorem B2603569 : Blo 1541468 2603569 := bstep (se 2 (by rfl) ⟨976338, by rfl⟩ : syracuseStep 2603569 = 1952677) B1952677
theorem B17570357 : Blo 1541468 17570357 := bstep (se 5 (by rfl) ⟨823610, by rfl⟩ : syracuseStep 17570357 = 1647221) B1647221
theorem B2603603 : Blo 1541468 2603603 := bstep (se 1 (by rfl) ⟨1952702, by rfl⟩ : syracuseStep 2603603 = 3905405) B3905405
theorem B1735267 : Blo 1541468 1735267 := bstep (se 1 (by rfl) ⟨1301450, by rfl⟩ : syracuseStep 1735267 = 2602901) B2602901
theorem B7813745 : Blo 1541468 7813745 := bstep (se 2 (by rfl) ⟨2930154, by rfl⟩ : syracuseStep 7813745 = 5860309) B5860309
theorem B5855921 : Blo 1541468 5855921 := bstep (se 2 (by rfl) ⟨2195970, by rfl⟩ : syracuseStep 5855921 = 4391941) B4391941
theorem B7805645 : Blo 1541468 7805645 := bstep (se 3 (by rfl) ⟨1463558, by rfl⟩ : syracuseStep 7805645 = 2927117) B2927117
theorem B5208785 : Blo 1541468 5208785 := bstep (se 2 (by rfl) ⟨1953294, by rfl⟩ : syracuseStep 5208785 = 3906589) B3906589
theorem B2603731 : Blo 1541468 2603731 := bstep (se 1 (by rfl) ⟨1952798, by rfl⟩ : syracuseStep 2603731 = 3905597) B3905597
theorem B1735411 : Blo 1541468 1735411 := bstep (se 1 (by rfl) ⟨1301558, by rfl⟩ : syracuseStep 1735411 = 2603117) B2603117
theorem B3472145 : Blo 1541468 3472145 := bstep (se 2 (by rfl) ⟨1302054, by rfl⟩ : syracuseStep 3472145 = 2604109) B2604109
theorem B3472163 : Blo 1541468 3472163 := bstep (se 1 (by rfl) ⟨2604122, by rfl⟩ : syracuseStep 3472163 = 5208245) B5208245
theorem B2603873 : Blo 1541468 2603873 := bstep (se 2 (by rfl) ⟨976452, by rfl⟩ : syracuseStep 2603873 = 1952905) B1952905
theorem B1735555 : Blo 1541468 1735555 := bstep (se 1 (by rfl) ⟨1301666, by rfl⟩ : syracuseStep 1735555 = 2603333) B2603333
theorem B4938641 : Blo 1541468 4938641 := bstep (se 2 (by rfl) ⟨1851990, by rfl⟩ : syracuseStep 4938641 = 3703981) B3703981
theorem B4938691 : Blo 1541468 4938691 := bstep (se 1 (by rfl) ⟨3704018, by rfl⟩ : syracuseStep 4938691 = 7408037) B7408037
theorem B2604001 : Blo 1541468 2604001 := bstep (se 2 (by rfl) ⟨976500, by rfl⟩ : syracuseStep 2604001 = 1953001) B1953001
theorem B2604035 : Blo 1541468 2604035 := bstep (se 1 (by rfl) ⟨1953026, by rfl⟩ : syracuseStep 2604035 = 3906053) B3906053
theorem B1735699 : Blo 1541468 1735699 := bstep (se 1 (by rfl) ⟨1301774, by rfl⟩ : syracuseStep 1735699 = 2603549) B2603549
theorem B3472433 : Blo 1541468 3472433 := bstep (se 2 (by rfl) ⟨1302162, by rfl⟩ : syracuseStep 3472433 = 2604325) B2604325
theorem B3472451 : Blo 1541468 3472451 := bstep (se 1 (by rfl) ⟨2604338, by rfl⟩ : syracuseStep 3472451 = 5208677) B5208677
theorem B3955825 : Blo 1541468 3955825 := bstep (se 2 (by rfl) ⟨1483434, by rfl⟩ : syracuseStep 3955825 = 2966869) B2966869
theorem B2604163 : Blo 1541468 2604163 := bstep (se 1 (by rfl) ⟨1953122, by rfl⟩ : syracuseStep 2604163 = 3906245) B3906245
theorem B1735843 : Blo 1541468 1735843 := bstep (se 1 (by rfl) ⟨1301882, by rfl⟩ : syracuseStep 1735843 = 2603765) B2603765
theorem B21101795 : Blo 1541468 21101795 := bstep (se 1 (by rfl) ⟨15826346, by rfl⟩ : syracuseStep 21101795 = 31652693) B31652693
theorem B4390129 : Blo 1541468 4390129 := bstep (se 2 (by rfl) ⟨1646298, by rfl⟩ : syracuseStep 4390129 = 3292597) B3292597
theorem B2604305 : Blo 1541468 2604305 := bstep (se 2 (by rfl) ⟨976614, by rfl⟩ : syracuseStep 2604305 = 1953229) B1953229
theorem B1670419 : Blo 1541468 1670419 := bstep (se 1 (by rfl) ⟨1252814, by rfl⟩ : syracuseStep 1670419 = 2505629) B2505629
theorem B1735987 : Blo 1541468 1735987 := bstep (se 1 (by rfl) ⟨1301990, by rfl⟩ : syracuseStep 1735987 = 2603981) B2603981
theorem B13180229 : Blo 1541468 13180229 := bstep (se 4 (by rfl) ⟨1235646, by rfl⟩ : syracuseStep 13180229 = 2471293) B2471293
theorem B3472721 : Blo 1541468 3472721 := bstep (se 2 (by rfl) ⟨1302270, by rfl⟩ : syracuseStep 3472721 = 2604541) B2604541
theorem B3472739 : Blo 1541468 3472739 := bstep (se 1 (by rfl) ⟨2604554, by rfl⟩ : syracuseStep 3472739 = 5209109) B5209109
theorem B8781169 : Blo 1541468 8781169 := bstep (se 2 (by rfl) ⟨3292938, by rfl⟩ : syracuseStep 8781169 = 6585877) B6585877
theorem B2604433 : Blo 1541468 2604433 := bstep (se 2 (by rfl) ⟨976662, by rfl⟩ : syracuseStep 2604433 = 1953325) B1953325
theorem B2604467 : Blo 1541468 2604467 := bstep (se 1 (by rfl) ⟨1953350, by rfl⟩ : syracuseStep 2604467 = 3906701) B3906701
theorem B13172165 : Blo 1541468 13172165 := bstep (se 4 (by rfl) ⟨1234890, by rfl⟩ : syracuseStep 13172165 = 2469781) B2469781
theorem B1736131 : Blo 1541468 1736131 := bstep (se 1 (by rfl) ⟨1302098, by rfl⟩ : syracuseStep 1736131 = 2604197) B2604197
theorem B2604595 : Blo 1541468 2604595 := bstep (se 1 (by rfl) ⟨1953446, by rfl⟩ : syracuseStep 2604595 = 3906893) B3906893
theorem B77151797 : Blo 1541468 77151797 := bstep (se 5 (by rfl) ⟨3616490, by rfl⟩ : syracuseStep 77151797 = 7232981) B7232981
theorem B1736275 : Blo 1541468 1736275 := bstep (se 1 (by rfl) ⟨1302206, by rfl⟩ : syracuseStep 1736275 = 2604413) B2604413
theorem B3128963 : Blo 1541468 3128963 := bstep (se 1 (by rfl) ⟨2346722, by rfl⟩ : syracuseStep 3128963 = 4693445) B4693445
theorem B4169357 : Blo 1541468 4169357 := bstep (se 3 (by rfl) ⟨781754, by rfl⟩ : syracuseStep 4169357 = 1563509) B1563509
theorem B26353349 : Blo 1541468 26353349 := bstep (se 4 (by rfl) ⟨2470626, by rfl⟩ : syracuseStep 26353349 = 4941253) B4941253
theorem B5562083 : Blo 1541468 5562083 := bstep (se 1 (by rfl) ⟨4171562, by rfl⟩ : syracuseStep 5562083 = 8343125) B8343125
theorem B8339213 : Blo 1541468 8339213 := bstep (se 3 (by rfl) ⟨1563602, by rfl⟩ : syracuseStep 8339213 = 3127205) B3127205
theorem B4939537 : Blo 1541468 4939537 := bstep (se 2 (by rfl) ⟨1852326, by rfl⟩ : syracuseStep 4939537 = 3704653) B3704653
theorem B13180913 : Blo 1541468 13180913 := bstep (se 2 (by rfl) ⟨4942842, by rfl⟩ : syracuseStep 13180913 = 9885685) B9885685
theorem B5562371 : Blo 1541468 5562371 := bstep (se 1 (by rfl) ⟨4171778, by rfl⟩ : syracuseStep 5562371 = 8343557) B8343557
theorem B1646615 : Blo 1541468 1646615 := bstep (se 1 (by rfl) ⟨1234961, by rfl⟩ : syracuseStep 1646615 = 2469923) B2469923
theorem B2195543 : Blo 1541468 2195543 := bstep (se 1 (by rfl) ⟨1646657, by rfl⟩ : syracuseStep 2195543 = 3293315) B3293315
theorem B3293273 : Blo 1541468 3293273 := bstep (se 2 (by rfl) ⟨1234977, by rfl⟩ : syracuseStep 3293273 = 2469955) B2469955
theorem B5562589 : Blo 1541468 5562589 := bstep (se 3 (by rfl) ⟨1042985, by rfl⟩ : syracuseStep 5562589 = 2085971) B2085971
theorem B26362097 : Blo 1541468 26362097 := bstep (se 2 (by rfl) ⟨9885786, by rfl⟩ : syracuseStep 26362097 = 19771573) B19771573
theorem B7414033 : Blo 1541468 7414033 := bstep (se 2 (by rfl) ⟨2780262, by rfl⟩ : syracuseStep 7414033 = 5560525) B5560525
theorem B27066689 : Blo 1541468 27066689 := bstep (se 2 (by rfl) ⟨10150008, by rfl⟩ : syracuseStep 27066689 = 20300017) B20300017
theorem B5857667 : Blo 1541468 5857667 := bstep (se 1 (by rfl) ⟨4393250, by rfl⟩ : syracuseStep 5857667 = 8786501) B8786501
theorem B2195851 : Blo 1541468 2195851 := bstep (se 1 (by rfl) ⟨1646888, by rfl⟩ : syracuseStep 2195851 = 3293777) B3293777
theorem B26722885 : Blo 1541468 26722885 := bstep (se 4 (by rfl) ⟨2505270, by rfl⟩ : syracuseStep 26722885 = 5010541) B5010541
theorem B5202521 : Blo 1541468 5202521 := bstep (se 2 (by rfl) ⟨1950945, by rfl⟩ : syracuseStep 5202521 = 3901891) B3901891
theorem B1647307 : Blo 1541468 1647307 := bstep (se 1 (by rfl) ⟨1235480, by rfl⟩ : syracuseStep 1647307 = 2470961) B2470961
theorem B3294067 : Blo 1541468 3294067 := bstep (se 1 (by rfl) ⟨2470550, by rfl⟩ : syracuseStep 3294067 = 4941101) B4941101
theorem B10691459 : Blo 1541468 10691459 := bstep (se 1 (by rfl) ⟨8018594, by rfl⟩ : syracuseStep 10691459 = 16037189) B16037189
theorem B2778071 : Blo 1541468 2778071 := bstep (se 1 (by rfl) ⟨2083553, by rfl⟩ : syracuseStep 2778071 = 4167107) B4167107
theorem B6677569 : Blo 1541468 6677569 := bstep (se 2 (by rfl) ⟨2504088, by rfl⟩ : syracuseStep 6677569 = 5008177) B5008177
theorem B7808075 : Blo 1541468 7808075 := bstep (se 1 (by rfl) ⟨5856056, by rfl⟩ : syracuseStep 7808075 = 11712113) B11712113
theorem B4392157 : Blo 1541468 4392157 := bstep (se 3 (by rfl) ⟨823529, by rfl⟩ : syracuseStep 4392157 = 1647059) B1647059
theorem B33367301 : Blo 1541468 33367301 := bstep (se 4 (by rfl) ⟨3128184, by rfl⟩ : syracuseStep 33367301 = 6256369) B6256369
theorem B37545221 : Blo 1541468 37545221 := bstep (se 4 (by rfl) ⟨3519864, by rfl⟩ : syracuseStep 37545221 = 7039729) B7039729
theorem B5203223 : Blo 1541468 5203223 := bstep (se 1 (by rfl) ⟨3902417, by rfl⟩ : syracuseStep 5203223 = 7804835) B7804835
theorem B4392215 : Blo 1541468 4392215 := bstep (se 1 (by rfl) ⟨3294161, by rfl⟩ : syracuseStep 4392215 = 6588323) B6588323
theorem B6587723 : Blo 1541468 6587723 := bstep (se 1 (by rfl) ⟨4940792, by rfl⟩ : syracuseStep 6587723 = 9881585) B9881585
theorem B1541483 : Blo 1541468 1541483 := bstep (se 1 (by rfl) ⟨1156112, by rfl⟩ : syracuseStep 1541483 = 2312225) B2312225
theorem B1541495 : Blo 1541468 1541495 := bstep (se 1 (by rfl) ⟨1156121, by rfl⟩ : syracuseStep 1541495 = 2312243) B2312243
theorem B1541515 : Blo 1541468 1541515 := bstep (se 1 (by rfl) ⟨1156136, by rfl⟩ : syracuseStep 1541515 = 2312273) B2312273
theorem B1541527 : Blo 1541468 1541527 := bstep (se 1 (by rfl) ⟨1156145, by rfl⟩ : syracuseStep 1541527 = 2312291) B2312291
theorem B2196887 : Blo 1541468 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B1541547 : Blo 1541468 1541547 := bstep (se 1 (by rfl) ⟨1156160, by rfl⟩ : syracuseStep 1541547 = 2312321) B2312321
theorem B1541559 : Blo 1541468 1541559 := bstep (se 1 (by rfl) ⟨1156169, by rfl⟩ : syracuseStep 1541559 = 2312339) B2312339
theorem B1541579 : Blo 1541468 1541579 := bstep (se 1 (by rfl) ⟨1156184, by rfl⟩ : syracuseStep 1541579 = 2312369) B2312369
theorem B1541591 : Blo 1541468 1541591 := bstep (se 1 (by rfl) ⟨1156193, by rfl⟩ : syracuseStep 1541591 = 2312387) B2312387
theorem B1541611 : Blo 1541468 1541611 := bstep (se 1 (by rfl) ⟨1156208, by rfl⟩ : syracuseStep 1541611 = 2312417) B2312417
theorem B1541623 : Blo 1541468 1541623 := bstep (se 1 (by rfl) ⟨1156217, by rfl⟩ : syracuseStep 1541623 = 2312435) B2312435
theorem B1541643 : Blo 1541468 1541643 := bstep (se 1 (by rfl) ⟨1156232, by rfl⟩ : syracuseStep 1541643 = 2312465) B2312465
theorem B1541655 : Blo 1541468 1541655 := bstep (se 1 (by rfl) ⟨1156241, by rfl⟩ : syracuseStep 1541655 = 2312483) B2312483
theorem B1541675 : Blo 1541468 1541675 := bstep (se 1 (by rfl) ⟨1156256, by rfl⟩ : syracuseStep 1541675 = 2312513) B2312513
theorem B1541687 : Blo 1541468 1541687 := bstep (se 1 (by rfl) ⟨1156265, by rfl⟩ : syracuseStep 1541687 = 2312531) B2312531
theorem B1541707 : Blo 1541468 1541707 := bstep (se 1 (by rfl) ⟨1156280, by rfl⟩ : syracuseStep 1541707 = 2312561) B2312561
theorem B1541719 : Blo 1541468 1541719 := bstep (se 1 (by rfl) ⟨1156289, by rfl⟩ : syracuseStep 1541719 = 2312579) B2312579
theorem B2197081 : Blo 1541468 2197081 := bstep (se 2 (by rfl) ⟨823905, by rfl⟩ : syracuseStep 2197081 = 1647811) B1647811
theorem B24413789 : Blo 1541468 24413789 := bstep (se 3 (by rfl) ⟨4577585, by rfl⟩ : syracuseStep 24413789 = 9155171) B9155171
theorem B1541739 : Blo 1541468 1541739 := bstep (se 1 (by rfl) ⟨1156304, by rfl⟩ : syracuseStep 1541739 = 2312609) B2312609
theorem B1541751 : Blo 1541468 1541751 := bstep (se 1 (by rfl) ⟨1156313, by rfl⟩ : syracuseStep 1541751 = 2312627) B2312627
theorem B1541771 : Blo 1541468 1541771 := bstep (se 1 (by rfl) ⟨1156328, by rfl⟩ : syracuseStep 1541771 = 2312657) B2312657
theorem B1541783 : Blo 1541468 1541783 := bstep (se 1 (by rfl) ⟨1156337, by rfl⟩ : syracuseStep 1541783 = 2312675) B2312675
theorem B3704471 : Blo 1541468 3704471 := bstep (se 1 (by rfl) ⟨2778353, by rfl⟩ : syracuseStep 3704471 = 5556707) B5556707
theorem B1541803 : Blo 1541468 1541803 := bstep (se 1 (by rfl) ⟨1156352, by rfl⟩ : syracuseStep 1541803 = 2312705) B2312705
theorem B1541815 : Blo 1541468 1541815 := bstep (se 1 (by rfl) ⟨1156361, by rfl⟩ : syracuseStep 1541815 = 2312723) B2312723
theorem B3294913 : Blo 1541468 3294913 := bstep (se 2 (by rfl) ⟨1235592, by rfl⟩ : syracuseStep 3294913 = 2471185) B2471185
theorem B1541835 : Blo 1541468 1541835 := bstep (se 1 (by rfl) ⟨1156376, by rfl⟩ : syracuseStep 1541835 = 2312753) B2312753
theorem B1541847 : Blo 1541468 1541847 := bstep (se 1 (by rfl) ⟨1156385, by rfl⟩ : syracuseStep 1541847 = 2312771) B2312771
theorem B1951447 : Blo 1541468 1951447 := bstep (se 1 (by rfl) ⟨1463585, by rfl⟩ : syracuseStep 1951447 = 2927171) B2927171
theorem B1541867 : Blo 1541468 1541867 := bstep (se 1 (by rfl) ⟨1156400, by rfl⟩ : syracuseStep 1541867 = 2312801) B2312801
theorem B1541879 : Blo 1541468 1541879 := bstep (se 1 (by rfl) ⟨1156409, by rfl⟩ : syracuseStep 1541879 = 2312819) B2312819
theorem B1541899 : Blo 1541468 1541899 := bstep (se 1 (by rfl) ⟨1156424, by rfl⟩ : syracuseStep 1541899 = 2312849) B2312849
theorem B1541911 : Blo 1541468 1541911 := bstep (se 1 (by rfl) ⟨1156433, by rfl⟩ : syracuseStep 1541911 = 2312867) B2312867
theorem B1541931 : Blo 1541468 1541931 := bstep (se 1 (by rfl) ⟨1156448, by rfl⟩ : syracuseStep 1541931 = 2312897) B2312897
theorem B5203763 : Blo 1541468 5203763 := bstep (se 1 (by rfl) ⟨3902822, by rfl⟩ : syracuseStep 5203763 = 7805645) B7805645
theorem B1541943 : Blo 1541468 1541943 := bstep (se 1 (by rfl) ⟨1156457, by rfl⟩ : syracuseStep 1541943 = 2312915) B2312915
theorem B11708225 : Blo 1541468 11708225 := bstep (se 2 (by rfl) ⟨4390584, by rfl⟩ : syracuseStep 11708225 = 8781169) B8781169
theorem B1541963 : Blo 1541468 1541963 := bstep (se 1 (by rfl) ⟨1156472, by rfl⟩ : syracuseStep 1541963 = 2312945) B2312945
theorem B1541975 : Blo 1541468 1541975 := bstep (se 1 (by rfl) ⟨1156481, by rfl⟩ : syracuseStep 1541975 = 2312963) B2312963
theorem B1541995 : Blo 1541468 1541995 := bstep (se 1 (by rfl) ⟨1156496, by rfl⟩ : syracuseStep 1541995 = 2312993) B2312993
theorem B1542007 : Blo 1541468 1542007 := bstep (se 1 (by rfl) ⟨1156505, by rfl⟩ : syracuseStep 1542007 = 2313011) B2313011
theorem B2967425 : Blo 1541468 2967425 := bstep (se 2 (by rfl) ⟨1112784, by rfl⟩ : syracuseStep 2967425 = 2225569) B2225569
theorem B1542027 : Blo 1541468 1542027 := bstep (se 1 (by rfl) ⟨1156520, by rfl⟩ : syracuseStep 1542027 = 2313041) B2313041
theorem B1542039 : Blo 1541468 1542039 := bstep (se 1 (by rfl) ⟨1156529, by rfl⟩ : syracuseStep 1542039 = 2313059) B2313059
theorem B1542059 : Blo 1541468 1542059 := bstep (se 1 (by rfl) ⟨1156544, by rfl⟩ : syracuseStep 1542059 = 2313089) B2313089
theorem B1542071 : Blo 1541468 1542071 := bstep (se 1 (by rfl) ⟨1156553, by rfl⟩ : syracuseStep 1542071 = 2313107) B2313107
theorem B3958721 : Blo 1541468 3958721 := bstep (se 2 (by rfl) ⟨1484520, by rfl⟩ : syracuseStep 3958721 = 2969041) B2969041
theorem B1542091 : Blo 1541468 1542091 := bstep (se 1 (by rfl) ⟨1156568, by rfl⟩ : syracuseStep 1542091 = 2313137) B2313137
theorem B1542103 : Blo 1541468 1542103 := bstep (se 1 (by rfl) ⟨1156577, by rfl⟩ : syracuseStep 1542103 = 2313155) B2313155
theorem B1542123 : Blo 1541468 1542123 := bstep (se 1 (by rfl) ⟨1156592, by rfl⟩ : syracuseStep 1542123 = 2313185) B2313185
theorem B1542135 : Blo 1541468 1542135 := bstep (se 1 (by rfl) ⟨1156601, by rfl⟩ : syracuseStep 1542135 = 2313203) B2313203
theorem B1542155 : Blo 1541468 1542155 := bstep (se 1 (by rfl) ⟨1156616, by rfl⟩ : syracuseStep 1542155 = 2313233) B2313233
theorem B1542167 : Blo 1541468 1542167 := bstep (se 1 (by rfl) ⟨1156625, by rfl⟩ : syracuseStep 1542167 = 2313251) B2313251
theorem B3295255 : Blo 1541468 3295255 := bstep (se 1 (by rfl) ⟨2471441, by rfl⟩ : syracuseStep 3295255 = 4942883) B4942883
theorem B1542187 : Blo 1541468 1542187 := bstep (se 1 (by rfl) ⟨1156640, by rfl⟩ : syracuseStep 1542187 = 2313281) B2313281
theorem B1542199 : Blo 1541468 1542199 := bstep (se 1 (by rfl) ⟨1156649, by rfl⟩ : syracuseStep 1542199 = 2313299) B2313299
theorem B5204033 : Blo 1541468 5204033 := bstep (se 2 (by rfl) ⟨1951512, by rfl⟩ : syracuseStep 5204033 = 3903025) B3903025
theorem B2312267 : Blo 1541468 2312267 := bstep (se 1 (by rfl) ⟨1734200, by rfl⟩ : syracuseStep 2312267 = 3468401) B3468401
theorem B1542219 : Blo 1541468 1542219 := bstep (se 1 (by rfl) ⟨1156664, by rfl⟩ : syracuseStep 1542219 = 2313329) B2313329
theorem B2312279 : Blo 1541468 2312279 := bstep (se 1 (by rfl) ⟨1734209, by rfl⟩ : syracuseStep 2312279 = 3468419) B3468419
theorem B1542231 : Blo 1541468 1542231 := bstep (se 1 (by rfl) ⟨1156673, by rfl⟩ : syracuseStep 1542231 = 2313347) B2313347
theorem B1542251 : Blo 1541468 1542251 := bstep (se 1 (by rfl) ⟨1156688, by rfl⟩ : syracuseStep 1542251 = 2313377) B2313377
theorem B1542263 : Blo 1541468 1542263 := bstep (se 1 (by rfl) ⟨1156697, by rfl⟩ : syracuseStep 1542263 = 2313395) B2313395
theorem B1542283 : Blo 1541468 1542283 := bstep (se 1 (by rfl) ⟨1156712, by rfl⟩ : syracuseStep 1542283 = 2313425) B2313425
theorem B14067863 : Blo 1541468 14067863 := bstep (se 1 (by rfl) ⟨10550897, by rfl⟩ : syracuseStep 14067863 = 21101795) B21101795
theorem B1542295 : Blo 1541468 1542295 := bstep (se 1 (by rfl) ⟨1156721, by rfl⟩ : syracuseStep 1542295 = 2313443) B2313443
theorem B2312345 : Blo 1541468 2312345 := bstep (se 2 (by rfl) ⟨867129, by rfl⟩ : syracuseStep 2312345 = 1734259) B1734259
theorem B1542315 : Blo 1541468 1542315 := bstep (se 1 (by rfl) ⟨1156736, by rfl⟩ : syracuseStep 1542315 = 2313473) B2313473
theorem B1542327 : Blo 1541468 1542327 := bstep (se 1 (by rfl) ⟨1156745, by rfl⟩ : syracuseStep 1542327 = 2313491) B2313491
theorem B1542347 : Blo 1541468 1542347 := bstep (se 1 (by rfl) ⟨1156760, by rfl⟩ : syracuseStep 1542347 = 2313521) B2313521
theorem B1542359 : Blo 1541468 1542359 := bstep (se 1 (by rfl) ⟨1156769, by rfl⟩ : syracuseStep 1542359 = 2313539) B2313539
theorem B1542379 : Blo 1541468 1542379 := bstep (se 1 (by rfl) ⟨1156784, by rfl⟩ : syracuseStep 1542379 = 2313569) B2313569
theorem B1542391 : Blo 1541468 1542391 := bstep (se 1 (by rfl) ⟨1156793, by rfl⟩ : syracuseStep 1542391 = 2313587) B2313587
theorem B2312459 : Blo 1541468 2312459 := bstep (se 1 (by rfl) ⟨1734344, by rfl⟩ : syracuseStep 2312459 = 3468689) B3468689
theorem B1542411 : Blo 1541468 1542411 := bstep (se 1 (by rfl) ⟨1156808, by rfl⟩ : syracuseStep 1542411 = 2313617) B2313617
theorem B2312471 : Blo 1541468 2312471 := bstep (se 1 (by rfl) ⟨1734353, by rfl⟩ : syracuseStep 2312471 = 3468707) B3468707
theorem B1542423 : Blo 1541468 1542423 := bstep (se 1 (by rfl) ⟨1156817, by rfl⟩ : syracuseStep 1542423 = 2313635) B2313635
theorem B1542443 : Blo 1541468 1542443 := bstep (se 1 (by rfl) ⟨1156832, by rfl⟩ : syracuseStep 1542443 = 2313665) B2313665
theorem B1542455 : Blo 1541468 1542455 := bstep (se 1 (by rfl) ⟨1156841, by rfl⟩ : syracuseStep 1542455 = 2313683) B2313683
theorem B1542475 : Blo 1541468 1542475 := bstep (se 1 (by rfl) ⟨1156856, by rfl⟩ : syracuseStep 1542475 = 2313713) B2313713
theorem B1542487 : Blo 1541468 1542487 := bstep (se 1 (by rfl) ⟨1156865, by rfl⟩ : syracuseStep 1542487 = 2313731) B2313731
theorem B2312537 : Blo 1541468 2312537 := bstep (se 2 (by rfl) ⟨867201, by rfl⟩ : syracuseStep 2312537 = 1734403) B1734403
theorem B1542507 : Blo 1541468 1542507 := bstep (se 1 (by rfl) ⟨1156880, by rfl⟩ : syracuseStep 1542507 = 2313761) B2313761
theorem B1542519 : Blo 1541468 1542519 := bstep (se 1 (by rfl) ⟨1156889, by rfl⟩ : syracuseStep 1542519 = 2313779) B2313779
theorem B1542539 : Blo 1541468 1542539 := bstep (se 1 (by rfl) ⟨1156904, by rfl⟩ : syracuseStep 1542539 = 2313809) B2313809
theorem B1542551 : Blo 1541468 1542551 := bstep (se 1 (by rfl) ⟨1156913, by rfl⟩ : syracuseStep 1542551 = 2313827) B2313827
theorem B1542571 : Blo 1541468 1542571 := bstep (se 1 (by rfl) ⟨1156928, by rfl⟩ : syracuseStep 1542571 = 2313857) B2313857
theorem B2779571 : Blo 1541468 2779571 := bstep (se 1 (by rfl) ⟨2084678, by rfl⟩ : syracuseStep 2779571 = 4169357) B4169357
theorem B1542583 : Blo 1541468 1542583 := bstep (se 1 (by rfl) ⟨1156937, by rfl⟩ : syracuseStep 1542583 = 2313875) B2313875
theorem B2312651 : Blo 1541468 2312651 := bstep (se 1 (by rfl) ⟨1734488, by rfl⟩ : syracuseStep 2312651 = 3468977) B3468977
theorem B1542603 : Blo 1541468 1542603 := bstep (se 1 (by rfl) ⟨1156952, by rfl⟩ : syracuseStep 1542603 = 2313905) B2313905
theorem B2312663 : Blo 1541468 2312663 := bstep (se 1 (by rfl) ⟨1734497, by rfl⟩ : syracuseStep 2312663 = 3468995) B3468995
theorem B1542615 : Blo 1541468 1542615 := bstep (se 1 (by rfl) ⟨1156961, by rfl⟩ : syracuseStep 1542615 = 2313923) B2313923
theorem B4393433 : Blo 1541468 4393433 := bstep (se 2 (by rfl) ⟨1647537, by rfl⟩ : syracuseStep 4393433 = 3295075) B3295075
theorem B1542635 : Blo 1541468 1542635 := bstep (se 1 (by rfl) ⟨1156976, by rfl⟩ : syracuseStep 1542635 = 2313953) B2313953
theorem B1542647 : Blo 1541468 1542647 := bstep (se 1 (by rfl) ⟨1156985, by rfl⟩ : syracuseStep 1542647 = 2313971) B2313971
theorem B1542667 : Blo 1541468 1542667 := bstep (se 1 (by rfl) ⟨1157000, by rfl⟩ : syracuseStep 1542667 = 2314001) B2314001
theorem B1542679 : Blo 1541468 1542679 := bstep (se 1 (by rfl) ⟨1157009, by rfl⟩ : syracuseStep 1542679 = 2314019) B2314019
theorem B2312729 : Blo 1541468 2312729 := bstep (se 2 (by rfl) ⟨867273, by rfl⟩ : syracuseStep 2312729 = 1734547) B1734547
theorem B1542699 : Blo 1541468 1542699 := bstep (se 1 (by rfl) ⟨1157024, by rfl⟩ : syracuseStep 1542699 = 2314049) B2314049
theorem B3902003 : Blo 1541468 3902003 := bstep (se 1 (by rfl) ⟨2926502, by rfl⟩ : syracuseStep 3902003 = 5853005) B5853005
theorem B1542711 : Blo 1541468 1542711 := bstep (se 1 (by rfl) ⟨1157033, by rfl⟩ : syracuseStep 1542711 = 2314067) B2314067
theorem B1542731 : Blo 1541468 1542731 := bstep (se 1 (by rfl) ⟨1157048, by rfl⟩ : syracuseStep 1542731 = 2314097) B2314097
theorem B4393547 : Blo 1541468 4393547 := bstep (se 1 (by rfl) ⟨3295160, by rfl⟩ : syracuseStep 4393547 = 6590321) B6590321
theorem B1542743 : Blo 1541468 1542743 := bstep (se 1 (by rfl) ⟨1157057, by rfl⟩ : syracuseStep 1542743 = 2314115) B2314115
theorem B5204573 : Blo 1541468 5204573 := bstep (se 3 (by rfl) ⟨975857, by rfl⟩ : syracuseStep 5204573 = 1951715) B1951715
theorem B6589021 : Blo 1541468 6589021 := bstep (se 3 (by rfl) ⟨1235441, by rfl⟩ : syracuseStep 6589021 = 2470883) B2470883
theorem B1542763 : Blo 1541468 1542763 := bstep (se 1 (by rfl) ⟨1157072, by rfl⟩ : syracuseStep 1542763 = 2314145) B2314145
theorem B1542775 : Blo 1541468 1542775 := bstep (se 1 (by rfl) ⟨1157081, by rfl⟩ : syracuseStep 1542775 = 2314163) B2314163
theorem B2312843 : Blo 1541468 2312843 := bstep (se 1 (by rfl) ⟨1734632, by rfl⟩ : syracuseStep 2312843 = 3469265) B3469265
theorem B1542795 : Blo 1541468 1542795 := bstep (se 1 (by rfl) ⟨1157096, by rfl⟩ : syracuseStep 1542795 = 2314193) B2314193
theorem B2312855 : Blo 1541468 2312855 := bstep (se 1 (by rfl) ⟨1734641, by rfl⟩ : syracuseStep 2312855 = 3469283) B3469283
theorem B1542807 : Blo 1541468 1542807 := bstep (se 1 (by rfl) ⟨1157105, by rfl⟩ : syracuseStep 1542807 = 2314211) B2314211
theorem B2779801 : Blo 1541468 2779801 := bstep (se 2 (by rfl) ⟨1042425, by rfl⟩ : syracuseStep 2779801 = 2084851) B2084851
theorem B1542827 : Blo 1541468 1542827 := bstep (se 1 (by rfl) ⟨1157120, by rfl⟩ : syracuseStep 1542827 = 2314241) B2314241
theorem B1542839 : Blo 1541468 1542839 := bstep (se 1 (by rfl) ⟨1157129, by rfl⟩ : syracuseStep 1542839 = 2314259) B2314259
theorem B1542859 : Blo 1541468 1542859 := bstep (se 1 (by rfl) ⟨1157144, by rfl⟩ : syracuseStep 1542859 = 2314289) B2314289
theorem B1542871 : Blo 1541468 1542871 := bstep (se 1 (by rfl) ⟨1157153, by rfl⟩ : syracuseStep 1542871 = 2314307) B2314307
theorem B2312921 : Blo 1541468 2312921 := bstep (se 2 (by rfl) ⟨867345, by rfl⟩ : syracuseStep 2312921 = 1734691) B1734691
theorem B1542891 : Blo 1541468 1542891 := bstep (se 1 (by rfl) ⟨1157168, by rfl⟩ : syracuseStep 1542891 = 2314337) B2314337
theorem B1542903 : Blo 1541468 1542903 := bstep (se 1 (by rfl) ⟨1157177, by rfl⟩ : syracuseStep 1542903 = 2314355) B2314355
theorem B1542923 : Blo 1541468 1542923 := bstep (se 1 (by rfl) ⟨1157192, by rfl⟩ : syracuseStep 1542923 = 2314385) B2314385
theorem B1542935 : Blo 1541468 1542935 := bstep (se 1 (by rfl) ⟨1157201, by rfl⟩ : syracuseStep 1542935 = 2314403) B2314403
theorem B1542955 : Blo 1541468 1542955 := bstep (se 1 (by rfl) ⟨1157216, by rfl⟩ : syracuseStep 1542955 = 2314433) B2314433
theorem B14822189 : Blo 1541468 14822189 := bstep (se 3 (by rfl) ⟨2779160, by rfl⟩ : syracuseStep 14822189 = 5558321) B5558321
theorem B1542967 : Blo 1541468 1542967 := bstep (se 1 (by rfl) ⟨1157225, by rfl⟩ : syracuseStep 1542967 = 2314451) B2314451
theorem B7809857 : Blo 1541468 7809857 := bstep (se 2 (by rfl) ⟨2928696, by rfl⟩ : syracuseStep 7809857 = 5857393) B5857393
theorem B2313035 : Blo 1541468 2313035 := bstep (se 1 (by rfl) ⟨1734776, by rfl⟩ : syracuseStep 2313035 = 3469553) B3469553
theorem B1542987 : Blo 1541468 1542987 := bstep (se 1 (by rfl) ⟨1157240, by rfl⟩ : syracuseStep 1542987 = 2314481) B2314481
theorem B2313047 : Blo 1541468 2313047 := bstep (se 1 (by rfl) ⟨1734785, by rfl⟩ : syracuseStep 2313047 = 3469571) B3469571
theorem B1542999 : Blo 1541468 1542999 := bstep (se 1 (by rfl) ⟨1157249, by rfl⟩ : syracuseStep 1542999 = 2314499) B2314499
theorem B1543019 : Blo 1541468 1543019 := bstep (se 1 (by rfl) ⟨1157264, by rfl⟩ : syracuseStep 1543019 = 2314529) B2314529
theorem B1543031 : Blo 1541468 1543031 := bstep (se 1 (by rfl) ⟨1157273, by rfl⟩ : syracuseStep 1543031 = 2314547) B2314547
theorem B1543051 : Blo 1541468 1543051 := bstep (se 1 (by rfl) ⟨1157288, by rfl⟩ : syracuseStep 1543051 = 2314577) B2314577
theorem B1543063 : Blo 1541468 1543063 := bstep (se 1 (by rfl) ⟨1157297, by rfl⟩ : syracuseStep 1543063 = 2314595) B2314595
theorem B2313113 : Blo 1541468 2313113 := bstep (se 2 (by rfl) ⟨867417, by rfl⟩ : syracuseStep 2313113 = 1734835) B1734835
theorem B1543083 : Blo 1541468 1543083 := bstep (se 1 (by rfl) ⟨1157312, by rfl⟩ : syracuseStep 1543083 = 2314625) B2314625
theorem B6589363 : Blo 1541468 6589363 := bstep (se 1 (by rfl) ⟨4942022, by rfl⟩ : syracuseStep 6589363 = 9884045) B9884045
theorem B1543095 : Blo 1541468 1543095 := bstep (se 1 (by rfl) ⟨1157321, by rfl⟩ : syracuseStep 1543095 = 2314643) B2314643
theorem B1543115 : Blo 1541468 1543115 := bstep (se 1 (by rfl) ⟨1157336, by rfl⟩ : syracuseStep 1543115 = 2314673) B2314673
theorem B3337175 : Blo 1541468 3337175 := bstep (se 1 (by rfl) ⟨2502881, by rfl⟩ : syracuseStep 3337175 = 5005763) B5005763
theorem B2780119 : Blo 1541468 2780119 := bstep (se 1 (by rfl) ⟨2085089, by rfl⟩ : syracuseStep 2780119 = 4170179) B4170179
theorem B1543127 : Blo 1541468 1543127 := bstep (se 1 (by rfl) ⟨1157345, by rfl⟩ : syracuseStep 1543127 = 2314691) B2314691
theorem B1543147 : Blo 1541468 1543147 := bstep (se 1 (by rfl) ⟨1157360, by rfl⟩ : syracuseStep 1543147 = 2314721) B2314721
theorem B2927603 : Blo 1541468 2927603 := bstep (se 1 (by rfl) ⟨2195702, by rfl⟩ : syracuseStep 2927603 = 4391405) B4391405
theorem B2780147 : Blo 1541468 2780147 := bstep (se 1 (by rfl) ⟨2085110, by rfl⟩ : syracuseStep 2780147 = 4170221) B4170221
theorem B1543159 : Blo 1541468 1543159 := bstep (se 1 (by rfl) ⟨1157369, by rfl⟩ : syracuseStep 1543159 = 2314739) B2314739
theorem B2313227 : Blo 1541468 2313227 := bstep (se 1 (by rfl) ⟨1734920, by rfl⟩ : syracuseStep 2313227 = 3469841) B3469841
theorem B1543179 : Blo 1541468 1543179 := bstep (se 1 (by rfl) ⟨1157384, by rfl⟩ : syracuseStep 1543179 = 2314769) B2314769
theorem B3468311 : Blo 1541468 3468311 := bstep (se 1 (by rfl) ⟨2601233, by rfl⟩ : syracuseStep 3468311 = 5202467) B5202467
theorem B2313239 : Blo 1541468 2313239 := bstep (se 1 (by rfl) ⟨1734929, by rfl⟩ : syracuseStep 2313239 = 3469859) B3469859
theorem B1543191 : Blo 1541468 1543191 := bstep (se 1 (by rfl) ⟨1157393, by rfl⟩ : syracuseStep 1543191 = 2314787) B2314787
theorem B1543211 : Blo 1541468 1543211 := bstep (se 1 (by rfl) ⟨1157408, by rfl⟩ : syracuseStep 1543211 = 2314817) B2314817
theorem B1543223 : Blo 1541468 1543223 := bstep (se 1 (by rfl) ⟨1157417, by rfl⟩ : syracuseStep 1543223 = 2314835) B2314835
theorem B3902539 : Blo 1541468 3902539 := bstep (se 1 (by rfl) ⟨2926904, by rfl⟩ : syracuseStep 3902539 = 5853809) B5853809
theorem B1543243 : Blo 1541468 1543243 := bstep (se 1 (by rfl) ⟨1157432, by rfl⟩ : syracuseStep 1543243 = 2314865) B2314865
theorem B1543255 : Blo 1541468 1543255 := bstep (se 1 (by rfl) ⟨1157441, by rfl⟩ : syracuseStep 1543255 = 2314883) B2314883
theorem B2313305 : Blo 1541468 2313305 := bstep (se 2 (by rfl) ⟨867489, by rfl⟩ : syracuseStep 2313305 = 1734979) B1734979
theorem B3517529 : Blo 1541468 3517529 := bstep (se 2 (by rfl) ⟨1319073, by rfl⟩ : syracuseStep 3517529 = 2638147) B2638147
theorem B1543275 : Blo 1541468 1543275 := bstep (se 1 (by rfl) ⟨1157456, by rfl⟩ : syracuseStep 1543275 = 2314913) B2314913
theorem B1543287 : Blo 1541468 1543287 := bstep (se 1 (by rfl) ⟨1157465, by rfl⟩ : syracuseStep 1543287 = 2314931) B2314931
theorem B2927755 : Blo 1541468 2927755 := bstep (se 1 (by rfl) ⟨2195816, by rfl⟩ : syracuseStep 2927755 = 4391633) B4391633
theorem B1543307 : Blo 1541468 1543307 := bstep (se 1 (by rfl) ⟨1157480, by rfl⟩ : syracuseStep 1543307 = 2314961) B2314961
theorem B8899735 : Blo 1541468 8899735 := bstep (se 1 (by rfl) ⟨6674801, by rfl⟩ : syracuseStep 8899735 = 13349603) B13349603
theorem B1543319 : Blo 1541468 1543319 := bstep (se 1 (by rfl) ⟨1157489, by rfl⟩ : syracuseStep 1543319 = 2314979) B2314979
theorem B1543339 : Blo 1541468 1543339 := bstep (se 1 (by rfl) ⟨1157504, by rfl⟩ : syracuseStep 1543339 = 2315009) B2315009
theorem B12504241 : Blo 1541468 12504241 := bstep (se 2 (by rfl) ⟨4689090, by rfl⟩ : syracuseStep 12504241 = 9378181) B9378181
theorem B1543351 : Blo 1541468 1543351 := bstep (se 1 (by rfl) ⟨1157513, by rfl⟩ : syracuseStep 1543351 = 2315027) B2315027
theorem B3468491 : Blo 1541468 3468491 := bstep (se 1 (by rfl) ⟨2601368, by rfl⟩ : syracuseStep 3468491 = 5202737) B5202737
theorem B2313419 : Blo 1541468 2313419 := bstep (se 1 (by rfl) ⟨1735064, by rfl⟩ : syracuseStep 2313419 = 3470129) B3470129
theorem B1543371 : Blo 1541468 1543371 := bstep (se 1 (by rfl) ⟨1157528, by rfl⟩ : syracuseStep 1543371 = 2315057) B2315057
theorem B2313431 : Blo 1541468 2313431 := bstep (se 1 (by rfl) ⟨1735073, by rfl⟩ : syracuseStep 2313431 = 3470147) B3470147
theorem B1543383 : Blo 1541468 1543383 := bstep (se 1 (by rfl) ⟨1157537, by rfl⟩ : syracuseStep 1543383 = 2315075) B2315075
theorem B3902681 : Blo 1541468 3902681 := bstep (se 2 (by rfl) ⟨1463505, by rfl⟩ : syracuseStep 3902681 = 2927011) B2927011
theorem B1543403 : Blo 1541468 1543403 := bstep (se 1 (by rfl) ⟨1157552, by rfl⟩ : syracuseStep 1543403 = 2315105) B2315105
theorem B1543415 : Blo 1541468 1543415 := bstep (se 1 (by rfl) ⟨1157561, by rfl⟩ : syracuseStep 1543415 = 2315123) B2315123
theorem B3468545 : Blo 1541468 3468545 := bstep (se 2 (by rfl) ⟨1300704, by rfl⟩ : syracuseStep 3468545 = 2601409) B2601409
theorem B1543435 : Blo 1541468 1543435 := bstep (se 1 (by rfl) ⟨1157576, by rfl⟩ : syracuseStep 1543435 = 2315153) B2315153
theorem B1543447 : Blo 1541468 1543447 := bstep (se 1 (by rfl) ⟨1157585, by rfl⟩ : syracuseStep 1543447 = 2315171) B2315171
theorem B2313497 : Blo 1541468 2313497 := bstep (se 2 (by rfl) ⟨867561, by rfl⟩ : syracuseStep 2313497 = 1735123) B1735123
theorem B1543467 : Blo 1541468 1543467 := bstep (se 1 (by rfl) ⟨1157600, by rfl⟩ : syracuseStep 1543467 = 2315201) B2315201
theorem B2313611 : Blo 1541468 2313611 := bstep (se 1 (by rfl) ⟨1735208, by rfl⟩ : syracuseStep 2313611 = 3470417) B3470417
theorem B1953163 : Blo 1541468 1953163 := bstep (se 1 (by rfl) ⟨1464872, by rfl⟩ : syracuseStep 1953163 = 2929745) B2929745
theorem B2313623 : Blo 1541468 2313623 := bstep (se 1 (by rfl) ⟨1735217, by rfl⟩ : syracuseStep 2313623 = 3470435) B3470435
theorem B3468761 : Blo 1541468 3468761 := bstep (se 2 (by rfl) ⟨1300785, by rfl⟩ : syracuseStep 3468761 = 2601571) B2601571
theorem B2928089 : Blo 1541468 2928089 := bstep (se 2 (by rfl) ⟨1098033, by rfl⟩ : syracuseStep 2928089 = 2196067) B2196067
theorem B2313689 : Blo 1541468 2313689 := bstep (se 2 (by rfl) ⟨867633, by rfl⟩ : syracuseStep 2313689 = 1735267) B1735267
theorem B3468851 : Blo 1541468 3468851 := bstep (se 1 (by rfl) ⟨2601638, by rfl⟩ : syracuseStep 3468851 = 5203277) B5203277
theorem B2313803 : Blo 1541468 2313803 := bstep (se 1 (by rfl) ⟨1735352, by rfl⟩ : syracuseStep 2313803 = 3470705) B3470705
theorem B3468887 : Blo 1541468 3468887 := bstep (se 1 (by rfl) ⟨2601665, by rfl⟩ : syracuseStep 3468887 = 5203331) B5203331
theorem B2313815 : Blo 1541468 2313815 := bstep (se 1 (by rfl) ⟨1735361, by rfl⟩ : syracuseStep 2313815 = 3470723) B3470723
theorem B2313881 : Blo 1541468 2313881 := bstep (se 2 (by rfl) ⟨867705, by rfl⟩ : syracuseStep 2313881 = 1735411) B1735411
theorem B4394675 : Blo 1541468 4394675 := bstep (se 1 (by rfl) ⟨3296006, by rfl⟩ : syracuseStep 4394675 = 6592013) B6592013
theorem B5205707 : Blo 1541468 5205707 := bstep (se 1 (by rfl) ⟨3904280, by rfl⟩ : syracuseStep 5205707 = 7808561) B7808561
theorem B11710169 : Blo 1541468 11710169 := bstep (se 2 (by rfl) ⟨4391313, by rfl⟩ : syracuseStep 11710169 = 8782627) B8782627
theorem B3469067 : Blo 1541468 3469067 := bstep (se 1 (by rfl) ⟨2601800, by rfl⟩ : syracuseStep 3469067 = 5203601) B5203601
theorem B2313995 : Blo 1541468 2313995 := bstep (se 1 (by rfl) ⟨1735496, by rfl⟩ : syracuseStep 2313995 = 3470993) B3470993
theorem B2314007 : Blo 1541468 2314007 := bstep (se 1 (by rfl) ⟨1735505, by rfl⟩ : syracuseStep 2314007 = 3471011) B3471011
theorem B3469121 : Blo 1541468 3469121 := bstep (se 2 (by rfl) ⟨1300920, by rfl⟩ : syracuseStep 3469121 = 2601841) B2601841
theorem B2314073 : Blo 1541468 2314073 := bstep (se 2 (by rfl) ⟨867777, by rfl⟩ : syracuseStep 2314073 = 1735555) B1735555
theorem B2314187 : Blo 1541468 2314187 := bstep (se 1 (by rfl) ⟨1735640, by rfl⟩ : syracuseStep 2314187 = 3471281) B3471281
theorem B2314199 : Blo 1541468 2314199 := bstep (se 1 (by rfl) ⟨1735649, by rfl⟩ : syracuseStep 2314199 = 3471299) B3471299
theorem B5205977 : Blo 1541468 5205977 := bstep (se 2 (by rfl) ⟨1952241, by rfl⟩ : syracuseStep 5205977 = 3904483) B3904483
theorem B2781143 : Blo 1541468 2781143 := bstep (se 1 (by rfl) ⟨2085857, by rfl⟩ : syracuseStep 2781143 = 4171715) B4171715
theorem B3903511 : Blo 1541468 3903511 := bstep (se 1 (by rfl) ⟨2927633, by rfl⟩ : syracuseStep 3903511 = 5855267) B5855267
theorem B3469337 : Blo 1541468 3469337 := bstep (se 2 (by rfl) ⟨1301001, by rfl⟩ : syracuseStep 3469337 = 2602003) B2602003
theorem B2314265 : Blo 1541468 2314265 := bstep (se 2 (by rfl) ⟨867849, by rfl⟩ : syracuseStep 2314265 = 1735699) B1735699
theorem B3125299 : Blo 1541468 3125299 := bstep (se 1 (by rfl) ⟨2343974, by rfl⟩ : syracuseStep 3125299 = 4687949) B4687949
theorem B3706931 : Blo 1541468 3706931 := bstep (se 1 (by rfl) ⟨2780198, by rfl⟩ : syracuseStep 3706931 = 5560397) B5560397
theorem B4395073 : Blo 1541468 4395073 := bstep (se 2 (by rfl) ⟨1648152, by rfl⟩ : syracuseStep 4395073 = 3296305) B3296305
theorem B2928727 : Blo 1541468 2928727 := bstep (se 1 (by rfl) ⟨2196545, by rfl⟩ : syracuseStep 2928727 = 4393091) B4393091
theorem B5009501 : Blo 1541468 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B3469427 : Blo 1541468 3469427 := bstep (se 1 (by rfl) ⟨2602070, by rfl⟩ : syracuseStep 3469427 = 5204141) B5204141
theorem B2314379 : Blo 1541468 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B3469463 : Blo 1541468 3469463 := bstep (se 1 (by rfl) ⟨2602097, by rfl⟩ : syracuseStep 3469463 = 5204195) B5204195
theorem B2314391 : Blo 1541468 2314391 := bstep (se 1 (by rfl) ⟨1735793, by rfl⟩ : syracuseStep 2314391 = 3471587) B3471587
theorem B13168817 : Blo 1541468 13168817 := bstep (se 2 (by rfl) ⟨4938306, by rfl⟩ : syracuseStep 13168817 = 9876613) B9876613
theorem B2969779 : Blo 1541468 2969779 := bstep (se 1 (by rfl) ⟨2227334, by rfl⟩ : syracuseStep 2969779 = 4454669) B4454669
theorem B2314457 : Blo 1541468 2314457 := bstep (se 2 (by rfl) ⟨867921, by rfl⟩ : syracuseStep 2314457 = 1735843) B1735843
theorem B11718917 : Blo 1541468 11718917 := bstep (se 4 (by rfl) ⟨1098648, by rfl⟩ : syracuseStep 11718917 = 2197297) B2197297
theorem B7516433 : Blo 1541468 7516433 := bstep (se 2 (by rfl) ⟨2818662, by rfl⟩ : syracuseStep 7516433 = 5637325) B5637325
theorem B5853491 : Blo 1541468 5853491 := bstep (se 1 (by rfl) ⟨4390118, by rfl⟩ : syracuseStep 5853491 = 8780237) B8780237
theorem B5853505 : Blo 1541468 5853505 := bstep (se 2 (by rfl) ⟨2195064, by rfl⟩ : syracuseStep 5853505 = 4390129) B4390129
theorem B3469643 : Blo 1541468 3469643 := bstep (se 1 (by rfl) ⟨2602232, by rfl⟩ : syracuseStep 3469643 = 5204465) B5204465
theorem B2314571 : Blo 1541468 2314571 := bstep (se 1 (by rfl) ⟨1735928, by rfl⟩ : syracuseStep 2314571 = 3471857) B3471857
theorem B2314583 : Blo 1541468 2314583 := bstep (se 1 (by rfl) ⟨1735937, by rfl⟩ : syracuseStep 2314583 = 3471875) B3471875
theorem B8343901 : Blo 1541468 8343901 := bstep (se 3 (by rfl) ⟨1564481, by rfl⟩ : syracuseStep 8343901 = 3128963) B3128963
theorem B24080741 : Blo 1541468 24080741 := bstep (se 4 (by rfl) ⟨2257569, by rfl⟩ : syracuseStep 24080741 = 4515139) B4515139
theorem B3469697 : Blo 1541468 3469697 := bstep (se 2 (by rfl) ⟨1301136, by rfl⟩ : syracuseStep 3469697 = 2602273) B2602273
theorem B2601355 : Blo 1541468 2601355 := bstep (se 1 (by rfl) ⟨1951016, by rfl⟩ : syracuseStep 2601355 = 3902033) B3902033
theorem B2314649 : Blo 1541468 2314649 := bstep (se 2 (by rfl) ⟨867993, by rfl⟩ : syracuseStep 2314649 = 1735987) B1735987
theorem B3903947 : Blo 1541468 3903947 := bstep (se 1 (by rfl) ⟨2927960, by rfl⟩ : syracuseStep 3903947 = 5855921) B5855921
theorem B2314763 : Blo 1541468 2314763 := bstep (se 1 (by rfl) ⟨1736072, by rfl⟩ : syracuseStep 2314763 = 3472145) B3472145
theorem B2314775 : Blo 1541468 2314775 := bstep (se 1 (by rfl) ⟨1736081, by rfl⟩ : syracuseStep 2314775 = 3472163) B3472163
theorem B2601497 : Blo 1541468 2601497 := bstep (se 2 (by rfl) ⟨975561, by rfl⟩ : syracuseStep 2601497 = 1951123) B1951123
theorem B3125849 : Blo 1541468 3125849 := bstep (se 2 (by rfl) ⟨1172193, by rfl⟩ : syracuseStep 3125849 = 2344387) B2344387
theorem B3469913 : Blo 1541468 3469913 := bstep (se 2 (by rfl) ⟨1301217, by rfl⟩ : syracuseStep 3469913 = 2602435) B2602435
theorem B2314841 : Blo 1541468 2314841 := bstep (se 2 (by rfl) ⟨868065, by rfl⟩ : syracuseStep 2314841 = 1736131) B1736131
theorem B5206679 : Blo 1541468 5206679 := bstep (se 1 (by rfl) ⟨3905009, by rfl⟩ : syracuseStep 5206679 = 7810019) B7810019
theorem B2601625 : Blo 1541468 2601625 := bstep (se 2 (by rfl) ⟨975609, by rfl⟩ : syracuseStep 2601625 = 1951219) B1951219
theorem B3470003 : Blo 1541468 3470003 := bstep (se 1 (by rfl) ⟨2602502, by rfl⟩ : syracuseStep 3470003 = 5205005) B5205005
theorem B2314955 : Blo 1541468 2314955 := bstep (se 1 (by rfl) ⟨1736216, by rfl⟩ : syracuseStep 2314955 = 3472433) B3472433
theorem B3470039 : Blo 1541468 3470039 := bstep (se 1 (by rfl) ⟨2602529, by rfl⟩ : syracuseStep 3470039 = 5205059) B5205059
theorem B4690649 : Blo 1541468 4690649 := bstep (se 2 (by rfl) ⟨1758993, by rfl⟩ : syracuseStep 4690649 = 3517987) B3517987
theorem B7811801 : Blo 1541468 7811801 := bstep (se 2 (by rfl) ⟨2929425, by rfl⟩ : syracuseStep 7811801 = 5858851) B5858851
theorem B2314967 : Blo 1541468 2314967 := bstep (se 1 (by rfl) ⟨1736225, by rfl⟩ : syracuseStep 2314967 = 3472451) B3472451
theorem B2315033 : Blo 1541468 2315033 := bstep (se 2 (by rfl) ⟨868137, by rfl⟩ : syracuseStep 2315033 = 1736275) B1736275
theorem B3904321 : Blo 1541468 3904321 := bstep (se 2 (by rfl) ⟨1464120, by rfl⟩ : syracuseStep 3904321 = 2928241) B2928241
theorem B16896869 : Blo 1541468 16896869 := bstep (se 4 (by rfl) ⟨1584081, by rfl⟩ : syracuseStep 16896869 = 3168163) B3168163
theorem B8786819 : Blo 1541468 8786819 := bstep (se 1 (by rfl) ⟨6590114, by rfl⟩ : syracuseStep 8786819 = 13180229) B13180229
theorem B3470219 : Blo 1541468 3470219 := bstep (se 1 (by rfl) ⟨2602664, by rfl⟩ : syracuseStep 3470219 = 5205329) B5205329
theorem B2929547 : Blo 1541468 2929547 := bstep (se 1 (by rfl) ⟨2197160, by rfl⟩ : syracuseStep 2929547 = 4394321) B4394321
theorem B2315147 : Blo 1541468 2315147 := bstep (se 1 (by rfl) ⟨1736360, by rfl⟩ : syracuseStep 2315147 = 3472721) B3472721
theorem B2315159 : Blo 1541468 2315159 := bstep (se 1 (by rfl) ⟨1736369, by rfl⟩ : syracuseStep 2315159 = 3472739) B3472739
theorem B12678065 : Blo 1541468 12678065 := bstep (se 2 (by rfl) ⟨4754274, by rfl⟩ : syracuseStep 12678065 = 9508549) B9508549
theorem B3470273 : Blo 1541468 3470273 := bstep (se 2 (by rfl) ⟨1301352, by rfl⟩ : syracuseStep 3470273 = 2602705) B2602705
theorem B2929601 : Blo 1541468 2929601 := bstep (se 2 (by rfl) ⟨1098600, by rfl⟩ : syracuseStep 2929601 = 2197201) B2197201
theorem B51434531 : Blo 1541468 51434531 := bstep (se 1 (by rfl) ⟨38575898, by rfl⟩ : syracuseStep 51434531 = 77151797) B77151797
theorem B2470999 : Blo 1541468 2470999 := bstep (se 1 (by rfl) ⟨1853249, by rfl⟩ : syracuseStep 2470999 = 3706499) B3706499
theorem B3519575 : Blo 1541468 3519575 := bstep (se 1 (by rfl) ⟨2639681, by rfl⟩ : syracuseStep 3519575 = 5279363) B5279363
theorem B17568899 : Blo 1541468 17568899 := bstep (se 1 (by rfl) ⟨13176674, by rfl⟩ : syracuseStep 17568899 = 26353349) B26353349
theorem B3708055 : Blo 1541468 3708055 := bstep (se 1 (by rfl) ⟨2781041, by rfl⟩ : syracuseStep 3708055 = 5562083) B5562083
theorem B3470489 : Blo 1541468 3470489 := bstep (se 2 (by rfl) ⟨1301433, by rfl⟩ : syracuseStep 3470489 = 2602867) B2602867
theorem B5559475 : Blo 1541468 5559475 := bstep (se 1 (by rfl) ⟨4169606, by rfl⟩ : syracuseStep 5559475 = 8339213) B8339213
theorem B5207219 : Blo 1541468 5207219 := bstep (se 1 (by rfl) ⟨3905414, by rfl⟩ : syracuseStep 5207219 = 7810829) B7810829
theorem B94926005 : Blo 1541468 94926005 := bstep (se 5 (by rfl) ⟨4449656, by rfl⟩ : syracuseStep 94926005 = 8899313) B8899313
theorem B2602199 : Blo 1541468 2602199 := bstep (se 1 (by rfl) ⟨1951649, by rfl⟩ : syracuseStep 2602199 = 3903299) B3903299
theorem B3470579 : Blo 1541468 3470579 := bstep (se 1 (by rfl) ⟨2602934, by rfl⟩ : syracuseStep 3470579 = 5205869) B5205869
theorem B3470615 : Blo 1541468 3470615 := bstep (se 1 (by rfl) ⟨2602961, by rfl⟩ : syracuseStep 3470615 = 5205923) B5205923
theorem B8787275 : Blo 1541468 8787275 := bstep (se 1 (by rfl) ⟨6590456, by rfl⟩ : syracuseStep 8787275 = 13180913) B13180913
theorem B2602327 : Blo 1541468 2602327 := bstep (se 1 (by rfl) ⟨1951745, by rfl⟩ : syracuseStep 2602327 = 3903491) B3903491
theorem B6255965 : Blo 1541468 6255965 := bstep (se 3 (by rfl) ⟨1172993, by rfl⟩ : syracuseStep 6255965 = 2345987) B2345987
theorem B10704221 : Blo 1541468 10704221 := bstep (se 3 (by rfl) ⟨2007041, by rfl⟩ : syracuseStep 10704221 = 4014083) B4014083
theorem B3904919 : Blo 1541468 3904919 := bstep (se 1 (by rfl) ⟨2928689, by rfl⟩ : syracuseStep 3904919 = 5857379) B5857379
theorem B5207489 : Blo 1541468 5207489 := bstep (se 2 (by rfl) ⟨1952808, by rfl⟩ : syracuseStep 5207489 = 3905617) B3905617
theorem B3470795 : Blo 1541468 3470795 := bstep (se 1 (by rfl) ⟨2603096, by rfl⟩ : syracuseStep 3470795 = 5206193) B5206193
theorem B3470849 : Blo 1541468 3470849 := bstep (se 2 (by rfl) ⟨1301568, by rfl⟩ : syracuseStep 3470849 = 2603137) B2603137
theorem B1734187 : Blo 1541468 1734187 := bstep (se 1 (by rfl) ⟨1300640, by rfl⟩ : syracuseStep 1734187 = 2601281) B2601281
theorem B1758775 : Blo 1541468 1758775 := bstep (se 1 (by rfl) ⟨1319081, by rfl⟩ : syracuseStep 1758775 = 2638163) B2638163
theorem B7411265 : Blo 1541468 7411265 := bstep (se 2 (by rfl) ⟨2779224, by rfl⟩ : syracuseStep 7411265 = 5558449) B5558449
theorem B14816843 : Blo 1541468 14816843 := bstep (se 1 (by rfl) ⟨11112632, by rfl⟩ : syracuseStep 14816843 = 22225265) B22225265
theorem B2471563 : Blo 1541468 2471563 := bstep (se 1 (by rfl) ⟨1853672, by rfl⟩ : syracuseStep 2471563 = 3707345) B3707345
theorem B6256273 : Blo 1541468 6256273 := bstep (se 2 (by rfl) ⟨2346102, by rfl⟩ : syracuseStep 6256273 = 4692205) B4692205
theorem B1734295 : Blo 1541468 1734295 := bstep (se 1 (by rfl) ⟨1300721, by rfl⟩ : syracuseStep 1734295 = 2601443) B2601443
theorem B2471627 : Blo 1541468 2471627 := bstep (se 1 (by rfl) ⟨1853720, by rfl⟩ : syracuseStep 2471627 = 3707441) B3707441
theorem B3471065 : Blo 1541468 3471065 := bstep (se 2 (by rfl) ⟨1301649, by rfl⟩ : syracuseStep 3471065 = 2603299) B2603299
theorem B4167389 : Blo 1541468 4167389 := bstep (se 3 (by rfl) ⟨781385, by rfl⟩ : syracuseStep 4167389 = 1562771) B1562771
theorem B3471155 : Blo 1541468 3471155 := bstep (se 1 (by rfl) ⟨2603366, by rfl⟩ : syracuseStep 3471155 = 5206733) B5206733
theorem B16684865 : Blo 1541468 16684865 := bstep (se 2 (by rfl) ⟨6256824, by rfl⟩ : syracuseStep 16684865 = 12513649) B12513649
theorem B1734475 : Blo 1541468 1734475 := bstep (se 1 (by rfl) ⟨1300856, by rfl⟩ : syracuseStep 1734475 = 2601713) B2601713
theorem B3471191 : Blo 1541468 3471191 := bstep (se 1 (by rfl) ⟨2603393, by rfl⟩ : syracuseStep 3471191 = 5206787) B5206787
theorem B1734583 : Blo 1541468 1734583 := bstep (se 1 (by rfl) ⟨1300937, by rfl⟩ : syracuseStep 1734583 = 2601875) B2601875
theorem B2602955 : Blo 1541468 2602955 := bstep (se 1 (by rfl) ⟨1952216, by rfl⟩ : syracuseStep 2602955 = 3904433) B3904433
theorem B5208029 : Blo 1541468 5208029 := bstep (se 3 (by rfl) ⟨976505, by rfl⟩ : syracuseStep 5208029 = 1953011) B1953011
theorem B3471371 : Blo 1541468 3471371 := bstep (se 1 (by rfl) ⟨2603528, by rfl⟩ : syracuseStep 3471371 = 5207057) B5207057
theorem B3471425 : Blo 1541468 3471425 := bstep (se 2 (by rfl) ⟨1301784, by rfl⟩ : syracuseStep 3471425 = 2603569) B2603569
theorem B2603083 : Blo 1541468 2603083 := bstep (se 1 (by rfl) ⟨1952312, by rfl⟩ : syracuseStep 2603083 = 3904625) B3904625
theorem B1734763 : Blo 1541468 1734763 := bstep (se 1 (by rfl) ⟨1301072, by rfl⟩ : syracuseStep 1734763 = 2602145) B2602145
theorem B3905729 : Blo 1541468 3905729 := bstep (se 2 (by rfl) ⟨1464648, by rfl⟩ : syracuseStep 3905729 = 2929297) B2929297
theorem B5855435 : Blo 1541468 5855435 := bstep (se 1 (by rfl) ⟨4391576, by rfl⟩ : syracuseStep 5855435 = 8783153) B8783153
theorem B1734871 : Blo 1541468 1734871 := bstep (se 1 (by rfl) ⟨1301153, by rfl⟩ : syracuseStep 1734871 = 2602307) B2602307
theorem B5855449 : Blo 1541468 5855449 := bstep (se 2 (by rfl) ⟨2195793, by rfl⟩ : syracuseStep 5855449 = 4391587) B4391587
theorem B2603225 : Blo 1541468 2603225 := bstep (se 2 (by rfl) ⟨976209, by rfl⟩ : syracuseStep 2603225 = 1952419) B1952419
theorem B3471641 : Blo 1541468 3471641 := bstep (se 2 (by rfl) ⟨1301865, by rfl⟩ : syracuseStep 3471641 = 2603731) B2603731
theorem B7813421 : Blo 1541468 7813421 := bstep (se 3 (by rfl) ⟨1465016, by rfl⟩ : syracuseStep 7813421 = 2930033) B2930033
theorem B7919947 : Blo 1541468 7919947 := bstep (se 1 (by rfl) ⟨5939960, by rfl⟩ : syracuseStep 7919947 = 11879921) B11879921
theorem B2603353 : Blo 1541468 2603353 := bstep (se 2 (by rfl) ⟨976257, by rfl⟩ : syracuseStep 2603353 = 1952515) B1952515
theorem B3471731 : Blo 1541468 3471731 := bstep (se 1 (by rfl) ⟨2603798, by rfl⟩ : syracuseStep 3471731 = 5207597) B5207597
theorem B1735051 : Blo 1541468 1735051 := bstep (se 1 (by rfl) ⟨1301288, by rfl⟩ : syracuseStep 1735051 = 2602577) B2602577
theorem B3471767 : Blo 1541468 3471767 := bstep (se 1 (by rfl) ⟨2603825, by rfl⟩ : syracuseStep 3471767 = 5207651) B5207651
theorem B1735159 : Blo 1541468 1735159 := bstep (se 1 (by rfl) ⟨1301369, by rfl⟩ : syracuseStep 1735159 = 2602739) B2602739
theorem B11868677 : Blo 1541468 11868677 := bstep (se 4 (by rfl) ⟨1112688, by rfl⟩ : syracuseStep 11868677 = 2225377) B2225377
theorem B11115053 : Blo 1541468 11115053 := bstep (se 3 (by rfl) ⟨2084072, by rfl⟩ : syracuseStep 11115053 = 4168145) B4168145
theorem B3471947 : Blo 1541468 3471947 := bstep (se 1 (by rfl) ⟨2603960, by rfl⟩ : syracuseStep 3471947 = 5207921) B5207921
theorem B6584921 : Blo 1541468 6584921 := bstep (se 2 (by rfl) ⟨2469345, by rfl⟩ : syracuseStep 6584921 = 4938691) B4938691
theorem B3472001 : Blo 1541468 3472001 := bstep (se 2 (by rfl) ⟨1302000, by rfl⟩ : syracuseStep 3472001 = 2604001) B2604001
theorem B1735339 : Blo 1541468 1735339 := bstep (se 1 (by rfl) ⟨1301504, by rfl⟩ : syracuseStep 1735339 = 2603009) B2603009
theorem B3906265 : Blo 1541468 3906265 := bstep (se 2 (by rfl) ⟨1464849, by rfl⟩ : syracuseStep 3906265 = 2929699) B2929699
theorem B1735447 : Blo 1541468 1735447 := bstep (se 1 (by rfl) ⟨1301585, by rfl⟩ : syracuseStep 1735447 = 2603171) B2603171
theorem B5274433 : Blo 1541468 5274433 := bstep (se 2 (by rfl) ⟨1977912, by rfl⟩ : syracuseStep 5274433 = 3955825) B3955825
theorem B3472217 : Blo 1541468 3472217 := bstep (se 2 (by rfl) ⟨1302081, by rfl⟩ : syracuseStep 3472217 = 2604163) B2604163
theorem B2603927 : Blo 1541468 2603927 := bstep (se 1 (by rfl) ⟨1952945, by rfl⟩ : syracuseStep 2603927 = 3905891) B3905891
theorem B7035827 : Blo 1541468 7035827 := bstep (se 1 (by rfl) ⟨5276870, by rfl⟩ : syracuseStep 7035827 = 10553741) B10553741
theorem B3431347 : Blo 1541468 3431347 := bstep (se 1 (by rfl) ⟨2573510, by rfl⟩ : syracuseStep 3431347 = 5147021) B5147021
theorem B3472307 : Blo 1541468 3472307 := bstep (se 1 (by rfl) ⟨2604230, by rfl⟩ : syracuseStep 3472307 = 5208461) B5208461
theorem B1735627 : Blo 1541468 1735627 := bstep (se 1 (by rfl) ⟨1301720, by rfl⟩ : syracuseStep 1735627 = 2603441) B2603441
theorem B3472343 : Blo 1541468 3472343 := bstep (se 1 (by rfl) ⟨2604257, by rfl⟩ : syracuseStep 3472343 = 5208515) B5208515
theorem B7805969 : Blo 1541468 7805969 := bstep (se 2 (by rfl) ⟨2927238, by rfl⟩ : syracuseStep 7805969 = 5854477) B5854477
theorem B2604055 : Blo 1541468 2604055 := bstep (se 1 (by rfl) ⟨1953041, by rfl⟩ : syracuseStep 2604055 = 3906083) B3906083
theorem B2227225 : Blo 1541468 2227225 := bstep (se 2 (by rfl) ⟨835209, by rfl⟩ : syracuseStep 2227225 = 1670419) B1670419
theorem B11713571 : Blo 1541468 11713571 := bstep (se 1 (by rfl) ⟨8785178, by rfl⟩ : syracuseStep 11713571 = 17570357) B17570357
theorem B1735735 : Blo 1541468 1735735 := bstep (se 1 (by rfl) ⟨1301801, by rfl⟩ : syracuseStep 1735735 = 2603603) B2603603
theorem B5209163 : Blo 1541468 5209163 := bstep (se 1 (by rfl) ⟨3906872, by rfl⟩ : syracuseStep 5209163 = 7813745) B7813745
theorem B3472523 : Blo 1541468 3472523 := bstep (se 1 (by rfl) ⟨2604392, by rfl⟩ : syracuseStep 3472523 = 5208785) B5208785
theorem B5856407 : Blo 1541468 5856407 := bstep (se 1 (by rfl) ⟨4392305, by rfl⟩ : syracuseStep 5856407 = 8784611) B8784611
theorem B7806131 : Blo 1541468 7806131 := bstep (se 1 (by rfl) ⟨5854598, by rfl⟩ : syracuseStep 7806131 = 11709197) B11709197
theorem B3472577 : Blo 1541468 3472577 := bstep (se 2 (by rfl) ⟨1302216, by rfl⟩ : syracuseStep 3472577 = 2604433) B2604433
theorem B1735915 : Blo 1541468 1735915 := bstep (se 1 (by rfl) ⟨1301936, by rfl⟩ : syracuseStep 1735915 = 2603873) B2603873
theorem B3292427 : Blo 1541468 3292427 := bstep (se 1 (by rfl) ⟨2469320, by rfl⟩ : syracuseStep 3292427 = 4938641) B4938641
theorem B1736023 : Blo 1541468 1736023 := bstep (se 1 (by rfl) ⟨1302017, by rfl⟩ : syracuseStep 1736023 = 2604035) B2604035
theorem B3472793 : Blo 1541468 3472793 := bstep (se 2 (by rfl) ⟨1302297, by rfl⟩ : syracuseStep 3472793 = 2604595) B2604595
theorem B11115953 : Blo 1541468 11115953 := bstep (se 2 (by rfl) ⟨4168482, by rfl⟩ : syracuseStep 11115953 = 8336965) B8336965
theorem B1736203 : Blo 1541468 1736203 := bstep (se 1 (by rfl) ⟨1302152, by rfl⟩ : syracuseStep 1736203 = 2604305) B2604305
theorem B15228491 : Blo 1541468 15228491 := bstep (se 1 (by rfl) ⟨11421368, by rfl⟩ : syracuseStep 15228491 = 22842737) B22842737
theorem B1736311 : Blo 1541468 1736311 := bstep (se 1 (by rfl) ⟨1302233, by rfl⟩ : syracuseStep 1736311 = 2604467) B2604467
theorem B8781443 : Blo 1541468 8781443 := bstep (se 1 (by rfl) ⟨6586082, by rfl⟩ : syracuseStep 8781443 = 13172165) B13172165
theorem B6586049 : Blo 1541468 6586049 := bstep (se 2 (by rfl) ⟨2469768, by rfl⟩ : syracuseStep 6586049 = 4939537) B4939537
theorem B11124485 : Blo 1541468 11124485 := bstep (se 4 (by rfl) ⟨1042920, by rfl⟩ : syracuseStep 11124485 = 2085841) B2085841
theorem B11116439 : Blo 1541468 11116439 := bstep (se 1 (by rfl) ⟨8337329, by rfl⟩ : syracuseStep 11116439 = 16674659) B16674659
theorem B16670681 : Blo 1541468 16670681 := bstep (se 2 (by rfl) ⟨6251505, by rfl⟩ : syracuseStep 16670681 = 12503011) B12503011
theorem B2195515 : Blo 1541468 2195515 := bstep (se 1 (by rfl) ⟨1646636, by rfl⟩ : syracuseStep 2195515 = 3293273) B3293273
theorem B4390973 : Blo 1541468 4390973 := bstep (se 3 (by rfl) ⟨823307, by rfl⟩ : syracuseStep 4390973 = 1646615) B1646615
theorem B7807265 : Blo 1541468 7807265 := bstep (se 2 (by rfl) ⟨2927724, by rfl⟩ : syracuseStep 7807265 = 5855449) B5855449
theorem B11125201 : Blo 1541468 11125201 := bstep (se 2 (by rfl) ⟨4171950, by rfl⟩ : syracuseStep 11125201 = 8343901) B8343901
theorem B11264579 : Blo 1541468 11264579 := bstep (se 1 (by rfl) ⟨8448434, by rfl⟩ : syracuseStep 11264579 = 16896869) B16896869
theorem B7127639 : Blo 1541468 7127639 := bstep (se 1 (by rfl) ⟨5345729, by rfl⟩ : syracuseStep 7127639 = 10691459) B10691459
theorem B5857879 : Blo 1541468 5857879 := bstep (se 1 (by rfl) ⟨4393409, by rfl⟩ : syracuseStep 5857879 = 8786819) B8786819
theorem B63284003 : Blo 1541468 63284003 := bstep (se 1 (by rfl) ⟨47463002, by rfl⟩ : syracuseStep 63284003 = 94926005) B94926005
theorem B4391815 : Blo 1541468 4391815 := bstep (se 1 (by rfl) ⟨3293861, by rfl⟩ : syracuseStep 4391815 = 6587723) B6587723
theorem B5858183 : Blo 1541468 5858183 := bstep (se 1 (by rfl) ⟨4393637, by rfl⟩ : syracuseStep 5858183 = 8787275) B8787275
theorem B7136147 : Blo 1541468 7136147 := bstep (se 1 (by rfl) ⟨5352110, by rfl⟩ : syracuseStep 7136147 = 10704221) B10704221
theorem B37520309 : Blo 1541468 37520309 := bstep (se 5 (by rfl) ⟨1758764, by rfl⟩ : syracuseStep 37520309 = 3517529) B3517529
theorem B2196409 : Blo 1541468 2196409 := bstep (se 2 (by rfl) ⟨823653, by rfl⟩ : syracuseStep 2196409 = 1647307) B1647307
theorem B4940843 : Blo 1541468 4940843 := bstep (se 1 (by rfl) ⟨3705632, by rfl⟩ : syracuseStep 4940843 = 7411265) B7411265
theorem B5858365 : Blo 1541468 5858365 := bstep (se 3 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 5858365 = 2196887) B2196887
theorem B1647751 : Blo 1541468 1647751 := bstep (se 1 (by rfl) ⟨1235813, by rfl⟩ : syracuseStep 1647751 = 2471627) B2471627
theorem B4392089 : Blo 1541468 4392089 := bstep (se 2 (by rfl) ⟨1647033, by rfl⟩ : syracuseStep 4392089 = 3294067) B3294067
theorem B7808237 : Blo 1541468 7808237 := bstep (se 3 (by rfl) ⟨1464044, by rfl⟩ : syracuseStep 7808237 = 2928089) B2928089
theorem B2639147 : Blo 1541468 2639147 := bstep (se 1 (by rfl) ⟨1979360, by rfl⟩ : syracuseStep 2639147 = 3958721) B3958721
theorem B1541511 : Blo 1541468 1541511 := bstep (se 1 (by rfl) ⟨1156133, by rfl⟩ : syracuseStep 1541511 = 2312267) B2312267
theorem B1541519 : Blo 1541468 1541519 := bstep (se 1 (by rfl) ⟨1156139, by rfl⟩ : syracuseStep 1541519 = 2312279) B2312279
theorem B5203385 : Blo 1541468 5203385 := bstep (se 2 (by rfl) ⟨1951269, by rfl⟩ : syracuseStep 5203385 = 3902539) B3902539
theorem B1541563 : Blo 1541468 1541563 := bstep (se 1 (by rfl) ⟨1156172, by rfl⟩ : syracuseStep 1541563 = 2312345) B2312345
theorem B3294665 : Blo 1541468 3294665 := bstep (se 2 (by rfl) ⟨1235499, by rfl⟩ : syracuseStep 3294665 = 2470999) B2470999
theorem B1541639 : Blo 1541468 1541639 := bstep (se 1 (by rfl) ⟨1156229, by rfl⟩ : syracuseStep 1541639 = 2312459) B2312459
theorem B1541647 : Blo 1541468 1541647 := bstep (se 1 (by rfl) ⟨1156235, by rfl⟩ : syracuseStep 1541647 = 2312471) B2312471
theorem B1541691 : Blo 1541468 1541691 := bstep (se 1 (by rfl) ⟨1156268, by rfl⟩ : syracuseStep 1541691 = 2312537) B2312537
theorem B16672321 : Blo 1541468 16672321 := bstep (se 2 (by rfl) ⟨6252120, by rfl⟩ : syracuseStep 16672321 = 12504241) B12504241
theorem B65103437 : Blo 1541468 65103437 := bstep (se 3 (by rfl) ⟨12206894, by rfl⟩ : syracuseStep 65103437 = 24413789) B24413789
theorem B1853047 : Blo 1541468 1853047 := bstep (se 1 (by rfl) ⟨1389785, by rfl⟩ : syracuseStep 1853047 = 2779571) B2779571
theorem B1541767 : Blo 1541468 1541767 := bstep (se 1 (by rfl) ⟨1156325, by rfl⟩ : syracuseStep 1541767 = 2312651) B2312651
theorem B1541775 : Blo 1541468 1541775 := bstep (se 1 (by rfl) ⟨1156331, by rfl⟩ : syracuseStep 1541775 = 2312663) B2312663
theorem B1541819 : Blo 1541468 1541819 := bstep (se 1 (by rfl) ⟨1156364, by rfl⟩ : syracuseStep 1541819 = 2312729) B2312729
theorem B42239717 : Blo 1541468 42239717 := bstep (se 4 (by rfl) ⟨3959973, by rfl⟩ : syracuseStep 42239717 = 7919947) B7919947
theorem B1541895 : Blo 1541468 1541895 := bstep (se 1 (by rfl) ⟨1156421, by rfl⟩ : syracuseStep 1541895 = 2312843) B2312843
theorem B1541903 : Blo 1541468 1541903 := bstep (se 1 (by rfl) ⟨1156427, by rfl⟩ : syracuseStep 1541903 = 2312855) B2312855
theorem B1541947 : Blo 1541468 1541947 := bstep (se 1 (by rfl) ⟨1156460, by rfl⟩ : syracuseStep 1541947 = 2312921) B2312921
theorem B9881459 : Blo 1541468 9881459 := bstep (se 1 (by rfl) ⟨7411094, by rfl⟩ : syracuseStep 9881459 = 14822189) B14822189
theorem B1542023 : Blo 1541468 1542023 := bstep (se 1 (by rfl) ⟨1156517, by rfl⟩ : syracuseStep 1542023 = 2313035) B2313035
theorem B1542031 : Blo 1541468 1542031 := bstep (se 1 (by rfl) ⟨1156523, by rfl⟩ : syracuseStep 1542031 = 2313047) B2313047
theorem B1542075 : Blo 1541468 1542075 := bstep (se 1 (by rfl) ⟨1156556, by rfl⟩ : syracuseStep 1542075 = 2313113) B2313113
theorem B1542151 : Blo 1541468 1542151 := bstep (se 1 (by rfl) ⟨1156613, by rfl⟩ : syracuseStep 1542151 = 2313227) B2313227
theorem B5203979 : Blo 1541468 5203979 := bstep (se 1 (by rfl) ⟨3902984, by rfl⟩ : syracuseStep 5203979 = 7805969) B7805969
theorem B2312207 : Blo 1541468 2312207 := bstep (se 1 (by rfl) ⟨1734155, by rfl⟩ : syracuseStep 2312207 = 3468311) B3468311
theorem B1542159 : Blo 1541468 1542159 := bstep (se 1 (by rfl) ⟨1156619, by rfl⟩ : syracuseStep 1542159 = 2313239) B2313239
theorem B7809047 : Blo 1541468 7809047 := bstep (se 1 (by rfl) ⟨5856785, by rfl⟩ : syracuseStep 7809047 = 11713571) B11713571
theorem B2312249 : Blo 1541468 2312249 := bstep (se 2 (by rfl) ⟨867093, by rfl⟩ : syracuseStep 2312249 = 1734187) B1734187
theorem B1542203 : Blo 1541468 1542203 := bstep (se 1 (by rfl) ⟨1156652, by rfl⟩ : syracuseStep 1542203 = 2313305) B2313305
theorem B2345033 : Blo 1541468 2345033 := bstep (se 2 (by rfl) ⟨879387, by rfl⟩ : syracuseStep 2345033 = 1758775) B1758775
theorem B5204087 : Blo 1541468 5204087 := bstep (se 1 (by rfl) ⟨3903065, by rfl⟩ : syracuseStep 5204087 = 7806131) B7806131
theorem B2312327 : Blo 1541468 2312327 := bstep (se 1 (by rfl) ⟨1734245, by rfl⟩ : syracuseStep 2312327 = 3468491) B3468491
theorem B1542279 : Blo 1541468 1542279 := bstep (se 1 (by rfl) ⟨1156709, by rfl⟩ : syracuseStep 1542279 = 2313419) B2313419
theorem B1542287 : Blo 1541468 1542287 := bstep (se 1 (by rfl) ⟨1156715, by rfl⟩ : syracuseStep 1542287 = 2313431) B2313431
theorem B2312363 : Blo 1541468 2312363 := bstep (se 1 (by rfl) ⟨1734272, by rfl⟩ : syracuseStep 2312363 = 3468545) B3468545
theorem B3295417 : Blo 1541468 3295417 := bstep (se 2 (by rfl) ⟨1235781, by rfl⟩ : syracuseStep 3295417 = 2471563) B2471563
theorem B1542331 : Blo 1541468 1542331 := bstep (se 1 (by rfl) ⟨1156748, by rfl⟩ : syracuseStep 1542331 = 2313497) B2313497
theorem B8341697 : Blo 1541468 8341697 := bstep (se 2 (by rfl) ⟨3128136, by rfl⟩ : syracuseStep 8341697 = 6256273) B6256273
theorem B2312393 : Blo 1541468 2312393 := bstep (se 2 (by rfl) ⟨867147, by rfl⟩ : syracuseStep 2312393 = 1734295) B1734295
theorem B4393217 : Blo 1541468 4393217 := bstep (se 2 (by rfl) ⟨1647456, by rfl⟩ : syracuseStep 4393217 = 3294913) B3294913
theorem B1542407 : Blo 1541468 1542407 := bstep (se 1 (by rfl) ⟨1156805, by rfl⟩ : syracuseStep 1542407 = 2313611) B2313611
theorem B1542415 : Blo 1541468 1542415 := bstep (se 1 (by rfl) ⟨1156811, by rfl⟩ : syracuseStep 1542415 = 2313623) B2313623
theorem B2312507 : Blo 1541468 2312507 := bstep (se 1 (by rfl) ⟨1734380, by rfl⟩ : syracuseStep 2312507 = 3468761) B3468761
theorem B1542459 : Blo 1541468 1542459 := bstep (se 1 (by rfl) ⟨1156844, by rfl⟩ : syracuseStep 1542459 = 2313689) B2313689
theorem B2312567 : Blo 1541468 2312567 := bstep (se 1 (by rfl) ⟨1734425, by rfl⟩ : syracuseStep 2312567 = 3468851) B3468851
theorem B1542535 : Blo 1541468 1542535 := bstep (se 1 (by rfl) ⟨1156901, by rfl⟩ : syracuseStep 1542535 = 2313803) B2313803
theorem B2312591 : Blo 1541468 2312591 := bstep (se 1 (by rfl) ⟨1734443, by rfl⟩ : syracuseStep 2312591 = 3468887) B3468887
theorem B1542543 : Blo 1541468 1542543 := bstep (se 1 (by rfl) ⟨1156907, by rfl⟩ : syracuseStep 1542543 = 2313815) B2313815
theorem B2312633 : Blo 1541468 2312633 := bstep (se 2 (by rfl) ⟨867237, by rfl⟩ : syracuseStep 2312633 = 1734475) B1734475
theorem B1542587 : Blo 1541468 1542587 := bstep (se 1 (by rfl) ⟨1156940, by rfl⟩ : syracuseStep 1542587 = 2313881) B2313881
theorem B18762205 : Blo 1541468 18762205 := bstep (se 3 (by rfl) ⟨3517913, by rfl⟩ : syracuseStep 18762205 = 7035827) B7035827
theorem B7416323 : Blo 1541468 7416323 := bstep (se 1 (by rfl) ⟨5562242, by rfl⟩ : syracuseStep 7416323 = 11124485) B11124485
theorem B2312711 : Blo 1541468 2312711 := bstep (se 1 (by rfl) ⟨1734533, by rfl⟩ : syracuseStep 2312711 = 3469067) B3469067
theorem B1542663 : Blo 1541468 1542663 := bstep (se 1 (by rfl) ⟨1156997, by rfl⟩ : syracuseStep 1542663 = 2313995) B2313995
theorem B1542671 : Blo 1541468 1542671 := bstep (se 1 (by rfl) ⟨1157003, by rfl⟩ : syracuseStep 1542671 = 2314007) B2314007
theorem B2312747 : Blo 1541468 2312747 := bstep (se 1 (by rfl) ⟨1734560, by rfl⟩ : syracuseStep 2312747 = 3469121) B3469121
theorem B1542715 : Blo 1541468 1542715 := bstep (se 1 (by rfl) ⟨1157036, by rfl⟩ : syracuseStep 1542715 = 2314073) B2314073
theorem B7408189 : Blo 1541468 7408189 := bstep (se 3 (by rfl) ⟨1389035, by rfl⟩ : syracuseStep 7408189 = 2778071) B2778071
theorem B2312777 : Blo 1541468 2312777 := bstep (se 2 (by rfl) ⟨867291, by rfl⟩ : syracuseStep 2312777 = 1734583) B1734583
theorem B1542791 : Blo 1541468 1542791 := bstep (se 1 (by rfl) ⟨1157093, by rfl⟩ : syracuseStep 1542791 = 2314187) B2314187
theorem B1542799 : Blo 1541468 1542799 := bstep (se 1 (by rfl) ⟨1157099, by rfl⟩ : syracuseStep 1542799 = 2314199) B2314199
theorem B1854095 : Blo 1541468 1854095 := bstep (se 1 (by rfl) ⟨1390571, by rfl⟩ : syracuseStep 1854095 = 2781143) B2781143
theorem B2312891 : Blo 1541468 2312891 := bstep (se 1 (by rfl) ⟨1734668, by rfl⟩ : syracuseStep 2312891 = 3469337) B3469337
theorem B1542843 : Blo 1541468 1542843 := bstep (se 1 (by rfl) ⟨1157132, by rfl⟩ : syracuseStep 1542843 = 2314265) B2314265
theorem B5204681 : Blo 1541468 5204681 := bstep (se 2 (by rfl) ⟨1951755, by rfl⟩ : syracuseStep 5204681 = 3903511) B3903511
theorem B4393673 : Blo 1541468 4393673 := bstep (se 2 (by rfl) ⟨1647627, by rfl⟩ : syracuseStep 4393673 = 3295255) B3295255
theorem B2312951 : Blo 1541468 2312951 := bstep (se 1 (by rfl) ⟨1734713, by rfl⟩ : syracuseStep 2312951 = 3469427) B3469427
theorem B5860097 : Blo 1541468 5860097 := bstep (se 2 (by rfl) ⟨2197536, by rfl⟩ : syracuseStep 5860097 = 4395073) B4395073
theorem B1542919 : Blo 1541468 1542919 := bstep (se 1 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 1542919 = 2314379) B2314379
theorem B2312975 : Blo 1541468 2312975 := bstep (se 1 (by rfl) ⟨1734731, by rfl⟩ : syracuseStep 2312975 = 3469463) B3469463
theorem B1542927 : Blo 1541468 1542927 := bstep (se 1 (by rfl) ⟨1157195, by rfl⟩ : syracuseStep 1542927 = 2314391) B2314391
theorem B2313017 : Blo 1541468 2313017 := bstep (se 2 (by rfl) ⟨867381, by rfl⟩ : syracuseStep 2313017 = 1734763) B1734763
theorem B1542971 : Blo 1541468 1542971 := bstep (se 1 (by rfl) ⟨1157228, by rfl⟩ : syracuseStep 1542971 = 2314457) B2314457
theorem B17574731 : Blo 1541468 17574731 := bstep (se 1 (by rfl) ⟨13181048, by rfl⟩ : syracuseStep 17574731 = 26362097) B26362097
theorem B3902327 : Blo 1541468 3902327 := bstep (se 1 (by rfl) ⟨2926745, by rfl⟩ : syracuseStep 3902327 = 5853491) B5853491
theorem B2313095 : Blo 1541468 2313095 := bstep (se 1 (by rfl) ⟨1734821, by rfl⟩ : syracuseStep 2313095 = 3469643) B3469643
theorem B1543047 : Blo 1541468 1543047 := bstep (se 1 (by rfl) ⟨1157285, by rfl⟩ : syracuseStep 1543047 = 2314571) B2314571
theorem B1543055 : Blo 1541468 1543055 := bstep (se 1 (by rfl) ⟨1157291, by rfl⟩ : syracuseStep 1543055 = 2314583) B2314583
theorem B3959705 : Blo 1541468 3959705 := bstep (se 2 (by rfl) ⟨1484889, by rfl⟩ : syracuseStep 3959705 = 2969779) B2969779
theorem B2313131 : Blo 1541468 2313131 := bstep (se 1 (by rfl) ⟨1734848, by rfl⟩ : syracuseStep 2313131 = 3469697) B3469697
theorem B1543099 : Blo 1541468 1543099 := bstep (se 1 (by rfl) ⟨1157324, by rfl⟩ : syracuseStep 1543099 = 2314649) B2314649
theorem B2313161 : Blo 1541468 2313161 := bstep (se 2 (by rfl) ⟨867435, by rfl⟩ : syracuseStep 2313161 = 1734871) B1734871
theorem B7416785 : Blo 1541468 7416785 := bstep (se 2 (by rfl) ⟨2781294, by rfl⟩ : syracuseStep 7416785 = 5562589) B5562589
theorem B35613701 : Blo 1541468 35613701 := bstep (se 4 (by rfl) ⟨3338784, by rfl⟩ : syracuseStep 35613701 = 6677569) B6677569
theorem B1543175 : Blo 1541468 1543175 := bstep (se 1 (by rfl) ⟨1157381, by rfl⟩ : syracuseStep 1543175 = 2314763) B2314763
theorem B1543183 : Blo 1541468 1543183 := bstep (se 1 (by rfl) ⟨1157387, by rfl⟩ : syracuseStep 1543183 = 2314775) B2314775
theorem B3468347 : Blo 1541468 3468347 := bstep (se 1 (by rfl) ⟨2601260, by rfl⟩ : syracuseStep 3468347 = 5202521) B5202521
theorem B2313275 : Blo 1541468 2313275 := bstep (se 1 (by rfl) ⟨1734956, by rfl⟩ : syracuseStep 2313275 = 3469913) B3469913
theorem B1543227 : Blo 1541468 1543227 := bstep (se 1 (by rfl) ⟨1157420, by rfl⟩ : syracuseStep 1543227 = 2314841) B2314841
theorem B2313335 : Blo 1541468 2313335 := bstep (se 1 (by rfl) ⟨1735001, by rfl⟩ : syracuseStep 2313335 = 3470003) B3470003
theorem B1543303 : Blo 1541468 1543303 := bstep (se 1 (by rfl) ⟨1157477, by rfl⟩ : syracuseStep 1543303 = 2314955) B2314955
theorem B2313359 : Blo 1541468 2313359 := bstep (se 1 (by rfl) ⟨1735019, by rfl⟩ : syracuseStep 2313359 = 3470039) B3470039
theorem B1543311 : Blo 1541468 1543311 := bstep (se 1 (by rfl) ⟨1157483, by rfl⟩ : syracuseStep 1543311 = 2314967) B2314967
theorem B3468473 : Blo 1541468 3468473 := bstep (se 2 (by rfl) ⟨1300677, by rfl⟩ : syracuseStep 3468473 = 2601355) B2601355
theorem B2927801 : Blo 1541468 2927801 := bstep (se 2 (by rfl) ⟨1097925, by rfl⟩ : syracuseStep 2927801 = 2195851) B2195851
theorem B2313401 : Blo 1541468 2313401 := bstep (se 2 (by rfl) ⟨867525, by rfl⟩ : syracuseStep 2313401 = 1735051) B1735051
theorem B1543355 : Blo 1541468 1543355 := bstep (se 1 (by rfl) ⟨1157516, by rfl⟩ : syracuseStep 1543355 = 2315033) B2315033
theorem B2313479 : Blo 1541468 2313479 := bstep (se 1 (by rfl) ⟨1735109, by rfl⟩ : syracuseStep 2313479 = 3470219) B3470219
theorem B1543431 : Blo 1541468 1543431 := bstep (se 1 (by rfl) ⟨1157573, by rfl⟩ : syracuseStep 1543431 = 2315147) B2315147
theorem B1543439 : Blo 1541468 1543439 := bstep (se 1 (by rfl) ⟨1157579, by rfl⟩ : syracuseStep 1543439 = 2315159) B2315159
theorem B2313515 : Blo 1541468 2313515 := bstep (se 1 (by rfl) ⟨1735136, by rfl⟩ : syracuseStep 2313515 = 3470273) B3470273
theorem B1953067 : Blo 1541468 1953067 := bstep (se 1 (by rfl) ⟨1464800, by rfl⟩ : syracuseStep 1953067 = 2929601) B2929601
theorem B2313545 : Blo 1541468 2313545 := bstep (se 2 (by rfl) ⟨867579, by rfl⟩ : syracuseStep 2313545 = 1735159) B1735159
theorem B5205383 : Blo 1541468 5205383 := bstep (se 1 (by rfl) ⟨3904037, by rfl⟩ : syracuseStep 5205383 = 7808075) B7808075
theorem B2346383 : Blo 1541468 2346383 := bstep (se 1 (by rfl) ⟨1759787, by rfl⟩ : syracuseStep 2346383 = 3519575) B3519575
theorem B35630513 : Blo 1541468 35630513 := bstep (se 2 (by rfl) ⟨13361442, by rfl⟩ : syracuseStep 35630513 = 26722885) B26722885
theorem B2313659 : Blo 1541468 2313659 := bstep (se 1 (by rfl) ⟨1735244, by rfl⟩ : syracuseStep 2313659 = 3470489) B3470489
theorem B8785361 : Blo 1541468 8785361 := bstep (se 2 (by rfl) ⟨3294510, by rfl⟩ : syracuseStep 8785361 = 6589021) B6589021
theorem B2313719 : Blo 1541468 2313719 := bstep (se 1 (by rfl) ⟨1735289, by rfl⟩ : syracuseStep 2313719 = 3470579) B3470579
theorem B22244867 : Blo 1541468 22244867 := bstep (se 1 (by rfl) ⟨16683650, by rfl⟩ : syracuseStep 22244867 = 33367301) B33367301
theorem B25030147 : Blo 1541468 25030147 := bstep (se 1 (by rfl) ⟨18772610, by rfl⟩ : syracuseStep 25030147 = 37545221) B37545221
theorem B3468815 : Blo 1541468 3468815 := bstep (se 1 (by rfl) ⟨2601611, by rfl⟩ : syracuseStep 3468815 = 5203223) B5203223
theorem B2928143 : Blo 1541468 2928143 := bstep (se 1 (by rfl) ⟨2196107, by rfl⟩ : syracuseStep 2928143 = 4392215) B4392215
theorem B2313743 : Blo 1541468 2313743 := bstep (se 1 (by rfl) ⟨1735307, by rfl⟩ : syracuseStep 2313743 = 3470615) B3470615
theorem B3468833 : Blo 1541468 3468833 := bstep (se 2 (by rfl) ⟨1300812, by rfl⟩ : syracuseStep 3468833 = 2601625) B2601625
theorem B2313785 : Blo 1541468 2313785 := bstep (se 2 (by rfl) ⟨867669, by rfl⟩ : syracuseStep 2313785 = 1735339) B1735339
theorem B16682573 : Blo 1541468 16682573 := bstep (se 3 (by rfl) ⟨3127982, by rfl⟩ : syracuseStep 16682573 = 6255965) B6255965
theorem B2313863 : Blo 1541468 2313863 := bstep (se 1 (by rfl) ⟨1735397, by rfl⟩ : syracuseStep 2313863 = 3470795) B3470795
theorem B2313899 : Blo 1541468 2313899 := bstep (se 1 (by rfl) ⟨1735424, by rfl⟩ : syracuseStep 2313899 = 3470849) B3470849
theorem B2313929 : Blo 1541468 2313929 := bstep (se 2 (by rfl) ⟨867723, by rfl⟩ : syracuseStep 2313929 = 1735447) B1735447
theorem B7032577 : Blo 1541468 7032577 := bstep (se 2 (by rfl) ⟨2637216, by rfl⟩ : syracuseStep 7032577 = 5274433) B5274433
theorem B5205761 : Blo 1541468 5205761 := bstep (se 2 (by rfl) ⟨1952160, by rfl⟩ : syracuseStep 5205761 = 3904321) B3904321
theorem B2469647 : Blo 1541468 2469647 := bstep (se 1 (by rfl) ⟨1852235, by rfl⟩ : syracuseStep 2469647 = 3704471) B3704471
theorem B2314043 : Blo 1541468 2314043 := bstep (se 1 (by rfl) ⟨1735532, by rfl⟩ : syracuseStep 2314043 = 3471065) B3471065
theorem B3469175 : Blo 1541468 3469175 := bstep (se 1 (by rfl) ⟨2601881, by rfl⟩ : syracuseStep 3469175 = 5203763) B5203763
theorem B2314103 : Blo 1541468 2314103 := bstep (se 1 (by rfl) ⟨1735577, by rfl⟩ : syracuseStep 2314103 = 3471155) B3471155
theorem B2314127 : Blo 1541468 2314127 := bstep (se 1 (by rfl) ⟨1735595, by rfl⟩ : syracuseStep 2314127 = 3471191) B3471191
theorem B8785817 : Blo 1541468 8785817 := bstep (se 2 (by rfl) ⟨3294681, by rfl⟩ : syracuseStep 8785817 = 6589363) B6589363
theorem B1978283 : Blo 1541468 1978283 := bstep (se 1 (by rfl) ⟨1483712, by rfl⟩ : syracuseStep 1978283 = 2967425) B2967425
theorem B2314169 : Blo 1541468 2314169 := bstep (se 2 (by rfl) ⟨867813, by rfl⟩ : syracuseStep 2314169 = 1735627) B1735627
theorem B3706825 : Blo 1541468 3706825 := bstep (se 2 (by rfl) ⟨1390059, by rfl⟩ : syracuseStep 3706825 = 2780119) B2780119
theorem B2314247 : Blo 1541468 2314247 := bstep (se 1 (by rfl) ⟨1735685, by rfl⟩ : syracuseStep 2314247 = 3471371) B3471371
theorem B2969633 : Blo 1541468 2969633 := bstep (se 2 (by rfl) ⟨1113612, by rfl⟩ : syracuseStep 2969633 = 2227225) B2227225
theorem B3469355 : Blo 1541468 3469355 := bstep (se 1 (by rfl) ⟨2602016, by rfl⟩ : syracuseStep 3469355 = 5204033) B5204033
theorem B2314283 : Blo 1541468 2314283 := bstep (se 1 (by rfl) ⟨1735712, by rfl⟩ : syracuseStep 2314283 = 3471425) B3471425
theorem B2314313 : Blo 1541468 2314313 := bstep (se 2 (by rfl) ⟨867867, by rfl⟩ : syracuseStep 2314313 = 1735735) B1735735
theorem B3903623 : Blo 1541468 3903623 := bstep (se 1 (by rfl) ⟨2927717, by rfl⟩ : syracuseStep 3903623 = 5855435) B5855435
theorem B3903673 : Blo 1541468 3903673 := bstep (se 2 (by rfl) ⟨1463877, by rfl⟩ : syracuseStep 3903673 = 2927755) B2927755
theorem B2314427 : Blo 1541468 2314427 := bstep (se 1 (by rfl) ⟨1735820, by rfl⟩ : syracuseStep 2314427 = 3471641) B3471641
theorem B11866313 : Blo 1541468 11866313 := bstep (se 2 (by rfl) ⟨4449867, by rfl⟩ : syracuseStep 11866313 = 8899735) B8899735
theorem B4944073 : Blo 1541468 4944073 := bstep (se 2 (by rfl) ⟨1854027, by rfl⟩ : syracuseStep 4944073 = 3708055) B3708055
theorem B8335597 : Blo 1541468 8335597 := bstep (se 3 (by rfl) ⟨1562924, by rfl⟩ : syracuseStep 8335597 = 3125849) B3125849
theorem B2314487 : Blo 1541468 2314487 := bstep (se 1 (by rfl) ⟨1735865, by rfl⟩ : syracuseStep 2314487 = 3471731) B3471731
theorem B2314511 : Blo 1541468 2314511 := bstep (se 1 (by rfl) ⟨1735883, by rfl⟩ : syracuseStep 2314511 = 3471767) B3471767
theorem B2314553 : Blo 1541468 2314553 := bstep (se 2 (by rfl) ⟨867957, by rfl⟩ : syracuseStep 2314553 = 1735915) B1735915
theorem B2928955 : Blo 1541468 2928955 := bstep (se 1 (by rfl) ⟨2196716, by rfl⟩ : syracuseStep 2928955 = 4393433) B4393433
theorem B7410035 : Blo 1541468 7410035 := bstep (se 1 (by rfl) ⟨5557526, by rfl⟩ : syracuseStep 7410035 = 11115053) B11115053
theorem B2601335 : Blo 1541468 2601335 := bstep (se 1 (by rfl) ⟨1951001, by rfl⟩ : syracuseStep 2601335 = 3902003) B3902003
theorem B2929031 : Blo 1541468 2929031 := bstep (se 1 (by rfl) ⟨2196773, by rfl⟩ : syracuseStep 2929031 = 4393547) B4393547
theorem B2314631 : Blo 1541468 2314631 := bstep (se 1 (by rfl) ⟨1735973, by rfl⟩ : syracuseStep 2314631 = 3471947) B3471947
theorem B3469715 : Blo 1541468 3469715 := bstep (se 1 (by rfl) ⟨2602286, by rfl⟩ : syracuseStep 3469715 = 5204573) B5204573
theorem B2314667 : Blo 1541468 2314667 := bstep (se 1 (by rfl) ⟨1736000, by rfl⟩ : syracuseStep 2314667 = 3472001) B3472001
theorem B3469769 : Blo 1541468 3469769 := bstep (se 2 (by rfl) ⟨1301163, by rfl⟩ : syracuseStep 3469769 = 2602327) B2602327
theorem B2314697 : Blo 1541468 2314697 := bstep (se 2 (by rfl) ⟨868011, by rfl⟩ : syracuseStep 2314697 = 1736023) B1736023
theorem B5206571 : Blo 1541468 5206571 := bstep (se 1 (by rfl) ⟨3904928, by rfl⟩ : syracuseStep 5206571 = 7809857) B7809857
theorem B2314811 : Blo 1541468 2314811 := bstep (se 1 (by rfl) ⟨1736108, by rfl⟩ : syracuseStep 2314811 = 3472217) B3472217
theorem B11113037 : Blo 1541468 11113037 := bstep (se 3 (by rfl) ⟨2083694, by rfl⟩ : syracuseStep 11113037 = 4167389) B4167389
theorem B2314871 : Blo 1541468 2314871 := bstep (se 1 (by rfl) ⟨1736153, by rfl⟩ : syracuseStep 2314871 = 3472307) B3472307
theorem B2224783 : Blo 1541468 2224783 := bstep (se 1 (by rfl) ⟨1668587, by rfl⟩ : syracuseStep 2224783 = 3337175) B3337175
theorem B2314895 : Blo 1541468 2314895 := bstep (se 1 (by rfl) ⟨1736171, by rfl⟩ : syracuseStep 2314895 = 3472343) B3472343
theorem B2314937 : Blo 1541468 2314937 := bstep (se 2 (by rfl) ⟨868101, by rfl⟩ : syracuseStep 2314937 = 1736203) B1736203
theorem B2315015 : Blo 1541468 2315015 := bstep (se 1 (by rfl) ⟨1736261, by rfl⟩ : syracuseStep 2315015 = 3472523) B3472523
theorem B3904271 : Blo 1541468 3904271 := bstep (se 1 (by rfl) ⟨2928203, by rfl⟩ : syracuseStep 3904271 = 5856407) B5856407
theorem B2929441 : Blo 1541468 2929441 := bstep (se 2 (by rfl) ⟨1098540, by rfl⟩ : syracuseStep 2929441 = 2197081) B2197081
theorem B2315051 : Blo 1541468 2315051 := bstep (se 1 (by rfl) ⟨1736288, by rfl⟩ : syracuseStep 2315051 = 3472577) B3472577
theorem B2601787 : Blo 1541468 2601787 := bstep (se 1 (by rfl) ⟨1951340, by rfl⟩ : syracuseStep 2601787 = 3902681) B3902681
theorem B2315081 : Blo 1541468 2315081 := bstep (se 2 (by rfl) ⟨868155, by rfl⟩ : syracuseStep 2315081 = 1736311) B1736311
theorem B2315195 : Blo 1541468 2315195 := bstep (se 1 (by rfl) ⟨1736396, by rfl⟩ : syracuseStep 2315195 = 3472793) B3472793
theorem B2601929 : Blo 1541468 2601929 := bstep (se 2 (by rfl) ⟨975723, by rfl⟩ : syracuseStep 2601929 = 1951447) B1951447
theorem B7410635 : Blo 1541468 7410635 := bstep (se 1 (by rfl) ⟨5557976, by rfl⟩ : syracuseStep 7410635 = 11115953) B11115953
theorem B7812125 : Blo 1541468 7812125 := bstep (se 3 (by rfl) ⟨1464773, by rfl⟩ : syracuseStep 7812125 = 2929547) B2929547
theorem B5854295 : Blo 1541468 5854295 := bstep (se 1 (by rfl) ⟨4390721, by rfl⟩ : syracuseStep 5854295 = 8781443) B8781443
theorem B2929783 : Blo 1541468 2929783 := bstep (se 1 (by rfl) ⟨2197337, by rfl⟩ : syracuseStep 2929783 = 4394675) B4394675
theorem B3470471 : Blo 1541468 3470471 := bstep (se 1 (by rfl) ⟨2602853, by rfl⟩ : syracuseStep 3470471 = 5205707) B5205707
theorem B7410959 : Blo 1541468 7410959 := bstep (se 1 (by rfl) ⟨5558219, by rfl⟩ : syracuseStep 7410959 = 11116439) B11116439
theorem B11113787 : Blo 1541468 11113787 := bstep (se 1 (by rfl) ⟨8335340, by rfl⟩ : syracuseStep 11113787 = 16670681) B16670681
theorem B3470651 : Blo 1541468 3470651 := bstep (se 1 (by rfl) ⟨2602988, by rfl⟩ : syracuseStep 3470651 = 5205977) B5205977
theorem B3708247 : Blo 1541468 3708247 := bstep (se 1 (by rfl) ⟨2781185, by rfl⟩ : syracuseStep 3708247 = 5562371) B5562371
theorem B3339667 : Blo 1541468 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B4167065 : Blo 1541468 4167065 := bstep (se 2 (by rfl) ⟨1562649, by rfl⟩ : syracuseStep 4167065 = 3125299) B3125299
theorem B3470777 : Blo 1541468 3470777 := bstep (se 2 (by rfl) ⟨1301541, by rfl⟩ : syracuseStep 3470777 = 2603083) B2603083
theorem B3904969 : Blo 1541468 3904969 := bstep (se 2 (by rfl) ⟨1464363, by rfl⟩ : syracuseStep 3904969 = 2928727) B2928727
theorem B8779211 : Blo 1541468 8779211 := bstep (se 1 (by rfl) ⟨6584408, by rfl⟩ : syracuseStep 8779211 = 13168817) B13168817
theorem B9885149 : Blo 1541468 9885149 := bstep (se 3 (by rfl) ⟨1853465, by rfl⟩ : syracuseStep 9885149 = 3706931) B3706931
theorem B7812611 : Blo 1541468 7812611 := bstep (se 1 (by rfl) ⟨5859458, by rfl⟩ : syracuseStep 7812611 = 11718917) B11718917
theorem B18044459 : Blo 1541468 18044459 := bstep (se 1 (by rfl) ⟨13533344, by rfl⟩ : syracuseStep 18044459 = 27066689) B27066689
theorem B5854781 : Blo 1541468 5854781 := bstep (se 3 (by rfl) ⟨1097771, by rfl⟩ : syracuseStep 5854781 = 2195543) B2195543
theorem B16053827 : Blo 1541468 16053827 := bstep (se 1 (by rfl) ⟨12040370, by rfl⟩ : syracuseStep 16053827 = 24080741) B24080741
theorem B3905111 : Blo 1541468 3905111 := bstep (se 1 (by rfl) ⟨2928833, by rfl⟩ : syracuseStep 3905111 = 5857667) B5857667
theorem B2602631 : Blo 1541468 2602631 := bstep (se 1 (by rfl) ⟨1951973, by rfl⟩ : syracuseStep 2602631 = 3903947) B3903947
theorem B1734331 : Blo 1541468 1734331 := bstep (se 1 (by rfl) ⟨1300748, by rfl⟩ : syracuseStep 1734331 = 2601497) B2601497
theorem B9885377 : Blo 1541468 9885377 := bstep (se 2 (by rfl) ⟨3707016, by rfl⟩ : syracuseStep 9885377 = 7414033) B7414033
theorem B7804673 : Blo 1541468 7804673 := bstep (se 2 (by rfl) ⟨2926752, by rfl⟩ : syracuseStep 7804673 = 5853505) B5853505
theorem B3471119 : Blo 1541468 3471119 := bstep (se 1 (by rfl) ⟨2603339, by rfl⟩ : syracuseStep 3471119 = 5206679) B5206679
theorem B3471137 : Blo 1541468 3471137 := bstep (se 2 (by rfl) ⟨1301676, by rfl⟩ : syracuseStep 3471137 = 2603353) B2603353
theorem B3127099 : Blo 1541468 3127099 := bstep (se 1 (by rfl) ⟨2345324, by rfl⟩ : syracuseStep 3127099 = 4690649) B4690649
theorem B5207867 : Blo 1541468 5207867 := bstep (se 1 (by rfl) ⟨3905900, by rfl⟩ : syracuseStep 5207867 = 7811801) B7811801
theorem B8452043 : Blo 1541468 8452043 := bstep (se 1 (by rfl) ⟨6339032, by rfl⟩ : syracuseStep 8452043 = 12678065) B12678065
theorem B34289687 : Blo 1541468 34289687 := bstep (se 1 (by rfl) ⟨25717265, by rfl⟩ : syracuseStep 34289687 = 51434531) B51434531
theorem B20043821 : Blo 1541468 20043821 := bstep (se 3 (by rfl) ⟨3758216, by rfl⟩ : syracuseStep 20043821 = 7516433) B7516433
theorem B11712599 : Blo 1541468 11712599 := bstep (se 1 (by rfl) ⟨8784449, by rfl⟩ : syracuseStep 11712599 = 17568899) B17568899
theorem B162437237 : Blo 1541468 162437237 := bstep (se 5 (by rfl) ⟨7614245, by rfl⟩ : syracuseStep 162437237 = 15228491) B15228491
theorem B3471479 : Blo 1541468 3471479 := bstep (se 1 (by rfl) ⟨2603609, by rfl⟩ : syracuseStep 3471479 = 5207219) B5207219
theorem B14825605 : Blo 1541468 14825605 := bstep (se 4 (by rfl) ⟨1389900, by rfl⟩ : syracuseStep 14825605 = 2779801) B2779801
theorem B1734799 : Blo 1541468 1734799 := bstep (se 1 (by rfl) ⟨1301099, by rfl⟩ : syracuseStep 1734799 = 2602199) B2602199
theorem B2603279 : Blo 1541468 2603279 := bstep (se 1 (by rfl) ⟨1952459, by rfl⟩ : syracuseStep 2603279 = 3904919) B3904919
theorem B5208353 : Blo 1541468 5208353 := bstep (se 2 (by rfl) ⟨1953132, by rfl⟩ : syracuseStep 5208353 = 3906265) B3906265
theorem B3471659 : Blo 1541468 3471659 := bstep (se 1 (by rfl) ⟨2603744, by rfl⟩ : syracuseStep 3471659 = 5207489) B5207489
theorem B9877895 : Blo 1541468 9877895 := bstep (se 1 (by rfl) ⟨7408421, by rfl⟩ : syracuseStep 9877895 = 14816843) B14816843
theorem B73202069 : Blo 1541468 73202069 := bstep (se 6 (by rfl) ⟨1715673, by rfl⟩ : syracuseStep 73202069 = 3431347) B3431347
theorem B7805483 : Blo 1541468 7805483 := bstep (se 1 (by rfl) ⟨5854112, by rfl⟩ : syracuseStep 7805483 = 11708225) B11708225
theorem B11123243 : Blo 1541468 11123243 := bstep (se 1 (by rfl) ⟨8342432, by rfl⟩ : syracuseStep 11123243 = 16684865) B16684865
theorem B1735303 : Blo 1541468 1735303 := bstep (se 1 (by rfl) ⟨1301477, by rfl⟩ : syracuseStep 1735303 = 2602955) B2602955
theorem B3472019 : Blo 1541468 3472019 := bstep (se 1 (by rfl) ⟨2604014, by rfl⟩ : syracuseStep 3472019 = 5208029) B5208029
theorem B3472073 : Blo 1541468 3472073 := bstep (se 2 (by rfl) ⟨1302027, by rfl⟩ : syracuseStep 3472073 = 2604055) B2604055
theorem B9378575 : Blo 1541468 9378575 := bstep (se 1 (by rfl) ⟨7033931, by rfl⟩ : syracuseStep 9378575 = 14067863) B14067863
theorem B2603819 : Blo 1541468 2603819 := bstep (se 1 (by rfl) ⟨1952864, by rfl⟩ : syracuseStep 2603819 = 3905729) B3905729
theorem B1735483 : Blo 1541468 1735483 := bstep (se 1 (by rfl) ⟨1301612, by rfl⟩ : syracuseStep 1735483 = 2603225) B2603225
theorem B5208947 : Blo 1541468 5208947 := bstep (se 1 (by rfl) ⟨3906710, by rfl⟩ : syracuseStep 5208947 = 7813421) B7813421
theorem B7412633 : Blo 1541468 7412633 := bstep (se 2 (by rfl) ⟨2779737, by rfl⟩ : syracuseStep 7412633 = 5559475) B5559475
theorem B5856209 : Blo 1541468 5856209 := bstep (se 2 (by rfl) ⟨2196078, by rfl⟩ : syracuseStep 5856209 = 4392157) B4392157
theorem B7912451 : Blo 1541468 7912451 := bstep (se 1 (by rfl) ⟨5934338, by rfl⟩ : syracuseStep 7912451 = 11868677) B11868677
theorem B4389947 : Blo 1541468 4389947 := bstep (se 1 (by rfl) ⟨3292460, by rfl⟩ : syracuseStep 4389947 = 6584921) B6584921
theorem B2604217 : Blo 1541468 2604217 := bstep (se 2 (by rfl) ⟨976581, by rfl⟩ : syracuseStep 2604217 = 1953163) B1953163
theorem B1735951 : Blo 1541468 1735951 := bstep (se 1 (by rfl) ⟨1301963, by rfl⟩ : syracuseStep 1735951 = 2603927) B2603927
theorem B3472775 : Blo 1541468 3472775 := bstep (se 1 (by rfl) ⟨2604581, by rfl⟩ : syracuseStep 3472775 = 5209163) B5209163
theorem B2194951 : Blo 1541468 2194951 := bstep (se 1 (by rfl) ⟨1646213, by rfl⟩ : syracuseStep 2194951 = 3292427) B3292427
theorem B4390699 : Blo 1541468 4390699 := bstep (se 1 (by rfl) ⟨3293024, by rfl⟩ : syracuseStep 4390699 = 6586049) B6586049
theorem B7806779 : Blo 1541468 7806779 := bstep (se 1 (by rfl) ⟨5855084, by rfl⟩ : syracuseStep 7806779 = 11710169) B11710169
theorem B7806941 : Blo 1541468 7806941 := bstep (se 3 (by rfl) ⟨1463801, by rfl⟩ : syracuseStep 7806941 = 2927603) B2927603
theorem B7413725 : Blo 1541468 7413725 := bstep (se 3 (by rfl) ⟨1390073, by rfl⟩ : syracuseStep 7413725 = 2780147) B2780147
theorem B91439165 : Blo 1541468 91439165 := bstep (se 3 (by rfl) ⟨17144843, by rfl⟩ : syracuseStep 91439165 = 34289687) B34289687
theorem B19767473 : Blo 1541468 19767473 := bstep (se 2 (by rfl) ⟨7412802, by rfl⟩ : syracuseStep 19767473 = 14825605) B14825605
theorem B4940023 : Blo 1541468 4940023 := bstep (se 1 (by rfl) ⟨3705017, by rfl⟩ : syracuseStep 4940023 = 7410035) B7410035
theorem B39510341 : Blo 1541468 39510341 := bstep (se 4 (by rfl) ⟨3704094, by rfl⟩ : syracuseStep 39510341 = 7408189) B7408189
theorem B4751759 : Blo 1541468 4751759 := bstep (se 1 (by rfl) ⟨3563819, by rfl⟩ : syracuseStep 4751759 = 7127639) B7127639
theorem B42189335 : Blo 1541468 42189335 := bstep (se 1 (by rfl) ⟨31642001, by rfl⟩ : syracuseStep 42189335 = 63284003) B63284003
theorem B4940423 : Blo 1541468 4940423 := bstep (se 1 (by rfl) ⟨3705317, by rfl⟩ : syracuseStep 4940423 = 7410635) B7410635
theorem B7037725 : Blo 1541468 7037725 := bstep (se 3 (by rfl) ⟨1319573, by rfl⟩ : syracuseStep 7037725 = 2639147) B2639147
theorem B4940639 : Blo 1541468 4940639 := bstep (se 1 (by rfl) ⟨3705479, by rfl⟩ : syracuseStep 4940639 = 7410959) B7410959
theorem B2966377 : Blo 1541468 2966377 := bstep (se 2 (by rfl) ⟨1112391, by rfl⟩ : syracuseStep 2966377 = 2224783) B2224783
theorem B2778043 : Blo 1541468 2778043 := bstep (se 1 (by rfl) ⟨2083532, by rfl⟩ : syracuseStep 2778043 = 4167065) B4167065
theorem B2196443 : Blo 1541468 2196443 := bstep (se 1 (by rfl) ⟨1647332, by rfl⟩ : syracuseStep 2196443 = 3294665) B3294665
theorem B43402291 : Blo 1541468 43402291 := bstep (se 1 (by rfl) ⟨32551718, by rfl⟩ : syracuseStep 43402291 = 65103437) B65103437
theorem B5203115 : Blo 1541468 5203115 := bstep (se 1 (by rfl) ⟨3902336, by rfl⟩ : syracuseStep 5203115 = 7804673) B7804673
theorem B6587639 : Blo 1541468 6587639 := bstep (se 1 (by rfl) ⟨4940729, by rfl⟩ : syracuseStep 6587639 = 9881459) B9881459
theorem B1541471 : Blo 1541468 1541471 := bstep (se 1 (by rfl) ⟨1156103, by rfl⟩ : syracuseStep 1541471 = 2312207) B2312207
theorem B1541499 : Blo 1541468 1541499 := bstep (se 1 (by rfl) ⟨1156124, by rfl⟩ : syracuseStep 1541499 = 2312249) B2312249
theorem B7808399 : Blo 1541468 7808399 := bstep (se 1 (by rfl) ⟨5856299, by rfl⟩ : syracuseStep 7808399 = 11712599) B11712599
theorem B108291491 : Blo 1541468 108291491 := bstep (se 1 (by rfl) ⟨81218618, by rfl⟩ : syracuseStep 108291491 = 162437237) B162437237
theorem B1541551 : Blo 1541468 1541551 := bstep (se 1 (by rfl) ⟨1156163, by rfl⟩ : syracuseStep 1541551 = 2312327) B2312327
theorem B1541575 : Blo 1541468 1541575 := bstep (se 1 (by rfl) ⟨1156181, by rfl⟩ : syracuseStep 1541575 = 2312363) B2312363
theorem B1541595 : Blo 1541468 1541595 := bstep (se 1 (by rfl) ⟨1156196, by rfl⟩ : syracuseStep 1541595 = 2312393) B2312393
theorem B2197001 : Blo 1541468 2197001 := bstep (se 2 (by rfl) ⟨823875, by rfl⟩ : syracuseStep 2197001 = 1647751) B1647751
theorem B1541671 : Blo 1541468 1541671 := bstep (se 1 (by rfl) ⟨1156253, by rfl⟩ : syracuseStep 1541671 = 2312507) B2312507
theorem B1541711 : Blo 1541468 1541711 := bstep (se 1 (by rfl) ⟨1156283, by rfl⟩ : syracuseStep 1541711 = 2312567) B2312567
theorem B1541727 : Blo 1541468 1541727 := bstep (se 1 (by rfl) ⟨1156295, by rfl⟩ : syracuseStep 1541727 = 2312591) B2312591
theorem B48801379 : Blo 1541468 48801379 := bstep (se 1 (by rfl) ⟨36601034, by rfl⟩ : syracuseStep 48801379 = 73202069) B73202069
theorem B1541755 : Blo 1541468 1541755 := bstep (se 1 (by rfl) ⟨1156316, by rfl⟩ : syracuseStep 1541755 = 2312633) B2312633
theorem B1541807 : Blo 1541468 1541807 := bstep (se 1 (by rfl) ⟨1156355, by rfl⟩ : syracuseStep 1541807 = 2312711) B2312711
theorem B5203655 : Blo 1541468 5203655 := bstep (se 1 (by rfl) ⟨3902741, by rfl⟩ : syracuseStep 5203655 = 7805483) B7805483
theorem B1541831 : Blo 1541468 1541831 := bstep (se 1 (by rfl) ⟨1156373, by rfl⟩ : syracuseStep 1541831 = 2312747) B2312747
theorem B7415495 : Blo 1541468 7415495 := bstep (se 1 (by rfl) ⟨5561621, by rfl⟩ : syracuseStep 7415495 = 11123243) B11123243
theorem B1541851 : Blo 1541468 1541851 := bstep (se 1 (by rfl) ⟨1156388, by rfl⟩ : syracuseStep 1541851 = 2312777) B2312777
theorem B1541927 : Blo 1541468 1541927 := bstep (se 1 (by rfl) ⟨1156445, by rfl⟩ : syracuseStep 1541927 = 2312891) B2312891
theorem B1541967 : Blo 1541468 1541967 := bstep (se 1 (by rfl) ⟨1156475, by rfl⟩ : syracuseStep 1541967 = 2312951) B2312951
theorem B1541983 : Blo 1541468 1541983 := bstep (se 1 (by rfl) ⟨1156487, by rfl⟩ : syracuseStep 1541983 = 2312975) B2312975
theorem B6252383 : Blo 1541468 6252383 := bstep (se 1 (by rfl) ⟨4689287, by rfl⟩ : syracuseStep 6252383 = 9378575) B9378575
theorem B1542011 : Blo 1541468 1542011 := bstep (se 1 (by rfl) ⟨1156508, by rfl⟩ : syracuseStep 1542011 = 2313017) B2313017
theorem B11716487 : Blo 1541468 11716487 := bstep (se 1 (by rfl) ⟨8787365, by rfl⟩ : syracuseStep 11716487 = 17574731) B17574731
theorem B1542063 : Blo 1541468 1542063 := bstep (se 1 (by rfl) ⟨1156547, by rfl⟩ : syracuseStep 1542063 = 2313095) B2313095
theorem B4941755 : Blo 1541468 4941755 := bstep (se 1 (by rfl) ⟨3706316, by rfl⟩ : syracuseStep 4941755 = 7412633) B7412633
theorem B1542087 : Blo 1541468 1542087 := bstep (se 1 (by rfl) ⟨1156565, by rfl⟩ : syracuseStep 1542087 = 2313131) B2313131
theorem B1542107 : Blo 1541468 1542107 := bstep (se 1 (by rfl) ⟨1156580, by rfl⟩ : syracuseStep 1542107 = 2313161) B2313161
theorem B23742467 : Blo 1541468 23742467 := bstep (se 1 (by rfl) ⟨17806850, by rfl⟩ : syracuseStep 23742467 = 35613701) B35613701
theorem B2926601 : Blo 1541468 2926601 := bstep (se 2 (by rfl) ⟨1097475, by rfl⟩ : syracuseStep 2926601 = 2194951) B2194951
theorem B2312231 : Blo 1541468 2312231 := bstep (se 1 (by rfl) ⟨1734173, by rfl⟩ : syracuseStep 2312231 = 3468347) B3468347
theorem B2926631 : Blo 1541468 2926631 := bstep (se 1 (by rfl) ⟨2194973, by rfl⟩ : syracuseStep 2926631 = 4389947) B4389947
theorem B1542183 : Blo 1541468 1542183 := bstep (se 1 (by rfl) ⟨1156637, by rfl⟩ : syracuseStep 1542183 = 2313275) B2313275
theorem B1542223 : Blo 1541468 1542223 := bstep (se 1 (by rfl) ⟨1156667, by rfl⟩ : syracuseStep 1542223 = 2313335) B2313335
theorem B1542239 : Blo 1541468 1542239 := bstep (se 1 (by rfl) ⟨1156679, by rfl⟩ : syracuseStep 1542239 = 2313359) B2313359
theorem B2312315 : Blo 1541468 2312315 := bstep (se 1 (by rfl) ⟨1734236, by rfl⟩ : syracuseStep 2312315 = 3468473) B3468473
theorem B1951867 : Blo 1541468 1951867 := bstep (se 1 (by rfl) ⟨1463900, by rfl⟩ : syracuseStep 1951867 = 2927801) B2927801
theorem B1542267 : Blo 1541468 1542267 := bstep (se 1 (by rfl) ⟨1156700, by rfl⟩ : syracuseStep 1542267 = 2313401) B2313401
theorem B1542319 : Blo 1541468 1542319 := bstep (se 1 (by rfl) ⟨1156739, by rfl⟩ : syracuseStep 1542319 = 2313479) B2313479
theorem B1542343 : Blo 1541468 1542343 := bstep (se 1 (by rfl) ⟨1156757, by rfl⟩ : syracuseStep 1542343 = 2313515) B2313515
theorem B1542363 : Blo 1541468 1542363 := bstep (se 1 (by rfl) ⟨1156772, by rfl⟩ : syracuseStep 1542363 = 2313545) B2313545
theorem B2312441 : Blo 1541468 2312441 := bstep (se 2 (by rfl) ⟨867165, by rfl⟩ : syracuseStep 2312441 = 1734331) B1734331
theorem B1542439 : Blo 1541468 1542439 := bstep (se 1 (by rfl) ⟨1156829, by rfl⟩ : syracuseStep 1542439 = 2313659) B2313659
theorem B1542479 : Blo 1541468 1542479 := bstep (se 1 (by rfl) ⟨1156859, by rfl⟩ : syracuseStep 1542479 = 2313719) B2313719
theorem B14829911 : Blo 1541468 14829911 := bstep (se 1 (by rfl) ⟨11122433, by rfl⟩ : syracuseStep 14829911 = 22244867) B22244867
theorem B2312543 : Blo 1541468 2312543 := bstep (se 1 (by rfl) ⟨1734407, by rfl⟩ : syracuseStep 2312543 = 3468815) B3468815
theorem B1952095 : Blo 1541468 1952095 := bstep (se 1 (by rfl) ⟨1464071, by rfl⟩ : syracuseStep 1952095 = 2928143) B2928143
theorem B1542495 : Blo 1541468 1542495 := bstep (se 1 (by rfl) ⟨1156871, by rfl⟩ : syracuseStep 1542495 = 2313743) B2313743
theorem B2312555 : Blo 1541468 2312555 := bstep (se 1 (by rfl) ⟨1734416, by rfl⟩ : syracuseStep 2312555 = 3468833) B3468833
theorem B1542523 : Blo 1541468 1542523 := bstep (se 1 (by rfl) ⟨1156892, by rfl⟩ : syracuseStep 1542523 = 2313785) B2313785
theorem B1542575 : Blo 1541468 1542575 := bstep (se 1 (by rfl) ⟨1156931, by rfl⟩ : syracuseStep 1542575 = 2313863) B2313863
theorem B1542599 : Blo 1541468 1542599 := bstep (se 1 (by rfl) ⟨1156949, by rfl⟩ : syracuseStep 1542599 = 2313899) B2313899
theorem B1542619 : Blo 1541468 1542619 := bstep (se 1 (by rfl) ⟨1156964, by rfl⟩ : syracuseStep 1542619 = 2313929) B2313929
theorem B5204519 : Blo 1541468 5204519 := bstep (se 1 (by rfl) ⟨3903389, by rfl⟩ : syracuseStep 5204519 = 7806779) B7806779
theorem B1542695 : Blo 1541468 1542695 := bstep (se 1 (by rfl) ⟨1157021, by rfl⟩ : syracuseStep 1542695 = 2314043) B2314043
theorem B19769933 : Blo 1541468 19769933 := bstep (se 3 (by rfl) ⟨3706862, by rfl⟩ : syracuseStep 19769933 = 7413725) B7413725
theorem B2312783 : Blo 1541468 2312783 := bstep (se 1 (by rfl) ⟨1734587, by rfl⟩ : syracuseStep 2312783 = 3469175) B3469175
theorem B1542735 : Blo 1541468 1542735 := bstep (se 1 (by rfl) ⟨1157051, by rfl⟩ : syracuseStep 1542735 = 2314103) B2314103
theorem B1542751 : Blo 1541468 1542751 := bstep (se 1 (by rfl) ⟨1157063, by rfl⟩ : syracuseStep 1542751 = 2314127) B2314127
theorem B4942433 : Blo 1541468 4942433 := bstep (se 2 (by rfl) ⟨1853412, by rfl⟩ : syracuseStep 4942433 = 3706825) B3706825
theorem B1542779 : Blo 1541468 1542779 := bstep (se 1 (by rfl) ⟨1157084, by rfl⟩ : syracuseStep 1542779 = 2314169) B2314169
theorem B5204627 : Blo 1541468 5204627 := bstep (se 1 (by rfl) ⟨3903470, by rfl⟩ : syracuseStep 5204627 = 7806941) B7806941
theorem B1542831 : Blo 1541468 1542831 := bstep (se 1 (by rfl) ⟨1157123, by rfl⟩ : syracuseStep 1542831 = 2314247) B2314247
theorem B2312903 : Blo 1541468 2312903 := bstep (se 1 (by rfl) ⟨1734677, by rfl⟩ : syracuseStep 2312903 = 3469355) B3469355
theorem B1542855 : Blo 1541468 1542855 := bstep (se 1 (by rfl) ⟨1157141, by rfl⟩ : syracuseStep 1542855 = 2314283) B2314283
theorem B2927315 : Blo 1541468 2927315 := bstep (se 1 (by rfl) ⟨2195486, by rfl⟩ : syracuseStep 2927315 = 4390973) B4390973
theorem B1542875 : Blo 1541468 1542875 := bstep (se 1 (by rfl) ⟨1157156, by rfl⟩ : syracuseStep 1542875 = 2314313) B2314313
theorem B2927353 : Blo 1541468 2927353 := bstep (se 2 (by rfl) ⟨1097757, by rfl⟩ : syracuseStep 2927353 = 2195515) B2195515
theorem B13175581 : Blo 1541468 13175581 := bstep (se 3 (by rfl) ⟨2470421, by rfl⟩ : syracuseStep 13175581 = 4940843) B4940843
theorem B1542951 : Blo 1541468 1542951 := bstep (se 1 (by rfl) ⟨1157213, by rfl⟩ : syracuseStep 1542951 = 2314427) B2314427
theorem B1542991 : Blo 1541468 1542991 := bstep (se 1 (by rfl) ⟨1157243, by rfl⟩ : syracuseStep 1542991 = 2314487) B2314487
theorem B1543007 : Blo 1541468 1543007 := bstep (se 1 (by rfl) ⟨1157255, by rfl⟩ : syracuseStep 1543007 = 2314511) B2314511
theorem B2313065 : Blo 1541468 2313065 := bstep (se 2 (by rfl) ⟨867399, by rfl⟩ : syracuseStep 2313065 = 1734799) B1734799
theorem B5204843 : Blo 1541468 5204843 := bstep (se 1 (by rfl) ⟨3903632, by rfl⟩ : syracuseStep 5204843 = 7807265) B7807265
theorem B1543035 : Blo 1541468 1543035 := bstep (se 1 (by rfl) ⟨1157276, by rfl⟩ : syracuseStep 1543035 = 2314553) B2314553
theorem B5204897 : Blo 1541468 5204897 := bstep (se 2 (by rfl) ⟨1951836, by rfl⟩ : syracuseStep 5204897 = 3903673) B3903673
theorem B4393889 : Blo 1541468 4393889 := bstep (se 2 (by rfl) ⟨1647708, by rfl⟩ : syracuseStep 4393889 = 3295417) B3295417
theorem B1952687 : Blo 1541468 1952687 := bstep (se 1 (by rfl) ⟨1464515, by rfl⟩ : syracuseStep 1952687 = 2929031) B2929031
theorem B1543087 : Blo 1541468 1543087 := bstep (se 1 (by rfl) ⟨1157315, by rfl⟩ : syracuseStep 1543087 = 2314631) B2314631
theorem B2313143 : Blo 1541468 2313143 := bstep (se 1 (by rfl) ⟨1734857, by rfl⟩ : syracuseStep 2313143 = 3469715) B3469715
theorem B1543111 : Blo 1541468 1543111 := bstep (se 1 (by rfl) ⟨1157333, by rfl⟩ : syracuseStep 1543111 = 2314667) B2314667
theorem B2313179 : Blo 1541468 2313179 := bstep (se 1 (by rfl) ⟨1734884, by rfl⟩ : syracuseStep 2313179 = 3469769) B3469769
theorem B1543131 : Blo 1541468 1543131 := bstep (se 1 (by rfl) ⟨1157348, by rfl⟩ : syracuseStep 1543131 = 2314697) B2314697
theorem B1543207 : Blo 1541468 1543207 := bstep (se 1 (by rfl) ⟨1157405, by rfl⟩ : syracuseStep 1543207 = 2314811) B2314811
theorem B7408691 : Blo 1541468 7408691 := bstep (se 1 (by rfl) ⟨5556518, by rfl⟩ : syracuseStep 7408691 = 11113037) B11113037
theorem B1543247 : Blo 1541468 1543247 := bstep (se 1 (by rfl) ⟨1157435, by rfl⟩ : syracuseStep 1543247 = 2314871) B2314871
theorem B1543263 : Blo 1541468 1543263 := bstep (se 1 (by rfl) ⟨1157447, by rfl⟩ : syracuseStep 1543263 = 2314895) B2314895
theorem B1543291 : Blo 1541468 1543291 := bstep (se 1 (by rfl) ⟨1157468, by rfl⟩ : syracuseStep 1543291 = 2314937) B2314937
theorem B1543343 : Blo 1541468 1543343 := bstep (se 1 (by rfl) ⟨1157507, by rfl⟩ : syracuseStep 1543343 = 2315015) B2315015
theorem B1543367 : Blo 1541468 1543367 := bstep (se 1 (by rfl) ⟨1157525, by rfl⟩ : syracuseStep 1543367 = 2315051) B2315051
theorem B1543387 : Blo 1541468 1543387 := bstep (se 1 (by rfl) ⟨1157540, by rfl⟩ : syracuseStep 1543387 = 2315081) B2315081
theorem B25013539 : Blo 1541468 25013539 := bstep (se 1 (by rfl) ⟨18760154, by rfl⟩ : syracuseStep 25013539 = 37520309) B37520309
theorem B9882917 : Blo 1541468 9882917 := bstep (se 4 (by rfl) ⟨926523, by rfl⟩ : syracuseStep 9882917 = 1853047) B1853047
theorem B1543463 : Blo 1541468 1543463 := bstep (se 1 (by rfl) ⟨1157597, by rfl⟩ : syracuseStep 1543463 = 2315195) B2315195
theorem B3902863 : Blo 1541468 3902863 := bstep (se 1 (by rfl) ⟨2927147, by rfl⟩ : syracuseStep 3902863 = 5854295) B5854295
theorem B2313647 : Blo 1541468 2313647 := bstep (se 1 (by rfl) ⟨1735235, by rfl⟩ : syracuseStep 2313647 = 3470471) B3470471
theorem B2928059 : Blo 1541468 2928059 := bstep (se 1 (by rfl) ⟨2196044, by rfl⟩ : syracuseStep 2928059 = 4392089) B4392089
theorem B7810505 : Blo 1541468 7810505 := bstep (se 2 (by rfl) ⟨2928939, by rfl⟩ : syracuseStep 7810505 = 5857879) B5857879
theorem B5205491 : Blo 1541468 5205491 := bstep (se 1 (by rfl) ⟨3904118, by rfl⟩ : syracuseStep 5205491 = 7808237) B7808237
theorem B2313737 : Blo 1541468 2313737 := bstep (se 2 (by rfl) ⟨867651, by rfl⟩ : syracuseStep 2313737 = 1735303) B1735303
theorem B7409191 : Blo 1541468 7409191 := bstep (se 1 (by rfl) ⟨5556893, by rfl⟩ : syracuseStep 7409191 = 11113787) B11113787
theorem B2313767 : Blo 1541468 2313767 := bstep (se 1 (by rfl) ⟨1735325, by rfl⟩ : syracuseStep 2313767 = 3470651) B3470651
theorem B3468923 : Blo 1541468 3468923 := bstep (se 1 (by rfl) ⟨2601692, by rfl⟩ : syracuseStep 3468923 = 5203385) B5203385
theorem B2313851 : Blo 1541468 2313851 := bstep (se 1 (by rfl) ⟨1735388, by rfl⟩ : syracuseStep 2313851 = 3470777) B3470777
theorem B5852807 : Blo 1541468 5852807 := bstep (se 1 (by rfl) ⟨4389605, by rfl⟩ : syracuseStep 5852807 = 8779211) B8779211
theorem B6590099 : Blo 1541468 6590099 := bstep (se 1 (by rfl) ⟨4942574, by rfl⟩ : syracuseStep 6590099 = 9885149) B9885149
theorem B12029639 : Blo 1541468 12029639 := bstep (se 1 (by rfl) ⟨9022229, by rfl⟩ : syracuseStep 12029639 = 18044459) B18044459
theorem B3903187 : Blo 1541468 3903187 := bstep (se 1 (by rfl) ⟨2927390, by rfl⟩ : syracuseStep 3903187 = 5854781) B5854781
theorem B3469049 : Blo 1541468 3469049 := bstep (se 2 (by rfl) ⟨1300893, by rfl⟩ : syracuseStep 3469049 = 2601787) B2601787
theorem B2313977 : Blo 1541468 2313977 := bstep (se 2 (by rfl) ⟨867741, by rfl⟩ : syracuseStep 2313977 = 1735483) B1735483
theorem B6590251 : Blo 1541468 6590251 := bstep (se 1 (by rfl) ⟨4942688, by rfl⟩ : syracuseStep 6590251 = 9885377) B9885377
theorem B28159811 : Blo 1541468 28159811 := bstep (se 1 (by rfl) ⟨21119858, by rfl⟩ : syracuseStep 28159811 = 42239717) B42239717
theorem B2314079 : Blo 1541468 2314079 := bstep (se 1 (by rfl) ⟨1735559, by rfl⟩ : syracuseStep 2314079 = 3471119) B3471119
theorem B2314091 : Blo 1541468 2314091 := bstep (se 1 (by rfl) ⟨1735568, by rfl⟩ : syracuseStep 2314091 = 3471137) B3471137
theorem B2928545 : Blo 1541468 2928545 := bstep (se 2 (by rfl) ⟨1098204, by rfl⟩ : syracuseStep 2928545 = 2196409) B2196409
theorem B3469319 : Blo 1541468 3469319 := bstep (se 1 (by rfl) ⟨2601989, by rfl⟩ : syracuseStep 3469319 = 5203979) B5203979
theorem B5206031 : Blo 1541468 5206031 := bstep (se 1 (by rfl) ⟨3904523, by rfl⟩ : syracuseStep 5206031 = 7809047) B7809047
theorem B3469391 : Blo 1541468 3469391 := bstep (se 1 (by rfl) ⟨2602043, by rfl⟩ : syracuseStep 3469391 = 5204087) B5204087
theorem B2314319 : Blo 1541468 2314319 := bstep (se 1 (by rfl) ⟨1735739, by rfl⟩ : syracuseStep 2314319 = 3471479) B3471479
theorem B7811153 : Blo 1541468 7811153 := bstep (se 2 (by rfl) ⟨2929182, by rfl⟩ : syracuseStep 7811153 = 5858365) B5858365
theorem B2928811 : Blo 1541468 2928811 := bstep (se 1 (by rfl) ⟨2196608, by rfl⟩ : syracuseStep 2928811 = 4393217) B4393217
theorem B2314439 : Blo 1541468 2314439 := bstep (se 1 (by rfl) ⟨1735829, by rfl⟩ : syracuseStep 2314439 = 3471659) B3471659
theorem B4944215 : Blo 1541468 4944215 := bstep (se 1 (by rfl) ⟨3708161, by rfl⟩ : syracuseStep 4944215 = 7416323) B7416323
theorem B2314601 : Blo 1541468 2314601 := bstep (se 2 (by rfl) ⟨867975, by rfl⟩ : syracuseStep 2314601 = 1735951) B1735951
theorem B4944253 : Blo 1541468 4944253 := bstep (se 3 (by rfl) ⟨927047, by rfl⟩ : syracuseStep 4944253 = 1854095) B1854095
theorem B2314679 : Blo 1541468 2314679 := bstep (se 1 (by rfl) ⟨1736009, by rfl⟩ : syracuseStep 2314679 = 3472019) B3472019
theorem B4944329 : Blo 1541468 4944329 := bstep (se 2 (by rfl) ⟨1854123, by rfl⟩ : syracuseStep 4944329 = 3708247) B3708247
theorem B3469787 : Blo 1541468 3469787 := bstep (se 1 (by rfl) ⟨2602340, by rfl⟩ : syracuseStep 3469787 = 5204681) B5204681
theorem B2929115 : Blo 1541468 2929115 := bstep (se 1 (by rfl) ⟨2196836, by rfl⟩ : syracuseStep 2929115 = 4393673) B4393673
theorem B2314715 : Blo 1541468 2314715 := bstep (se 1 (by rfl) ⟨1736036, by rfl⟩ : syracuseStep 2314715 = 3472073) B3472073
theorem B4452889 : Blo 1541468 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B2601551 : Blo 1541468 2601551 := bstep (se 1 (by rfl) ⟨1951163, by rfl⟩ : syracuseStep 2601551 = 3902327) B3902327
theorem B5206625 : Blo 1541468 5206625 := bstep (se 2 (by rfl) ⟨1952484, by rfl⟩ : syracuseStep 5206625 = 3904969) B3904969
theorem B3904139 : Blo 1541468 3904139 := bstep (se 1 (by rfl) ⟨2928104, by rfl⟩ : syracuseStep 3904139 = 5856209) B5856209
theorem B4944523 : Blo 1541468 4944523 := bstep (se 1 (by rfl) ⟨3708392, by rfl⟩ : syracuseStep 4944523 = 7416785) B7416785
theorem B22229761 : Blo 1541468 22229761 := bstep (se 2 (by rfl) ⟨8336160, by rfl⟩ : syracuseStep 22229761 = 16672321) B16672321
theorem B3470255 : Blo 1541468 3470255 := bstep (se 1 (by rfl) ⟨2602691, by rfl⟩ : syracuseStep 3470255 = 5205383) B5205383
theorem B2315183 : Blo 1541468 2315183 := bstep (se 1 (by rfl) ⟨1736387, by rfl⟩ : syracuseStep 2315183 = 3472775) B3472775
theorem B23753675 : Blo 1541468 23753675 := bstep (se 1 (by rfl) ⟨17815256, by rfl⟩ : syracuseStep 23753675 = 35630513) B35630513
theorem B9376769 : Blo 1541468 9376769 := bstep (se 2 (by rfl) ⟨3516288, by rfl⟩ : syracuseStep 9376769 = 7032577) B7032577
theorem B11121715 : Blo 1541468 11121715 := bstep (se 1 (by rfl) ⟨8341286, by rfl⟩ : syracuseStep 11121715 = 16682573) B16682573
theorem B5854265 : Blo 1541468 5854265 := bstep (se 2 (by rfl) ⟨2195349, by rfl⟩ : syracuseStep 5854265 = 4390699) B4390699
theorem B3470507 : Blo 1541468 3470507 := bstep (se 1 (by rfl) ⟨2602880, by rfl⟩ : syracuseStep 3470507 = 5205761) B5205761
theorem B21099869 : Blo 1541468 21099869 := bstep (se 3 (by rfl) ⟨3956225, by rfl⟩ : syracuseStep 21099869 = 7912451) B7912451
theorem B7919021 : Blo 1541468 7919021 := bstep (se 3 (by rfl) ⟨1484816, by rfl⟩ : syracuseStep 7919021 = 2969633) B2969633
theorem B2602415 : Blo 1541468 2602415 := bstep (se 1 (by rfl) ⟨1951811, by rfl⟩ : syracuseStep 2602415 = 3903623) B3903623
theorem B53450189 : Blo 1541468 53450189 := bstep (se 3 (by rfl) ⟨10021910, by rfl⟩ : syracuseStep 53450189 = 20043821) B20043821
theorem B7910875 : Blo 1541468 7910875 := bstep (se 1 (by rfl) ⟨5933156, by rfl⟩ : syracuseStep 7910875 = 11866313) B11866313
theorem B1734223 : Blo 1541468 1734223 := bstep (se 1 (by rfl) ⟨1300667, by rfl⟩ : syracuseStep 1734223 = 2601335) B2601335
theorem B6592097 : Blo 1541468 6592097 := bstep (se 2 (by rfl) ⟨2472036, by rfl⟩ : syracuseStep 6592097 = 4944073) B4944073
theorem B11114129 : Blo 1541468 11114129 := bstep (se 2 (by rfl) ⟨4167798, by rfl⟩ : syracuseStep 11114129 = 8335597) B8335597
theorem B3471047 : Blo 1541468 3471047 := bstep (se 1 (by rfl) ⟨2603285, by rfl⟩ : syracuseStep 3471047 = 5206571) B5206571
theorem B7509719 : Blo 1541468 7509719 := bstep (se 1 (by rfl) ⟨5632289, by rfl⟩ : syracuseStep 7509719 = 11264579) B11264579
theorem B3905273 : Blo 1541468 3905273 := bstep (se 2 (by rfl) ⟨1464477, by rfl⟩ : syracuseStep 3905273 = 2928955) B2928955
theorem B2602847 : Blo 1541468 2602847 := bstep (se 1 (by rfl) ⟨1952135, by rfl⟩ : syracuseStep 2602847 = 3904271) B3904271
theorem B3905455 : Blo 1541468 3905455 := bstep (se 1 (by rfl) ⟨2929091, by rfl⟩ : syracuseStep 3905455 = 5858183) B5858183
theorem B14833601 : Blo 1541468 14833601 := bstep (se 2 (by rfl) ⟨5562600, by rfl⟩ : syracuseStep 14833601 = 11125201) B11125201
theorem B25016273 : Blo 1541468 25016273 := bstep (se 2 (by rfl) ⟨9381102, by rfl⟩ : syracuseStep 25016273 = 18762205) B18762205
theorem B1734619 : Blo 1541468 1734619 := bstep (se 1 (by rfl) ⟨1300964, by rfl⟩ : syracuseStep 1734619 = 2601929) B2601929
theorem B5208083 : Blo 1541468 5208083 := bstep (se 1 (by rfl) ⟨3906062, by rfl⟩ : syracuseStep 5208083 = 7812125) B7812125
theorem B5208407 : Blo 1541468 5208407 := bstep (se 1 (by rfl) ⟨3906305, by rfl⟩ : syracuseStep 5208407 = 7812611) B7812611
theorem B3905921 : Blo 1541468 3905921 := bstep (se 2 (by rfl) ⟨1464720, by rfl⟩ : syracuseStep 3905921 = 2929441) B2929441
theorem B2603407 : Blo 1541468 2603407 := bstep (se 1 (by rfl) ⟨1952555, by rfl⟩ : syracuseStep 2603407 = 3905111) B3905111
theorem B1735087 : Blo 1541468 1735087 := bstep (se 1 (by rfl) ⟨1301315, by rfl⟩ : syracuseStep 1735087 = 2602631) B2602631
theorem B5855753 : Blo 1541468 5855753 := bstep (se 2 (by rfl) ⟨2195907, by rfl⟩ : syracuseStep 5855753 = 4391815) B4391815
theorem B3471911 : Blo 1541468 3471911 := bstep (se 1 (by rfl) ⟨2603933, by rfl⟩ : syracuseStep 3471911 = 5207867) B5207867
theorem B5634695 : Blo 1541468 5634695 := bstep (se 1 (by rfl) ⟨4226021, by rfl⟩ : syracuseStep 5634695 = 8452043) B8452043
theorem B1563355 : Blo 1541468 1563355 := bstep (se 1 (by rfl) ⟨1172516, by rfl⟩ : syracuseStep 1563355 = 2345033) B2345033
theorem B5561131 : Blo 1541468 5561131 := bstep (se 1 (by rfl) ⟨4170848, by rfl⟩ : syracuseStep 5561131 = 8341697) B8341697
theorem B3906377 : Blo 1541468 3906377 := bstep (se 2 (by rfl) ⟨1464891, by rfl⟩ : syracuseStep 3906377 = 2929783) B2929783
theorem B42810205 : Blo 1541468 42810205 := bstep (se 3 (by rfl) ⟨8026913, by rfl⟩ : syracuseStep 42810205 = 16053827) B16053827
theorem B1735519 : Blo 1541468 1735519 := bstep (se 1 (by rfl) ⟨1301639, by rfl⟩ : syracuseStep 1735519 = 2603279) B2603279
theorem B3472235 : Blo 1541468 3472235 := bstep (se 1 (by rfl) ⟨2604176, by rfl⟩ : syracuseStep 3472235 = 5208353) B5208353
theorem B3472289 : Blo 1541468 3472289 := bstep (se 2 (by rfl) ⟨1302108, by rfl⟩ : syracuseStep 3472289 = 2604217) B2604217
theorem B6585263 : Blo 1541468 6585263 := bstep (se 1 (by rfl) ⟨4938947, by rfl⟩ : syracuseStep 6585263 = 9877895) B9877895
theorem B2604089 : Blo 1541468 2604089 := bstep (se 2 (by rfl) ⟨976533, by rfl⟩ : syracuseStep 2604089 = 1953067) B1953067
theorem B3906731 : Blo 1541468 3906731 := bstep (se 1 (by rfl) ⟨2930048, by rfl⟩ : syracuseStep 3906731 = 5860097) B5860097
theorem B1735879 : Blo 1541468 1735879 := bstep (se 1 (by rfl) ⟨1301909, by rfl⟩ : syracuseStep 1735879 = 2603819) B2603819
theorem B3472631 : Blo 1541468 3472631 := bstep (se 1 (by rfl) ⟨2604473, by rfl⟩ : syracuseStep 3472631 = 5208947) B5208947
theorem B33373529 : Blo 1541468 33373529 := bstep (se 2 (by rfl) ⟨12515073, by rfl⟩ : syracuseStep 33373529 = 25030147) B25030147
theorem B6585725 : Blo 1541468 6585725 := bstep (se 3 (by rfl) ⟨1234823, by rfl⟩ : syracuseStep 6585725 = 2469647) B2469647
theorem B1564255 : Blo 1541468 1564255 := bstep (se 1 (by rfl) ⟨1173191, by rfl⟩ : syracuseStep 1564255 = 2346383) B2346383
theorem B5856907 : Blo 1541468 5856907 := bstep (se 1 (by rfl) ⟨4392680, by rfl⟩ : syracuseStep 5856907 = 8785361) B8785361
theorem B19029725 : Blo 1541468 19029725 := bstep (se 3 (by rfl) ⟨3568073, by rfl⟩ : syracuseStep 19029725 = 7136147) B7136147
theorem B10559213 : Blo 1541468 10559213 := bstep (se 3 (by rfl) ⟨1979852, by rfl⟩ : syracuseStep 10559213 = 3959705) B3959705
theorem B4169465 : Blo 1541468 4169465 := bstep (se 2 (by rfl) ⟨1563549, by rfl⟩ : syracuseStep 4169465 = 3127099) B3127099
theorem B5275421 : Blo 1541468 5275421 := bstep (se 3 (by rfl) ⟨989141, by rfl⟩ : syracuseStep 5275421 = 1978283) B1978283
theorem B5857211 : Blo 1541468 5857211 := bstep (se 1 (by rfl) ⟨4392908, by rfl⟩ : syracuseStep 5857211 = 8785817) B8785817
theorem B6586697 : Blo 1541468 6586697 := bstep (se 2 (by rfl) ⟨2470011, by rfl⟩ : syracuseStep 6586697 = 4940023) B4940023
theorem B3293615 : Blo 1541468 3293615 := bstep (se 1 (by rfl) ⟨2470211, by rfl⟩ : syracuseStep 3293615 = 4940423) B4940423
theorem B3293759 : Blo 1541468 3293759 := bstep (se 1 (by rfl) ⟨2470319, by rfl⟩ : syracuseStep 3293759 = 4940639) B4940639
theorem B15835783 : Blo 1541468 15835783 := bstep (se 1 (by rfl) ⟨11876837, by rfl⟩ : syracuseStep 15835783 = 23753675) B23753675
theorem B6251179 : Blo 1541468 6251179 := bstep (se 1 (by rfl) ⟨4688384, by rfl⟩ : syracuseStep 6251179 = 9376769) B9376769
theorem B4391759 : Blo 1541468 4391759 := bstep (se 1 (by rfl) ⟨3293819, by rfl⟩ : syracuseStep 4391759 = 6587639) B6587639
theorem B14066579 : Blo 1541468 14066579 := bstep (se 1 (by rfl) ⟨10549934, by rfl⟩ : syracuseStep 14066579 = 21099869) B21099869
theorem B29639681 : Blo 1541468 29639681 := bstep (se 2 (by rfl) ⟨11114880, by rfl⟩ : syracuseStep 29639681 = 22229761) B22229761
theorem B7414841 : Blo 1541468 7414841 := bstep (se 2 (by rfl) ⟨2780565, by rfl⟩ : syracuseStep 7414841 = 5561131) B5561131
theorem B5006479 : Blo 1541468 5006479 := bstep (se 1 (by rfl) ⟨3754859, by rfl⟩ : syracuseStep 5006479 = 7509719) B7509719
theorem B3704057 : Blo 1541468 3704057 := bstep (se 2 (by rfl) ⟨1389021, by rfl⟩ : syracuseStep 3704057 = 2778043) B2778043
theorem B3294503 : Blo 1541468 3294503 := bstep (se 1 (by rfl) ⟨2470877, by rfl⟩ : syracuseStep 3294503 = 4941755) B4941755
theorem B9889067 : Blo 1541468 9889067 := bstep (se 1 (by rfl) ⟨7416800, by rfl⟩ : syracuseStep 9889067 = 14833601) B14833601
theorem B15828311 : Blo 1541468 15828311 := bstep (se 1 (by rfl) ⟨11871233, by rfl⟩ : syracuseStep 15828311 = 23742467) B23742467
theorem B1951067 : Blo 1541468 1951067 := bstep (se 1 (by rfl) ⟨1463300, by rfl⟩ : syracuseStep 1951067 = 2926601) B2926601
theorem B5858669 : Blo 1541468 5858669 := bstep (se 3 (by rfl) ⟨1098500, by rfl⟩ : syracuseStep 5858669 = 2197001) B2197001
theorem B1541487 : Blo 1541468 1541487 := bstep (se 1 (by rfl) ⟨1156115, by rfl⟩ : syracuseStep 1541487 = 2312231) B2312231
theorem B14828953 : Blo 1541468 14828953 := bstep (se 2 (by rfl) ⟨5560857, by rfl⟩ : syracuseStep 14828953 = 11121715) B11121715
theorem B1541543 : Blo 1541468 1541543 := bstep (se 1 (by rfl) ⟨1156157, by rfl⟩ : syracuseStep 1541543 = 2312315) B2312315
theorem B1541627 : Blo 1541468 1541627 := bstep (se 1 (by rfl) ⟨1156220, by rfl⟩ : syracuseStep 1541627 = 2312441) B2312441
theorem B1541695 : Blo 1541468 1541695 := bstep (se 1 (by rfl) ⟨1156271, by rfl⟩ : syracuseStep 1541695 = 2312543) B2312543
theorem B1541703 : Blo 1541468 1541703 := bstep (se 1 (by rfl) ⟨1156277, by rfl⟩ : syracuseStep 1541703 = 2312555) B2312555
theorem B33351385 : Blo 1541468 33351385 := bstep (se 2 (by rfl) ⟨12506769, by rfl⟩ : syracuseStep 33351385 = 25013539) B25013539
theorem B1541855 : Blo 1541468 1541855 := bstep (se 1 (by rfl) ⟨1156391, by rfl⟩ : syracuseStep 1541855 = 2312783) B2312783
theorem B3294955 : Blo 1541468 3294955 := bstep (se 1 (by rfl) ⟨2471216, by rfl⟩ : syracuseStep 3294955 = 4942433) B4942433
theorem B1541935 : Blo 1541468 1541935 := bstep (se 1 (by rfl) ⟨1156451, by rfl⟩ : syracuseStep 1541935 = 2312903) B2312903
theorem B1951543 : Blo 1541468 1951543 := bstep (se 1 (by rfl) ⟨1463657, by rfl⟩ : syracuseStep 1951543 = 2927315) B2927315
theorem B5203817 : Blo 1541468 5203817 := bstep (se 2 (by rfl) ⟨1951431, by rfl⟩ : syracuseStep 5203817 = 3902863) B3902863
theorem B1542043 : Blo 1541468 1542043 := bstep (se 1 (by rfl) ⟨1156532, by rfl⟩ : syracuseStep 1542043 = 2313065) B2313065
theorem B1542095 : Blo 1541468 1542095 := bstep (se 1 (by rfl) ⟨1156571, by rfl⟩ : syracuseStep 1542095 = 2313143) B2313143
theorem B1542119 : Blo 1541468 1542119 := bstep (se 1 (by rfl) ⟨1156589, by rfl⟩ : syracuseStep 1542119 = 2313179) B2313179
theorem B2312297 : Blo 1541468 2312297 := bstep (se 2 (by rfl) ⟨867111, by rfl⟩ : syracuseStep 2312297 = 1734223) B1734223
theorem B7809209 : Blo 1541468 7809209 := bstep (se 2 (by rfl) ⟨2928453, by rfl⟩ : syracuseStep 7809209 = 5856907) B5856907
theorem B6588611 : Blo 1541468 6588611 := bstep (se 1 (by rfl) ⟨4941458, by rfl⟩ : syracuseStep 6588611 = 9882917) B9882917
theorem B5204249 : Blo 1541468 5204249 := bstep (se 2 (by rfl) ⟨1951593, by rfl⟩ : syracuseStep 5204249 = 3903187) B3903187
theorem B1542431 : Blo 1541468 1542431 := bstep (se 1 (by rfl) ⟨1156823, by rfl⟩ : syracuseStep 1542431 = 2313647) B2313647
theorem B1952039 : Blo 1541468 1952039 := bstep (se 1 (by rfl) ⟨1464029, by rfl⟩ : syracuseStep 1952039 = 2928059) B2928059
theorem B1542491 : Blo 1541468 1542491 := bstep (se 1 (by rfl) ⟨1156868, by rfl⟩ : syracuseStep 1542491 = 2313737) B2313737
theorem B1542511 : Blo 1541468 1542511 := bstep (se 1 (by rfl) ⟨1156883, by rfl⟩ : syracuseStep 1542511 = 2313767) B2313767
theorem B2312615 : Blo 1541468 2312615 := bstep (se 1 (by rfl) ⟨1734461, by rfl⟩ : syracuseStep 2312615 = 3468923) B3468923
theorem B1542567 : Blo 1541468 1542567 := bstep (se 1 (by rfl) ⟨1156925, by rfl⟩ : syracuseStep 1542567 = 2313851) B2313851
theorem B3901871 : Blo 1541468 3901871 := bstep (se 1 (by rfl) ⟨2926403, by rfl⟩ : syracuseStep 3901871 = 5852807) B5852807
theorem B4393399 : Blo 1541468 4393399 := bstep (se 1 (by rfl) ⟨3295049, by rfl⟩ : syracuseStep 4393399 = 6590099) B6590099
theorem B7039475 : Blo 1541468 7039475 := bstep (se 1 (by rfl) ⟨5279606, by rfl⟩ : syracuseStep 7039475 = 10559213) B10559213
theorem B2312699 : Blo 1541468 2312699 := bstep (se 1 (by rfl) ⟨1734524, by rfl⟩ : syracuseStep 2312699 = 3469049) B3469049
theorem B2779643 : Blo 1541468 2779643 := bstep (se 1 (by rfl) ⟨2084732, by rfl⟩ : syracuseStep 2779643 = 4169465) B4169465
theorem B1542651 : Blo 1541468 1542651 := bstep (se 1 (by rfl) ⟨1156988, by rfl⟩ : syracuseStep 1542651 = 2313977) B2313977
theorem B3516947 : Blo 1541468 3516947 := bstep (se 1 (by rfl) ⟨2637710, by rfl⟩ : syracuseStep 3516947 = 5275421) B5275421
theorem B1542719 : Blo 1541468 1542719 := bstep (se 1 (by rfl) ⟨1157039, by rfl⟩ : syracuseStep 1542719 = 2314079) B2314079
theorem B1542727 : Blo 1541468 1542727 := bstep (se 1 (by rfl) ⟨1157045, by rfl⟩ : syracuseStep 1542727 = 2314091) B2314091
theorem B1952363 : Blo 1541468 1952363 := bstep (se 1 (by rfl) ⟨1464272, by rfl⟩ : syracuseStep 1952363 = 2928545) B2928545
theorem B2312825 : Blo 1541468 2312825 := bstep (se 2 (by rfl) ⟨867309, by rfl⟩ : syracuseStep 2312825 = 1734619) B1734619
theorem B2312879 : Blo 1541468 2312879 := bstep (se 1 (by rfl) ⟨1734659, by rfl⟩ : syracuseStep 2312879 = 3469319) B3469319
theorem B2312927 : Blo 1541468 2312927 := bstep (se 1 (by rfl) ⟨1734695, by rfl⟩ : syracuseStep 2312927 = 3469391) B3469391
theorem B1542879 : Blo 1541468 1542879 := bstep (se 1 (by rfl) ⟨1157159, by rfl⟩ : syracuseStep 1542879 = 2314319) B2314319
theorem B1542959 : Blo 1541468 1542959 := bstep (se 1 (by rfl) ⟨1157219, by rfl⟩ : syracuseStep 1542959 = 2314439) B2314439
theorem B243837773 : Blo 1541468 243837773 := bstep (se 3 (by rfl) ⟨45719582, by rfl⟩ : syracuseStep 243837773 = 91439165) B91439165
theorem B26340227 : Blo 1541468 26340227 := bstep (se 1 (by rfl) ⟨19755170, by rfl⟩ : syracuseStep 26340227 = 39510341) B39510341
theorem B3296143 : Blo 1541468 3296143 := bstep (se 1 (by rfl) ⟨2472107, by rfl⟩ : syracuseStep 3296143 = 4944215) B4944215
theorem B1543067 : Blo 1541468 1543067 := bstep (se 1 (by rfl) ⟨1157300, by rfl⟩ : syracuseStep 1543067 = 2314601) B2314601
theorem B1543119 : Blo 1541468 1543119 := bstep (se 1 (by rfl) ⟨1157339, by rfl⟩ : syracuseStep 1543119 = 2314679) B2314679
theorem B3296219 : Blo 1541468 3296219 := bstep (se 1 (by rfl) ⟨2472164, by rfl⟩ : syracuseStep 3296219 = 4944329) B4944329
theorem B2313191 : Blo 1541468 2313191 := bstep (se 1 (by rfl) ⟨1734893, by rfl⟩ : syracuseStep 2313191 = 3469787) B3469787
theorem B1952743 : Blo 1541468 1952743 := bstep (se 1 (by rfl) ⟨1464557, by rfl⟩ : syracuseStep 1952743 = 2929115) B2929115
theorem B1543143 : Blo 1541468 1543143 := bstep (se 1 (by rfl) ⟨1157357, by rfl⟩ : syracuseStep 1543143 = 2314715) B2314715
theorem B28126223 : Blo 1541468 28126223 := bstep (se 1 (by rfl) ⟨21094667, by rfl⟩ : syracuseStep 28126223 = 42189335) B42189335
theorem B2313449 : Blo 1541468 2313449 := bstep (se 2 (by rfl) ⟨867543, by rfl⟩ : syracuseStep 2313449 = 1735087) B1735087
theorem B2313503 : Blo 1541468 2313503 := bstep (se 1 (by rfl) ⟨1735127, by rfl⟩ : syracuseStep 2313503 = 3470255) B3470255
theorem B1543455 : Blo 1541468 1543455 := bstep (se 1 (by rfl) ⟨1157591, by rfl⟩ : syracuseStep 1543455 = 2315183) B2315183
theorem B3902843 : Blo 1541468 3902843 := bstep (se 1 (by rfl) ⟨2927132, by rfl⟩ : syracuseStep 3902843 = 5854265) B5854265
theorem B3468743 : Blo 1541468 3468743 := bstep (se 1 (by rfl) ⟨2601557, by rfl⟩ : syracuseStep 3468743 = 5203115) B5203115
theorem B2313671 : Blo 1541468 2313671 := bstep (se 1 (by rfl) ⟨1735253, by rfl⟩ : syracuseStep 2313671 = 3470507) B3470507
theorem B5205599 : Blo 1541468 5205599 := bstep (se 1 (by rfl) ⟨3904199, by rfl⟩ : syracuseStep 5205599 = 7808399) B7808399
theorem B5279347 : Blo 1541468 5279347 := bstep (se 1 (by rfl) ⟨3959510, by rfl⟩ : syracuseStep 5279347 = 7919021) B7919021
theorem B2084473 : Blo 1541468 2084473 := bstep (se 2 (by rfl) ⟨781677, by rfl⟩ : syracuseStep 2084473 = 1563355) B1563355
theorem B3903137 : Blo 1541468 3903137 := bstep (se 2 (by rfl) ⟨1463676, by rfl⟩ : syracuseStep 3903137 = 2927353) B2927353
theorem B17567441 : Blo 1541468 17567441 := bstep (se 2 (by rfl) ⟨6587790, by rfl⟩ : syracuseStep 17567441 = 13175581) B13175581
theorem B9383633 : Blo 1541468 9383633 := bstep (se 2 (by rfl) ⟨3518862, by rfl⟩ : syracuseStep 9383633 = 7037725) B7037725
theorem B4394731 : Blo 1541468 4394731 := bstep (se 1 (by rfl) ⟨3296048, by rfl⟩ : syracuseStep 4394731 = 6592097) B6592097
theorem B2314025 : Blo 1541468 2314025 := bstep (se 2 (by rfl) ⟨867759, by rfl⟩ : syracuseStep 2314025 = 1735519) B1735519
theorem B3469103 : Blo 1541468 3469103 := bstep (se 1 (by rfl) ⟨2601827, by rfl⟩ : syracuseStep 3469103 = 5203655) B5203655
theorem B2314031 : Blo 1541468 2314031 := bstep (se 1 (by rfl) ⟨1735523, by rfl⟩ : syracuseStep 2314031 = 3471047) B3471047
theorem B4943663 : Blo 1541468 4943663 := bstep (se 1 (by rfl) ⟨3707747, by rfl⟩ : syracuseStep 4943663 = 7415495) B7415495
theorem B7810991 : Blo 1541468 7810991 := bstep (se 1 (by rfl) ⟨5858243, by rfl⟩ : syracuseStep 7810991 = 11716487) B11716487
theorem B2314505 : Blo 1541468 2314505 := bstep (se 2 (by rfl) ⟨867939, by rfl⟩ : syracuseStep 2314505 = 1735879) B1735879
theorem B3903835 : Blo 1541468 3903835 := bstep (se 1 (by rfl) ⟨2927876, by rfl⟩ : syracuseStep 3903835 = 5855753) B5855753
theorem B3469679 : Blo 1541468 3469679 := bstep (se 1 (by rfl) ⟨2602259, by rfl⟩ : syracuseStep 3469679 = 5204519) B5204519
theorem B2314607 : Blo 1541468 2314607 := bstep (se 1 (by rfl) ⟨1735955, by rfl⟩ : syracuseStep 2314607 = 3471911) B3471911
theorem B3756463 : Blo 1541468 3756463 := bstep (se 1 (by rfl) ⟨2817347, by rfl⟩ : syracuseStep 3756463 = 5634695) B5634695
theorem B3469751 : Blo 1541468 3469751 := bstep (se 1 (by rfl) ⟨2602313, by rfl⟩ : syracuseStep 3469751 = 5204627) B5204627
theorem B3469895 : Blo 1541468 3469895 := bstep (se 1 (by rfl) ⟨2602421, by rfl⟩ : syracuseStep 3469895 = 5204843) B5204843
theorem B2314823 : Blo 1541468 2314823 := bstep (se 1 (by rfl) ⟨1736117, by rfl⟩ : syracuseStep 2314823 = 3472235) B3472235
theorem B3469931 : Blo 1541468 3469931 := bstep (se 1 (by rfl) ⟨2602448, by rfl⟩ : syracuseStep 3469931 = 5204897) B5204897
theorem B2929259 : Blo 1541468 2929259 := bstep (se 1 (by rfl) ⟨2196944, by rfl⟩ : syracuseStep 2929259 = 4393889) B4393889
theorem B2314859 : Blo 1541468 2314859 := bstep (se 1 (by rfl) ⟨1736144, by rfl⟩ : syracuseStep 2314859 = 3472289) B3472289
theorem B10547833 : Blo 1541468 10547833 := bstep (se 2 (by rfl) ⟨3955437, by rfl⟩ : syracuseStep 10547833 = 7910875) B7910875
theorem B2085673 : Blo 1541468 2085673 := bstep (se 2 (by rfl) ⟨782127, by rfl⟩ : syracuseStep 2085673 = 1564255) B1564255
theorem B2315087 : Blo 1541468 2315087 := bstep (se 1 (by rfl) ⟨1736315, by rfl⟩ : syracuseStep 2315087 = 3472631) B3472631
theorem B5207003 : Blo 1541468 5207003 := bstep (se 1 (by rfl) ⟨3905252, by rfl⟩ : syracuseStep 5207003 = 7810505) B7810505
theorem B3470327 : Blo 1541468 3470327 := bstep (se 1 (by rfl) ⟨2602745, by rfl⟩ : syracuseStep 3470327 = 5205491) B5205491
theorem B8787001 : Blo 1541468 8787001 := bstep (se 2 (by rfl) ⟨3295125, by rfl⟩ : syracuseStep 8787001 = 6590251) B6590251
theorem B5207165 : Blo 1541468 5207165 := bstep (se 3 (by rfl) ⟨976343, by rfl⟩ : syracuseStep 5207165 = 1952687) B1952687
theorem B12686483 : Blo 1541468 12686483 := bstep (se 1 (by rfl) ⟨9514862, by rfl⟩ : syracuseStep 12686483 = 19029725) B19029725
theorem B18773207 : Blo 1541468 18773207 := bstep (se 1 (by rfl) ⟨14079905, by rfl⟩ : syracuseStep 18773207 = 28159811) B28159811
theorem B5207273 : Blo 1541468 5207273 := bstep (se 2 (by rfl) ⟨1952727, by rfl⟩ : syracuseStep 5207273 = 3905455) B3905455
theorem B3904807 : Blo 1541468 3904807 := bstep (se 1 (by rfl) ⟨2928605, by rfl⟩ : syracuseStep 3904807 = 5857211) B5857211
theorem B3470687 : Blo 1541468 3470687 := bstep (se 1 (by rfl) ⟨2603015, by rfl⟩ : syracuseStep 3470687 = 5206031) B5206031
theorem B5207435 : Blo 1541468 5207435 := bstep (se 1 (by rfl) ⟨3905576, by rfl⟩ : syracuseStep 5207435 = 7811153) B7811153
theorem B7804349 : Blo 1541468 7804349 := bstep (se 3 (by rfl) ⟨1463315, by rfl⟩ : syracuseStep 7804349 = 2926631) B2926631
theorem B13178315 : Blo 1541468 13178315 := bstep (se 1 (by rfl) ⟨9883736, by rfl⟩ : syracuseStep 13178315 = 19767473) B19767473
theorem B2602489 : Blo 1541468 2602489 := bstep (se 2 (by rfl) ⟨975933, by rfl⟩ : syracuseStep 2602489 = 1951867) B1951867
theorem B3905081 : Blo 1541468 3905081 := bstep (se 2 (by rfl) ⟨1464405, by rfl⟩ : syracuseStep 3905081 = 2928811) B2928811
theorem B3167839 : Blo 1541468 3167839 := bstep (se 1 (by rfl) ⟨2375879, by rfl⟩ : syracuseStep 3167839 = 4751759) B4751759
theorem B231478885 : Blo 1541468 231478885 := bstep (se 4 (by rfl) ⟨21701145, by rfl⟩ : syracuseStep 231478885 = 43402291) B43402291
theorem B1734367 : Blo 1541468 1734367 := bstep (se 1 (by rfl) ⟨1300775, by rfl⟩ : syracuseStep 1734367 = 2601551) B2601551
theorem B3471083 : Blo 1541468 3471083 := bstep (se 1 (by rfl) ⟨2603312, by rfl⟩ : syracuseStep 3471083 = 5206625) B5206625
theorem B2602759 : Blo 1541468 2602759 := bstep (se 1 (by rfl) ⟨1952069, by rfl⟩ : syracuseStep 2602759 = 3904139) B3904139
theorem B2602793 : Blo 1541468 2602793 := bstep (se 2 (by rfl) ⟨976047, by rfl⟩ : syracuseStep 2602793 = 1952095) B1952095
theorem B6592337 : Blo 1541468 6592337 := bstep (se 2 (by rfl) ⟨2472126, by rfl⟩ : syracuseStep 6592337 = 4944253) B4944253
theorem B3471209 : Blo 1541468 3471209 := bstep (se 2 (by rfl) ⟨1301703, by rfl⟩ : syracuseStep 3471209 = 2603407) B2603407
theorem B5937185 : Blo 1541468 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B6592697 : Blo 1541468 6592697 := bstep (se 2 (by rfl) ⟨2472261, by rfl⟩ : syracuseStep 6592697 = 4944523) B4944523
theorem B72194327 : Blo 1541468 72194327 := bstep (se 1 (by rfl) ⟨54145745, by rfl⟩ : syracuseStep 72194327 = 108291491) B108291491
theorem B1734943 : Blo 1541468 1734943 := bstep (se 1 (by rfl) ⟨1301207, by rfl⟩ : syracuseStep 1734943 = 2602415) B2602415
theorem B35633459 : Blo 1541468 35633459 := bstep (se 1 (by rfl) ⟨26725094, by rfl⟩ : syracuseStep 35633459 = 53450189) B53450189
theorem B57080273 : Blo 1541468 57080273 := bstep (se 2 (by rfl) ⟨21405102, by rfl⟩ : syracuseStep 57080273 = 42810205) B42810205
theorem B3955169 : Blo 1541468 3955169 := bstep (se 2 (by rfl) ⟨1483188, by rfl⟩ : syracuseStep 3955169 = 2966377) B2966377
theorem B2603515 : Blo 1541468 2603515 := bstep (se 1 (by rfl) ⟨1952636, by rfl⟩ : syracuseStep 2603515 = 3905273) B3905273
theorem B4168255 : Blo 1541468 4168255 := bstep (se 1 (by rfl) ⟨3126191, by rfl⟩ : syracuseStep 4168255 = 6252383) B6252383
theorem B1735231 : Blo 1541468 1735231 := bstep (se 1 (by rfl) ⟨1301423, by rfl⟩ : syracuseStep 1735231 = 2602847) B2602847
theorem B16677515 : Blo 1541468 16677515 := bstep (se 1 (by rfl) ⟨12508136, by rfl⟩ : syracuseStep 16677515 = 25016273) B25016273
theorem B3472055 : Blo 1541468 3472055 := bstep (se 1 (by rfl) ⟨2604041, by rfl⟩ : syracuseStep 3472055 = 5208083) B5208083
theorem B9886607 : Blo 1541468 9886607 := bstep (se 1 (by rfl) ⟨7414955, by rfl⟩ : syracuseStep 9886607 = 14829911) B14829911
theorem B3472271 : Blo 1541468 3472271 := bstep (se 1 (by rfl) ⟨2604203, by rfl⟩ : syracuseStep 3472271 = 5208407) B5208407
theorem B2603947 : Blo 1541468 2603947 := bstep (se 1 (by rfl) ⟨1952960, by rfl⟩ : syracuseStep 2603947 = 3905921) B3905921
theorem B29637677 : Blo 1541468 29637677 := bstep (se 3 (by rfl) ⟨5557064, by rfl⟩ : syracuseStep 29637677 = 11114129) B11114129
theorem B13179955 : Blo 1541468 13179955 := bstep (se 1 (by rfl) ⟨9884966, by rfl⟩ : syracuseStep 13179955 = 19769933) B19769933
theorem B32079037 : Blo 1541468 32079037 := bstep (se 3 (by rfl) ⟨6014819, by rfl⟩ : syracuseStep 32079037 = 12029639) B12029639
theorem B2604251 : Blo 1541468 2604251 := bstep (se 1 (by rfl) ⟨1953188, by rfl⟩ : syracuseStep 2604251 = 3906377) B3906377
theorem B4390175 : Blo 1541468 4390175 := bstep (se 1 (by rfl) ⟨3292631, by rfl⟩ : syracuseStep 4390175 = 6585263) B6585263
theorem B4939127 : Blo 1541468 4939127 := bstep (se 1 (by rfl) ⟨3704345, by rfl⟩ : syracuseStep 4939127 = 7408691) B7408691
theorem B1736059 : Blo 1541468 1736059 := bstep (se 1 (by rfl) ⟨1302044, by rfl⟩ : syracuseStep 1736059 = 2604089) B2604089
theorem B9878921 : Blo 1541468 9878921 := bstep (se 2 (by rfl) ⟨3704595, by rfl⟩ : syracuseStep 9878921 = 7409191) B7409191
theorem B2604487 : Blo 1541468 2604487 := bstep (se 1 (by rfl) ⟨1953365, by rfl⟩ : syracuseStep 2604487 = 3906731) B3906731
theorem B65068505 : Blo 1541468 65068505 := bstep (se 2 (by rfl) ⟨24400689, by rfl⟩ : syracuseStep 65068505 = 48801379) B48801379
theorem B22249019 : Blo 1541468 22249019 := bstep (se 1 (by rfl) ⟨16686764, by rfl⟩ : syracuseStep 22249019 = 33373529) B33373529
theorem B4390483 : Blo 1541468 4390483 := bstep (se 1 (by rfl) ⟨3292862, by rfl⟩ : syracuseStep 4390483 = 6585725) B6585725
theorem B5857181 : Blo 1541468 5857181 := bstep (se 3 (by rfl) ⟨1098221, by rfl⟩ : syracuseStep 5857181 = 2196443) B2196443
theorem B2195743 : Blo 1541468 2195743 := bstep (se 1 (by rfl) ⟨1646807, by rfl⟩ : syracuseStep 2195743 = 3293615) B3293615
theorem B2195839 : Blo 1541468 2195839 := bstep (se 1 (by rfl) ⟨1646879, by rfl⟩ : syracuseStep 2195839 = 3293759) B3293759
theorem B5857865 : Blo 1541468 5857865 := bstep (se 2 (by rfl) ⟨2196699, by rfl⟩ : syracuseStep 5857865 = 4393399) B4393399
theorem B28156517 : Blo 1541468 28156517 := bstep (se 4 (by rfl) ⟨2639673, by rfl⟩ : syracuseStep 28156517 = 5279347) B5279347
theorem B11117189 : Blo 1541468 11117189 := bstep (se 4 (by rfl) ⟨1042236, by rfl⟩ : syracuseStep 11117189 = 2084473) B2084473
theorem B19759787 : Blo 1541468 19759787 := bstep (se 1 (by rfl) ⟨14819840, by rfl⟩ : syracuseStep 19759787 = 29639681) B29639681
theorem B26370845 : Blo 1541468 26370845 := bstep (se 3 (by rfl) ⟨4944533, by rfl⟩ : syracuseStep 26370845 = 9889067) B9889067
theorem B17564525 : Blo 1541468 17564525 := bstep (se 3 (by rfl) ⟨3293348, by rfl⟩ : syracuseStep 17564525 = 6586697) B6586697
theorem B2196335 : Blo 1541468 2196335 := bstep (se 1 (by rfl) ⟨1647251, by rfl⟩ : syracuseStep 2196335 = 3294503) B3294503
theorem B10552207 : Blo 1541468 10552207 := bstep (se 1 (by rfl) ⟨7914155, by rfl⟩ : syracuseStep 10552207 = 15828311) B15828311
theorem B5202845 : Blo 1541468 5202845 := bstep (se 3 (by rfl) ⟨975533, by rfl⟩ : syracuseStep 5202845 = 1951067) B1951067
theorem B5202899 : Blo 1541468 5202899 := bstep (se 1 (by rfl) ⟨3902174, by rfl⟩ : syracuseStep 5202899 = 7804349) B7804349
theorem B17573273 : Blo 1541468 17573273 := bstep (se 2 (by rfl) ⟨6589977, by rfl⟩ : syracuseStep 17573273 = 13179955) B13179955
theorem B1541531 : Blo 1541468 1541531 := bstep (se 1 (by rfl) ⟨1156148, by rfl⟩ : syracuseStep 1541531 = 2312297) B2312297
theorem B11716001 : Blo 1541468 11716001 := bstep (se 2 (by rfl) ⟨4393500, by rfl⟩ : syracuseStep 11716001 = 8787001) B8787001
theorem B4392407 : Blo 1541468 4392407 := bstep (se 1 (by rfl) ⟨3294305, by rfl⟩ : syracuseStep 4392407 = 6588611) B6588611
theorem B48129551 : Blo 1541468 48129551 := bstep (se 1 (by rfl) ⟨36097163, by rfl⟩ : syracuseStep 48129551 = 72194327) B72194327
theorem B42772049 : Blo 1541468 42772049 := bstep (se 2 (by rfl) ⟨16039518, by rfl⟩ : syracuseStep 42772049 = 32079037) B32079037
theorem B1541743 : Blo 1541468 1541743 := bstep (se 1 (by rfl) ⟨1156307, by rfl⟩ : syracuseStep 1541743 = 2312615) B2312615
theorem B1541799 : Blo 1541468 1541799 := bstep (se 1 (by rfl) ⟨1156349, by rfl⟩ : syracuseStep 1541799 = 2312699) B2312699
theorem B2344631 : Blo 1541468 2344631 := bstep (se 1 (by rfl) ⟨1758473, by rfl⟩ : syracuseStep 2344631 = 3516947) B3516947
theorem B1541883 : Blo 1541468 1541883 := bstep (se 1 (by rfl) ⟨1156412, by rfl⟩ : syracuseStep 1541883 = 2312825) B2312825
theorem B11118343 : Blo 1541468 11118343 := bstep (se 1 (by rfl) ⟨8338757, by rfl⟩ : syracuseStep 11118343 = 16677515) B16677515
theorem B1541919 : Blo 1541468 1541919 := bstep (se 1 (by rfl) ⟨1156439, by rfl⟩ : syracuseStep 1541919 = 2312879) B2312879
theorem B1541951 : Blo 1541468 1541951 := bstep (se 1 (by rfl) ⟨1156463, by rfl⟩ : syracuseStep 1541951 = 2312927) B2312927
theorem B1542127 : Blo 1541468 1542127 := bstep (se 1 (by rfl) ⟨1156595, by rfl⟩ : syracuseStep 1542127 = 2313191) B2313191
theorem B1542299 : Blo 1541468 1542299 := bstep (se 1 (by rfl) ⟨1156724, by rfl⟩ : syracuseStep 1542299 = 2313449) B2313449
theorem B2926783 : Blo 1541468 2926783 := bstep (se 1 (by rfl) ⟨2195087, by rfl⟩ : syracuseStep 2926783 = 4390175) B4390175
theorem B1542335 : Blo 1541468 1542335 := bstep (se 1 (by rfl) ⟨1156751, by rfl⟩ : syracuseStep 1542335 = 2313503) B2313503
theorem B44468513 : Blo 1541468 44468513 := bstep (se 2 (by rfl) ⟨16675692, by rfl⟩ : syracuseStep 44468513 = 33351385) B33351385
theorem B2312489 : Blo 1541468 2312489 := bstep (se 2 (by rfl) ⟨867183, by rfl⟩ : syracuseStep 2312489 = 1734367) B1734367
theorem B2312495 : Blo 1541468 2312495 := bstep (se 1 (by rfl) ⟨1734371, by rfl⟩ : syracuseStep 2312495 = 3468743) B3468743
theorem B1542447 : Blo 1541468 1542447 := bstep (se 1 (by rfl) ⟨1156835, by rfl⟩ : syracuseStep 1542447 = 2313671) B2313671
theorem B4393273 : Blo 1541468 4393273 := bstep (se 2 (by rfl) ⟨1647477, by rfl⟩ : syracuseStep 4393273 = 3294955) B3294955
theorem B5859641 : Blo 1541468 5859641 := bstep (se 2 (by rfl) ⟨2197365, by rfl⟩ : syracuseStep 5859641 = 4394731) B4394731
theorem B43379003 : Blo 1541468 43379003 := bstep (se 1 (by rfl) ⟨32534252, by rfl⟩ : syracuseStep 43379003 = 65068505) B65068505
theorem B1542683 : Blo 1541468 1542683 := bstep (se 1 (by rfl) ⟨1157012, by rfl⟩ : syracuseStep 1542683 = 2314025) B2314025
theorem B2312735 : Blo 1541468 2312735 := bstep (se 1 (by rfl) ⟨1734551, by rfl⟩ : syracuseStep 2312735 = 3469103) B3469103
theorem B1542687 : Blo 1541468 1542687 := bstep (se 1 (by rfl) ⟨1157015, by rfl⟩ : syracuseStep 1542687 = 2314031) B2314031
theorem B3295775 : Blo 1541468 3295775 := bstep (se 1 (by rfl) ⟨2471831, by rfl⟩ : syracuseStep 3295775 = 4943663) B4943663
theorem B1543003 : Blo 1541468 1543003 := bstep (se 1 (by rfl) ⟨1157252, by rfl⟩ : syracuseStep 1543003 = 2314505) B2314505
theorem B2313119 : Blo 1541468 2313119 := bstep (se 1 (by rfl) ⟨1734839, by rfl⟩ : syracuseStep 2313119 = 3469679) B3469679
theorem B1543071 : Blo 1541468 1543071 := bstep (se 1 (by rfl) ⟨1157303, by rfl⟩ : syracuseStep 1543071 = 2314607) B2314607
theorem B2313167 : Blo 1541468 2313167 := bstep (se 1 (by rfl) ⟨1734875, by rfl⟩ : syracuseStep 2313167 = 3469751) B3469751
theorem B2313257 : Blo 1541468 2313257 := bstep (se 2 (by rfl) ⟨867471, by rfl⟩ : syracuseStep 2313257 = 1734943) B1734943
theorem B2313263 : Blo 1541468 2313263 := bstep (se 1 (by rfl) ⟨1734947, by rfl⟩ : syracuseStep 2313263 = 3469895) B3469895
theorem B1543215 : Blo 1541468 1543215 := bstep (se 1 (by rfl) ⟨1157411, by rfl⟩ : syracuseStep 1543215 = 2314823) B2314823
theorem B2313287 : Blo 1541468 2313287 := bstep (se 1 (by rfl) ⟨1734965, by rfl⟩ : syracuseStep 2313287 = 3469931) B3469931
theorem B1952839 : Blo 1541468 1952839 := bstep (se 1 (by rfl) ⟨1464629, by rfl⟩ : syracuseStep 1952839 = 2929259) B2929259
theorem B1543239 : Blo 1541468 1543239 := bstep (se 1 (by rfl) ⟨1157429, by rfl⟩ : syracuseStep 1543239 = 2314859) B2314859
theorem B5205113 : Blo 1541468 5205113 := bstep (se 2 (by rfl) ⟨1951917, by rfl⟩ : syracuseStep 5205113 = 3903835) B3903835
theorem B16895141 : Blo 1541468 16895141 := bstep (se 4 (by rfl) ⟨1583919, by rfl⟩ : syracuseStep 16895141 = 3167839) B3167839
theorem B2927839 : Blo 1541468 2927839 := bstep (se 1 (by rfl) ⟨2195879, by rfl⟩ : syracuseStep 2927839 = 4391759) B4391759
theorem B1543391 : Blo 1541468 1543391 := bstep (se 1 (by rfl) ⟨1157543, by rfl⟩ : syracuseStep 1543391 = 2315087) B2315087
theorem B2313551 : Blo 1541468 2313551 := bstep (se 1 (by rfl) ⟨1735163, by rfl⟩ : syracuseStep 2313551 = 3470327) B3470327
theorem B5557673 : Blo 1541468 5557673 := bstep (se 2 (by rfl) ⟨2084127, by rfl⟩ : syracuseStep 5557673 = 4168255) B4168255
theorem B2313641 : Blo 1541468 2313641 := bstep (se 2 (by rfl) ⟨867615, by rfl⟩ : syracuseStep 2313641 = 1735231) B1735231
theorem B5205437 : Blo 1541468 5205437 := bstep (se 3 (by rfl) ⟨976019, by rfl⟩ : syracuseStep 5205437 = 1952039) B1952039
theorem B2469371 : Blo 1541468 2469371 := bstep (se 1 (by rfl) ⟨1852028, by rfl⟩ : syracuseStep 2469371 = 3704057) B3704057
theorem B21114377 : Blo 1541468 21114377 := bstep (se 2 (by rfl) ⟨7917891, by rfl⟩ : syracuseStep 21114377 = 15835783) B15835783
theorem B8334905 : Blo 1541468 8334905 := bstep (se 2 (by rfl) ⟨3125589, by rfl⟩ : syracuseStep 8334905 = 6251179) B6251179
theorem B2313791 : Blo 1541468 2313791 := bstep (se 1 (by rfl) ⟨1735343, by rfl⟩ : syracuseStep 2313791 = 3470687) B3470687
theorem B8785543 : Blo 1541468 8785543 := bstep (se 1 (by rfl) ⟨6589157, by rfl⟩ : syracuseStep 8785543 = 13178315) B13178315
theorem B2780897 : Blo 1541468 2780897 := bstep (se 2 (by rfl) ⟨1042836, by rfl⟩ : syracuseStep 2780897 = 2085673) B2085673
theorem B2314055 : Blo 1541468 2314055 := bstep (se 1 (by rfl) ⟨1735541, by rfl⟩ : syracuseStep 2314055 = 3471083) B3471083
theorem B4394857 : Blo 1541468 4394857 := bstep (se 2 (by rfl) ⟨1648071, by rfl⟩ : syracuseStep 4394857 = 3296143) B3296143
theorem B4394891 : Blo 1541468 4394891 := bstep (se 1 (by rfl) ⟨3296168, by rfl⟩ : syracuseStep 4394891 = 6592337) B6592337
theorem B3469211 : Blo 1541468 3469211 := bstep (se 1 (by rfl) ⟨2601908, by rfl⟩ : syracuseStep 3469211 = 5203817) B5203817
theorem B2314139 : Blo 1541468 2314139 := bstep (se 1 (by rfl) ⟨1735604, by rfl⟩ : syracuseStep 2314139 = 3471209) B3471209
theorem B10547117 : Blo 1541468 10547117 := bstep (se 3 (by rfl) ⟨1977584, by rfl⟩ : syracuseStep 10547117 = 3955169) B3955169
theorem B5206139 : Blo 1541468 5206139 := bstep (se 1 (by rfl) ⟨3904604, by rfl⟩ : syracuseStep 5206139 = 7809209) B7809209
theorem B4395131 : Blo 1541468 4395131 := bstep (se 1 (by rfl) ⟨3296348, by rfl⟩ : syracuseStep 4395131 = 6592697) B6592697
theorem B3469499 : Blo 1541468 3469499 := bstep (se 1 (by rfl) ⟨2602124, by rfl⟩ : syracuseStep 3469499 = 5204249) B5204249
theorem B5206301 : Blo 1541468 5206301 := bstep (se 3 (by rfl) ⟨976181, by rfl⟩ : syracuseStep 5206301 = 1952363) B1952363
theorem B2601247 : Blo 1541468 2601247 := bstep (se 1 (by rfl) ⟨1950935, by rfl⟩ : syracuseStep 2601247 = 3901871) B3901871
theorem B5206409 : Blo 1541468 5206409 := bstep (se 2 (by rfl) ⟨1952403, by rfl⟩ : syracuseStep 5206409 = 3904807) B3904807
theorem B2314703 : Blo 1541468 2314703 := bstep (se 1 (by rfl) ⟨1736027, by rfl⟩ : syracuseStep 2314703 = 3472055) B3472055
theorem B2314745 : Blo 1541468 2314745 := bstep (se 2 (by rfl) ⟨868029, by rfl⟩ : syracuseStep 2314745 = 1736059) B1736059
theorem B19771937 : Blo 1541468 19771937 := bstep (se 2 (by rfl) ⟨7414476, by rfl⟩ : syracuseStep 19771937 = 14828953) B14828953
theorem B162558515 : Blo 1541468 162558515 := bstep (se 1 (by rfl) ⟨121918886, by rfl⟩ : syracuseStep 162558515 = 243837773) B243837773
theorem B17560151 : Blo 1541468 17560151 := bstep (se 1 (by rfl) ⟨13170113, by rfl⟩ : syracuseStep 17560151 = 26340227) B26340227
theorem B6591071 : Blo 1541468 6591071 := bstep (se 1 (by rfl) ⟨4943303, by rfl⟩ : syracuseStep 6591071 = 9886607) B9886607
theorem B2314847 : Blo 1541468 2314847 := bstep (se 1 (by rfl) ⟨1736135, by rfl⟩ : syracuseStep 2314847 = 3472271) B3472271
theorem B3469985 : Blo 1541468 3469985 := bstep (se 2 (by rfl) ⟨1301244, by rfl⟩ : syracuseStep 3469985 = 2602489) B2602489
theorem B5853977 : Blo 1541468 5853977 := bstep (se 2 (by rfl) ⟨2195241, by rfl⟩ : syracuseStep 5853977 = 4390483) B4390483
theorem B308638513 : Blo 1541468 308638513 := bstep (se 2 (by rfl) ⟨115739442, by rfl⟩ : syracuseStep 308638513 = 231478885) B231478885
theorem B20034469 : Blo 1541468 20034469 := bstep (se 4 (by rfl) ⟨1878231, by rfl⟩ : syracuseStep 20034469 = 3756463) B3756463
theorem B2601895 : Blo 1541468 2601895 := bstep (se 1 (by rfl) ⟨1951421, by rfl⟩ : syracuseStep 2601895 = 3902843) B3902843
theorem B3470345 : Blo 1541468 3470345 := bstep (se 2 (by rfl) ⟨1301379, by rfl⟩ : syracuseStep 3470345 = 2602759) B2602759
theorem B14832679 : Blo 1541468 14832679 := bstep (se 1 (by rfl) ⟨11124509, by rfl⟩ : syracuseStep 14832679 = 22249019) B22249019
theorem B3470399 : Blo 1541468 3470399 := bstep (se 1 (by rfl) ⟨2602799, by rfl⟩ : syracuseStep 3470399 = 5205599) B5205599
theorem B2602057 : Blo 1541468 2602057 := bstep (se 2 (by rfl) ⟨975771, by rfl⟩ : syracuseStep 2602057 = 1951543) B1951543
theorem B2602091 : Blo 1541468 2602091 := bstep (se 1 (by rfl) ⟨1951568, by rfl⟩ : syracuseStep 2602091 = 3903137) B3903137
theorem B11711627 : Blo 1541468 11711627 := bstep (se 1 (by rfl) ⟨8783720, by rfl⟩ : syracuseStep 11711627 = 17567441) B17567441
theorem B6255755 : Blo 1541468 6255755 := bstep (se 1 (by rfl) ⟨4691816, by rfl⟩ : syracuseStep 6255755 = 9383633) B9383633
theorem B3904787 : Blo 1541468 3904787 := bstep (se 1 (by rfl) ⟨2928590, by rfl⟩ : syracuseStep 3904787 = 5857181) B5857181
theorem B5207327 : Blo 1541468 5207327 := bstep (se 1 (by rfl) ⟨3905495, by rfl⟩ : syracuseStep 5207327 = 7810991) B7810991
theorem B15832493 : Blo 1541468 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B19772909 : Blo 1541468 19772909 := bstep (se 3 (by rfl) ⟨3707420, by rfl⟩ : syracuseStep 19772909 = 7414841) B7414841
theorem B33830621 : Blo 1541468 33830621 := bstep (se 3 (by rfl) ⟨6343241, by rfl⟩ : syracuseStep 33830621 = 12686483) B12686483
theorem B3471335 : Blo 1541468 3471335 := bstep (se 1 (by rfl) ⟨2603501, by rfl⟩ : syracuseStep 3471335 = 5207003) B5207003
theorem B3471353 : Blo 1541468 3471353 := bstep (se 2 (by rfl) ⟨1301757, by rfl⟩ : syracuseStep 3471353 = 2603515) B2603515
theorem B3471443 : Blo 1541468 3471443 := bstep (se 1 (by rfl) ⟨2603582, by rfl⟩ : syracuseStep 3471443 = 5207165) B5207165
theorem B12515471 : Blo 1541468 12515471 := bstep (se 1 (by rfl) ⟨9386603, by rfl⟩ : syracuseStep 12515471 = 18773207) B18773207
theorem B3471515 : Blo 1541468 3471515 := bstep (se 1 (by rfl) ⟨2603636, by rfl⟩ : syracuseStep 3471515 = 5207273) B5207273
theorem B14063777 : Blo 1541468 14063777 := bstep (se 2 (by rfl) ⟨5273916, by rfl⟩ : syracuseStep 14063777 = 10547833) B10547833
theorem B3905779 : Blo 1541468 3905779 := bstep (se 1 (by rfl) ⟨2929334, by rfl⟩ : syracuseStep 3905779 = 5858669) B5858669
theorem B3471623 : Blo 1541468 3471623 := bstep (se 1 (by rfl) ⟨2603717, by rfl⟩ : syracuseStep 3471623 = 5207435) B5207435
theorem B2603387 : Blo 1541468 2603387 := bstep (se 1 (by rfl) ⟨1952540, by rfl⟩ : syracuseStep 2603387 = 3905081) B3905081
theorem B1735195 : Blo 1541468 1735195 := bstep (se 1 (by rfl) ⟨1301396, by rfl⟩ : syracuseStep 1735195 = 2602793) B2602793
theorem B152214061 : Blo 1541468 152214061 := bstep (se 3 (by rfl) ⟨28540136, by rfl⟩ : syracuseStep 152214061 = 57080273) B57080273
theorem B3471929 : Blo 1541468 3471929 := bstep (se 2 (by rfl) ⟨1301973, by rfl⟩ : syracuseStep 3471929 = 2603947) B2603947
theorem B2603657 : Blo 1541468 2603657 := bstep (se 2 (by rfl) ⟨976371, by rfl⟩ : syracuseStep 2603657 = 1952743) B1952743
theorem B7412381 : Blo 1541468 7412381 := bstep (se 3 (by rfl) ⟨1389821, by rfl⟩ : syracuseStep 7412381 = 2779643) B2779643
theorem B6675305 : Blo 1541468 6675305 := bstep (se 2 (by rfl) ⟨2503239, by rfl⟩ : syracuseStep 6675305 = 5006479) B5006479
theorem B23755639 : Blo 1541468 23755639 := bstep (se 1 (by rfl) ⟨17816729, by rfl⟩ : syracuseStep 23755639 = 35633459) B35633459
theorem B4692983 : Blo 1541468 4692983 := bstep (se 1 (by rfl) ⟨3519737, by rfl⟩ : syracuseStep 4692983 = 7039475) B7039475
theorem B3472649 : Blo 1541468 3472649 := bstep (se 2 (by rfl) ⟨1302243, by rfl⟩ : syracuseStep 3472649 = 2604487) B2604487
theorem B18750815 : Blo 1541468 18750815 := bstep (se 1 (by rfl) ⟨14063111, by rfl⟩ : syracuseStep 18750815 = 28126223) B28126223
theorem B19758451 : Blo 1541468 19758451 := bstep (se 1 (by rfl) ⟨14818838, by rfl⟩ : syracuseStep 19758451 = 29637677) B29637677
theorem B1736167 : Blo 1541468 1736167 := bstep (se 1 (by rfl) ⟨1302125, by rfl⟩ : syracuseStep 1736167 = 2604251) B2604251
theorem B3292751 : Blo 1541468 3292751 := bstep (se 1 (by rfl) ⟨2469563, by rfl⟩ : syracuseStep 3292751 = 4939127) B4939127
theorem B6585947 : Blo 1541468 6585947 := bstep (se 1 (by rfl) ⟨4939460, by rfl⟩ : syracuseStep 6585947 = 9878921) B9878921
theorem B37510877 : Blo 1541468 37510877 := bstep (se 3 (by rfl) ⟨7033289, by rfl⟩ : syracuseStep 37510877 = 14066579) B14066579
theorem B8789917 : Blo 1541468 8789917 := bstep (se 3 (by rfl) ⟨1648109, by rfl⟩ : syracuseStep 8789917 = 3296219) B3296219
theorem B13181291 : Blo 1541468 13181291 := bstep (se 1 (by rfl) ⟨9885968, by rfl⟩ : syracuseStep 13181291 = 19771937) B19771937
theorem B108372343 : Blo 1541468 108372343 := bstep (se 1 (by rfl) ⟨81279257, by rfl⟩ : syracuseStep 108372343 = 162558515) B162558515
theorem B11706767 : Blo 1541468 11706767 := bstep (se 1 (by rfl) ⟨8780075, by rfl⟩ : syracuseStep 11706767 = 17560151) B17560151
theorem B5857697 : Blo 1541468 5857697 := bstep (se 2 (by rfl) ⟨2196636, by rfl⟩ : syracuseStep 5857697 = 4393273) B4393273
theorem B13173191 : Blo 1541468 13173191 := bstep (se 1 (by rfl) ⟨9879893, by rfl⟩ : syracuseStep 13173191 = 19759787) B19759787
theorem B17580563 : Blo 1541468 17580563 := bstep (se 1 (by rfl) ⟨13185422, by rfl⟩ : syracuseStep 17580563 = 26370845) B26370845
theorem B7807751 : Blo 1541468 7807751 := bstep (se 1 (by rfl) ⟨5855813, by rfl⟩ : syracuseStep 7807751 = 11711627) B11711627
theorem B4170503 : Blo 1541468 4170503 := bstep (se 1 (by rfl) ⟨3127877, by rfl⟩ : syracuseStep 4170503 = 6255755) B6255755
theorem B11715515 : Blo 1541468 11715515 := bstep (se 1 (by rfl) ⟨8786636, by rfl⟩ : syracuseStep 11715515 = 17573273) B17573273
theorem B13181939 : Blo 1541468 13181939 := bstep (se 1 (by rfl) ⟨9886454, by rfl⟩ : syracuseStep 13181939 = 19772909) B19772909
theorem B411518017 : Blo 1541468 411518017 := bstep (se 2 (by rfl) ⟨154319256, by rfl⟩ : syracuseStep 411518017 = 308638513) B308638513
theorem B22553747 : Blo 1541468 22553747 := bstep (se 1 (by rfl) ⟨16915310, by rfl⟩ : syracuseStep 22553747 = 33830621) B33830621
theorem B19776905 : Blo 1541468 19776905 := bstep (se 2 (by rfl) ⟨7416339, by rfl⟩ : syracuseStep 19776905 = 14832679) B14832679
theorem B22226413 : Blo 1541468 22226413 := bstep (se 3 (by rfl) ⟨4167452, by rfl⟩ : syracuseStep 22226413 = 8334905) B8334905
theorem B1541659 : Blo 1541468 1541659 := bstep (se 1 (by rfl) ⟨1156244, by rfl⟩ : syracuseStep 1541659 = 2312489) B2312489
theorem B1541663 : Blo 1541468 1541663 := bstep (se 1 (by rfl) ⟨1156247, by rfl⟩ : syracuseStep 1541663 = 2312495) B2312495
theorem B1541823 : Blo 1541468 1541823 := bstep (se 1 (by rfl) ⟨1156367, by rfl⟩ : syracuseStep 1541823 = 2312735) B2312735
theorem B4941587 : Blo 1541468 4941587 := bstep (se 1 (by rfl) ⟨3706190, by rfl⟩ : syracuseStep 4941587 = 7412381) B7412381
theorem B6252349 : Blo 1541468 6252349 := bstep (se 3 (by rfl) ⟨1172315, by rfl⟩ : syracuseStep 6252349 = 2344631) B2344631
theorem B7415725 : Blo 1541468 7415725 := bstep (se 3 (by rfl) ⟨1390448, by rfl⟩ : syracuseStep 7415725 = 2780897) B2780897
theorem B1542079 : Blo 1541468 1542079 := bstep (se 1 (by rfl) ⟨1156559, by rfl⟩ : syracuseStep 1542079 = 2313119) B2313119
theorem B1542111 : Blo 1541468 1542111 := bstep (se 1 (by rfl) ⟨1156583, by rfl⟩ : syracuseStep 1542111 = 2313167) B2313167
theorem B1542171 : Blo 1541468 1542171 := bstep (se 1 (by rfl) ⟨1156628, by rfl⟩ : syracuseStep 1542171 = 2313257) B2313257
theorem B1542175 : Blo 1541468 1542175 := bstep (se 1 (by rfl) ⟨1156631, by rfl⟩ : syracuseStep 1542175 = 2313263) B2313263
theorem B1542191 : Blo 1541468 1542191 := bstep (se 1 (by rfl) ⟨1156643, by rfl⟩ : syracuseStep 1542191 = 2313287) B2313287
theorem B106850501 : Blo 1541468 106850501 := bstep (se 4 (by rfl) ⟨10017234, by rfl⟩ : syracuseStep 106850501 = 20034469) B20034469
theorem B1542367 : Blo 1541468 1542367 := bstep (se 1 (by rfl) ⟨1156775, by rfl⟩ : syracuseStep 1542367 = 2313551) B2313551
theorem B3705115 : Blo 1541468 3705115 := bstep (se 1 (by rfl) ⟨2778836, by rfl⟩ : syracuseStep 3705115 = 5557673) B5557673
theorem B1542427 : Blo 1541468 1542427 := bstep (se 1 (by rfl) ⟨1156820, by rfl⟩ : syracuseStep 1542427 = 2313641) B2313641
theorem B14076251 : Blo 1541468 14076251 := bstep (se 1 (by rfl) ⟨10557188, by rfl⟩ : syracuseStep 14076251 = 21114377) B21114377
theorem B1542527 : Blo 1541468 1542527 := bstep (se 1 (by rfl) ⟨1156895, by rfl⟩ : syracuseStep 1542527 = 2313791) B2313791
theorem B5859809 : Blo 1541468 5859809 := bstep (se 2 (by rfl) ⟨2197428, by rfl⟩ : syracuseStep 5859809 = 4394857) B4394857
theorem B1542703 : Blo 1541468 1542703 := bstep (se 1 (by rfl) ⟨1157027, by rfl⟩ : syracuseStep 1542703 = 2314055) B2314055
theorem B2312807 : Blo 1541468 2312807 := bstep (se 1 (by rfl) ⟨1734605, by rfl⟩ : syracuseStep 2312807 = 3469211) B3469211
theorem B1542759 : Blo 1541468 1542759 := bstep (se 1 (by rfl) ⟨1157069, by rfl⟩ : syracuseStep 1542759 = 2314139) B2314139
theorem B7031411 : Blo 1541468 7031411 := bstep (se 1 (by rfl) ⟨5273558, by rfl⟩ : syracuseStep 7031411 = 10547117) B10547117
theorem B2312999 : Blo 1541468 2312999 := bstep (se 1 (by rfl) ⟨1734749, by rfl⟩ : syracuseStep 2312999 = 3469499) B3469499
theorem B3902377 : Blo 1541468 3902377 := bstep (se 2 (by rfl) ⟨1463391, by rfl⟩ : syracuseStep 3902377 = 2926783) B2926783
theorem B1543135 : Blo 1541468 1543135 := bstep (se 1 (by rfl) ⟨1157351, by rfl⟩ : syracuseStep 1543135 = 2314703) B2314703
theorem B1543163 : Blo 1541468 1543163 := bstep (se 1 (by rfl) ⟨1157372, by rfl⟩ : syracuseStep 1543163 = 2314745) B2314745
theorem B3468329 : Blo 1541468 3468329 := bstep (se 2 (by rfl) ⟨1300623, by rfl⟩ : syracuseStep 3468329 = 2601247) B2601247
theorem B2927657 : Blo 1541468 2927657 := bstep (se 2 (by rfl) ⟨1097871, by rfl⟩ : syracuseStep 2927657 = 2195743) B2195743
theorem B1543231 : Blo 1541468 1543231 := bstep (se 1 (by rfl) ⟨1157423, by rfl⟩ : syracuseStep 1543231 = 2314847) B2314847
theorem B18771011 : Blo 1541468 18771011 := bstep (se 1 (by rfl) ⟨14078258, by rfl⟩ : syracuseStep 18771011 = 28156517) B28156517
theorem B2313323 : Blo 1541468 2313323 := bstep (se 1 (by rfl) ⟨1734992, by rfl⟩ : syracuseStep 2313323 = 3469985) B3469985
theorem B3902651 : Blo 1541468 3902651 := bstep (se 1 (by rfl) ⟨2926988, by rfl⟩ : syracuseStep 3902651 = 5853977) B5853977
theorem B11709683 : Blo 1541468 11709683 := bstep (se 1 (by rfl) ⟨8782262, by rfl⟩ : syracuseStep 11709683 = 17564525) B17564525
theorem B3468563 : Blo 1541468 3468563 := bstep (se 1 (by rfl) ⟨2601422, by rfl⟩ : syracuseStep 3468563 = 5202845) B5202845
theorem B3468599 : Blo 1541468 3468599 := bstep (se 1 (by rfl) ⟨2601449, by rfl⟩ : syracuseStep 3468599 = 5202899) B5202899
theorem B2313563 : Blo 1541468 2313563 := bstep (se 1 (by rfl) ⟨1735172, by rfl⟩ : syracuseStep 2313563 = 3470345) B3470345
theorem B2313593 : Blo 1541468 2313593 := bstep (se 2 (by rfl) ⟨867597, by rfl⟩ : syracuseStep 2313593 = 1735195) B1735195
theorem B2313599 : Blo 1541468 2313599 := bstep (se 1 (by rfl) ⟨1735199, by rfl⟩ : syracuseStep 2313599 = 3470399) B3470399
theorem B202952081 : Blo 1541468 202952081 := bstep (se 2 (by rfl) ⟨76107030, by rfl⟩ : syracuseStep 202952081 = 152214061) B152214061
theorem B7810667 : Blo 1541468 7810667 := bstep (se 1 (by rfl) ⟨5858000, by rfl⟩ : syracuseStep 7810667 = 11716001) B11716001
theorem B10554995 : Blo 1541468 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B31674185 : Blo 1541468 31674185 := bstep (se 2 (by rfl) ⟨11877819, by rfl⟩ : syracuseStep 31674185 = 23755639) B23755639
theorem B14069609 : Blo 1541468 14069609 := bstep (se 2 (by rfl) ⟨5276103, by rfl⟩ : syracuseStep 14069609 = 10552207) B10552207
theorem B3469193 : Blo 1541468 3469193 := bstep (se 2 (by rfl) ⟨1300947, by rfl⟩ : syracuseStep 3469193 = 2601895) B2601895
theorem B2314223 : Blo 1541468 2314223 := bstep (se 1 (by rfl) ⟨1735667, by rfl⟩ : syracuseStep 2314223 = 3471335) B3471335
theorem B2314235 : Blo 1541468 2314235 := bstep (se 1 (by rfl) ⟨1735676, by rfl⟩ : syracuseStep 2314235 = 3471353) B3471353
theorem B2314295 : Blo 1541468 2314295 := bstep (se 1 (by rfl) ⟨1735721, by rfl⟩ : syracuseStep 2314295 = 3471443) B3471443
theorem B8343647 : Blo 1541468 8343647 := bstep (se 1 (by rfl) ⟨6257735, by rfl⟩ : syracuseStep 8343647 = 12515471) B12515471
theorem B3469409 : Blo 1541468 3469409 := bstep (se 2 (by rfl) ⟨1301028, by rfl⟩ : syracuseStep 3469409 = 2602057) B2602057
theorem B2314343 : Blo 1541468 2314343 := bstep (se 1 (by rfl) ⟨1735757, by rfl⟩ : syracuseStep 2314343 = 3471515) B3471515
theorem B9375851 : Blo 1541468 9375851 := bstep (se 1 (by rfl) ⟨7031888, by rfl⟩ : syracuseStep 9375851 = 14063777) B14063777
theorem B2314415 : Blo 1541468 2314415 := bstep (se 1 (by rfl) ⟨1735811, by rfl⟩ : syracuseStep 2314415 = 3471623) B3471623
theorem B17576189 : Blo 1541468 17576189 := bstep (se 3 (by rfl) ⟨3295535, by rfl⟩ : syracuseStep 17576189 = 6591071) B6591071
theorem B3903785 : Blo 1541468 3903785 := bstep (se 2 (by rfl) ⟨1463919, by rfl⟩ : syracuseStep 3903785 = 2927839) B2927839
theorem B2314619 : Blo 1541468 2314619 := bstep (se 1 (by rfl) ⟨1735964, by rfl⟩ : syracuseStep 2314619 = 3471929) B3471929
theorem B100029005 : Blo 1541468 100029005 := bstep (se 3 (by rfl) ⟨18755438, by rfl⟩ : syracuseStep 100029005 = 37510877) B37510877
theorem B2314889 : Blo 1541468 2314889 := bstep (se 2 (by rfl) ⟨868083, by rfl⟩ : syracuseStep 2314889 = 1736167) B1736167
theorem B11711141 : Blo 1541468 11711141 := bstep (se 4 (by rfl) ⟨1097919, by rfl⟩ : syracuseStep 11711141 = 2195839) B2195839
theorem B3470075 : Blo 1541468 3470075 := bstep (se 1 (by rfl) ⟨2602556, by rfl⟩ : syracuseStep 3470075 = 5205113) B5205113
theorem B2315099 : Blo 1541468 2315099 := bstep (se 1 (by rfl) ⟨1736324, by rfl⟩ : syracuseStep 2315099 = 3472649) B3472649
theorem B3470291 : Blo 1541468 3470291 := bstep (se 1 (by rfl) ⟨2602718, by rfl⟩ : syracuseStep 3470291 = 5205437) B5205437
theorem B14824457 : Blo 1541468 14824457 := bstep (se 2 (by rfl) ⟨5559171, by rfl⟩ : syracuseStep 14824457 = 11118343) B11118343
theorem B11719889 : Blo 1541468 11719889 := bstep (se 2 (by rfl) ⟨4394958, by rfl⟩ : syracuseStep 11719889 = 8789917) B8789917
theorem B50058485 : Blo 1541468 50058485 := bstep (se 5 (by rfl) ⟨2346491, by rfl⟩ : syracuseStep 50058485 = 4692983) B4692983
theorem B2929927 : Blo 1541468 2929927 := bstep (se 1 (by rfl) ⟨2197445, by rfl⟩ : syracuseStep 2929927 = 4394891) B4394891
theorem B3470759 : Blo 1541468 3470759 := bstep (se 1 (by rfl) ⟨2603069, by rfl⟩ : syracuseStep 3470759 = 5206139) B5206139
theorem B2930087 : Blo 1541468 2930087 := bstep (se 1 (by rfl) ⟨2197565, by rfl⟩ : syracuseStep 2930087 = 4395131) B4395131
theorem B3470867 : Blo 1541468 3470867 := bstep (se 1 (by rfl) ⟨2603150, by rfl⟩ : syracuseStep 3470867 = 5206301) B5206301
theorem B3470939 : Blo 1541468 3470939 := bstep (se 1 (by rfl) ⟨2603204, by rfl⟩ : syracuseStep 3470939 = 5206409) B5206409
theorem B5207705 : Blo 1541468 5207705 := bstep (se 2 (by rfl) ⟨1952889, by rfl⟩ : syracuseStep 5207705 = 3905779) B3905779
theorem B3905243 : Blo 1541468 3905243 := bstep (se 1 (by rfl) ⟨2928932, by rfl⟩ : syracuseStep 3905243 = 5857865) B5857865
theorem B7411459 : Blo 1541468 7411459 := bstep (se 1 (by rfl) ⟨5558594, by rfl⟩ : syracuseStep 7411459 = 11117189) B11117189
theorem B1734727 : Blo 1541468 1734727 := bstep (se 1 (by rfl) ⟨1301045, by rfl⟩ : syracuseStep 1734727 = 2602091) B2602091
theorem B115677341 : Blo 1541468 115677341 := bstep (se 3 (by rfl) ⟨21689501, by rfl⟩ : syracuseStep 115677341 = 43379003) B43379003
theorem B2603191 : Blo 1541468 2603191 := bstep (se 1 (by rfl) ⟨1952393, by rfl⟩ : syracuseStep 2603191 = 3904787) B3904787
theorem B3471551 : Blo 1541468 3471551 := bstep (se 1 (by rfl) ⟨2603663, by rfl⟩ : syracuseStep 3471551 = 5207327) B5207327
theorem B32086367 : Blo 1541468 32086367 := bstep (se 1 (by rfl) ⟨24064775, by rfl⟩ : syracuseStep 32086367 = 48129551) B48129551
theorem B28514699 : Blo 1541468 28514699 := bstep (se 1 (by rfl) ⟨21386024, by rfl⟩ : syracuseStep 28514699 = 42772049) B42772049
theorem B11713085 : Blo 1541468 11713085 := bstep (se 3 (by rfl) ⟨2196203, by rfl⟩ : syracuseStep 11713085 = 4392407) B4392407
theorem B6584989 : Blo 1541468 6584989 := bstep (se 3 (by rfl) ⟨1234685, by rfl⟩ : syracuseStep 6584989 = 2469371) B2469371
theorem B8788733 : Blo 1541468 8788733 := bstep (se 3 (by rfl) ⟨1647887, by rfl⟩ : syracuseStep 8788733 = 3295775) B3295775
theorem B2603785 : Blo 1541468 2603785 := bstep (se 2 (by rfl) ⟨976419, by rfl⟩ : syracuseStep 2603785 = 1952839) B1952839
theorem B29645675 : Blo 1541468 29645675 := bstep (se 1 (by rfl) ⟨22234256, by rfl⟩ : syracuseStep 29645675 = 44468513) B44468513
theorem B3906427 : Blo 1541468 3906427 := bstep (se 1 (by rfl) ⟨2929820, by rfl⟩ : syracuseStep 3906427 = 5859641) B5859641
theorem B8780669 : Blo 1541468 8780669 := bstep (se 3 (by rfl) ⟨1646375, by rfl⟩ : syracuseStep 8780669 = 3292751) B3292751
theorem B1735591 : Blo 1541468 1735591 := bstep (se 1 (by rfl) ⟨1301693, by rfl⟩ : syracuseStep 1735591 = 2603387) B2603387
theorem B1735771 : Blo 1541468 1735771 := bstep (se 1 (by rfl) ⟨1301828, by rfl⟩ : syracuseStep 1735771 = 2603657) B2603657
theorem B26344601 : Blo 1541468 26344601 := bstep (se 2 (by rfl) ⟨9879225, by rfl⟩ : syracuseStep 26344601 = 19758451) B19758451
theorem B11263427 : Blo 1541468 11263427 := bstep (se 1 (by rfl) ⟨8447570, by rfl⟩ : syracuseStep 11263427 = 16895141) B16895141
theorem B11714057 : Blo 1541468 11714057 := bstep (se 2 (by rfl) ⟨4392771, by rfl⟩ : syracuseStep 11714057 = 8785543) B8785543
theorem B12500543 : Blo 1541468 12500543 := bstep (se 1 (by rfl) ⟨9375407, by rfl⟩ : syracuseStep 12500543 = 18750815) B18750815
theorem B17800813 : Blo 1541468 17800813 := bstep (se 3 (by rfl) ⟨3337652, by rfl⟩ : syracuseStep 17800813 = 6675305) B6675305
theorem B5856893 : Blo 1541468 5856893 := bstep (se 3 (by rfl) ⟨1098167, by rfl⟩ : syracuseStep 5856893 = 2196335) B2196335
theorem B4390631 : Blo 1541468 4390631 := bstep (se 1 (by rfl) ⟨3292973, by rfl⟩ : syracuseStep 4390631 = 6585947) B6585947
theorem B5562431 : Blo 1541468 5562431 := bstep (se 1 (by rfl) ⟨4171823, by rfl⟩ : syracuseStep 5562431 = 8343647) B8343647
theorem B6250567 : Blo 1541468 6250567 := bstep (se 1 (by rfl) ⟨4687925, by rfl⟩ : syracuseStep 6250567 = 9375851) B9375851
theorem B8782127 : Blo 1541468 8782127 := bstep (se 1 (by rfl) ⟨6586595, by rfl⟩ : syracuseStep 8782127 = 13173191) B13173191
theorem B4940153 : Blo 1541468 4940153 := bstep (se 2 (by rfl) ⟨1852557, by rfl⟩ : syracuseStep 4940153 = 3705115) B3705115
theorem B7807427 : Blo 1541468 7807427 := bstep (se 1 (by rfl) ⟨5855570, by rfl⟩ : syracuseStep 7807427 = 11711141) B11711141
theorem B5203169 : Blo 1541468 5203169 := bstep (se 2 (by rfl) ⟨1951188, by rfl⟩ : syracuseStep 5203169 = 3902377) B3902377
theorem B21390911 : Blo 1541468 21390911 := bstep (se 1 (by rfl) ⟨16043183, by rfl⟩ : syracuseStep 21390911 = 32086367) B32086367
theorem B7808723 : Blo 1541468 7808723 := bstep (se 1 (by rfl) ⟨5856542, by rfl⟩ : syracuseStep 7808723 = 11713085) B11713085
theorem B1541871 : Blo 1541468 1541871 := bstep (se 1 (by rfl) ⟨1156403, by rfl⟩ : syracuseStep 1541871 = 2312807) B2312807
theorem B4687607 : Blo 1541468 4687607 := bstep (se 1 (by rfl) ⟨3515705, by rfl⟩ : syracuseStep 4687607 = 7031411) B7031411
theorem B5859155 : Blo 1541468 5859155 := bstep (se 1 (by rfl) ⟨4394366, by rfl⟩ : syracuseStep 5859155 = 8788733) B8788733
theorem B1541999 : Blo 1541468 1541999 := bstep (se 1 (by rfl) ⟨1156499, by rfl⟩ : syracuseStep 1541999 = 2312999) B2312999
theorem B2312219 : Blo 1541468 2312219 := bstep (se 1 (by rfl) ⟨1734164, by rfl⟩ : syracuseStep 2312219 = 3468329) B3468329
theorem B1951771 : Blo 1541468 1951771 := bstep (se 1 (by rfl) ⟨1463828, by rfl⟩ : syracuseStep 1951771 = 2927657) B2927657
theorem B1542215 : Blo 1541468 1542215 := bstep (se 1 (by rfl) ⟨1156661, by rfl⟩ : syracuseStep 1542215 = 2313323) B2313323
theorem B23734417 : Blo 1541468 23734417 := bstep (se 2 (by rfl) ⟨8900406, by rfl⟩ : syracuseStep 23734417 = 17800813) B17800813
theorem B2312375 : Blo 1541468 2312375 := bstep (se 1 (by rfl) ⟨1734281, by rfl⟩ : syracuseStep 2312375 = 3468563) B3468563
theorem B2312399 : Blo 1541468 2312399 := bstep (se 1 (by rfl) ⟨1734299, by rfl⟩ : syracuseStep 2312399 = 3468599) B3468599
theorem B1542375 : Blo 1541468 1542375 := bstep (se 1 (by rfl) ⟨1156781, by rfl⟩ : syracuseStep 1542375 = 2313563) B2313563
theorem B1542395 : Blo 1541468 1542395 := bstep (se 1 (by rfl) ⟨1156796, by rfl⟩ : syracuseStep 1542395 = 2313593) B2313593
theorem B1542399 : Blo 1541468 1542399 := bstep (se 1 (by rfl) ⟨1156799, by rfl⟩ : syracuseStep 1542399 = 2313599) B2313599
theorem B135301387 : Blo 1541468 135301387 := bstep (se 1 (by rfl) ⟨101476040, by rfl⟩ : syracuseStep 135301387 = 202952081) B202952081
theorem B9881945 : Blo 1541468 9881945 := bstep (se 2 (by rfl) ⟨3705729, by rfl⟩ : syracuseStep 9881945 = 7411459) B7411459
theorem B7809371 : Blo 1541468 7809371 := bstep (se 1 (by rfl) ⟨5857028, by rfl⟩ : syracuseStep 7809371 = 11714057) B11714057
theorem B8333695 : Blo 1541468 8333695 := bstep (se 1 (by rfl) ⟨6250271, by rfl⟩ : syracuseStep 8333695 = 12500543) B12500543
theorem B2927087 : Blo 1541468 2927087 := bstep (se 1 (by rfl) ⟨2195315, by rfl⟩ : syracuseStep 2927087 = 4390631) B4390631
theorem B2312795 : Blo 1541468 2312795 := bstep (se 1 (by rfl) ⟨1734596, by rfl⟩ : syracuseStep 2312795 = 3469193) B3469193
theorem B1542815 : Blo 1541468 1542815 := bstep (se 1 (by rfl) ⟨1157111, by rfl⟩ : syracuseStep 1542815 = 2314223) B2314223
theorem B1542823 : Blo 1541468 1542823 := bstep (se 1 (by rfl) ⟨1157117, by rfl⟩ : syracuseStep 1542823 = 2314235) B2314235
theorem B1542863 : Blo 1541468 1542863 := bstep (se 1 (by rfl) ⟨1157147, by rfl⟩ : syracuseStep 1542863 = 2314295) B2314295
theorem B2312939 : Blo 1541468 2312939 := bstep (se 1 (by rfl) ⟨1734704, by rfl⟩ : syracuseStep 2312939 = 3469409) B3469409
theorem B1542895 : Blo 1541468 1542895 := bstep (se 1 (by rfl) ⟨1157171, by rfl⟩ : syracuseStep 1542895 = 2314343) B2314343
theorem B2312969 : Blo 1541468 2312969 := bstep (se 2 (by rfl) ⟨867363, by rfl⟩ : syracuseStep 2312969 = 1734727) B1734727
theorem B1542943 : Blo 1541468 1542943 := bstep (se 1 (by rfl) ⟨1157207, by rfl⟩ : syracuseStep 1542943 = 2314415) B2314415
theorem B11717459 : Blo 1541468 11717459 := bstep (se 1 (by rfl) ⟨8788094, by rfl⟩ : syracuseStep 11717459 = 17576189) B17576189
theorem B1543079 : Blo 1541468 1543079 := bstep (se 1 (by rfl) ⟨1157309, by rfl⟩ : syracuseStep 1543079 = 2314619) B2314619
theorem B66686003 : Blo 1541468 66686003 := bstep (se 1 (by rfl) ⟨50014502, by rfl⟩ : syracuseStep 66686003 = 100029005) B100029005
theorem B1543259 : Blo 1541468 1543259 := bstep (se 1 (by rfl) ⟨1157444, by rfl⟩ : syracuseStep 1543259 = 2314889) B2314889
theorem B2313383 : Blo 1541468 2313383 := bstep (se 1 (by rfl) ⟨1735037, by rfl⟩ : syracuseStep 2313383 = 3470075) B3470075
theorem B5205167 : Blo 1541468 5205167 := bstep (se 1 (by rfl) ⟨3903875, by rfl⟩ : syracuseStep 5205167 = 7807751) B7807751
theorem B2780335 : Blo 1541468 2780335 := bstep (se 1 (by rfl) ⟨2085251, by rfl⟩ : syracuseStep 2780335 = 4170503) B4170503
theorem B1543399 : Blo 1541468 1543399 := bstep (se 1 (by rfl) ⟨1157549, by rfl⟩ : syracuseStep 1543399 = 2315099) B2315099
theorem B7810343 : Blo 1541468 7810343 := bstep (se 1 (by rfl) ⟨5857757, by rfl⟩ : syracuseStep 7810343 = 11715515) B11715515
theorem B2313527 : Blo 1541468 2313527 := bstep (se 1 (by rfl) ⟨1735145, by rfl⟩ : syracuseStep 2313527 = 3470291) B3470291
theorem B9882971 : Blo 1541468 9882971 := bstep (se 1 (by rfl) ⟨7412228, by rfl⟩ : syracuseStep 9882971 = 14824457) B14824457
theorem B15035831 : Blo 1541468 15035831 := bstep (se 1 (by rfl) ⟨11276873, by rfl⟩ : syracuseStep 15035831 = 22553747) B22553747
theorem B13184603 : Blo 1541468 13184603 := bstep (se 1 (by rfl) ⟨9888452, by rfl⟩ : syracuseStep 13184603 = 19776905) B19776905
theorem B2313839 : Blo 1541468 2313839 := bstep (se 1 (by rfl) ⟨1735379, by rfl⟩ : syracuseStep 2313839 = 3470759) B3470759
theorem B1953391 : Blo 1541468 1953391 := bstep (se 1 (by rfl) ⟨1465043, by rfl⟩ : syracuseStep 1953391 = 2930087) B2930087
theorem B2313911 : Blo 1541468 2313911 := bstep (se 1 (by rfl) ⟨1735433, by rfl⟩ : syracuseStep 2313911 = 3470867) B3470867
theorem B2313959 : Blo 1541468 2313959 := bstep (se 1 (by rfl) ⟨1735469, by rfl⟩ : syracuseStep 2313959 = 3470939) B3470939
theorem B2314121 : Blo 1541468 2314121 := bstep (se 2 (by rfl) ⟨867795, by rfl⟩ : syracuseStep 2314121 = 1735591) B1735591
theorem B2314361 : Blo 1541468 2314361 := bstep (se 2 (by rfl) ⟨867885, by rfl⟩ : syracuseStep 2314361 = 1735771) B1735771
theorem B2314367 : Blo 1541468 2314367 := bstep (se 1 (by rfl) ⟨1735775, by rfl⟩ : syracuseStep 2314367 = 3471551) B3471551
theorem B71233667 : Blo 1541468 71233667 := bstep (se 1 (by rfl) ⟨53425250, by rfl⟩ : syracuseStep 71233667 = 106850501) B106850501
theorem B9384167 : Blo 1541468 9384167 := bstep (se 1 (by rfl) ⟨7038125, by rfl⟩ : syracuseStep 9384167 = 14076251) B14076251
theorem B19009799 : Blo 1541468 19009799 := bstep (se 1 (by rfl) ⟨14257349, by rfl⟩ : syracuseStep 19009799 = 28514699) B28514699
theorem B19763783 : Blo 1541468 19763783 := bstep (se 1 (by rfl) ⟨14822837, by rfl⟩ : syracuseStep 19763783 = 29645675) B29645675
theorem B5853779 : Blo 1541468 5853779 := bstep (se 1 (by rfl) ⟨4390334, by rfl⟩ : syracuseStep 5853779 = 8780669) B8780669
theorem B29635217 : Blo 1541468 29635217 := bstep (se 2 (by rfl) ⟨11113206, by rfl⟩ : syracuseStep 29635217 = 22226413) B22226413
theorem B12514007 : Blo 1541468 12514007 := bstep (se 1 (by rfl) ⟨9385505, by rfl⟩ : syracuseStep 12514007 = 18771011) B18771011
theorem B13177565 : Blo 1541468 13177565 := bstep (se 3 (by rfl) ⟨2470793, by rfl⟩ : syracuseStep 13177565 = 4941587) B4941587
theorem B2601767 : Blo 1541468 2601767 := bstep (se 1 (by rfl) ⟨1951325, by rfl⟩ : syracuseStep 2601767 = 3902651) B3902651
theorem B7508951 : Blo 1541468 7508951 := bstep (se 1 (by rfl) ⟨5631713, by rfl⟩ : syracuseStep 7508951 = 11263427) B11263427
theorem B5207111 : Blo 1541468 5207111 := bstep (se 1 (by rfl) ⟨3905333, by rfl⟩ : syracuseStep 5207111 = 7810667) B7810667
theorem B8336465 : Blo 1541468 8336465 := bstep (se 2 (by rfl) ⟨3126174, by rfl⟩ : syracuseStep 8336465 = 6252349) B6252349
theorem B3904595 : Blo 1541468 3904595 := bstep (se 1 (by rfl) ⟨2928446, by rfl⟩ : syracuseStep 3904595 = 5856893) B5856893
theorem B21116123 : Blo 1541468 21116123 := bstep (se 1 (by rfl) ⟨15837092, by rfl⟩ : syracuseStep 21116123 = 31674185) B31674185
theorem B2602523 : Blo 1541468 2602523 := bstep (se 1 (by rfl) ⟨1951892, by rfl⟩ : syracuseStep 2602523 = 3903785) B3903785
theorem B8787527 : Blo 1541468 8787527 := bstep (se 1 (by rfl) ⟨6590645, by rfl⟩ : syracuseStep 8787527 = 13181291) B13181291
theorem B3470921 : Blo 1541468 3470921 := bstep (se 2 (by rfl) ⟨1301595, by rfl⟩ : syracuseStep 3470921 = 2603191) B2603191
theorem B7804511 : Blo 1541468 7804511 := bstep (se 1 (by rfl) ⟨5853383, by rfl⟩ : syracuseStep 7804511 = 11706767) B11706767
theorem B3905131 : Blo 1541468 3905131 := bstep (se 1 (by rfl) ⟨2928848, by rfl⟩ : syracuseStep 3905131 = 5857697) B5857697
theorem B11720375 : Blo 1541468 11720375 := bstep (se 1 (by rfl) ⟨8790281, by rfl⟩ : syracuseStep 11720375 = 17580563) B17580563
theorem B144496457 : Blo 1541468 144496457 := bstep (se 2 (by rfl) ⟨54186171, by rfl⟩ : syracuseStep 144496457 = 108372343) B108372343
theorem B8787959 : Blo 1541468 8787959 := bstep (se 1 (by rfl) ⟨6590969, by rfl⟩ : syracuseStep 8787959 = 13181939) B13181939
theorem B7813259 : Blo 1541468 7813259 := bstep (se 1 (by rfl) ⟨5859944, by rfl⟩ : syracuseStep 7813259 = 11719889) B11719889
theorem B33372323 : Blo 1541468 33372323 := bstep (se 1 (by rfl) ⟨25029242, by rfl⟩ : syracuseStep 33372323 = 50058485) B50058485
theorem B8779985 : Blo 1541468 8779985 := bstep (se 2 (by rfl) ⟨3292494, by rfl⟩ : syracuseStep 8779985 = 6584989) B6584989
theorem B3471713 : Blo 1541468 3471713 := bstep (se 2 (by rfl) ⟨1301892, by rfl⟩ : syracuseStep 3471713 = 2603785) B2603785
theorem B3471803 : Blo 1541468 3471803 := bstep (se 1 (by rfl) ⟨2603852, by rfl⟩ : syracuseStep 3471803 = 5207705) B5207705
theorem B2603495 : Blo 1541468 2603495 := bstep (se 1 (by rfl) ⟨1952621, by rfl⟩ : syracuseStep 2603495 = 3905243) B3905243
theorem B5208569 : Blo 1541468 5208569 := bstep (se 2 (by rfl) ⟨1953213, by rfl⟩ : syracuseStep 5208569 = 3906427) B3906427
theorem B548690689 : Blo 1541468 548690689 := bstep (se 2 (by rfl) ⟨205759008, by rfl⟩ : syracuseStep 548690689 = 411518017) B411518017
theorem B77118227 : Blo 1541468 77118227 := bstep (se 1 (by rfl) ⟨57838670, by rfl⟩ : syracuseStep 77118227 = 115677341) B115677341
theorem B28146653 : Blo 1541468 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B3906539 : Blo 1541468 3906539 := bstep (se 1 (by rfl) ⟨2929904, by rfl⟩ : syracuseStep 3906539 = 5859809) B5859809
theorem B3906569 : Blo 1541468 3906569 := bstep (se 2 (by rfl) ⟨1464963, by rfl⟩ : syracuseStep 3906569 = 2929927) B2929927
theorem B17563067 : Blo 1541468 17563067 := bstep (se 1 (by rfl) ⟨13172300, by rfl⟩ : syracuseStep 17563067 = 26344601) B26344601
theorem B7806455 : Blo 1541468 7806455 := bstep (se 1 (by rfl) ⟨5854841, by rfl⟩ : syracuseStep 7806455 = 11709683) B11709683
theorem B9887633 : Blo 1541468 9887633 := bstep (se 2 (by rfl) ⟨3707862, by rfl⟩ : syracuseStep 9887633 = 7415725) B7415725
theorem B9379739 : Blo 1541468 9379739 := bstep (se 1 (by rfl) ⟨7034804, by rfl⟩ : syracuseStep 9379739 = 14069609) B14069609
theorem B47489111 : Blo 1541468 47489111 := bstep (se 1 (by rfl) ⟨35616833, by rfl⟩ : syracuseStep 47489111 = 71233667) B71233667
theorem B12673199 : Blo 1541468 12673199 := bstep (se 1 (by rfl) ⟨9504899, by rfl⟩ : syracuseStep 12673199 = 19009799) B19009799
theorem B31645889 : Blo 1541468 31645889 := bstep (se 2 (by rfl) ⟨11867208, by rfl⟩ : syracuseStep 31645889 = 23734417) B23734417
theorem B3293435 : Blo 1541468 3293435 := bstep (se 1 (by rfl) ⟨2470076, by rfl⟩ : syracuseStep 3293435 = 4940153) B4940153
theorem B5005967 : Blo 1541468 5005967 := bstep (se 1 (by rfl) ⟨3754475, by rfl⟩ : syracuseStep 5005967 = 7508951) B7508951
theorem B14828453 : Blo 1541468 14828453 := bstep (se 4 (by rfl) ⟨1390167, by rfl⟩ : syracuseStep 14828453 = 2780335) B2780335
theorem B731587585 : Blo 1541468 731587585 := bstep (se 2 (by rfl) ⟨274345344, by rfl⟩ : syracuseStep 731587585 = 548690689) B548690689
theorem B5858351 : Blo 1541468 5858351 := bstep (se 1 (by rfl) ⟨4393763, by rfl⟩ : syracuseStep 5858351 = 8787527) B8787527
theorem B5203007 : Blo 1541468 5203007 := bstep (se 1 (by rfl) ⟨3902255, by rfl⟩ : syracuseStep 5203007 = 7804511) B7804511
theorem B96330971 : Blo 1541468 96330971 := bstep (se 1 (by rfl) ⟨72248228, by rfl⟩ : syracuseStep 96330971 = 144496457) B144496457
theorem B5858639 : Blo 1541468 5858639 := bstep (se 1 (by rfl) ⟨4393979, by rfl⟩ : syracuseStep 5858639 = 8787959) B8787959
theorem B1541479 : Blo 1541468 1541479 := bstep (se 1 (by rfl) ⟨1156109, by rfl⟩ : syracuseStep 1541479 = 2312219) B2312219
theorem B1541583 : Blo 1541468 1541583 := bstep (se 1 (by rfl) ⟨1156187, by rfl⟩ : syracuseStep 1541583 = 2312375) B2312375
theorem B1541599 : Blo 1541468 1541599 := bstep (se 1 (by rfl) ⟨1156199, by rfl⟩ : syracuseStep 1541599 = 2312399) B2312399
theorem B6587963 : Blo 1541468 6587963 := bstep (se 1 (by rfl) ⟨4940972, by rfl⟩ : syracuseStep 6587963 = 9881945) B9881945
theorem B1951391 : Blo 1541468 1951391 := bstep (se 1 (by rfl) ⟨1463543, by rfl⟩ : syracuseStep 1951391 = 2927087) B2927087
theorem B1541863 : Blo 1541468 1541863 := bstep (se 1 (by rfl) ⟨1156397, by rfl⟩ : syracuseStep 1541863 = 2312795) B2312795
theorem B1541959 : Blo 1541468 1541959 := bstep (se 1 (by rfl) ⟨1156469, by rfl⟩ : syracuseStep 1541959 = 2312939) B2312939
theorem B1541979 : Blo 1541468 1541979 := bstep (se 1 (by rfl) ⟨1156484, by rfl⟩ : syracuseStep 1541979 = 2312969) B2312969
theorem B1542255 : Blo 1541468 1542255 := bstep (se 1 (by rfl) ⟨1156691, by rfl⟩ : syracuseStep 1542255 = 2313383) B2313383
theorem B1542351 : Blo 1541468 1542351 := bstep (se 1 (by rfl) ⟨1156763, by rfl⟩ : syracuseStep 1542351 = 2313527) B2313527
theorem B6588647 : Blo 1541468 6588647 := bstep (se 1 (by rfl) ⟨4941485, by rfl⟩ : syracuseStep 6588647 = 9882971) B9882971
theorem B11708711 : Blo 1541468 11708711 := bstep (se 1 (by rfl) ⟨8781533, by rfl⟩ : syracuseStep 11708711 = 17563067) B17563067
theorem B5204303 : Blo 1541468 5204303 := bstep (se 1 (by rfl) ⟨3903227, by rfl⟩ : syracuseStep 5204303 = 7806455) B7806455
theorem B25012637 : Blo 1541468 25012637 := bstep (se 3 (by rfl) ⟨4689869, by rfl⟩ : syracuseStep 25012637 = 9379739) B9379739
theorem B1542559 : Blo 1541468 1542559 := bstep (se 1 (by rfl) ⟨1156919, by rfl⟩ : syracuseStep 1542559 = 2313839) B2313839
theorem B1542607 : Blo 1541468 1542607 := bstep (se 1 (by rfl) ⟨1156955, by rfl⟩ : syracuseStep 1542607 = 2313911) B2313911
theorem B1542639 : Blo 1541468 1542639 := bstep (se 1 (by rfl) ⟨1156979, by rfl⟩ : syracuseStep 1542639 = 2313959) B2313959
theorem B1542747 : Blo 1541468 1542747 := bstep (se 1 (by rfl) ⟨1157060, by rfl⟩ : syracuseStep 1542747 = 2314121) B2314121
theorem B1542907 : Blo 1541468 1542907 := bstep (se 1 (by rfl) ⟨1157180, by rfl⟩ : syracuseStep 1542907 = 2314361) B2314361
theorem B1542911 : Blo 1541468 1542911 := bstep (se 1 (by rfl) ⟨1157183, by rfl⟩ : syracuseStep 1542911 = 2314367) B2314367
theorem B8334089 : Blo 1541468 8334089 := bstep (se 2 (by rfl) ⟨3125283, by rfl⟩ : syracuseStep 8334089 = 6250567) B6250567
theorem B5204951 : Blo 1541468 5204951 := bstep (se 1 (by rfl) ⟨3903713, by rfl⟩ : syracuseStep 5204951 = 7807427) B7807427
theorem B13175855 : Blo 1541468 13175855 := bstep (se 1 (by rfl) ⟨9881891, by rfl⟩ : syracuseStep 13175855 = 19763783) B19763783
theorem B3902519 : Blo 1541468 3902519 := bstep (se 1 (by rfl) ⟨2926889, by rfl⟩ : syracuseStep 3902519 = 5853779) B5853779
theorem B8342671 : Blo 1541468 8342671 := bstep (se 1 (by rfl) ⟨6257003, by rfl⟩ : syracuseStep 8342671 = 12514007) B12514007
theorem B8785043 : Blo 1541468 8785043 := bstep (se 1 (by rfl) ⟨6588782, by rfl⟩ : syracuseStep 8785043 = 13177565) B13177565
theorem B11111593 : Blo 1541468 11111593 := bstep (se 2 (by rfl) ⟨4166847, by rfl⟩ : syracuseStep 11111593 = 8333695) B8333695
theorem B5557643 : Blo 1541468 5557643 := bstep (se 1 (by rfl) ⟨4168232, by rfl⟩ : syracuseStep 5557643 = 8336465) B8336465
theorem B14077415 : Blo 1541468 14077415 := bstep (se 1 (by rfl) ⟨10558061, by rfl⟩ : syracuseStep 14077415 = 21116123) B21116123
theorem B3468779 : Blo 1541468 3468779 := bstep (se 1 (by rfl) ⟨2601584, by rfl⟩ : syracuseStep 3468779 = 5203169) B5203169
theorem B2313947 : Blo 1541468 2313947 := bstep (se 1 (by rfl) ⟨1735460, by rfl⟩ : syracuseStep 2313947 = 3470921) B3470921
theorem B5205815 : Blo 1541468 5205815 := bstep (se 1 (by rfl) ⟨3904361, by rfl⟩ : syracuseStep 5205815 = 7808723) B7808723
theorem B3125071 : Blo 1541468 3125071 := bstep (se 1 (by rfl) ⟨2343803, by rfl⟩ : syracuseStep 3125071 = 4687607) B4687607
theorem B5853323 : Blo 1541468 5853323 := bstep (se 1 (by rfl) ⟨4389992, by rfl⟩ : syracuseStep 5853323 = 8779985) B8779985
theorem B5206247 : Blo 1541468 5206247 := bstep (se 1 (by rfl) ⟨3904685, by rfl⟩ : syracuseStep 5206247 = 7809371) B7809371
theorem B2314475 : Blo 1541468 2314475 := bstep (se 1 (by rfl) ⟨1735856, by rfl⟩ : syracuseStep 2314475 = 3471713) B3471713
theorem B2314535 : Blo 1541468 2314535 := bstep (se 1 (by rfl) ⟨1735901, by rfl⟩ : syracuseStep 2314535 = 3471803) B3471803
theorem B7811639 : Blo 1541468 7811639 := bstep (se 1 (by rfl) ⟨5858729, by rfl⟩ : syracuseStep 7811639 = 11717459) B11717459
theorem B18764435 : Blo 1541468 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B3470111 : Blo 1541468 3470111 := bstep (se 1 (by rfl) ⟨2602583, by rfl⟩ : syracuseStep 3470111 = 5205167) B5205167
theorem B5206841 : Blo 1541468 5206841 := bstep (se 2 (by rfl) ⟨1952565, by rfl⟩ : syracuseStep 5206841 = 3905131) B3905131
theorem B5206895 : Blo 1541468 5206895 := bstep (se 1 (by rfl) ⟨3905171, by rfl⟩ : syracuseStep 5206895 = 7810343) B7810343
theorem B10023887 : Blo 1541468 10023887 := bstep (se 1 (by rfl) ⟨7517915, by rfl⟩ : syracuseStep 10023887 = 15035831) B15035831
theorem B6591755 : Blo 1541468 6591755 := bstep (se 1 (by rfl) ⟨4943816, by rfl⟩ : syracuseStep 6591755 = 9887633) B9887633
theorem B2602361 : Blo 1541468 2602361 := bstep (se 2 (by rfl) ⟨975885, by rfl⟩ : syracuseStep 2602361 = 1951771) B1951771
theorem B3708287 : Blo 1541468 3708287 := bstep (se 1 (by rfl) ⟨2781215, by rfl⟩ : syracuseStep 3708287 = 5562431) B5562431
theorem B6256111 : Blo 1541468 6256111 := bstep (se 1 (by rfl) ⟨4692083, by rfl⟩ : syracuseStep 6256111 = 9384167) B9384167
theorem B5854751 : Blo 1541468 5854751 := bstep (se 1 (by rfl) ⟨4391063, by rfl⟩ : syracuseStep 5854751 = 8782127) B8782127
theorem B180401849 : Blo 1541468 180401849 := bstep (se 2 (by rfl) ⟨67650693, by rfl⟩ : syracuseStep 180401849 = 135301387) B135301387
theorem B19756811 : Blo 1541468 19756811 := bstep (se 1 (by rfl) ⟨14817608, by rfl⟩ : syracuseStep 19756811 = 29635217) B29635217
theorem B1734511 : Blo 1541468 1734511 := bstep (se 1 (by rfl) ⟨1300883, by rfl⟩ : syracuseStep 1734511 = 2601767) B2601767
theorem B3471407 : Blo 1541468 3471407 := bstep (se 1 (by rfl) ⟨2603555, by rfl⟩ : syracuseStep 3471407 = 5207111) B5207111
theorem B2603063 : Blo 1541468 2603063 := bstep (se 1 (by rfl) ⟨1952297, by rfl⟩ : syracuseStep 2603063 = 3904595) B3904595
theorem B1735015 : Blo 1541468 1735015 := bstep (se 1 (by rfl) ⟨1301261, by rfl⟩ : syracuseStep 1735015 = 2602523) B2602523
theorem B14260607 : Blo 1541468 14260607 := bstep (se 1 (by rfl) ⟨10695455, by rfl⟩ : syracuseStep 14260607 = 21390911) B21390911
theorem B7813583 : Blo 1541468 7813583 := bstep (se 1 (by rfl) ⟨5860187, by rfl⟩ : syracuseStep 7813583 = 11720375) B11720375
theorem B3906103 : Blo 1541468 3906103 := bstep (se 1 (by rfl) ⟨2929577, by rfl⟩ : syracuseStep 3906103 = 5859155) B5859155
theorem B5208839 : Blo 1541468 5208839 := bstep (se 1 (by rfl) ⟨3906629, by rfl⟩ : syracuseStep 5208839 = 7813259) B7813259
theorem B22248215 : Blo 1541468 22248215 := bstep (se 1 (by rfl) ⟨16686161, by rfl⟩ : syracuseStep 22248215 = 33372323) B33372323
theorem B1735663 : Blo 1541468 1735663 := bstep (se 1 (by rfl) ⟨1301747, by rfl⟩ : syracuseStep 1735663 = 2603495) B2603495
theorem B3472379 : Blo 1541468 3472379 := bstep (se 1 (by rfl) ⟨2604284, by rfl⟩ : syracuseStep 3472379 = 5208569) B5208569
theorem B51412151 : Blo 1541468 51412151 := bstep (se 1 (by rfl) ⟨38559113, by rfl⟩ : syracuseStep 51412151 = 77118227) B77118227
theorem B2604359 : Blo 1541468 2604359 := bstep (se 1 (by rfl) ⟨1953269, by rfl⟩ : syracuseStep 2604359 = 3906539) B3906539
theorem B2604379 : Blo 1541468 2604379 := bstep (se 1 (by rfl) ⟨1953284, by rfl⟩ : syracuseStep 2604379 = 3906569) B3906569
theorem B44457335 : Blo 1541468 44457335 := bstep (se 1 (by rfl) ⟨33343001, by rfl⟩ : syracuseStep 44457335 = 66686003) B66686003
theorem B2604521 : Blo 1541468 2604521 := bstep (se 2 (by rfl) ⟨976695, by rfl⟩ : syracuseStep 2604521 = 1953391) B1953391
theorem B8789735 : Blo 1541468 8789735 := bstep (se 1 (by rfl) ⟨6592301, by rfl⟩ : syracuseStep 8789735 = 13184603) B13184603
theorem B2195623 : Blo 1541468 2195623 := bstep (se 1 (by rfl) ⟨1646717, by rfl⟩ : syracuseStep 2195623 = 3293435) B3293435
theorem B12509623 : Blo 1541468 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B4391975 : Blo 1541468 4391975 := bstep (se 1 (by rfl) ⟨3293981, by rfl⟩ : syracuseStep 4391975 = 6587963) B6587963
theorem B120267899 : Blo 1541468 120267899 := bstep (se 1 (by rfl) ⟨90200924, by rfl⟩ : syracuseStep 120267899 = 180401849) B180401849
theorem B4392431 : Blo 1541468 4392431 := bstep (se 1 (by rfl) ⟨3294323, by rfl⟩ : syracuseStep 4392431 = 6588647) B6588647
theorem B53396981 : Blo 1541468 53396981 := bstep (se 5 (by rfl) ⟨2502983, by rfl⟩ : syracuseStep 53396981 = 5005967) B5005967
theorem B5203709 : Blo 1541468 5203709 := bstep (se 3 (by rfl) ⟨975695, by rfl⟩ : syracuseStep 5203709 = 1951391) B1951391
theorem B5556059 : Blo 1541468 5556059 := bstep (se 1 (by rfl) ⟨4167044, by rfl⟩ : syracuseStep 5556059 = 8334089) B8334089
theorem B8341481 : Blo 1541468 8341481 := bstep (se 2 (by rfl) ⟨3128055, by rfl⟩ : syracuseStep 8341481 = 6256111) B6256111
theorem B8783903 : Blo 1541468 8783903 := bstep (se 1 (by rfl) ⟨6587927, by rfl⟩ : syracuseStep 8783903 = 13175855) B13175855
theorem B3705095 : Blo 1541468 3705095 := bstep (se 1 (by rfl) ⟨2778821, by rfl⟩ : syracuseStep 3705095 = 5557643) B5557643
theorem B2312519 : Blo 1541468 2312519 := bstep (se 1 (by rfl) ⟨1734389, by rfl⟩ : syracuseStep 2312519 = 3468779) B3468779
theorem B1542631 : Blo 1541468 1542631 := bstep (se 1 (by rfl) ⟨1156973, by rfl⟩ : syracuseStep 1542631 = 2313947) B2313947
theorem B2312681 : Blo 1541468 2312681 := bstep (se 2 (by rfl) ⟨867255, by rfl⟩ : syracuseStep 2312681 = 1734511) B1734511
theorem B5859823 : Blo 1541468 5859823 := bstep (se 1 (by rfl) ⟨4394867, by rfl⟩ : syracuseStep 5859823 = 8789735) B8789735
theorem B3902215 : Blo 1541468 3902215 := bstep (se 1 (by rfl) ⟨2926661, by rfl⟩ : syracuseStep 3902215 = 5853323) B5853323
theorem B8448799 : Blo 1541468 8448799 := bstep (se 1 (by rfl) ⟨6336599, by rfl⟩ : syracuseStep 8448799 = 12673199) B12673199
theorem B21097259 : Blo 1541468 21097259 := bstep (se 1 (by rfl) ⟨15822944, by rfl⟩ : syracuseStep 21097259 = 31645889) B31645889
theorem B1542983 : Blo 1541468 1542983 := bstep (se 1 (by rfl) ⟨1157237, by rfl⟩ : syracuseStep 1542983 = 2314475) B2314475
theorem B1543023 : Blo 1541468 1543023 := bstep (se 1 (by rfl) ⟨1157267, by rfl⟩ : syracuseStep 1543023 = 2314535) B2314535
theorem B2313353 : Blo 1541468 2313353 := bstep (se 2 (by rfl) ⟨867507, by rfl⟩ : syracuseStep 2313353 = 1735015) B1735015
theorem B2313407 : Blo 1541468 2313407 := bstep (se 1 (by rfl) ⟨1735055, by rfl⟩ : syracuseStep 2313407 = 3470111) B3470111
theorem B3468671 : Blo 1541468 3468671 := bstep (se 1 (by rfl) ⟨2601503, by rfl⟩ : syracuseStep 3468671 = 5203007) B5203007
theorem B64220647 : Blo 1541468 64220647 := bstep (se 1 (by rfl) ⟨48165485, by rfl⟩ : syracuseStep 64220647 = 96330971) B96330971
theorem B4394503 : Blo 1541468 4394503 := bstep (se 1 (by rfl) ⟨3295877, by rfl⟩ : syracuseStep 4394503 = 6591755) B6591755
theorem B3903167 : Blo 1541468 3903167 := bstep (se 1 (by rfl) ⟨2927375, by rfl⟩ : syracuseStep 3903167 = 5854751) B5854751
theorem B37539773 : Blo 1541468 37539773 := bstep (se 3 (by rfl) ⟨7038707, by rfl⟩ : syracuseStep 37539773 = 14077415) B14077415
theorem B2314217 : Blo 1541468 2314217 := bstep (se 2 (by rfl) ⟨867831, by rfl⟩ : syracuseStep 2314217 = 1735663) B1735663
theorem B975450113 : Blo 1541468 975450113 := bstep (se 2 (by rfl) ⟨365793792, by rfl⟩ : syracuseStep 975450113 = 731587585) B731587585
theorem B2314271 : Blo 1541468 2314271 := bstep (se 1 (by rfl) ⟨1735703, by rfl⟩ : syracuseStep 2314271 = 3471407) B3471407
theorem B3469535 : Blo 1541468 3469535 := bstep (se 1 (by rfl) ⟨2602151, by rfl⟩ : syracuseStep 3469535 = 5204303) B5204303
theorem B14815457 : Blo 1541468 14815457 := bstep (se 2 (by rfl) ⟨5555796, by rfl⟩ : syracuseStep 14815457 = 11111593) B11111593
theorem B9507071 : Blo 1541468 9507071 := bstep (se 1 (by rfl) ⟨7130303, by rfl⟩ : syracuseStep 9507071 = 14260607) B14260607
theorem B16675091 : Blo 1541468 16675091 := bstep (se 1 (by rfl) ⟨12506318, by rfl⟩ : syracuseStep 16675091 = 25012637) B25012637
theorem B16667045 : Blo 1541468 16667045 := bstep (se 4 (by rfl) ⟨1562535, by rfl⟩ : syracuseStep 16667045 = 3125071) B3125071
theorem B14832143 : Blo 1541468 14832143 := bstep (se 1 (by rfl) ⟨11124107, by rfl⟩ : syracuseStep 14832143 = 22248215) B22248215
theorem B3469967 : Blo 1541468 3469967 := bstep (se 1 (by rfl) ⟨2602475, by rfl⟩ : syracuseStep 3469967 = 5204951) B5204951
theorem B2314919 : Blo 1541468 2314919 := bstep (se 1 (by rfl) ⟨1736189, by rfl⟩ : syracuseStep 2314919 = 3472379) B3472379
theorem B2601679 : Blo 1541468 2601679 := bstep (se 1 (by rfl) ⟨1951259, by rfl⟩ : syracuseStep 2601679 = 3902519) B3902519
theorem B3470543 : Blo 1541468 3470543 := bstep (se 1 (by rfl) ⟨2602907, by rfl⟩ : syracuseStep 3470543 = 5205815) B5205815
theorem B31659407 : Blo 1541468 31659407 := bstep (se 1 (by rfl) ⟨23744555, by rfl⟩ : syracuseStep 31659407 = 47489111) B47489111
theorem B3470831 : Blo 1541468 3470831 := bstep (se 1 (by rfl) ⟨2603123, by rfl⟩ : syracuseStep 3470831 = 5206247) B5206247
theorem B5207759 : Blo 1541468 5207759 := bstep (se 1 (by rfl) ⟨3905819, by rfl⟩ : syracuseStep 5207759 = 7811639) B7811639
theorem B3471227 : Blo 1541468 3471227 := bstep (se 1 (by rfl) ⟨2603420, by rfl⟩ : syracuseStep 3471227 = 5206841) B5206841
theorem B3471263 : Blo 1541468 3471263 := bstep (se 1 (by rfl) ⟨2603447, by rfl⟩ : syracuseStep 3471263 = 5206895) B5206895
theorem B9885635 : Blo 1541468 9885635 := bstep (se 1 (by rfl) ⟨7414226, by rfl⟩ : syracuseStep 9885635 = 14828453) B14828453
theorem B6682591 : Blo 1541468 6682591 := bstep (se 1 (by rfl) ⟨5011943, by rfl⟩ : syracuseStep 6682591 = 10023887) B10023887
theorem B3905567 : Blo 1541468 3905567 := bstep (se 1 (by rfl) ⟨2929175, by rfl⟩ : syracuseStep 3905567 = 5858351) B5858351
theorem B5208137 : Blo 1541468 5208137 := bstep (se 2 (by rfl) ⟨1953051, by rfl⟩ : syracuseStep 5208137 = 3906103) B3906103
theorem B3905759 : Blo 1541468 3905759 := bstep (se 1 (by rfl) ⟨2929319, by rfl⟩ : syracuseStep 3905759 = 5858639) B5858639
theorem B1734907 : Blo 1541468 1734907 := bstep (se 1 (by rfl) ⟨1301180, by rfl⟩ : syracuseStep 1734907 = 2602361) B2602361
theorem B2472191 : Blo 1541468 2472191 := bstep (se 1 (by rfl) ⟨1854143, by rfl⟩ : syracuseStep 2472191 = 3708287) B3708287
theorem B13171207 : Blo 1541468 13171207 := bstep (se 1 (by rfl) ⟨9878405, by rfl⟩ : syracuseStep 13171207 = 19756811) B19756811
theorem B1735375 : Blo 1541468 1735375 := bstep (se 1 (by rfl) ⟨1301531, by rfl⟩ : syracuseStep 1735375 = 2603063) B2603063
theorem B11123561 : Blo 1541468 11123561 := bstep (se 2 (by rfl) ⟨4171335, by rfl⟩ : syracuseStep 11123561 = 8342671) B8342671
theorem B7805807 : Blo 1541468 7805807 := bstep (se 1 (by rfl) ⟨5854355, by rfl⟩ : syracuseStep 7805807 = 11708711) B11708711
theorem B5209055 : Blo 1541468 5209055 := bstep (se 1 (by rfl) ⟨3906791, by rfl⟩ : syracuseStep 5209055 = 7813583) B7813583
theorem B3472505 : Blo 1541468 3472505 := bstep (se 2 (by rfl) ⟨1302189, by rfl⟩ : syracuseStep 3472505 = 2604379) B2604379
theorem B3472559 : Blo 1541468 3472559 := bstep (se 1 (by rfl) ⟨2604419, by rfl⟩ : syracuseStep 3472559 = 5208839) B5208839
theorem B5856695 : Blo 1541468 5856695 := bstep (se 1 (by rfl) ⟨4392521, by rfl⟩ : syracuseStep 5856695 = 8785043) B8785043
theorem B34274767 : Blo 1541468 34274767 := bstep (se 1 (by rfl) ⟨25706075, by rfl⟩ : syracuseStep 34274767 = 51412151) B51412151
theorem B1736239 : Blo 1541468 1736239 := bstep (se 1 (by rfl) ⟨1302179, by rfl⟩ : syracuseStep 1736239 = 2604359) B2604359
theorem B29638223 : Blo 1541468 29638223 := bstep (se 1 (by rfl) ⟨22228667, by rfl⟩ : syracuseStep 29638223 = 44457335) B44457335
theorem B1736347 : Blo 1541468 1736347 := bstep (se 1 (by rfl) ⟨1302260, by rfl⟩ : syracuseStep 1736347 = 2604521) B2604521
theorem B11116727 : Blo 1541468 11116727 := bstep (se 1 (by rfl) ⟨8337545, by rfl⟩ : syracuseStep 11116727 = 16675091) B16675091
theorem B9888095 : Blo 1541468 9888095 := bstep (se 1 (by rfl) ⟨7416071, by rfl⟩ : syracuseStep 9888095 = 14832143) B14832143
theorem B5202953 : Blo 1541468 5202953 := bstep (se 2 (by rfl) ⟨1951107, by rfl⟩ : syracuseStep 5202953 = 3902215) B3902215
theorem B11265065 : Blo 1541468 11265065 := bstep (se 2 (by rfl) ⟨4224399, by rfl⟩ : syracuseStep 11265065 = 8448799) B8448799
theorem B3704039 : Blo 1541468 3704039 := bstep (se 1 (by rfl) ⟨2778029, by rfl⟩ : syracuseStep 3704039 = 5556059) B5556059
theorem B1648127 : Blo 1541468 1648127 := bstep (se 1 (by rfl) ⟨1236095, by rfl⟩ : syracuseStep 1648127 = 2472191) B2472191
theorem B1541679 : Blo 1541468 1541679 := bstep (se 1 (by rfl) ⟨1156259, by rfl⟩ : syracuseStep 1541679 = 2312519) B2312519
theorem B1541787 : Blo 1541468 1541787 := bstep (se 1 (by rfl) ⟨1156340, by rfl⟩ : syracuseStep 1541787 = 2312681) B2312681
theorem B7415707 : Blo 1541468 7415707 := bstep (se 1 (by rfl) ⟨5561780, by rfl⟩ : syracuseStep 7415707 = 11123561) B11123561
theorem B5203871 : Blo 1541468 5203871 := bstep (se 1 (by rfl) ⟨3902903, by rfl⟩ : syracuseStep 5203871 = 7805807) B7805807
theorem B5859337 : Blo 1541468 5859337 := bstep (se 2 (by rfl) ⟨2197251, by rfl⟩ : syracuseStep 5859337 = 4394503) B4394503
theorem B1542235 : Blo 1541468 1542235 := bstep (se 1 (by rfl) ⟨1156676, by rfl⟩ : syracuseStep 1542235 = 2313353) B2313353
theorem B1542271 : Blo 1541468 1542271 := bstep (se 1 (by rfl) ⟨1156703, by rfl⟩ : syracuseStep 1542271 = 2313407) B2313407
theorem B2312447 : Blo 1541468 2312447 := bstep (se 1 (by rfl) ⟨1734335, by rfl⟩ : syracuseStep 2312447 = 3468671) B3468671
theorem B66717989 : Blo 1541468 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B1542811 : Blo 1541468 1542811 := bstep (se 1 (by rfl) ⟨1157108, by rfl⟩ : syracuseStep 1542811 = 2314217) B2314217
theorem B650300075 : Blo 1541468 650300075 := bstep (se 1 (by rfl) ⟨487725056, by rfl⟩ : syracuseStep 650300075 = 975450113) B975450113
theorem B1542847 : Blo 1541468 1542847 := bstep (se 1 (by rfl) ⟨1157135, by rfl⟩ : syracuseStep 1542847 = 2314271) B2314271
theorem B2313023 : Blo 1541468 2313023 := bstep (se 1 (by rfl) ⟨1734767, by rfl⟩ : syracuseStep 2313023 = 3469535) B3469535
theorem B2927497 : Blo 1541468 2927497 := bstep (se 2 (by rfl) ⟨1097811, by rfl⟩ : syracuseStep 2927497 = 2195623) B2195623
theorem B11111363 : Blo 1541468 11111363 := bstep (se 1 (by rfl) ⟨8333522, by rfl⟩ : syracuseStep 11111363 = 16667045) B16667045
theorem B2313209 : Blo 1541468 2313209 := bstep (se 2 (by rfl) ⟨867453, by rfl⟩ : syracuseStep 2313209 = 1734907) B1734907
theorem B2313311 : Blo 1541468 2313311 := bstep (se 1 (by rfl) ⟨1734983, by rfl⟩ : syracuseStep 2313311 = 3469967) B3469967
theorem B1543279 : Blo 1541468 1543279 := bstep (se 1 (by rfl) ⟨1157459, by rfl⟩ : syracuseStep 1543279 = 2314919) B2314919
theorem B2927983 : Blo 1541468 2927983 := bstep (se 1 (by rfl) ⟨2195987, by rfl⟩ : syracuseStep 2927983 = 4391975) B4391975
theorem B80178599 : Blo 1541468 80178599 := bstep (se 1 (by rfl) ⟨60133949, by rfl⟩ : syracuseStep 80178599 = 120267899) B120267899
theorem B2313695 : Blo 1541468 2313695 := bstep (se 1 (by rfl) ⟨1735271, by rfl⟩ : syracuseStep 2313695 = 3470543) B3470543
theorem B21106271 : Blo 1541468 21106271 := bstep (se 1 (by rfl) ⟨15829703, by rfl⟩ : syracuseStep 21106271 = 31659407) B31659407
theorem B3468905 : Blo 1541468 3468905 := bstep (se 2 (by rfl) ⟨1300839, by rfl⟩ : syracuseStep 3468905 = 2601679) B2601679
theorem B2313833 : Blo 1541468 2313833 := bstep (se 2 (by rfl) ⟨867687, by rfl⟩ : syracuseStep 2313833 = 1735375) B1735375
theorem B2928287 : Blo 1541468 2928287 := bstep (se 1 (by rfl) ⟨2196215, by rfl⟩ : syracuseStep 2928287 = 4392431) B4392431
theorem B2313887 : Blo 1541468 2313887 := bstep (se 1 (by rfl) ⟨1735415, by rfl⟩ : syracuseStep 2313887 = 3470831) B3470831
theorem B35597987 : Blo 1541468 35597987 := bstep (se 1 (by rfl) ⟨26698490, by rfl⟩ : syracuseStep 35597987 = 53396981) B53396981
theorem B3469139 : Blo 1541468 3469139 := bstep (se 1 (by rfl) ⟨2601854, by rfl⟩ : syracuseStep 3469139 = 5203709) B5203709
theorem B2314151 : Blo 1541468 2314151 := bstep (se 1 (by rfl) ⟨1735613, by rfl⟩ : syracuseStep 2314151 = 3471227) B3471227
theorem B2314175 : Blo 1541468 2314175 := bstep (se 1 (by rfl) ⟨1735631, by rfl⟩ : syracuseStep 2314175 = 3471263) B3471263
theorem B6590423 : Blo 1541468 6590423 := bstep (se 1 (by rfl) ⟨4942817, by rfl⟩ : syracuseStep 6590423 = 9885635) B9885635
theorem B2470063 : Blo 1541468 2470063 := bstep (se 1 (by rfl) ⟨1852547, by rfl⟩ : syracuseStep 2470063 = 3705095) B3705095
theorem B45699689 : Blo 1541468 45699689 := bstep (se 2 (by rfl) ⟨17137383, by rfl⟩ : syracuseStep 45699689 = 34274767) B34274767
theorem B85627529 : Blo 1541468 85627529 := bstep (se 2 (by rfl) ⟨32110323, by rfl⟩ : syracuseStep 85627529 = 64220647) B64220647
theorem B2314985 : Blo 1541468 2314985 := bstep (se 2 (by rfl) ⟨868119, by rfl⟩ : syracuseStep 2314985 = 1736239) B1736239
theorem B2315003 : Blo 1541468 2315003 := bstep (se 1 (by rfl) ⟨1736252, by rfl⟩ : syracuseStep 2315003 = 3472505) B3472505
theorem B2315039 : Blo 1541468 2315039 := bstep (se 1 (by rfl) ⟨1736279, by rfl⟩ : syracuseStep 2315039 = 3472559) B3472559
theorem B2315129 : Blo 1541468 2315129 := bstep (se 2 (by rfl) ⟨868173, by rfl⟩ : syracuseStep 2315129 = 1736347) B1736347
theorem B3904463 : Blo 1541468 3904463 := bstep (se 1 (by rfl) ⟨2928347, by rfl⟩ : syracuseStep 3904463 = 5856695) B5856695
theorem B2602111 : Blo 1541468 2602111 := bstep (se 1 (by rfl) ⟨1951583, by rfl⟩ : syracuseStep 2602111 = 3903167) B3903167
theorem B8910121 : Blo 1541468 8910121 := bstep (se 2 (by rfl) ⟨3341295, by rfl⟩ : syracuseStep 8910121 = 6682591) B6682591
theorem B9876971 : Blo 1541468 9876971 := bstep (se 1 (by rfl) ⟨7407728, by rfl⟩ : syracuseStep 9876971 = 14815457) B14815457
theorem B6338047 : Blo 1541468 6338047 := bstep (se 1 (by rfl) ⟨4753535, by rfl⟩ : syracuseStep 6338047 = 9507071) B9507071
theorem B7813097 : Blo 1541468 7813097 := bstep (se 2 (by rfl) ⟨2929911, by rfl⟩ : syracuseStep 7813097 = 5859823) B5859823
theorem B17561609 : Blo 1541468 17561609 := bstep (se 2 (by rfl) ⟨6585603, by rfl⟩ : syracuseStep 17561609 = 13171207) B13171207
theorem B3471839 : Blo 1541468 3471839 := bstep (se 1 (by rfl) ⟨2603879, by rfl⟩ : syracuseStep 3471839 = 5207759) B5207759
theorem B5560987 : Blo 1541468 5560987 := bstep (se 1 (by rfl) ⟨4170740, by rfl⟩ : syracuseStep 5560987 = 8341481) B8341481
theorem B5855935 : Blo 1541468 5855935 := bstep (se 1 (by rfl) ⟨4391951, by rfl⟩ : syracuseStep 5855935 = 8783903) B8783903
theorem B2603711 : Blo 1541468 2603711 := bstep (se 1 (by rfl) ⟨1952783, by rfl⟩ : syracuseStep 2603711 = 3905567) B3905567
theorem B3472091 : Blo 1541468 3472091 := bstep (se 1 (by rfl) ⟨2604068, by rfl⟩ : syracuseStep 3472091 = 5208137) B5208137
theorem B2603839 : Blo 1541468 2603839 := bstep (se 1 (by rfl) ⟨1952879, by rfl⟩ : syracuseStep 2603839 = 3905759) B3905759
theorem B14064839 : Blo 1541468 14064839 := bstep (se 1 (by rfl) ⟨10548629, by rfl⟩ : syracuseStep 14064839 = 21097259) B21097259
theorem B3472703 : Blo 1541468 3472703 := bstep (se 1 (by rfl) ⟨2604527, by rfl⟩ : syracuseStep 3472703 = 5209055) B5209055
theorem B19758815 : Blo 1541468 19758815 := bstep (se 1 (by rfl) ⟨14819111, by rfl⟩ : syracuseStep 19758815 = 29638223) B29638223
theorem B25026515 : Blo 1541468 25026515 := bstep (se 1 (by rfl) ⟨18769886, by rfl⟩ : syracuseStep 25026515 = 37539773) B37539773
theorem B3293417 : Blo 1541468 3293417 := bstep (se 2 (by rfl) ⟨1235031, by rfl⟩ : syracuseStep 3293417 = 2470063) B2470063
theorem B30466459 : Blo 1541468 30466459 := bstep (se 1 (by rfl) ⟨22849844, by rfl⟩ : syracuseStep 30466459 = 45699689) B45699689
theorem B7414649 : Blo 1541468 7414649 := bstep (se 2 (by rfl) ⟨2780493, by rfl⟩ : syracuseStep 7414649 = 5560987) B5560987
theorem B7807913 : Blo 1541468 7807913 := bstep (se 2 (by rfl) ⟨2927967, by rfl⟩ : syracuseStep 7807913 = 5855935) B5855935
theorem B11707739 : Blo 1541468 11707739 := bstep (se 1 (by rfl) ⟨8780804, by rfl⟩ : syracuseStep 11707739 = 17561609) B17561609
theorem B1541631 : Blo 1541468 1541631 := bstep (se 1 (by rfl) ⟨1156223, by rfl⟩ : syracuseStep 1541631 = 2312447) B2312447
theorem B11880161 : Blo 1541468 11880161 := bstep (se 2 (by rfl) ⟨4455060, by rfl⟩ : syracuseStep 11880161 = 8910121) B8910121
theorem B1542015 : Blo 1541468 1542015 := bstep (se 1 (by rfl) ⟨1156511, by rfl⟩ : syracuseStep 1542015 = 2313023) B2313023
theorem B7407575 : Blo 1541468 7407575 := bstep (se 1 (by rfl) ⟨5555681, by rfl⟩ : syracuseStep 7407575 = 11111363) B11111363
theorem B1542139 : Blo 1541468 1542139 := bstep (se 1 (by rfl) ⟨1156604, by rfl⟩ : syracuseStep 1542139 = 2313209) B2313209
theorem B1542207 : Blo 1541468 1542207 := bstep (se 1 (by rfl) ⟨1156655, by rfl⟩ : syracuseStep 1542207 = 2313311) B2313311
theorem B1542463 : Blo 1541468 1542463 := bstep (se 1 (by rfl) ⟨1156847, by rfl⟩ : syracuseStep 1542463 = 2313695) B2313695
theorem B2312603 : Blo 1541468 2312603 := bstep (se 1 (by rfl) ⟨1734452, by rfl⟩ : syracuseStep 2312603 = 3468905) B3468905
theorem B1542555 : Blo 1541468 1542555 := bstep (se 1 (by rfl) ⟨1156916, by rfl⟩ : syracuseStep 1542555 = 2313833) B2313833
theorem B1952191 : Blo 1541468 1952191 := bstep (se 1 (by rfl) ⟨1464143, by rfl⟩ : syracuseStep 1952191 = 2928287) B2928287
theorem B1542591 : Blo 1541468 1542591 := bstep (se 1 (by rfl) ⟨1156943, by rfl⟩ : syracuseStep 1542591 = 2313887) B2313887
theorem B2312759 : Blo 1541468 2312759 := bstep (se 1 (by rfl) ⟨1734569, by rfl⟩ : syracuseStep 2312759 = 3469139) B3469139
theorem B1542767 : Blo 1541468 1542767 := bstep (se 1 (by rfl) ⟨1157075, by rfl⟩ : syracuseStep 1542767 = 2314151) B2314151
theorem B1542783 : Blo 1541468 1542783 := bstep (se 1 (by rfl) ⟨1157087, by rfl⟩ : syracuseStep 1542783 = 2314175) B2314175
theorem B4393615 : Blo 1541468 4393615 := bstep (se 1 (by rfl) ⟨3295211, by rfl⟩ : syracuseStep 4393615 = 6590423) B6590423
theorem B57085019 : Blo 1541468 57085019 := bstep (se 1 (by rfl) ⟨42813764, by rfl⟩ : syracuseStep 57085019 = 85627529) B85627529
theorem B1543323 : Blo 1541468 1543323 := bstep (se 1 (by rfl) ⟨1157492, by rfl⟩ : syracuseStep 1543323 = 2314985) B2314985
theorem B1543335 : Blo 1541468 1543335 := bstep (se 1 (by rfl) ⟨1157501, by rfl⟩ : syracuseStep 1543335 = 2315003) B2315003
theorem B1543359 : Blo 1541468 1543359 := bstep (se 1 (by rfl) ⟨1157519, by rfl⟩ : syracuseStep 1543359 = 2315039) B2315039
theorem B1543419 : Blo 1541468 1543419 := bstep (se 1 (by rfl) ⟨1157564, by rfl⟩ : syracuseStep 1543419 = 2315129) B2315129
theorem B3468635 : Blo 1541468 3468635 := bstep (se 1 (by rfl) ⟨2601476, by rfl⟩ : syracuseStep 3468635 = 5202953) B5202953
theorem B2469359 : Blo 1541468 2469359 := bstep (se 1 (by rfl) ⟨1852019, by rfl⟩ : syracuseStep 2469359 = 3704039) B3704039
theorem B3903329 : Blo 1541468 3903329 := bstep (se 2 (by rfl) ⟨1463748, by rfl⟩ : syracuseStep 3903329 = 2927497) B2927497
theorem B3469247 : Blo 1541468 3469247 := bstep (se 1 (by rfl) ⟨2601935, by rfl⟩ : syracuseStep 3469247 = 5203871) B5203871
theorem B4395005 : Blo 1541468 4395005 := bstep (se 3 (by rfl) ⟨824063, by rfl⟩ : syracuseStep 4395005 = 1648127) B1648127
theorem B3469481 : Blo 1541468 3469481 := bstep (se 2 (by rfl) ⟨1301055, by rfl⟩ : syracuseStep 3469481 = 2602111) B2602111
theorem B44478659 : Blo 1541468 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B2314559 : Blo 1541468 2314559 := bstep (se 1 (by rfl) ⟨1735919, by rfl⟩ : syracuseStep 2314559 = 3471839) B3471839
theorem B433533383 : Blo 1541468 433533383 := bstep (se 1 (by rfl) ⟨325150037, by rfl⟩ : syracuseStep 433533383 = 650300075) B650300075
theorem B2314727 : Blo 1541468 2314727 := bstep (se 1 (by rfl) ⟨1736045, by rfl⟩ : syracuseStep 2314727 = 3472091) B3472091
theorem B3903977 : Blo 1541468 3903977 := bstep (se 2 (by rfl) ⟨1463991, by rfl⟩ : syracuseStep 3903977 = 2927983) B2927983
theorem B8450729 : Blo 1541468 8450729 := bstep (se 2 (by rfl) ⟨3169023, by rfl⟩ : syracuseStep 8450729 = 6338047) B6338047
theorem B9376559 : Blo 1541468 9376559 := bstep (se 1 (by rfl) ⟨7032419, by rfl⟩ : syracuseStep 9376559 = 14064839) B14064839
theorem B2315135 : Blo 1541468 2315135 := bstep (se 1 (by rfl) ⟨1736351, by rfl⟩ : syracuseStep 2315135 = 3472703) B3472703
theorem B14070847 : Blo 1541468 14070847 := bstep (se 1 (by rfl) ⟨10553135, by rfl⟩ : syracuseStep 14070847 = 21106271) B21106271
theorem B16684343 : Blo 1541468 16684343 := bstep (se 1 (by rfl) ⟨12513257, by rfl⟩ : syracuseStep 16684343 = 25026515) B25026515
theorem B7812449 : Blo 1541468 7812449 := bstep (se 2 (by rfl) ⟨2929668, by rfl⟩ : syracuseStep 7812449 = 5859337) B5859337
theorem B7411151 : Blo 1541468 7411151 := bstep (se 1 (by rfl) ⟨5558363, by rfl⟩ : syracuseStep 7411151 = 11116727) B11116727
theorem B6592063 : Blo 1541468 6592063 := bstep (se 1 (by rfl) ⟨4944047, by rfl⟩ : syracuseStep 6592063 = 9888095) B9888095
theorem B2602975 : Blo 1541468 2602975 := bstep (se 1 (by rfl) ⟨1952231, by rfl⟩ : syracuseStep 2602975 = 3904463) B3904463
theorem B7510043 : Blo 1541468 7510043 := bstep (se 1 (by rfl) ⟨5632532, by rfl⟩ : syracuseStep 7510043 = 11265065) B11265065
theorem B6584647 : Blo 1541468 6584647 := bstep (se 1 (by rfl) ⟨4938485, by rfl⟩ : syracuseStep 6584647 = 9876971) B9876971
theorem B3471785 : Blo 1541468 3471785 := bstep (se 2 (by rfl) ⟨1301919, by rfl⟩ : syracuseStep 3471785 = 2603839) B2603839
theorem B5208731 : Blo 1541468 5208731 := bstep (se 1 (by rfl) ⟨3906548, by rfl⟩ : syracuseStep 5208731 = 7813097) B7813097
theorem B1735807 : Blo 1541468 1735807 := bstep (se 1 (by rfl) ⟨1301855, by rfl⟩ : syracuseStep 1735807 = 2603711) B2603711
theorem B53452399 : Blo 1541468 53452399 := bstep (se 1 (by rfl) ⟨40089299, by rfl⟩ : syracuseStep 53452399 = 80178599) B80178599
theorem B23731991 : Blo 1541468 23731991 := bstep (se 1 (by rfl) ⟨17798993, by rfl⟩ : syracuseStep 23731991 = 35597987) B35597987
theorem B13172543 : Blo 1541468 13172543 := bstep (se 1 (by rfl) ⟨9879407, by rfl⟩ : syracuseStep 13172543 = 19758815) B19758815
theorem B9887609 : Blo 1541468 9887609 := bstep (se 2 (by rfl) ⟨3707853, by rfl⟩ : syracuseStep 9887609 = 7415707) B7415707
theorem B289022255 : Blo 1541468 289022255 := bstep (se 1 (by rfl) ⟨216766691, by rfl⟩ : syracuseStep 289022255 = 433533383) B433533383
theorem B6251039 : Blo 1541468 6251039 := bstep (se 1 (by rfl) ⟨4688279, by rfl⟩ : syracuseStep 6251039 = 9376559) B9376559
theorem B8782445 : Blo 1541468 8782445 := bstep (se 3 (by rfl) ⟨1646708, by rfl⟩ : syracuseStep 8782445 = 3293417) B3293417
theorem B5858153 : Blo 1541468 5858153 := bstep (se 2 (by rfl) ⟨2196807, by rfl⟩ : syracuseStep 5858153 = 4393615) B4393615
theorem B4940767 : Blo 1541468 4940767 := bstep (se 1 (by rfl) ⟨3705575, by rfl⟩ : syracuseStep 4940767 = 7411151) B7411151
theorem B18761129 : Blo 1541468 18761129 := bstep (se 2 (by rfl) ⟨7035423, by rfl⟩ : syracuseStep 18761129 = 14070847) B14070847
theorem B1541735 : Blo 1541468 1541735 := bstep (se 1 (by rfl) ⟨1156301, by rfl⟩ : syracuseStep 1541735 = 2312603) B2312603
theorem B1541839 : Blo 1541468 1541839 := bstep (se 1 (by rfl) ⟨1156379, by rfl⟩ : syracuseStep 1541839 = 2312759) B2312759
theorem B2312423 : Blo 1541468 2312423 := bstep (se 1 (by rfl) ⟨1734317, by rfl⟩ : syracuseStep 2312423 = 3468635) B3468635
theorem B15821327 : Blo 1541468 15821327 := bstep (se 1 (by rfl) ⟨11865995, by rfl⟩ : syracuseStep 15821327 = 23731991) B23731991
theorem B2312831 : Blo 1541468 2312831 := bstep (se 1 (by rfl) ⟨1734623, by rfl⟩ : syracuseStep 2312831 = 3469247) B3469247
theorem B2312987 : Blo 1541468 2312987 := bstep (se 1 (by rfl) ⟨1734740, by rfl⟩ : syracuseStep 2312987 = 3469481) B3469481
theorem B1543039 : Blo 1541468 1543039 := bstep (se 1 (by rfl) ⟨1157279, by rfl⟩ : syracuseStep 1543039 = 2314559) B2314559
theorem B1543151 : Blo 1541468 1543151 := bstep (se 1 (by rfl) ⟨1157363, by rfl⟩ : syracuseStep 1543151 = 2314727) B2314727
theorem B4943099 : Blo 1541468 4943099 := bstep (se 1 (by rfl) ⟨3707324, by rfl⟩ : syracuseStep 4943099 = 7414649) B7414649
theorem B1543423 : Blo 1541468 1543423 := bstep (se 1 (by rfl) ⟨1157567, by rfl⟩ : syracuseStep 1543423 = 2315135) B2315135
theorem B5205275 : Blo 1541468 5205275 := bstep (se 1 (by rfl) ⟨3903956, by rfl⟩ : syracuseStep 5205275 = 7807913) B7807913
theorem B2314409 : Blo 1541468 2314409 := bstep (se 2 (by rfl) ⟨867903, by rfl⟩ : syracuseStep 2314409 = 1735807) B1735807
theorem B2314523 : Blo 1541468 2314523 := bstep (se 1 (by rfl) ⟨1735892, by rfl⟩ : syracuseStep 2314523 = 3471785) B3471785
theorem B38056679 : Blo 1541468 38056679 := bstep (se 1 (by rfl) ⟨28542509, by rfl⟩ : syracuseStep 38056679 = 57085019) B57085019
theorem B2602219 : Blo 1541468 2602219 := bstep (se 1 (by rfl) ⟨1951664, by rfl⟩ : syracuseStep 2602219 = 3903329) B3903329
theorem B6591739 : Blo 1541468 6591739 := bstep (se 1 (by rfl) ⟨4943804, by rfl⟩ : syracuseStep 6591739 = 9887609) B9887609
theorem B3470633 : Blo 1541468 3470633 := bstep (se 2 (by rfl) ⟨1301487, by rfl⟩ : syracuseStep 3470633 = 2602975) B2602975
theorem B2930003 : Blo 1541468 2930003 := bstep (se 1 (by rfl) ⟨2197502, by rfl⟩ : syracuseStep 2930003 = 4395005) B4395005
theorem B20026781 : Blo 1541468 20026781 := bstep (se 3 (by rfl) ⟨3755021, by rfl⟩ : syracuseStep 20026781 = 7510043) B7510043
theorem B29652439 : Blo 1541468 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B2602651 : Blo 1541468 2602651 := bstep (se 1 (by rfl) ⟨1951988, by rfl⟩ : syracuseStep 2602651 = 3903977) B3903977
theorem B8779529 : Blo 1541468 8779529 := bstep (se 2 (by rfl) ⟨3292323, by rfl⟩ : syracuseStep 8779529 = 6584647) B6584647
theorem B5633819 : Blo 1541468 5633819 := bstep (se 1 (by rfl) ⟨4225364, by rfl⟩ : syracuseStep 5633819 = 8450729) B8450729
theorem B2602921 : Blo 1541468 2602921 := bstep (se 2 (by rfl) ⟨976095, by rfl⟩ : syracuseStep 2602921 = 1952191) B1952191
theorem B11122895 : Blo 1541468 11122895 := bstep (se 1 (by rfl) ⟨8342171, by rfl⟩ : syracuseStep 11122895 = 16684343) B16684343
theorem B7805159 : Blo 1541468 7805159 := bstep (se 1 (by rfl) ⟨5853869, by rfl⟩ : syracuseStep 7805159 = 11707739) B11707739
theorem B5208299 : Blo 1541468 5208299 := bstep (se 1 (by rfl) ⟨3906224, by rfl⟩ : syracuseStep 5208299 = 7812449) B7812449
theorem B7920107 : Blo 1541468 7920107 := bstep (se 1 (by rfl) ⟨5940080, by rfl⟩ : syracuseStep 7920107 = 11880161) B11880161
theorem B4938383 : Blo 1541468 4938383 := bstep (se 1 (by rfl) ⟨3703787, by rfl⟩ : syracuseStep 4938383 = 7407575) B7407575
theorem B3472487 : Blo 1541468 3472487 := bstep (se 1 (by rfl) ⟨2604365, by rfl⟩ : syracuseStep 3472487 = 5208731) B5208731
theorem B8789417 : Blo 1541468 8789417 := bstep (se 2 (by rfl) ⟨3296031, by rfl⟩ : syracuseStep 8789417 = 6592063) B6592063
theorem B162487781 : Blo 1541468 162487781 := bstep (se 4 (by rfl) ⟨15233229, by rfl⟩ : syracuseStep 162487781 = 30466459) B30466459
theorem B71269865 : Blo 1541468 71269865 := bstep (se 2 (by rfl) ⟨26726199, by rfl⟩ : syracuseStep 71269865 = 53452399) B53452399
theorem B1646239 : Blo 1541468 1646239 := bstep (se 1 (by rfl) ⟨1234679, by rfl⟩ : syracuseStep 1646239 = 2469359) B2469359
theorem B8781695 : Blo 1541468 8781695 := bstep (se 1 (by rfl) ⟨6586271, by rfl⟩ : syracuseStep 8781695 = 13172543) B13172543
theorem B25371119 : Blo 1541468 25371119 := bstep (se 1 (by rfl) ⟨19028339, by rfl⟩ : syracuseStep 25371119 = 38056679) B38056679
theorem B6587689 : Blo 1541468 6587689 := bstep (se 2 (by rfl) ⟨2470383, by rfl⟩ : syracuseStep 6587689 = 4940767) B4940767
theorem B7415263 : Blo 1541468 7415263 := bstep (se 1 (by rfl) ⟨5561447, by rfl⟩ : syracuseStep 7415263 = 11122895) B11122895
theorem B1541615 : Blo 1541468 1541615 := bstep (se 1 (by rfl) ⟨1156211, by rfl⟩ : syracuseStep 1541615 = 2312423) B2312423
theorem B5203439 : Blo 1541468 5203439 := bstep (se 1 (by rfl) ⟨3902579, by rfl⟩ : syracuseStep 5203439 = 7805159) B7805159
theorem B1541887 : Blo 1541468 1541887 := bstep (se 1 (by rfl) ⟨1156415, by rfl⟩ : syracuseStep 1541887 = 2312831) B2312831
theorem B1541991 : Blo 1541468 1541991 := bstep (se 1 (by rfl) ⟨1156493, by rfl⟩ : syracuseStep 1541991 = 2312987) B2312987
theorem B39536585 : Blo 1541468 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B3295399 : Blo 1541468 3295399 := bstep (se 1 (by rfl) ⟨2471549, by rfl⟩ : syracuseStep 3295399 = 4943099) B4943099
theorem B5859611 : Blo 1541468 5859611 := bstep (se 1 (by rfl) ⟨4394708, by rfl⟩ : syracuseStep 5859611 = 8789417) B8789417
theorem B108325187 : Blo 1541468 108325187 := bstep (se 1 (by rfl) ⟨81243890, by rfl⟩ : syracuseStep 108325187 = 162487781) B162487781
theorem B1542939 : Blo 1541468 1542939 := bstep (se 1 (by rfl) ⟨1157204, by rfl⟩ : syracuseStep 1542939 = 2314409) B2314409
theorem B1543015 : Blo 1541468 1543015 := bstep (se 1 (by rfl) ⟨1157261, by rfl⟩ : syracuseStep 1543015 = 2314523) B2314523
theorem B2313755 : Blo 1541468 2313755 := bstep (se 1 (by rfl) ⟨1735316, by rfl⟩ : syracuseStep 2313755 = 3470633) B3470633
theorem B1953335 : Blo 1541468 1953335 := bstep (se 1 (by rfl) ⟨1465001, by rfl⟩ : syracuseStep 1953335 = 2930003) B2930003
theorem B5853019 : Blo 1541468 5853019 := bstep (se 1 (by rfl) ⟨4389764, by rfl⟩ : syracuseStep 5853019 = 8779529) B8779529
theorem B3755879 : Blo 1541468 3755879 := bstep (se 1 (by rfl) ⟨2816909, by rfl⟩ : syracuseStep 3755879 = 5633819) B5633819
theorem B3469625 : Blo 1541468 3469625 := bstep (se 2 (by rfl) ⟨1301109, by rfl⟩ : syracuseStep 3469625 = 2602219) B2602219
theorem B5280071 : Blo 1541468 5280071 := bstep (se 1 (by rfl) ⟨3960053, by rfl⟩ : syracuseStep 5280071 = 7920107) B7920107
theorem B10547551 : Blo 1541468 10547551 := bstep (se 1 (by rfl) ⟨7910663, by rfl⟩ : syracuseStep 10547551 = 15821327) B15821327
theorem B2314991 : Blo 1541468 2314991 := bstep (se 1 (by rfl) ⟨1736243, by rfl⟩ : syracuseStep 2314991 = 3472487) B3472487
theorem B3470183 : Blo 1541468 3470183 := bstep (se 1 (by rfl) ⟨2602637, by rfl⟩ : syracuseStep 3470183 = 5205275) B5205275
theorem B3470201 : Blo 1541468 3470201 := bstep (se 2 (by rfl) ⟨1301325, by rfl⟩ : syracuseStep 3470201 = 2602651) B2602651
theorem B3470561 : Blo 1541468 3470561 := bstep (se 2 (by rfl) ⟨1301460, by rfl⟩ : syracuseStep 3470561 = 2602921) B2602921
theorem B5854463 : Blo 1541468 5854463 := bstep (se 1 (by rfl) ⟨4390847, by rfl⟩ : syracuseStep 5854463 = 8781695) B8781695
theorem B192681503 : Blo 1541468 192681503 := bstep (se 1 (by rfl) ⟨144511127, by rfl⟩ : syracuseStep 192681503 = 289022255) B289022255
theorem B4167359 : Blo 1541468 4167359 := bstep (se 1 (by rfl) ⟨3125519, by rfl⟩ : syracuseStep 4167359 = 6251039) B6251039
theorem B5854963 : Blo 1541468 5854963 := bstep (se 1 (by rfl) ⟨4391222, by rfl⟩ : syracuseStep 5854963 = 8782445) B8782445
theorem B3905435 : Blo 1541468 3905435 := bstep (se 1 (by rfl) ⟨2929076, by rfl⟩ : syracuseStep 3905435 = 5858153) B5858153
theorem B13351187 : Blo 1541468 13351187 := bstep (se 1 (by rfl) ⟨10013390, by rfl⟩ : syracuseStep 13351187 = 20026781) B20026781
theorem B12507419 : Blo 1541468 12507419 := bstep (se 1 (by rfl) ⟨9380564, by rfl⟩ : syracuseStep 12507419 = 18761129) B18761129
theorem B3472199 : Blo 1541468 3472199 := bstep (se 1 (by rfl) ⟨2604149, by rfl⟩ : syracuseStep 3472199 = 5208299) B5208299
theorem B8788985 : Blo 1541468 8788985 := bstep (se 2 (by rfl) ⟨3295869, by rfl⟩ : syracuseStep 8788985 = 6591739) B6591739
theorem B3292255 : Blo 1541468 3292255 := bstep (se 1 (by rfl) ⟨2469191, by rfl⟩ : syracuseStep 3292255 = 4938383) B4938383
theorem B2194985 : Blo 1541468 2194985 := bstep (se 2 (by rfl) ⟨823119, by rfl⟩ : syracuseStep 2194985 = 1646239) B1646239
theorem B47513243 : Blo 1541468 47513243 := bstep (se 1 (by rfl) ⟨35634932, by rfl⟩ : syracuseStep 47513243 = 71269865) B71269865
theorem B35603165 : Blo 1541468 35603165 := bstep (se 3 (by rfl) ⟨6675593, by rfl⟩ : syracuseStep 35603165 = 13351187) B13351187
theorem B2778239 : Blo 1541468 2778239 := bstep (se 1 (by rfl) ⟨2083679, by rfl⟩ : syracuseStep 2778239 = 4167359) B4167359
theorem B8783585 : Blo 1541468 8783585 := bstep (se 2 (by rfl) ⟨3293844, by rfl⟩ : syracuseStep 8783585 = 6587689) B6587689
theorem B5859323 : Blo 1541468 5859323 := bstep (se 1 (by rfl) ⟨4394492, by rfl⟩ : syracuseStep 5859323 = 8788985) B8788985
theorem B1542503 : Blo 1541468 1542503 := bstep (se 1 (by rfl) ⟨1156877, by rfl⟩ : syracuseStep 1542503 = 2313755) B2313755
theorem B2313083 : Blo 1541468 2313083 := bstep (se 1 (by rfl) ⟨1734812, by rfl⟩ : syracuseStep 2313083 = 3469625) B3469625
theorem B4393865 : Blo 1541468 4393865 := bstep (se 2 (by rfl) ⟨1647699, by rfl⟩ : syracuseStep 4393865 = 3295399) B3295399
theorem B1543327 : Blo 1541468 1543327 := bstep (se 1 (by rfl) ⟨1157495, by rfl⟩ : syracuseStep 1543327 = 2314991) B2314991
theorem B17558693 : Blo 1541468 17558693 := bstep (se 4 (by rfl) ⟨1646127, by rfl⟩ : syracuseStep 17558693 = 3292255) B3292255
theorem B2313455 : Blo 1541468 2313455 := bstep (se 1 (by rfl) ⟨1735091, by rfl⟩ : syracuseStep 2313455 = 3470183) B3470183
theorem B2313467 : Blo 1541468 2313467 := bstep (se 1 (by rfl) ⟨1735100, by rfl⟩ : syracuseStep 2313467 = 3470201) B3470201
theorem B33353117 : Blo 1541468 33353117 := bstep (se 3 (by rfl) ⟨6253709, by rfl⟩ : syracuseStep 33353117 = 12507419) B12507419
theorem B2313707 : Blo 1541468 2313707 := bstep (se 1 (by rfl) ⟨1735280, by rfl⟩ : syracuseStep 2313707 = 3470561) B3470561
theorem B3902975 : Blo 1541468 3902975 := bstep (se 1 (by rfl) ⟨2927231, by rfl⟩ : syracuseStep 3902975 = 5854463) B5854463
theorem B3468959 : Blo 1541468 3468959 := bstep (se 1 (by rfl) ⟨2601719, by rfl⟩ : syracuseStep 3468959 = 5203439) B5203439
theorem B128454335 : Blo 1541468 128454335 := bstep (se 1 (by rfl) ⟨96340751, by rfl⟩ : syracuseStep 128454335 = 192681503) B192681503
theorem B26357723 : Blo 1541468 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B5853293 : Blo 1541468 5853293 := bstep (se 3 (by rfl) ⟨1097492, by rfl⟩ : syracuseStep 5853293 = 2194985) B2194985
theorem B72216791 : Blo 1541468 72216791 := bstep (se 1 (by rfl) ⟨54162593, by rfl⟩ : syracuseStep 72216791 = 108325187) B108325187
theorem B2314799 : Blo 1541468 2314799 := bstep (se 1 (by rfl) ⟨1736099, by rfl⟩ : syracuseStep 2314799 = 3472199) B3472199
theorem B31675495 : Blo 1541468 31675495 := bstep (se 1 (by rfl) ⟨23756621, by rfl⟩ : syracuseStep 31675495 = 47513243) B47513243
theorem B7804025 : Blo 1541468 7804025 := bstep (se 2 (by rfl) ⟨2926509, by rfl⟩ : syracuseStep 7804025 = 5853019) B5853019
theorem B2503919 : Blo 1541468 2503919 := bstep (se 1 (by rfl) ⟨1877939, by rfl⟩ : syracuseStep 2503919 = 3755879) B3755879
theorem B16914079 : Blo 1541468 16914079 := bstep (se 1 (by rfl) ⟨12685559, by rfl⟩ : syracuseStep 16914079 = 25371119) B25371119
theorem B14063401 : Blo 1541468 14063401 := bstep (se 2 (by rfl) ⟨5273775, by rfl⟩ : syracuseStep 14063401 = 10547551) B10547551
theorem B14080189 : Blo 1541468 14080189 := bstep (se 3 (by rfl) ⟨2640035, by rfl⟩ : syracuseStep 14080189 = 5280071) B5280071
theorem B2603623 : Blo 1541468 2603623 := bstep (se 1 (by rfl) ⟨1952717, by rfl⟩ : syracuseStep 2603623 = 3905435) B3905435
theorem B5208893 : Blo 1541468 5208893 := bstep (se 3 (by rfl) ⟨976667, by rfl⟩ : syracuseStep 5208893 = 1953335) B1953335
theorem B3906407 : Blo 1541468 3906407 := bstep (se 1 (by rfl) ⟨2929805, by rfl⟩ : syracuseStep 3906407 = 5859611) B5859611
theorem B9887017 : Blo 1541468 9887017 := bstep (se 2 (by rfl) ⟨3707631, by rfl⟩ : syracuseStep 9887017 = 7415263) B7415263
theorem B7806617 : Blo 1541468 7806617 := bstep (se 2 (by rfl) ⟨2927481, by rfl⟩ : syracuseStep 7806617 = 5854963) B5854963
theorem B48144527 : Blo 1541468 48144527 := bstep (se 1 (by rfl) ⟨36108395, by rfl⟩ : syracuseStep 48144527 = 72216791) B72216791
theorem B5202683 : Blo 1541468 5202683 := bstep (se 1 (by rfl) ⟨3902012, by rfl⟩ : syracuseStep 5202683 = 7804025) B7804025
theorem B1852159 : Blo 1541468 1852159 := bstep (se 1 (by rfl) ⟨1389119, by rfl⟩ : syracuseStep 1852159 = 2778239) B2778239
theorem B13182689 : Blo 1541468 13182689 := bstep (se 2 (by rfl) ⟨4943508, by rfl⟩ : syracuseStep 13182689 = 9887017) B9887017
theorem B1542055 : Blo 1541468 1542055 := bstep (se 1 (by rfl) ⟨1156541, by rfl⟩ : syracuseStep 1542055 = 2313083) B2313083
theorem B1542303 : Blo 1541468 1542303 := bstep (se 1 (by rfl) ⟨1156727, by rfl⟩ : syracuseStep 1542303 = 2313455) B2313455
theorem B1542311 : Blo 1541468 1542311 := bstep (se 1 (by rfl) ⟨1156733, by rfl⟩ : syracuseStep 1542311 = 2313467) B2313467
theorem B22235411 : Blo 1541468 22235411 := bstep (se 1 (by rfl) ⟨16676558, by rfl⟩ : syracuseStep 22235411 = 33353117) B33353117
theorem B1542471 : Blo 1541468 1542471 := bstep (se 1 (by rfl) ⟨1156853, by rfl⟩ : syracuseStep 1542471 = 2313707) B2313707
theorem B11716973 : Blo 1541468 11716973 := bstep (se 3 (by rfl) ⟨2196932, by rfl⟩ : syracuseStep 11716973 = 4393865) B4393865
theorem B5204411 : Blo 1541468 5204411 := bstep (se 1 (by rfl) ⟨3903308, by rfl⟩ : syracuseStep 5204411 = 7806617) B7806617
theorem B2312639 : Blo 1541468 2312639 := bstep (se 1 (by rfl) ⟨1734479, by rfl⟩ : syracuseStep 2312639 = 3468959) B3468959
theorem B3902195 : Blo 1541468 3902195 := bstep (se 1 (by rfl) ⟨2926646, by rfl⟩ : syracuseStep 3902195 = 5853293) B5853293
theorem B1543199 : Blo 1541468 1543199 := bstep (se 1 (by rfl) ⟨1157399, by rfl⟩ : syracuseStep 1543199 = 2314799) B2314799
theorem B23735443 : Blo 1541468 23735443 := bstep (se 1 (by rfl) ⟨17801582, by rfl⟩ : syracuseStep 23735443 = 35603165) B35603165
theorem B42233993 : Blo 1541468 42233993 := bstep (se 2 (by rfl) ⟨15837747, by rfl⟩ : syracuseStep 42233993 = 31675495) B31675495
theorem B2601983 : Blo 1541468 2601983 := bstep (se 1 (by rfl) ⟨1951487, by rfl⟩ : syracuseStep 2601983 = 3902975) B3902975
theorem B85636223 : Blo 1541468 85636223 := bstep (se 1 (by rfl) ⟨64227167, by rfl⟩ : syracuseStep 85636223 = 128454335) B128454335
theorem B18773585 : Blo 1541468 18773585 := bstep (se 2 (by rfl) ⟨7040094, by rfl⟩ : syracuseStep 18773585 = 14080189) B14080189
theorem B3471497 : Blo 1541468 3471497 := bstep (se 2 (by rfl) ⟨1301811, by rfl⟩ : syracuseStep 3471497 = 2603623) B2603623
theorem B1669279 : Blo 1541468 1669279 := bstep (se 1 (by rfl) ⟨1251959, by rfl⟩ : syracuseStep 1669279 = 2503919) B2503919
theorem B5855723 : Blo 1541468 5855723 := bstep (se 1 (by rfl) ⟨4391792, by rfl⟩ : syracuseStep 5855723 = 8783585) B8783585
theorem B3906215 : Blo 1541468 3906215 := bstep (se 1 (by rfl) ⟨2929661, by rfl⟩ : syracuseStep 3906215 = 5859323) B5859323
theorem B75004805 : Blo 1541468 75004805 := bstep (se 4 (by rfl) ⟨7031700, by rfl⟩ : syracuseStep 75004805 = 14063401) B14063401
theorem B3472595 : Blo 1541468 3472595 := bstep (se 1 (by rfl) ⟨2604446, by rfl⟩ : syracuseStep 3472595 = 5208893) B5208893
theorem B2604271 : Blo 1541468 2604271 := bstep (se 1 (by rfl) ⟨1953203, by rfl⟩ : syracuseStep 2604271 = 3906407) B3906407
theorem B11705795 : Blo 1541468 11705795 := bstep (se 1 (by rfl) ⟨8779346, by rfl⟩ : syracuseStep 11705795 = 17558693) B17558693
theorem B22552105 : Blo 1541468 22552105 := bstep (se 2 (by rfl) ⟨8457039, by rfl⟩ : syracuseStep 22552105 = 16914079) B16914079
theorem B17571815 : Blo 1541468 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B28155995 : Blo 1541468 28155995 := bstep (se 1 (by rfl) ⟨21116996, by rfl⟩ : syracuseStep 28155995 = 42233993) B42233993
theorem B32096351 : Blo 1541468 32096351 := bstep (se 1 (by rfl) ⟨24072263, by rfl⟩ : syracuseStep 32096351 = 48144527) B48144527
theorem B57090815 : Blo 1541468 57090815 := bstep (se 1 (by rfl) ⟨42818111, by rfl⟩ : syracuseStep 57090815 = 85636223) B85636223
theorem B31647257 : Blo 1541468 31647257 := bstep (se 2 (by rfl) ⟨11867721, by rfl⟩ : syracuseStep 31647257 = 23735443) B23735443
theorem B1541759 : Blo 1541468 1541759 := bstep (se 1 (by rfl) ⟨1156319, by rfl⟩ : syracuseStep 1541759 = 2312639) B2312639
theorem B142445141 : Blo 1541468 142445141 := bstep (se 8 (by rfl) ⟨834639, by rfl⟩ : syracuseStep 142445141 = 1669279) B1669279
theorem B3468455 : Blo 1541468 3468455 := bstep (se 1 (by rfl) ⟨2601341, by rfl⟩ : syracuseStep 3468455 = 5202683) B5202683
theorem B2469545 : Blo 1541468 2469545 := bstep (se 2 (by rfl) ⟨926079, by rfl⟩ : syracuseStep 2469545 = 1852159) B1852159
theorem B2314331 : Blo 1541468 2314331 := bstep (se 1 (by rfl) ⟨1735748, by rfl⟩ : syracuseStep 2314331 = 3471497) B3471497
theorem B14823607 : Blo 1541468 14823607 := bstep (se 1 (by rfl) ⟨11117705, by rfl⟩ : syracuseStep 14823607 = 22235411) B22235411
theorem B7811315 : Blo 1541468 7811315 := bstep (se 1 (by rfl) ⟨5858486, by rfl⟩ : syracuseStep 7811315 = 11716973) B11716973
theorem B3469607 : Blo 1541468 3469607 := bstep (se 1 (by rfl) ⟨2602205, by rfl⟩ : syracuseStep 3469607 = 5204411) B5204411
theorem B3903815 : Blo 1541468 3903815 := bstep (se 1 (by rfl) ⟨2927861, by rfl⟩ : syracuseStep 3903815 = 5855723) B5855723
theorem B2601463 : Blo 1541468 2601463 := bstep (se 1 (by rfl) ⟨1951097, by rfl⟩ : syracuseStep 2601463 = 3902195) B3902195
theorem B30069473 : Blo 1541468 30069473 := bstep (se 2 (by rfl) ⟨11276052, by rfl⟩ : syracuseStep 30069473 = 22552105) B22552105
theorem B2315063 : Blo 1541468 2315063 := bstep (se 1 (by rfl) ⟨1736297, by rfl⟩ : syracuseStep 2315063 = 3472595) B3472595
theorem B7803863 : Blo 1541468 7803863 := bstep (se 1 (by rfl) ⟨5852897, by rfl⟩ : syracuseStep 7803863 = 11705795) B11705795
theorem B1734655 : Blo 1541468 1734655 := bstep (se 1 (by rfl) ⟨1300991, by rfl⟩ : syracuseStep 1734655 = 2601983) B2601983
theorem B12515723 : Blo 1541468 12515723 := bstep (se 1 (by rfl) ⟨9386792, by rfl⟩ : syracuseStep 12515723 = 18773585) B18773585
theorem B8788459 : Blo 1541468 8788459 := bstep (se 1 (by rfl) ⟨6591344, by rfl⟩ : syracuseStep 8788459 = 13182689) B13182689
theorem B3472361 : Blo 1541468 3472361 := bstep (se 2 (by rfl) ⟨1302135, by rfl⟩ : syracuseStep 3472361 = 2604271) B2604271
theorem B2604143 : Blo 1541468 2604143 := bstep (se 1 (by rfl) ⟨1953107, by rfl⟩ : syracuseStep 2604143 = 3906215) B3906215
theorem B50003203 : Blo 1541468 50003203 := bstep (se 1 (by rfl) ⟨37502402, by rfl⟩ : syracuseStep 50003203 = 75004805) B75004805
theorem B11714543 : Blo 1541468 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B21397567 : Blo 1541468 21397567 := bstep (se 1 (by rfl) ⟨16048175, by rfl⟩ : syracuseStep 21397567 = 32096351) B32096351
theorem B38060543 : Blo 1541468 38060543 := bstep (se 1 (by rfl) ⟨28545407, by rfl⟩ : syracuseStep 38060543 = 57090815) B57090815
theorem B5202575 : Blo 1541468 5202575 := bstep (se 1 (by rfl) ⟨3901931, by rfl⟩ : syracuseStep 5202575 = 7803863) B7803863
theorem B94963427 : Blo 1541468 94963427 := bstep (se 1 (by rfl) ⟨71222570, by rfl⟩ : syracuseStep 94963427 = 142445141) B142445141
theorem B80185261 : Blo 1541468 80185261 := bstep (se 3 (by rfl) ⟨15034736, by rfl⟩ : syracuseStep 80185261 = 30069473) B30069473
theorem B2312303 : Blo 1541468 2312303 := bstep (se 1 (by rfl) ⟨1734227, by rfl⟩ : syracuseStep 2312303 = 3468455) B3468455
theorem B7809695 : Blo 1541468 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B2312873 : Blo 1541468 2312873 := bstep (se 2 (by rfl) ⟨867327, by rfl⟩ : syracuseStep 2312873 = 1734655) B1734655
theorem B1542887 : Blo 1541468 1542887 := bstep (se 1 (by rfl) ⟨1157165, by rfl⟩ : syracuseStep 1542887 = 2314331) B2314331
theorem B18770663 : Blo 1541468 18770663 := bstep (se 1 (by rfl) ⟨14077997, by rfl⟩ : syracuseStep 18770663 = 28155995) B28155995
theorem B2313071 : Blo 1541468 2313071 := bstep (se 1 (by rfl) ⟨1734803, by rfl⟩ : syracuseStep 2313071 = 3469607) B3469607
theorem B1543375 : Blo 1541468 1543375 := bstep (se 1 (by rfl) ⟨1157531, by rfl⟩ : syracuseStep 1543375 = 2315063) B2315063
theorem B11717945 : Blo 1541468 11717945 := bstep (se 2 (by rfl) ⟨4394229, by rfl⟩ : syracuseStep 11717945 = 8788459) B8788459
theorem B3468617 : Blo 1541468 3468617 := bstep (se 2 (by rfl) ⟨1300731, by rfl⟩ : syracuseStep 3468617 = 2601463) B2601463
theorem B21098171 : Blo 1541468 21098171 := bstep (se 1 (by rfl) ⟨15823628, by rfl⟩ : syracuseStep 21098171 = 31647257) B31647257
theorem B8343815 : Blo 1541468 8343815 := bstep (se 1 (by rfl) ⟨6257861, by rfl⟩ : syracuseStep 8343815 = 12515723) B12515723
theorem B66670937 : Blo 1541468 66670937 := bstep (se 2 (by rfl) ⟨25001601, by rfl⟩ : syracuseStep 66670937 = 50003203) B50003203
theorem B2314907 : Blo 1541468 2314907 := bstep (se 1 (by rfl) ⟨1736180, by rfl⟩ : syracuseStep 2314907 = 3472361) B3472361
theorem B5207543 : Blo 1541468 5207543 := bstep (se 1 (by rfl) ⟨3905657, by rfl⟩ : syracuseStep 5207543 = 7811315) B7811315
theorem B2602543 : Blo 1541468 2602543 := bstep (se 1 (by rfl) ⟨1951907, by rfl⟩ : syracuseStep 2602543 = 3903815) B3903815
theorem B19764809 : Blo 1541468 19764809 := bstep (se 2 (by rfl) ⟨7411803, by rfl⟩ : syracuseStep 19764809 = 14823607) B14823607
theorem B1736095 : Blo 1541468 1736095 := bstep (se 1 (by rfl) ⟨1302071, by rfl⟩ : syracuseStep 1736095 = 2604143) B2604143
theorem B1646363 : Blo 1541468 1646363 := bstep (se 1 (by rfl) ⟨1234772, by rfl⟩ : syracuseStep 1646363 = 2469545) B2469545
theorem B22250173 : Blo 1541468 22250173 := bstep (se 3 (by rfl) ⟨4171907, by rfl⟩ : syracuseStep 22250173 = 8343815) B8343815
theorem B63308951 : Blo 1541468 63308951 := bstep (se 1 (by rfl) ⟨47481713, by rfl⟩ : syracuseStep 63308951 = 94963427) B94963427
theorem B1541535 : Blo 1541468 1541535 := bstep (se 1 (by rfl) ⟨1156151, by rfl⟩ : syracuseStep 1541535 = 2312303) B2312303
theorem B1541915 : Blo 1541468 1541915 := bstep (se 1 (by rfl) ⟨1156436, by rfl⟩ : syracuseStep 1541915 = 2312873) B2312873
theorem B1542047 : Blo 1541468 1542047 := bstep (se 1 (by rfl) ⟨1156535, by rfl⟩ : syracuseStep 1542047 = 2313071) B2313071
theorem B2312411 : Blo 1541468 2312411 := bstep (se 1 (by rfl) ⟨1734308, by rfl⟩ : syracuseStep 2312411 = 3468617) B3468617
theorem B25373695 : Blo 1541468 25373695 := bstep (se 1 (by rfl) ⟨19030271, by rfl⟩ : syracuseStep 25373695 = 38060543) B38060543
theorem B3468383 : Blo 1541468 3468383 := bstep (se 1 (by rfl) ⟨2601287, by rfl⟩ : syracuseStep 3468383 = 5202575) B5202575
theorem B1543271 : Blo 1541468 1543271 := bstep (se 1 (by rfl) ⟨1157453, by rfl⟩ : syracuseStep 1543271 = 2314907) B2314907
theorem B13176539 : Blo 1541468 13176539 := bstep (se 1 (by rfl) ⟨9882404, by rfl⟩ : syracuseStep 13176539 = 19764809) B19764809
theorem B5206463 : Blo 1541468 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B12513775 : Blo 1541468 12513775 := bstep (se 1 (by rfl) ⟨9385331, by rfl⟩ : syracuseStep 12513775 = 18770663) B18770663
theorem B2314793 : Blo 1541468 2314793 := bstep (se 2 (by rfl) ⟨868047, by rfl⟩ : syracuseStep 2314793 = 1736095) B1736095
theorem B3470057 : Blo 1541468 3470057 := bstep (se 2 (by rfl) ⟨1301271, by rfl⟩ : syracuseStep 3470057 = 2602543) B2602543
theorem B7811963 : Blo 1541468 7811963 := bstep (se 1 (by rfl) ⟨5858972, by rfl⟩ : syracuseStep 7811963 = 11717945) B11717945
theorem B28530089 : Blo 1541468 28530089 := bstep (se 2 (by rfl) ⟨10698783, by rfl⟩ : syracuseStep 28530089 = 21397567) B21397567
theorem B44447291 : Blo 1541468 44447291 := bstep (se 1 (by rfl) ⟨33335468, by rfl⟩ : syracuseStep 44447291 = 66670937) B66670937
theorem B3471695 : Blo 1541468 3471695 := bstep (se 1 (by rfl) ⟨2603771, by rfl⟩ : syracuseStep 3471695 = 5207543) B5207543
theorem B4390301 : Blo 1541468 4390301 := bstep (se 3 (by rfl) ⟨823181, by rfl⟩ : syracuseStep 4390301 = 1646363) B1646363
theorem B14065447 : Blo 1541468 14065447 := bstep (se 1 (by rfl) ⟨10549085, by rfl⟩ : syracuseStep 14065447 = 21098171) B21098171
theorem B106913681 : Blo 1541468 106913681 := bstep (se 2 (by rfl) ⟨40092630, by rfl⟩ : syracuseStep 106913681 = 80185261) B80185261
theorem B42205967 : Blo 1541468 42205967 := bstep (se 1 (by rfl) ⟨31654475, by rfl⟩ : syracuseStep 42205967 = 63308951) B63308951
theorem B29631527 : Blo 1541468 29631527 := bstep (se 1 (by rfl) ⟨22223645, by rfl⟩ : syracuseStep 29631527 = 44447291) B44447291
theorem B1541607 : Blo 1541468 1541607 := bstep (se 1 (by rfl) ⟨1156205, by rfl⟩ : syracuseStep 1541607 = 2312411) B2312411
theorem B2312255 : Blo 1541468 2312255 := bstep (se 1 (by rfl) ⟨1734191, by rfl⟩ : syracuseStep 2312255 = 3468383) B3468383
theorem B2926867 : Blo 1541468 2926867 := bstep (se 1 (by rfl) ⟨2195150, by rfl⟩ : syracuseStep 2926867 = 4390301) B4390301
theorem B18753929 : Blo 1541468 18753929 := bstep (se 2 (by rfl) ⟨7032723, by rfl⟩ : syracuseStep 18753929 = 14065447) B14065447
theorem B8784359 : Blo 1541468 8784359 := bstep (se 1 (by rfl) ⟨6588269, by rfl⟩ : syracuseStep 8784359 = 13176539) B13176539
theorem B1543195 : Blo 1541468 1543195 := bstep (se 1 (by rfl) ⟨1157396, by rfl⟩ : syracuseStep 1543195 = 2314793) B2314793
theorem B2313371 : Blo 1541468 2313371 := bstep (se 1 (by rfl) ⟨1735028, by rfl⟩ : syracuseStep 2313371 = 3470057) B3470057
theorem B29666897 : Blo 1541468 29666897 := bstep (se 2 (by rfl) ⟨11125086, by rfl⟩ : syracuseStep 29666897 = 22250173) B22250173
theorem B2314463 : Blo 1541468 2314463 := bstep (se 1 (by rfl) ⟨1735847, by rfl⟩ : syracuseStep 2314463 = 3471695) B3471695
theorem B71275787 : Blo 1541468 71275787 := bstep (se 1 (by rfl) ⟨53456840, by rfl⟩ : syracuseStep 71275787 = 106913681) B106913681
theorem B3470975 : Blo 1541468 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B5207975 : Blo 1541468 5207975 := bstep (se 1 (by rfl) ⟨3905981, by rfl⟩ : syracuseStep 5207975 = 7811963) B7811963
theorem B16685033 : Blo 1541468 16685033 := bstep (se 2 (by rfl) ⟨6256887, by rfl⟩ : syracuseStep 16685033 = 12513775) B12513775
theorem B19020059 : Blo 1541468 19020059 := bstep (se 1 (by rfl) ⟨14265044, by rfl⟩ : syracuseStep 19020059 = 28530089) B28530089
theorem B33831593 : Blo 1541468 33831593 := bstep (se 2 (by rfl) ⟨12686847, by rfl⟩ : syracuseStep 33831593 = 25373695) B25373695
theorem B1541503 : Blo 1541468 1541503 := bstep (se 1 (by rfl) ⟨1156127, by rfl⟩ : syracuseStep 1541503 = 2312255) B2312255
theorem B12502619 : Blo 1541468 12502619 := bstep (se 1 (by rfl) ⟨9376964, by rfl⟩ : syracuseStep 12502619 = 18753929) B18753929
theorem B22554395 : Blo 1541468 22554395 := bstep (se 1 (by rfl) ⟨16915796, by rfl⟩ : syracuseStep 22554395 = 33831593) B33831593
theorem B1542247 : Blo 1541468 1542247 := bstep (se 1 (by rfl) ⟨1156685, by rfl⟩ : syracuseStep 1542247 = 2313371) B2313371
theorem B19777931 : Blo 1541468 19777931 := bstep (se 1 (by rfl) ⟨14833448, by rfl⟩ : syracuseStep 19777931 = 29666897) B29666897
theorem B44493421 : Blo 1541468 44493421 := bstep (se 3 (by rfl) ⟨8342516, by rfl⟩ : syracuseStep 44493421 = 16685033) B16685033
theorem B1542975 : Blo 1541468 1542975 := bstep (se 1 (by rfl) ⟨1157231, by rfl⟩ : syracuseStep 1542975 = 2314463) B2314463
theorem B3902489 : Blo 1541468 3902489 := bstep (se 2 (by rfl) ⟨1463433, by rfl⟩ : syracuseStep 3902489 = 2926867) B2926867
theorem B19754351 : Blo 1541468 19754351 := bstep (se 1 (by rfl) ⟨14815763, by rfl⟩ : syracuseStep 19754351 = 29631527) B29631527
theorem B47517191 : Blo 1541468 47517191 := bstep (se 1 (by rfl) ⟨35637893, by rfl⟩ : syracuseStep 47517191 = 71275787) B71275787
theorem B2313983 : Blo 1541468 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B28137311 : Blo 1541468 28137311 := bstep (se 1 (by rfl) ⟨21102983, by rfl⟩ : syracuseStep 28137311 = 42205967) B42205967
theorem B3471983 : Blo 1541468 3471983 := bstep (se 1 (by rfl) ⟨2603987, by rfl⟩ : syracuseStep 3471983 = 5207975) B5207975
theorem B12680039 : Blo 1541468 12680039 := bstep (se 1 (by rfl) ⟨9510029, by rfl⟩ : syracuseStep 12680039 = 19020059) B19020059
theorem B5856239 : Blo 1541468 5856239 := bstep (se 1 (by rfl) ⟨4392179, by rfl⟩ : syracuseStep 5856239 = 8784359) B8784359
theorem B1542655 : Blo 1541468 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B8335079 : Blo 1541468 8335079 := bstep (se 1 (by rfl) ⟨6251309, by rfl⟩ : syracuseStep 8335079 = 12502619) B12502619
theorem B15036263 : Blo 1541468 15036263 := bstep (se 1 (by rfl) ⟨11277197, by rfl⟩ : syracuseStep 15036263 = 22554395) B22554395
theorem B13185287 : Blo 1541468 13185287 := bstep (se 1 (by rfl) ⟨9888965, by rfl⟩ : syracuseStep 13185287 = 19777931) B19777931
theorem B2314655 : Blo 1541468 2314655 := bstep (se 1 (by rfl) ⟨1735991, by rfl⟩ : syracuseStep 2314655 = 3471983) B3471983
theorem B3904159 : Blo 1541468 3904159 := bstep (se 1 (by rfl) ⟨2928119, by rfl⟩ : syracuseStep 3904159 = 5856239) B5856239
theorem B2601659 : Blo 1541468 2601659 := bstep (se 1 (by rfl) ⟨1951244, by rfl⟩ : syracuseStep 2601659 = 3902489) B3902489
theorem B13169567 : Blo 1541468 13169567 := bstep (se 1 (by rfl) ⟨9877175, by rfl⟩ : syracuseStep 13169567 = 19754351) B19754351
theorem B59324561 : Blo 1541468 59324561 := bstep (se 2 (by rfl) ⟨22246710, by rfl⟩ : syracuseStep 59324561 = 44493421) B44493421
theorem B18758207 : Blo 1541468 18758207 := bstep (se 1 (by rfl) ⟨14068655, by rfl⟩ : syracuseStep 18758207 = 28137311) B28137311
theorem B8453359 : Blo 1541468 8453359 := bstep (se 1 (by rfl) ⟨6340019, by rfl⟩ : syracuseStep 8453359 = 12680039) B12680039
theorem B31678127 : Blo 1541468 31678127 := bstep (se 1 (by rfl) ⟨23758595, by rfl⟩ : syracuseStep 31678127 = 47517191) B47517191
theorem B8790191 : Blo 1541468 8790191 := bstep (se 1 (by rfl) ⟨6592643, by rfl⟩ : syracuseStep 8790191 = 13185287) B13185287
theorem B5556719 : Blo 1541468 5556719 := bstep (se 1 (by rfl) ⟨4167539, by rfl⟩ : syracuseStep 5556719 = 8335079) B8335079
theorem B1543103 : Blo 1541468 1543103 := bstep (se 1 (by rfl) ⟨1157327, by rfl⟩ : syracuseStep 1543103 = 2314655) B2314655
theorem B5205545 : Blo 1541468 5205545 := bstep (se 2 (by rfl) ⟨1952079, by rfl⟩ : syracuseStep 5205545 = 3904159) B3904159
theorem B12505471 : Blo 1541468 12505471 := bstep (se 1 (by rfl) ⟨9379103, by rfl⟩ : syracuseStep 12505471 = 18758207) B18758207
theorem B10024175 : Blo 1541468 10024175 := bstep (se 1 (by rfl) ⟨7518131, by rfl⟩ : syracuseStep 10024175 = 15036263) B15036263
theorem B1734439 : Blo 1541468 1734439 := bstep (se 1 (by rfl) ⟨1300829, by rfl⟩ : syracuseStep 1734439 = 2601659) B2601659
theorem B8779711 : Blo 1541468 8779711 := bstep (se 1 (by rfl) ⟨6584783, by rfl⟩ : syracuseStep 8779711 = 13169567) B13169567
theorem B39549707 : Blo 1541468 39549707 := bstep (se 1 (by rfl) ⟨29662280, by rfl⟩ : syracuseStep 39549707 = 59324561) B59324561
theorem B11271145 : Blo 1541468 11271145 := bstep (se 2 (by rfl) ⟨4226679, by rfl⟩ : syracuseStep 11271145 = 8453359) B8453359
theorem B21118751 : Blo 1541468 21118751 := bstep (se 1 (by rfl) ⟨15839063, by rfl⟩ : syracuseStep 21118751 = 31678127) B31678127
theorem B26731133 : Blo 1541468 26731133 := bstep (se 3 (by rfl) ⟨5012087, by rfl⟩ : syracuseStep 26731133 = 10024175) B10024175
theorem B2312585 : Blo 1541468 2312585 := bstep (se 2 (by rfl) ⟨867219, by rfl⟩ : syracuseStep 2312585 = 1734439) B1734439
theorem B5860127 : Blo 1541468 5860127 := bstep (se 1 (by rfl) ⟨4395095, by rfl⟩ : syracuseStep 5860127 = 8790191) B8790191
theorem B15028193 : Blo 1541468 15028193 := bstep (se 2 (by rfl) ⟨5635572, by rfl⟩ : syracuseStep 15028193 = 11271145) B11271145
theorem B26366471 : Blo 1541468 26366471 := bstep (se 1 (by rfl) ⟨19774853, by rfl⟩ : syracuseStep 26366471 = 39549707) B39549707
theorem B66695845 : Blo 1541468 66695845 := bstep (se 4 (by rfl) ⟨6252735, by rfl⟩ : syracuseStep 66695845 = 12505471) B12505471
theorem B3470363 : Blo 1541468 3470363 := bstep (se 1 (by rfl) ⟨2602772, by rfl⟩ : syracuseStep 3470363 = 5205545) B5205545
theorem B14079167 : Blo 1541468 14079167 := bstep (se 1 (by rfl) ⟨10559375, by rfl⟩ : syracuseStep 14079167 = 21118751) B21118751
theorem B14817917 : Blo 1541468 14817917 := bstep (se 3 (by rfl) ⟨2778359, by rfl⟩ : syracuseStep 14817917 = 5556719) B5556719
theorem B11706281 : Blo 1541468 11706281 := bstep (se 2 (by rfl) ⟨4389855, by rfl⟩ : syracuseStep 11706281 = 8779711) B8779711
theorem B1541723 : Blo 1541468 1541723 := bstep (se 1 (by rfl) ⟨1156292, by rfl⟩ : syracuseStep 1541723 = 2312585) B2312585
theorem B17820755 : Blo 1541468 17820755 := bstep (se 1 (by rfl) ⟨13365566, by rfl⟩ : syracuseStep 17820755 = 26731133) B26731133
theorem B2313575 : Blo 1541468 2313575 := bstep (se 1 (by rfl) ⟨1735181, by rfl⟩ : syracuseStep 2313575 = 3470363) B3470363
theorem B88927793 : Blo 1541468 88927793 := bstep (se 2 (by rfl) ⟨33347922, by rfl⟩ : syracuseStep 88927793 = 66695845) B66695845
theorem B7804187 : Blo 1541468 7804187 := bstep (se 1 (by rfl) ⟨5853140, by rfl⟩ : syracuseStep 7804187 = 11706281) B11706281
theorem B17577647 : Blo 1541468 17577647 := bstep (se 1 (by rfl) ⟨13183235, by rfl⟩ : syracuseStep 17577647 = 26366471) B26366471
theorem B9386111 : Blo 1541468 9386111 := bstep (se 1 (by rfl) ⟨7039583, by rfl⟩ : syracuseStep 9386111 = 14079167) B14079167
theorem B9878611 : Blo 1541468 9878611 := bstep (se 1 (by rfl) ⟨7408958, by rfl⟩ : syracuseStep 9878611 = 14817917) B14817917
theorem B3906751 : Blo 1541468 3906751 := bstep (se 1 (by rfl) ⟨2930063, by rfl⟩ : syracuseStep 3906751 = 5860127) B5860127
theorem B40075181 : Blo 1541468 40075181 := bstep (se 3 (by rfl) ⟨7514096, by rfl⟩ : syracuseStep 40075181 = 15028193) B15028193
theorem B5202791 : Blo 1541468 5202791 := bstep (se 1 (by rfl) ⟨3902093, by rfl⟩ : syracuseStep 5202791 = 7804187) B7804187
theorem B11880503 : Blo 1541468 11880503 := bstep (se 1 (by rfl) ⟨8910377, by rfl⟩ : syracuseStep 11880503 = 17820755) B17820755
theorem B1542383 : Blo 1541468 1542383 := bstep (se 1 (by rfl) ⟨1156787, by rfl⟩ : syracuseStep 1542383 = 2313575) B2313575
theorem B26716787 : Blo 1541468 26716787 := bstep (se 1 (by rfl) ⟨20037590, by rfl⟩ : syracuseStep 26716787 = 40075181) B40075181
theorem B11718431 : Blo 1541468 11718431 := bstep (se 1 (by rfl) ⟨8788823, by rfl⟩ : syracuseStep 11718431 = 17577647) B17577647
theorem B6257407 : Blo 1541468 6257407 := bstep (se 1 (by rfl) ⟨4693055, by rfl⟩ : syracuseStep 6257407 = 9386111) B9386111
theorem B13171481 : Blo 1541468 13171481 := bstep (se 2 (by rfl) ⟨4939305, by rfl⟩ : syracuseStep 13171481 = 9878611) B9878611
theorem B5209001 : Blo 1541468 5209001 := bstep (se 2 (by rfl) ⟨1953375, by rfl⟩ : syracuseStep 5209001 = 3906751) B3906751
theorem B59285195 : Blo 1541468 59285195 := bstep (se 1 (by rfl) ⟨44463896, by rfl⟩ : syracuseStep 59285195 = 88927793) B88927793
theorem B17811191 : Blo 1541468 17811191 := bstep (se 1 (by rfl) ⟨13358393, by rfl⟩ : syracuseStep 17811191 = 26716787) B26716787
theorem B3468527 : Blo 1541468 3468527 := bstep (se 1 (by rfl) ⟨2601395, by rfl⟩ : syracuseStep 3468527 = 5202791) B5202791
theorem B8343209 : Blo 1541468 8343209 := bstep (se 2 (by rfl) ⟨3128703, by rfl⟩ : syracuseStep 8343209 = 6257407) B6257407
theorem B39523463 : Blo 1541468 39523463 := bstep (se 1 (by rfl) ⟨29642597, by rfl⟩ : syracuseStep 39523463 = 59285195) B59285195
theorem B7812287 : Blo 1541468 7812287 := bstep (se 1 (by rfl) ⟨5859215, by rfl⟩ : syracuseStep 7812287 = 11718431) B11718431
theorem B7920335 : Blo 1541468 7920335 := bstep (se 1 (by rfl) ⟨5940251, by rfl⟩ : syracuseStep 7920335 = 11880503) B11880503
theorem B8780987 : Blo 1541468 8780987 := bstep (se 1 (by rfl) ⟨6585740, by rfl⟩ : syracuseStep 8780987 = 13171481) B13171481
theorem B3472667 : Blo 1541468 3472667 := bstep (se 1 (by rfl) ⟨2604500, by rfl⟩ : syracuseStep 3472667 = 5209001) B5209001
theorem B2312351 : Blo 1541468 2312351 := bstep (se 1 (by rfl) ⟨1734263, by rfl⟩ : syracuseStep 2312351 = 3468527) B3468527
theorem B26348975 : Blo 1541468 26348975 := bstep (se 1 (by rfl) ⟨19761731, by rfl⟩ : syracuseStep 26348975 = 39523463) B39523463
theorem B11874127 : Blo 1541468 11874127 := bstep (se 1 (by rfl) ⟨8905595, by rfl⟩ : syracuseStep 11874127 = 17811191) B17811191
theorem B5280223 : Blo 1541468 5280223 := bstep (se 1 (by rfl) ⟨3960167, by rfl⟩ : syracuseStep 5280223 = 7920335) B7920335
theorem B5853991 : Blo 1541468 5853991 := bstep (se 1 (by rfl) ⟨4390493, by rfl⟩ : syracuseStep 5853991 = 8780987) B8780987
theorem B2315111 : Blo 1541468 2315111 := bstep (se 1 (by rfl) ⟨1736333, by rfl⟩ : syracuseStep 2315111 = 3472667) B3472667
theorem B5208191 : Blo 1541468 5208191 := bstep (se 1 (by rfl) ⟨3906143, by rfl⟩ : syracuseStep 5208191 = 7812287) B7812287
theorem B22248557 : Blo 1541468 22248557 := bstep (se 3 (by rfl) ⟨4171604, by rfl⟩ : syracuseStep 22248557 = 8343209) B8343209
theorem B1541567 : Blo 1541468 1541567 := bstep (se 1 (by rfl) ⟨1156175, by rfl⟩ : syracuseStep 1541567 = 2312351) B2312351
theorem B17565983 : Blo 1541468 17565983 := bstep (se 1 (by rfl) ⟨13174487, by rfl⟩ : syracuseStep 17565983 = 26348975) B26348975
theorem B1543407 : Blo 1541468 1543407 := bstep (se 1 (by rfl) ⟨1157555, by rfl⟩ : syracuseStep 1543407 = 2315111) B2315111
theorem B7040297 : Blo 1541468 7040297 := bstep (se 2 (by rfl) ⟨2640111, by rfl⟩ : syracuseStep 7040297 = 5280223) B5280223
theorem B14832371 : Blo 1541468 14832371 := bstep (se 1 (by rfl) ⟨11124278, by rfl⟩ : syracuseStep 14832371 = 22248557) B22248557
theorem B15832169 : Blo 1541468 15832169 := bstep (se 2 (by rfl) ⟨5937063, by rfl⟩ : syracuseStep 15832169 = 11874127) B11874127
theorem B7805321 : Blo 1541468 7805321 := bstep (se 2 (by rfl) ⟨2926995, by rfl⟩ : syracuseStep 7805321 = 5853991) B5853991
theorem B3472127 : Blo 1541468 3472127 := bstep (se 1 (by rfl) ⟨2604095, by rfl⟩ : syracuseStep 3472127 = 5208191) B5208191
theorem B9888247 : Blo 1541468 9888247 := bstep (se 1 (by rfl) ⟨7416185, by rfl⟩ : syracuseStep 9888247 = 14832371) B14832371
theorem B5203547 : Blo 1541468 5203547 := bstep (se 1 (by rfl) ⟨3902660, by rfl⟩ : syracuseStep 5203547 = 7805321) B7805321
theorem B10554779 : Blo 1541468 10554779 := bstep (se 1 (by rfl) ⟨7916084, by rfl⟩ : syracuseStep 10554779 = 15832169) B15832169
theorem B11710655 : Blo 1541468 11710655 := bstep (se 1 (by rfl) ⟨8782991, by rfl⟩ : syracuseStep 11710655 = 17565983) B17565983
theorem B2314751 : Blo 1541468 2314751 := bstep (se 1 (by rfl) ⟨1736063, by rfl⟩ : syracuseStep 2314751 = 3472127) B3472127
theorem B18774125 : Blo 1541468 18774125 := bstep (se 3 (by rfl) ⟨3520148, by rfl⟩ : syracuseStep 18774125 = 7040297) B7040297
theorem B7807103 : Blo 1541468 7807103 := bstep (se 1 (by rfl) ⟨5855327, by rfl⟩ : syracuseStep 7807103 = 11710655) B11710655
theorem B1543167 : Blo 1541468 1543167 := bstep (se 1 (by rfl) ⟨1157375, by rfl⟩ : syracuseStep 1543167 = 2314751) B2314751
theorem B13184329 : Blo 1541468 13184329 := bstep (se 2 (by rfl) ⟨4944123, by rfl⟩ : syracuseStep 13184329 = 9888247) B9888247
theorem B3469031 : Blo 1541468 3469031 := bstep (se 1 (by rfl) ⟨2601773, by rfl⟩ : syracuseStep 3469031 = 5203547) B5203547
theorem B12516083 : Blo 1541468 12516083 := bstep (se 1 (by rfl) ⟨9387062, by rfl⟩ : syracuseStep 12516083 = 18774125) B18774125
theorem B7036519 : Blo 1541468 7036519 := bstep (se 1 (by rfl) ⟨5277389, by rfl⟩ : syracuseStep 7036519 = 10554779) B10554779
theorem B9382025 : Blo 1541468 9382025 := bstep (se 2 (by rfl) ⟨3518259, by rfl⟩ : syracuseStep 9382025 = 7036519) B7036519
theorem B2312687 : Blo 1541468 2312687 := bstep (se 1 (by rfl) ⟨1734515, by rfl⟩ : syracuseStep 2312687 = 3469031) B3469031
theorem B5204735 : Blo 1541468 5204735 := bstep (se 1 (by rfl) ⟨3903551, by rfl⟩ : syracuseStep 5204735 = 7807103) B7807103
theorem B8344055 : Blo 1541468 8344055 := bstep (se 1 (by rfl) ⟨6258041, by rfl⟩ : syracuseStep 8344055 = 12516083) B12516083
theorem B17579105 : Blo 1541468 17579105 := bstep (se 2 (by rfl) ⟨6592164, by rfl⟩ : syracuseStep 17579105 = 13184329) B13184329
theorem B5562703 : Blo 1541468 5562703 := bstep (se 1 (by rfl) ⟨4172027, by rfl⟩ : syracuseStep 5562703 = 8344055) B8344055
theorem B25018733 : Blo 1541468 25018733 := bstep (se 3 (by rfl) ⟨4691012, by rfl⟩ : syracuseStep 25018733 = 9382025) B9382025
theorem B1541791 : Blo 1541468 1541791 := bstep (se 1 (by rfl) ⟨1156343, by rfl⟩ : syracuseStep 1541791 = 2312687) B2312687
theorem B3469823 : Blo 1541468 3469823 := bstep (se 1 (by rfl) ⟨2602367, by rfl⟩ : syracuseStep 3469823 = 5204735) B5204735
theorem B11719403 : Blo 1541468 11719403 := bstep (se 1 (by rfl) ⟨8789552, by rfl⟩ : syracuseStep 11719403 = 17579105) B17579105
theorem B16679155 : Blo 1541468 16679155 := bstep (se 1 (by rfl) ⟨12509366, by rfl⟩ : syracuseStep 16679155 = 25018733) B25018733
theorem B2313215 : Blo 1541468 2313215 := bstep (se 1 (by rfl) ⟨1734911, by rfl⟩ : syracuseStep 2313215 = 3469823) B3469823
theorem B7416937 : Blo 1541468 7416937 := bstep (se 2 (by rfl) ⟨2781351, by rfl⟩ : syracuseStep 7416937 = 5562703) B5562703
theorem B7812935 : Blo 1541468 7812935 := bstep (se 1 (by rfl) ⟨5859701, by rfl⟩ : syracuseStep 7812935 = 11719403) B11719403
theorem B9889249 : Blo 1541468 9889249 := bstep (se 2 (by rfl) ⟨3708468, by rfl⟩ : syracuseStep 9889249 = 7416937) B7416937
theorem B1542143 : Blo 1541468 1542143 := bstep (se 1 (by rfl) ⟨1156607, by rfl⟩ : syracuseStep 1542143 = 2313215) B2313215
theorem B22238873 : Blo 1541468 22238873 := bstep (se 2 (by rfl) ⟨8339577, by rfl⟩ : syracuseStep 22238873 = 16679155) B16679155
theorem B5208623 : Blo 1541468 5208623 := bstep (se 1 (by rfl) ⟨3906467, by rfl⟩ : syracuseStep 5208623 = 7812935) B7812935
theorem B13185665 : Blo 1541468 13185665 := bstep (se 2 (by rfl) ⟨4944624, by rfl⟩ : syracuseStep 13185665 = 9889249) B9889249
theorem B14825915 : Blo 1541468 14825915 := bstep (se 1 (by rfl) ⟨11119436, by rfl⟩ : syracuseStep 14825915 = 22238873) B22238873
theorem B3472415 : Blo 1541468 3472415 := bstep (se 1 (by rfl) ⟨2604311, by rfl⟩ : syracuseStep 3472415 = 5208623) B5208623
theorem B8790443 : Blo 1541468 8790443 := bstep (se 1 (by rfl) ⟨6592832, by rfl⟩ : syracuseStep 8790443 = 13185665) B13185665
theorem B9883943 : Blo 1541468 9883943 := bstep (se 1 (by rfl) ⟨7412957, by rfl⟩ : syracuseStep 9883943 = 14825915) B14825915
theorem B2314943 : Blo 1541468 2314943 := bstep (se 1 (by rfl) ⟨1736207, by rfl⟩ : syracuseStep 2314943 = 3472415) B3472415
theorem B6589295 : Blo 1541468 6589295 := bstep (se 1 (by rfl) ⟨4941971, by rfl⟩ : syracuseStep 6589295 = 9883943) B9883943
theorem B5860295 : Blo 1541468 5860295 := bstep (se 1 (by rfl) ⟨4395221, by rfl⟩ : syracuseStep 5860295 = 8790443) B8790443
theorem B1543295 : Blo 1541468 1543295 := bstep (se 1 (by rfl) ⟨1157471, by rfl⟩ : syracuseStep 1543295 = 2314943) B2314943
theorem B4392863 : Blo 1541468 4392863 := bstep (se 1 (by rfl) ⟨3294647, by rfl⟩ : syracuseStep 4392863 = 6589295) B6589295
theorem B3906863 : Blo 1541468 3906863 := bstep (se 1 (by rfl) ⟨2930147, by rfl⟩ : syracuseStep 3906863 = 5860295) B5860295
theorem B2928575 : Blo 1541468 2928575 := bstep (se 1 (by rfl) ⟨2196431, by rfl⟩ : syracuseStep 2928575 = 4392863) B4392863
theorem B2604575 : Blo 1541468 2604575 := bstep (se 1 (by rfl) ⟨1953431, by rfl⟩ : syracuseStep 2604575 = 3906863) B3906863
theorem B7809533 : Blo 1541468 7809533 := bstep (se 3 (by rfl) ⟨1464287, by rfl⟩ : syracuseStep 7809533 = 2928575) B2928575
theorem B1736383 : Blo 1541468 1736383 := bstep (se 1 (by rfl) ⟨1302287, by rfl⟩ : syracuseStep 1736383 = 2604575) B2604575
theorem B5206355 : Blo 1541468 5206355 := bstep (se 1 (by rfl) ⟨3904766, by rfl⟩ : syracuseStep 5206355 = 7809533) B7809533
theorem B2315177 : Blo 1541468 2315177 := bstep (se 2 (by rfl) ⟨868191, by rfl⟩ : syracuseStep 2315177 = 1736383) B1736383
theorem B1543451 : Blo 1541468 1543451 := bstep (se 1 (by rfl) ⟨1157588, by rfl⟩ : syracuseStep 1543451 = 2315177) B2315177
theorem B3470903 : Blo 1541468 3470903 := bstep (se 1 (by rfl) ⟨2603177, by rfl⟩ : syracuseStep 3470903 = 5206355) B5206355
theorem B2313935 : Blo 1541468 2313935 := bstep (se 1 (by rfl) ⟨1735451, by rfl⟩ : syracuseStep 2313935 = 3470903) B3470903
theorem B1542623 : Blo 1541468 1542623 := bstep (se 1 (by rfl) ⟨1156967, by rfl⟩ : syracuseStep 1542623 = 2313935) B2313935

theorem C0 (j : ℕ) (h1 : 385367 ≤ j) (h2 : j ≤ 385866) : Blo 1541468 (4 * j + 3) := by
  interval_cases j
  · exact B1541471
  · exact B1541475
  · exact B1541479
  · exact B1541483
  · exact B1541487
  · exact B1541491
  · exact B1541495
  · exact B1541499
  · exact B1541503
  · exact B1541507
  · exact B1541511
  · exact B1541515
  · exact B1541519
  · exact B1541523
  · exact B1541527
  · exact B1541531
  · exact B1541535
  · exact B1541539
  · exact B1541543
  · exact B1541547
  · exact B1541551
  · exact B1541555
  · exact B1541559
  · exact B1541563
  · exact B1541567
  · exact B1541571
  · exact B1541575
  · exact B1541579
  · exact B1541583
  · exact B1541587
  · exact B1541591
  · exact B1541595
  · exact B1541599
  · exact B1541603
  · exact B1541607
  · exact B1541611
  · exact B1541615
  · exact B1541619
  · exact B1541623
  · exact B1541627
  · exact B1541631
  · exact B1541635
  · exact B1541639
  · exact B1541643
  · exact B1541647
  · exact B1541651
  · exact B1541655
  · exact B1541659
  · exact B1541663
  · exact B1541667
  · exact B1541671
  · exact B1541675
  · exact B1541679
  · exact B1541683
  · exact B1541687
  · exact B1541691
  · exact B1541695
  · exact B1541699
  · exact B1541703
  · exact B1541707
  · exact B1541711
  · exact B1541715
  · exact B1541719
  · exact B1541723
  · exact B1541727
  · exact B1541731
  · exact B1541735
  · exact B1541739
  · exact B1541743
  · exact B1541747
  · exact B1541751
  · exact B1541755
  · exact B1541759
  · exact B1541763
  · exact B1541767
  · exact B1541771
  · exact B1541775
  · exact B1541779
  · exact B1541783
  · exact B1541787
  · exact B1541791
  · exact B1541795
  · exact B1541799
  · exact B1541803
  · exact B1541807
  · exact B1541811
  · exact B1541815
  · exact B1541819
  · exact B1541823
  · exact B1541827
  · exact B1541831
  · exact B1541835
  · exact B1541839
  · exact B1541843
  · exact B1541847
  · exact B1541851
  · exact B1541855
  · exact B1541859
  · exact B1541863
  · exact B1541867
  · exact B1541871
  · exact B1541875
  · exact B1541879
  · exact B1541883
  · exact B1541887
  · exact B1541891
  · exact B1541895
  · exact B1541899
  · exact B1541903
  · exact B1541907
  · exact B1541911
  · exact B1541915
  · exact B1541919
  · exact B1541923
  · exact B1541927
  · exact B1541931
  · exact B1541935
  · exact B1541939
  · exact B1541943
  · exact B1541947
  · exact B1541951
  · exact B1541955
  · exact B1541959
  · exact B1541963
  · exact B1541967
  · exact B1541971
  · exact B1541975
  · exact B1541979
  · exact B1541983
  · exact B1541987
  · exact B1541991
  · exact B1541995
  · exact B1541999
  · exact B1542003
  · exact B1542007
  · exact B1542011
  · exact B1542015
  · exact B1542019
  · exact B1542023
  · exact B1542027
  · exact B1542031
  · exact B1542035
  · exact B1542039
  · exact B1542043
  · exact B1542047
  · exact B1542051
  · exact B1542055
  · exact B1542059
  · exact B1542063
  · exact B1542067
  · exact B1542071
  · exact B1542075
  · exact B1542079
  · exact B1542083
  · exact B1542087
  · exact B1542091
  · exact B1542095
  · exact B1542099
  · exact B1542103
  · exact B1542107
  · exact B1542111
  · exact B1542115
  · exact B1542119
  · exact B1542123
  · exact B1542127
  · exact B1542131
  · exact B1542135
  · exact B1542139
  · exact B1542143
  · exact B1542147
  · exact B1542151
  · exact B1542155
  · exact B1542159
  · exact B1542163
  · exact B1542167
  · exact B1542171
  · exact B1542175
  · exact B1542179
  · exact B1542183
  · exact B1542187
  · exact B1542191
  · exact B1542195
  · exact B1542199
  · exact B1542203
  · exact B1542207
  · exact B1542211
  · exact B1542215
  · exact B1542219
  · exact B1542223
  · exact B1542227
  · exact B1542231
  · exact B1542235
  · exact B1542239
  · exact B1542243
  · exact B1542247
  · exact B1542251
  · exact B1542255
  · exact B1542259
  · exact B1542263
  · exact B1542267
  · exact B1542271
  · exact B1542275
  · exact B1542279
  · exact B1542283
  · exact B1542287
  · exact B1542291
  · exact B1542295
  · exact B1542299
  · exact B1542303
  · exact B1542307
  · exact B1542311
  · exact B1542315
  · exact B1542319
  · exact B1542323
  · exact B1542327
  · exact B1542331
  · exact B1542335
  · exact B1542339
  · exact B1542343
  · exact B1542347
  · exact B1542351
  · exact B1542355
  · exact B1542359
  · exact B1542363
  · exact B1542367
  · exact B1542371
  · exact B1542375
  · exact B1542379
  · exact B1542383
  · exact B1542387
  · exact B1542391
  · exact B1542395
  · exact B1542399
  · exact B1542403
  · exact B1542407
  · exact B1542411
  · exact B1542415
  · exact B1542419
  · exact B1542423
  · exact B1542427
  · exact B1542431
  · exact B1542435
  · exact B1542439
  · exact B1542443
  · exact B1542447
  · exact B1542451
  · exact B1542455
  · exact B1542459
  · exact B1542463
  · exact B1542467
  · exact B1542471
  · exact B1542475
  · exact B1542479
  · exact B1542483
  · exact B1542487
  · exact B1542491
  · exact B1542495
  · exact B1542499
  · exact B1542503
  · exact B1542507
  · exact B1542511
  · exact B1542515
  · exact B1542519
  · exact B1542523
  · exact B1542527
  · exact B1542531
  · exact B1542535
  · exact B1542539
  · exact B1542543
  · exact B1542547
  · exact B1542551
  · exact B1542555
  · exact B1542559
  · exact B1542563
  · exact B1542567
  · exact B1542571
  · exact B1542575
  · exact B1542579
  · exact B1542583
  · exact B1542587
  · exact B1542591
  · exact B1542595
  · exact B1542599
  · exact B1542603
  · exact B1542607
  · exact B1542611
  · exact B1542615
  · exact B1542619
  · exact B1542623
  · exact B1542627
  · exact B1542631
  · exact B1542635
  · exact B1542639
  · exact B1542643
  · exact B1542647
  · exact B1542651
  · exact B1542655
  · exact B1542659
  · exact B1542663
  · exact B1542667
  · exact B1542671
  · exact B1542675
  · exact B1542679
  · exact B1542683
  · exact B1542687
  · exact B1542691
  · exact B1542695
  · exact B1542699
  · exact B1542703
  · exact B1542707
  · exact B1542711
  · exact B1542715
  · exact B1542719
  · exact B1542723
  · exact B1542727
  · exact B1542731
  · exact B1542735
  · exact B1542739
  · exact B1542743
  · exact B1542747
  · exact B1542751
  · exact B1542755
  · exact B1542759
  · exact B1542763
  · exact B1542767
  · exact B1542771
  · exact B1542775
  · exact B1542779
  · exact B1542783
  · exact B1542787
  · exact B1542791
  · exact B1542795
  · exact B1542799
  · exact B1542803
  · exact B1542807
  · exact B1542811
  · exact B1542815
  · exact B1542819
  · exact B1542823
  · exact B1542827
  · exact B1542831
  · exact B1542835
  · exact B1542839
  · exact B1542843
  · exact B1542847
  · exact B1542851
  · exact B1542855
  · exact B1542859
  · exact B1542863
  · exact B1542867
  · exact B1542871
  · exact B1542875
  · exact B1542879
  · exact B1542883
  · exact B1542887
  · exact B1542891
  · exact B1542895
  · exact B1542899
  · exact B1542903
  · exact B1542907
  · exact B1542911
  · exact B1542915
  · exact B1542919
  · exact B1542923
  · exact B1542927
  · exact B1542931
  · exact B1542935
  · exact B1542939
  · exact B1542943
  · exact B1542947
  · exact B1542951
  · exact B1542955
  · exact B1542959
  · exact B1542963
  · exact B1542967
  · exact B1542971
  · exact B1542975
  · exact B1542979
  · exact B1542983
  · exact B1542987
  · exact B1542991
  · exact B1542995
  · exact B1542999
  · exact B1543003
  · exact B1543007
  · exact B1543011
  · exact B1543015
  · exact B1543019
  · exact B1543023
  · exact B1543027
  · exact B1543031
  · exact B1543035
  · exact B1543039
  · exact B1543043
  · exact B1543047
  · exact B1543051
  · exact B1543055
  · exact B1543059
  · exact B1543063
  · exact B1543067
  · exact B1543071
  · exact B1543075
  · exact B1543079
  · exact B1543083
  · exact B1543087
  · exact B1543091
  · exact B1543095
  · exact B1543099
  · exact B1543103
  · exact B1543107
  · exact B1543111
  · exact B1543115
  · exact B1543119
  · exact B1543123
  · exact B1543127
  · exact B1543131
  · exact B1543135
  · exact B1543139
  · exact B1543143
  · exact B1543147
  · exact B1543151
  · exact B1543155
  · exact B1543159
  · exact B1543163
  · exact B1543167
  · exact B1543171
  · exact B1543175
  · exact B1543179
  · exact B1543183
  · exact B1543187
  · exact B1543191
  · exact B1543195
  · exact B1543199
  · exact B1543203
  · exact B1543207
  · exact B1543211
  · exact B1543215
  · exact B1543219
  · exact B1543223
  · exact B1543227
  · exact B1543231
  · exact B1543235
  · exact B1543239
  · exact B1543243
  · exact B1543247
  · exact B1543251
  · exact B1543255
  · exact B1543259
  · exact B1543263
  · exact B1543267
  · exact B1543271
  · exact B1543275
  · exact B1543279
  · exact B1543283
  · exact B1543287
  · exact B1543291
  · exact B1543295
  · exact B1543299
  · exact B1543303
  · exact B1543307
  · exact B1543311
  · exact B1543315
  · exact B1543319
  · exact B1543323
  · exact B1543327
  · exact B1543331
  · exact B1543335
  · exact B1543339
  · exact B1543343
  · exact B1543347
  · exact B1543351
  · exact B1543355
  · exact B1543359
  · exact B1543363
  · exact B1543367
  · exact B1543371
  · exact B1543375
  · exact B1543379
  · exact B1543383
  · exact B1543387
  · exact B1543391
  · exact B1543395
  · exact B1543399
  · exact B1543403
  · exact B1543407
  · exact B1543411
  · exact B1543415
  · exact B1543419
  · exact B1543423
  · exact B1543427
  · exact B1543431
  · exact B1543435
  · exact B1543439
  · exact B1543443
  · exact B1543447
  · exact B1543451
  · exact B1543455
  · exact B1543459
  · exact B1543463
  · exact B1543467

theorem solution (m : ℕ) (hlo : 1541468 ≤ m) (hhi : m ≤ 1543468) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 385367 ≤ j := by omega
    have hj2 : j ≤ 385866 := by omega
    have hb : Blo 1541468 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
