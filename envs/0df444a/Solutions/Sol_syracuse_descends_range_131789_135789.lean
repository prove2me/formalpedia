-- Prove2me | solution 1 for syracuse_descends_range_131789_135789
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:34.786992+00:00
-- url     : https://prove2.me/submissions/ff7d51bd-9865-44dc-a358-85f5b4343bed

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


theorem B426005 : Blo 131789 426005 := bbase (se 6 (by rfl) ⟨9984, by rfl⟩ : syracuseStep 426005 = 19969) (by norm_num)
theorem B295093 : Blo 131789 295093 := bbase (se 5 (by rfl) ⟨13832, by rfl⟩ : syracuseStep 295093 = 27665) (by norm_num)
theorem B327917 : Blo 131789 327917 := bbase (se 3 (by rfl) ⟨61484, by rfl⟩ : syracuseStep 327917 = 122969) (by norm_num)
theorem B262909 : Blo 131789 262909 := bbase (se 3 (by rfl) ⟨49295, by rfl⟩ : syracuseStep 262909 = 98591) (by norm_num)
theorem B819989 : Blo 131789 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B17662805 : Blo 131789 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B328661 : Blo 131789 328661 := bbase (se 7 (by rfl) ⟨3851, by rfl⟩ : syracuseStep 328661 = 7703) (by norm_num)
theorem B197693 : Blo 131789 197693 := bbase (se 3 (by rfl) ⟨37067, by rfl⟩ : syracuseStep 197693 = 74135) (by norm_num)
theorem B197717 : Blo 131789 197717 := bbase (se 8 (by rfl) ⟨1158, by rfl⟩ : syracuseStep 197717 = 2317) (by norm_num)
theorem B197741 : Blo 131789 197741 := bbase (se 3 (by rfl) ⟨37076, by rfl⟩ : syracuseStep 197741 = 74153) (by norm_num)
theorem B197765 : Blo 131789 197765 := bbase (se 4 (by rfl) ⟨18540, by rfl⟩ : syracuseStep 197765 = 37081) (by norm_num)
theorem B197789 : Blo 131789 197789 := bbase (se 3 (by rfl) ⟨37085, by rfl⟩ : syracuseStep 197789 = 74171) (by norm_num)
theorem B197813 : Blo 131789 197813 := bbase (se 5 (by rfl) ⟨9272, by rfl⟩ : syracuseStep 197813 = 18545) (by norm_num)
theorem B197837 : Blo 131789 197837 := bbase (se 3 (by rfl) ⟨37094, by rfl⟩ : syracuseStep 197837 = 74189) (by norm_num)
theorem B197861 : Blo 131789 197861 := bbase (se 4 (by rfl) ⟨18549, by rfl⟩ : syracuseStep 197861 = 37099) (by norm_num)
theorem B197885 : Blo 131789 197885 := bbase (se 3 (by rfl) ⟨37103, by rfl⟩ : syracuseStep 197885 = 74207) (by norm_num)
theorem B197909 : Blo 131789 197909 := bbase (se 6 (by rfl) ⟨4638, by rfl⟩ : syracuseStep 197909 = 9277) (by norm_num)
theorem B427285 : Blo 131789 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B197933 : Blo 131789 197933 := bbase (se 3 (by rfl) ⟨37112, by rfl⟩ : syracuseStep 197933 = 74225) (by norm_num)
theorem B197957 : Blo 131789 197957 := bbase (se 4 (by rfl) ⟨18558, by rfl⟩ : syracuseStep 197957 = 37117) (by norm_num)
theorem B197981 : Blo 131789 197981 := bbase (se 3 (by rfl) ⟨37121, by rfl⟩ : syracuseStep 197981 = 74243) (by norm_num)
theorem B198005 : Blo 131789 198005 := bbase (se 5 (by rfl) ⟨9281, by rfl⟩ : syracuseStep 198005 = 18563) (by norm_num)
theorem B198029 : Blo 131789 198029 := bbase (se 3 (by rfl) ⟨37130, by rfl⟩ : syracuseStep 198029 = 74261) (by norm_num)
theorem B198053 : Blo 131789 198053 := bbase (se 4 (by rfl) ⟨18567, by rfl⟩ : syracuseStep 198053 = 37135) (by norm_num)
theorem B198077 : Blo 131789 198077 := bbase (se 3 (by rfl) ⟨37139, by rfl⟩ : syracuseStep 198077 = 74279) (by norm_num)
theorem B198101 : Blo 131789 198101 := bbase (se 7 (by rfl) ⟨2321, by rfl⟩ : syracuseStep 198101 = 4643) (by norm_num)
theorem B198125 : Blo 131789 198125 := bbase (se 3 (by rfl) ⟨37148, by rfl⟩ : syracuseStep 198125 = 74297) (by norm_num)
theorem B198149 : Blo 131789 198149 := bbase (se 4 (by rfl) ⟨18576, by rfl⟩ : syracuseStep 198149 = 37153) (by norm_num)
theorem B198173 : Blo 131789 198173 := bbase (se 3 (by rfl) ⟨37157, by rfl⟩ : syracuseStep 198173 = 74315) (by norm_num)
theorem B198197 : Blo 131789 198197 := bbase (se 5 (by rfl) ⟨9290, by rfl⟩ : syracuseStep 198197 = 18581) (by norm_num)
theorem B198221 : Blo 131789 198221 := bbase (se 3 (by rfl) ⟨37166, by rfl⟩ : syracuseStep 198221 = 74333) (by norm_num)
theorem B296549 : Blo 131789 296549 := bbase (se 4 (by rfl) ⟨27801, by rfl⟩ : syracuseStep 296549 = 55603) (by norm_num)
theorem B198245 : Blo 131789 198245 := bbase (se 4 (by rfl) ⟨18585, by rfl⟩ : syracuseStep 198245 = 37171) (by norm_num)
theorem B198269 : Blo 131789 198269 := bbase (se 3 (by rfl) ⟨37175, by rfl⟩ : syracuseStep 198269 = 74351) (by norm_num)
theorem B198293 : Blo 131789 198293 := bbase (se 6 (by rfl) ⟨4647, by rfl⟩ : syracuseStep 198293 = 9295) (by norm_num)
theorem B296621 : Blo 131789 296621 := bbase (se 3 (by rfl) ⟨55616, by rfl⟩ : syracuseStep 296621 = 111233) (by norm_num)
theorem B198317 : Blo 131789 198317 := bbase (se 3 (by rfl) ⟨37184, by rfl⟩ : syracuseStep 198317 = 74369) (by norm_num)
theorem B198341 : Blo 131789 198341 := bbase (se 4 (by rfl) ⟨18594, by rfl⟩ : syracuseStep 198341 = 37189) (by norm_num)
theorem B198365 : Blo 131789 198365 := bbase (se 3 (by rfl) ⟨37193, by rfl⟩ : syracuseStep 198365 = 74387) (by norm_num)
theorem B296693 : Blo 131789 296693 := bbase (se 5 (by rfl) ⟨13907, by rfl⟩ : syracuseStep 296693 = 27815) (by norm_num)
theorem B198389 : Blo 131789 198389 := bbase (se 5 (by rfl) ⟨9299, by rfl⟩ : syracuseStep 198389 = 18599) (by norm_num)
theorem B198413 : Blo 131789 198413 := bbase (se 3 (by rfl) ⟨37202, by rfl⟩ : syracuseStep 198413 = 74405) (by norm_num)
theorem B198437 : Blo 131789 198437 := bbase (se 4 (by rfl) ⟨18603, by rfl⟩ : syracuseStep 198437 = 37207) (by norm_num)
theorem B296765 : Blo 131789 296765 := bbase (se 3 (by rfl) ⟨55643, by rfl⟩ : syracuseStep 296765 = 111287) (by norm_num)
theorem B198461 : Blo 131789 198461 := bbase (se 3 (by rfl) ⟨37211, by rfl⟩ : syracuseStep 198461 = 74423) (by norm_num)
theorem B198485 : Blo 131789 198485 := bbase (se 9 (by rfl) ⟨581, by rfl⟩ : syracuseStep 198485 = 1163) (by norm_num)
theorem B198509 : Blo 131789 198509 := bbase (se 3 (by rfl) ⟨37220, by rfl⟩ : syracuseStep 198509 = 74441) (by norm_num)
theorem B296837 : Blo 131789 296837 := bbase (se 4 (by rfl) ⟨27828, by rfl⟩ : syracuseStep 296837 = 55657) (by norm_num)
theorem B198533 : Blo 131789 198533 := bbase (se 4 (by rfl) ⟨18612, by rfl⟩ : syracuseStep 198533 = 37225) (by norm_num)
theorem B198557 : Blo 131789 198557 := bbase (se 3 (by rfl) ⟨37229, by rfl⟩ : syracuseStep 198557 = 74459) (by norm_num)
theorem B198581 : Blo 131789 198581 := bbase (se 5 (by rfl) ⟨9308, by rfl⟩ : syracuseStep 198581 = 18617) (by norm_num)
theorem B296909 : Blo 131789 296909 := bbase (se 3 (by rfl) ⟨55670, by rfl⟩ : syracuseStep 296909 = 111341) (by norm_num)
theorem B198605 : Blo 131789 198605 := bbase (se 3 (by rfl) ⟨37238, by rfl⟩ : syracuseStep 198605 = 74477) (by norm_num)
theorem B198629 : Blo 131789 198629 := bbase (se 4 (by rfl) ⟨18621, by rfl⟩ : syracuseStep 198629 = 37243) (by norm_num)
theorem B264173 : Blo 131789 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B198653 : Blo 131789 198653 := bbase (se 3 (by rfl) ⟨37247, by rfl⟩ : syracuseStep 198653 = 74495) (by norm_num)
theorem B296981 : Blo 131789 296981 := bbase (se 6 (by rfl) ⟨6960, by rfl⟩ : syracuseStep 296981 = 13921) (by norm_num)
theorem B198677 : Blo 131789 198677 := bbase (se 6 (by rfl) ⟨4656, by rfl⟩ : syracuseStep 198677 = 9313) (by norm_num)
theorem B198701 : Blo 131789 198701 := bbase (se 3 (by rfl) ⟨37256, by rfl⟩ : syracuseStep 198701 = 74513) (by norm_num)
theorem B198725 : Blo 131789 198725 := bbase (se 4 (by rfl) ⟨18630, by rfl⟩ : syracuseStep 198725 = 37261) (by norm_num)
theorem B297053 : Blo 131789 297053 := bbase (se 3 (by rfl) ⟨55697, by rfl⟩ : syracuseStep 297053 = 111395) (by norm_num)
theorem B198749 : Blo 131789 198749 := bbase (se 3 (by rfl) ⟨37265, by rfl⟩ : syracuseStep 198749 = 74531) (by norm_num)
theorem B198773 : Blo 131789 198773 := bbase (se 5 (by rfl) ⟨9317, by rfl⟩ : syracuseStep 198773 = 18635) (by norm_num)
theorem B198797 : Blo 131789 198797 := bbase (se 3 (by rfl) ⟨37274, by rfl⟩ : syracuseStep 198797 = 74549) (by norm_num)
theorem B297125 : Blo 131789 297125 := bbase (se 4 (by rfl) ⟨27855, by rfl⟩ : syracuseStep 297125 = 55711) (by norm_num)
theorem B198821 : Blo 131789 198821 := bbase (se 4 (by rfl) ⟨18639, by rfl⟩ : syracuseStep 198821 = 37279) (by norm_num)
theorem B198845 : Blo 131789 198845 := bbase (se 3 (by rfl) ⟨37283, by rfl⟩ : syracuseStep 198845 = 74567) (by norm_num)
theorem B198869 : Blo 131789 198869 := bbase (se 7 (by rfl) ⟨2330, by rfl⟩ : syracuseStep 198869 = 4661) (by norm_num)
theorem B297197 : Blo 131789 297197 := bbase (se 3 (by rfl) ⟨55724, by rfl⟩ : syracuseStep 297197 = 111449) (by norm_num)
theorem B198893 : Blo 131789 198893 := bbase (se 3 (by rfl) ⟨37292, by rfl⟩ : syracuseStep 198893 = 74585) (by norm_num)
theorem B198917 : Blo 131789 198917 := bbase (se 4 (by rfl) ⟨18648, by rfl⟩ : syracuseStep 198917 = 37297) (by norm_num)
theorem B198941 : Blo 131789 198941 := bbase (se 3 (by rfl) ⟨37301, by rfl⟩ : syracuseStep 198941 = 74603) (by norm_num)
theorem B297269 : Blo 131789 297269 := bbase (se 5 (by rfl) ⟨13934, by rfl⟩ : syracuseStep 297269 = 27869) (by norm_num)
theorem B198965 : Blo 131789 198965 := bbase (se 5 (by rfl) ⟨9326, by rfl⟩ : syracuseStep 198965 = 18653) (by norm_num)
theorem B198989 : Blo 131789 198989 := bbase (se 3 (by rfl) ⟨37310, by rfl⟩ : syracuseStep 198989 = 74621) (by norm_num)
theorem B1935701 : Blo 131789 1935701 := bbase (se 10 (by rfl) ⟨2835, by rfl⟩ : syracuseStep 1935701 = 5671) (by norm_num)
theorem B199013 : Blo 131789 199013 := bbase (se 4 (by rfl) ⟨18657, by rfl⟩ : syracuseStep 199013 = 37315) (by norm_num)
theorem B297341 : Blo 131789 297341 := bbase (se 3 (by rfl) ⟨55751, by rfl⟩ : syracuseStep 297341 = 111503) (by norm_num)
theorem B199037 : Blo 131789 199037 := bbase (se 3 (by rfl) ⟨37319, by rfl⟩ : syracuseStep 199037 = 74639) (by norm_num)
theorem B199061 : Blo 131789 199061 := bbase (se 6 (by rfl) ⟨4665, by rfl⟩ : syracuseStep 199061 = 9331) (by norm_num)
theorem B199085 : Blo 131789 199085 := bbase (se 3 (by rfl) ⟨37328, by rfl⟩ : syracuseStep 199085 = 74657) (by norm_num)
theorem B297413 : Blo 131789 297413 := bbase (se 4 (by rfl) ⟨27882, by rfl⟩ : syracuseStep 297413 = 55765) (by norm_num)
theorem B199109 : Blo 131789 199109 := bbase (se 4 (by rfl) ⟨18666, by rfl⟩ : syracuseStep 199109 = 37333) (by norm_num)
theorem B199133 : Blo 131789 199133 := bbase (se 3 (by rfl) ⟨37337, by rfl⟩ : syracuseStep 199133 = 74675) (by norm_num)
theorem B199157 : Blo 131789 199157 := bbase (se 5 (by rfl) ⟨9335, by rfl⟩ : syracuseStep 199157 = 18671) (by norm_num)
theorem B297485 : Blo 131789 297485 := bbase (se 3 (by rfl) ⟨55778, by rfl⟩ : syracuseStep 297485 = 111557) (by norm_num)
theorem B199181 : Blo 131789 199181 := bbase (se 3 (by rfl) ⟨37346, by rfl⟩ : syracuseStep 199181 = 74693) (by norm_num)
theorem B854549 : Blo 131789 854549 := bbase (se 6 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 854549 = 40057) (by norm_num)
theorem B199205 : Blo 131789 199205 := bbase (se 4 (by rfl) ⟨18675, by rfl⟩ : syracuseStep 199205 = 37351) (by norm_num)
theorem B199229 : Blo 131789 199229 := bbase (se 3 (by rfl) ⟨37355, by rfl⟩ : syracuseStep 199229 = 74711) (by norm_num)
theorem B297557 : Blo 131789 297557 := bbase (se 8 (by rfl) ⟨1743, by rfl⟩ : syracuseStep 297557 = 3487) (by norm_num)
theorem B199253 : Blo 131789 199253 := bbase (se 8 (by rfl) ⟨1167, by rfl⟩ : syracuseStep 199253 = 2335) (by norm_num)
theorem B428645 : Blo 131789 428645 := bbase (se 4 (by rfl) ⟨40185, by rfl⟩ : syracuseStep 428645 = 80371) (by norm_num)
theorem B199277 : Blo 131789 199277 := bbase (se 3 (by rfl) ⟨37364, by rfl⟩ : syracuseStep 199277 = 74729) (by norm_num)
theorem B199301 : Blo 131789 199301 := bbase (se 4 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 199301 = 37369) (by norm_num)
theorem B133769 : Blo 131789 133769 := bbase (se 2 (by rfl) ⟨50163, by rfl⟩ : syracuseStep 133769 = 100327) (by norm_num)
theorem B297629 : Blo 131789 297629 := bbase (se 3 (by rfl) ⟨55805, by rfl⟩ : syracuseStep 297629 = 111611) (by norm_num)
theorem B199325 : Blo 131789 199325 := bbase (se 3 (by rfl) ⟨37373, by rfl⟩ : syracuseStep 199325 = 74747) (by norm_num)
theorem B199349 : Blo 131789 199349 := bbase (se 5 (by rfl) ⟨9344, by rfl⟩ : syracuseStep 199349 = 18689) (by norm_num)
theorem B199373 : Blo 131789 199373 := bbase (se 3 (by rfl) ⟨37382, by rfl⟩ : syracuseStep 199373 = 74765) (by norm_num)
theorem B232141 : Blo 131789 232141 := bbase (se 3 (by rfl) ⟨43526, by rfl⟩ : syracuseStep 232141 = 87053) (by norm_num)
theorem B297701 : Blo 131789 297701 := bbase (se 4 (by rfl) ⟨27909, by rfl⟩ : syracuseStep 297701 = 55819) (by norm_num)
theorem B199397 : Blo 131789 199397 := bbase (se 4 (by rfl) ⟨18693, by rfl⟩ : syracuseStep 199397 = 37387) (by norm_num)
theorem B428773 : Blo 131789 428773 := bbase (se 4 (by rfl) ⟨40197, by rfl⟩ : syracuseStep 428773 = 80395) (by norm_num)
theorem B199421 : Blo 131789 199421 := bbase (se 3 (by rfl) ⟨37391, by rfl⟩ : syracuseStep 199421 = 74783) (by norm_num)
theorem B199445 : Blo 131789 199445 := bbase (se 6 (by rfl) ⟨4674, by rfl⟩ : syracuseStep 199445 = 9349) (by norm_num)
theorem B297773 : Blo 131789 297773 := bbase (se 3 (by rfl) ⟨55832, by rfl⟩ : syracuseStep 297773 = 111665) (by norm_num)
theorem B199469 : Blo 131789 199469 := bbase (se 3 (by rfl) ⟨37400, by rfl⟩ : syracuseStep 199469 = 74801) (by norm_num)
theorem B199493 : Blo 131789 199493 := bbase (se 4 (by rfl) ⟨18702, by rfl⟩ : syracuseStep 199493 = 37405) (by norm_num)
theorem B199517 : Blo 131789 199517 := bbase (se 3 (by rfl) ⟨37409, by rfl⟩ : syracuseStep 199517 = 74819) (by norm_num)
theorem B297845 : Blo 131789 297845 := bbase (se 5 (by rfl) ⟨13961, by rfl⟩ : syracuseStep 297845 = 27923) (by norm_num)
theorem B199541 : Blo 131789 199541 := bbase (se 5 (by rfl) ⟨9353, by rfl⟩ : syracuseStep 199541 = 18707) (by norm_num)
theorem B199565 : Blo 131789 199565 := bbase (se 3 (by rfl) ⟨37418, by rfl⟩ : syracuseStep 199565 = 74837) (by norm_num)
theorem B199589 : Blo 131789 199589 := bbase (se 4 (by rfl) ⟨18711, by rfl⟩ : syracuseStep 199589 = 37423) (by norm_num)
theorem B297917 : Blo 131789 297917 := bbase (se 3 (by rfl) ⟨55859, by rfl⟩ : syracuseStep 297917 = 111719) (by norm_num)
theorem B199613 : Blo 131789 199613 := bbase (se 3 (by rfl) ⟨37427, by rfl⟩ : syracuseStep 199613 = 74855) (by norm_num)
theorem B199637 : Blo 131789 199637 := bbase (se 7 (by rfl) ⟨2339, by rfl⟩ : syracuseStep 199637 = 4679) (by norm_num)
theorem B429029 : Blo 131789 429029 := bbase (se 4 (by rfl) ⟨40221, by rfl⟩ : syracuseStep 429029 = 80443) (by norm_num)
theorem B199661 : Blo 131789 199661 := bbase (se 3 (by rfl) ⟨37436, by rfl⟩ : syracuseStep 199661 = 74873) (by norm_num)
theorem B297989 : Blo 131789 297989 := bbase (se 4 (by rfl) ⟨27936, by rfl⟩ : syracuseStep 297989 = 55873) (by norm_num)
theorem B199685 : Blo 131789 199685 := bbase (se 4 (by rfl) ⟨18720, by rfl⟩ : syracuseStep 199685 = 37441) (by norm_num)
theorem B199709 : Blo 131789 199709 := bbase (se 3 (by rfl) ⟨37445, by rfl⟩ : syracuseStep 199709 = 74891) (by norm_num)
theorem B461861 : Blo 131789 461861 := bbase (se 4 (by rfl) ⟨43299, by rfl⟩ : syracuseStep 461861 = 86599) (by norm_num)
theorem B166961 : Blo 131789 166961 := bbase (se 2 (by rfl) ⟨62610, by rfl⟩ : syracuseStep 166961 = 125221) (by norm_num)
theorem B199733 : Blo 131789 199733 := bbase (se 5 (by rfl) ⟨9362, by rfl⟩ : syracuseStep 199733 = 18725) (by norm_num)
theorem B298061 : Blo 131789 298061 := bbase (se 3 (by rfl) ⟨55886, by rfl⟩ : syracuseStep 298061 = 111773) (by norm_num)
theorem B199757 : Blo 131789 199757 := bbase (se 3 (by rfl) ⟨37454, by rfl⟩ : syracuseStep 199757 = 74909) (by norm_num)
theorem B199781 : Blo 131789 199781 := bbase (se 4 (by rfl) ⟨18729, by rfl⟩ : syracuseStep 199781 = 37459) (by norm_num)
theorem B167017 : Blo 131789 167017 := bbase (se 2 (by rfl) ⟨62631, by rfl⟩ : syracuseStep 167017 = 125263) (by norm_num)
theorem B199805 : Blo 131789 199805 := bbase (se 3 (by rfl) ⟨37463, by rfl⟩ : syracuseStep 199805 = 74927) (by norm_num)
theorem B298133 : Blo 131789 298133 := bbase (se 6 (by rfl) ⟨6987, by rfl⟩ : syracuseStep 298133 = 13975) (by norm_num)
theorem B199829 : Blo 131789 199829 := bbase (se 6 (by rfl) ⟨4683, by rfl⟩ : syracuseStep 199829 = 9367) (by norm_num)
theorem B199853 : Blo 131789 199853 := bbase (se 3 (by rfl) ⟨37472, by rfl⟩ : syracuseStep 199853 = 74945) (by norm_num)
theorem B199877 : Blo 131789 199877 := bbase (se 4 (by rfl) ⟨18738, by rfl⟩ : syracuseStep 199877 = 37477) (by norm_num)
theorem B167113 : Blo 131789 167113 := bbase (se 2 (by rfl) ⟨62667, by rfl⟩ : syracuseStep 167113 = 125335) (by norm_num)
theorem B298205 : Blo 131789 298205 := bbase (se 3 (by rfl) ⟨55913, by rfl⟩ : syracuseStep 298205 = 111827) (by norm_num)
theorem B199901 : Blo 131789 199901 := bbase (se 3 (by rfl) ⟨37481, by rfl⟩ : syracuseStep 199901 = 74963) (by norm_num)
theorem B199925 : Blo 131789 199925 := bbase (se 5 (by rfl) ⟨9371, by rfl⟩ : syracuseStep 199925 = 18743) (by norm_num)
theorem B199949 : Blo 131789 199949 := bbase (se 3 (by rfl) ⟨37490, by rfl⟩ : syracuseStep 199949 = 74981) (by norm_num)
theorem B298277 : Blo 131789 298277 := bbase (se 4 (by rfl) ⟨27963, by rfl⟩ : syracuseStep 298277 = 55927) (by norm_num)
theorem B199973 : Blo 131789 199973 := bbase (se 4 (by rfl) ⟨18747, by rfl⟩ : syracuseStep 199973 = 37495) (by norm_num)
theorem B199997 : Blo 131789 199997 := bbase (se 3 (by rfl) ⟨37499, by rfl⟩ : syracuseStep 199997 = 74999) (by norm_num)
theorem B200021 : Blo 131789 200021 := bbase (se 11 (by rfl) ⟨146, by rfl⟩ : syracuseStep 200021 = 293) (by norm_num)
theorem B298349 : Blo 131789 298349 := bbase (se 3 (by rfl) ⟨55940, by rfl⟩ : syracuseStep 298349 = 111881) (by norm_num)
theorem B200045 : Blo 131789 200045 := bbase (se 3 (by rfl) ⟨37508, by rfl⟩ : syracuseStep 200045 = 75017) (by norm_num)
theorem B167285 : Blo 131789 167285 := bbase (se 5 (by rfl) ⟨7841, by rfl⟩ : syracuseStep 167285 = 15683) (by norm_num)
theorem B200069 : Blo 131789 200069 := bbase (se 4 (by rfl) ⟨18756, by rfl⟩ : syracuseStep 200069 = 37513) (by norm_num)
theorem B200093 : Blo 131789 200093 := bbase (se 3 (by rfl) ⟨37517, by rfl⟩ : syracuseStep 200093 = 75035) (by norm_num)
theorem B167341 : Blo 131789 167341 := bbase (se 3 (by rfl) ⟨31376, by rfl⟩ : syracuseStep 167341 = 62753) (by norm_num)
theorem B298421 : Blo 131789 298421 := bbase (se 5 (by rfl) ⟨13988, by rfl⟩ : syracuseStep 298421 = 27977) (by norm_num)
theorem B200117 : Blo 131789 200117 := bbase (se 5 (by rfl) ⟨9380, by rfl⟩ : syracuseStep 200117 = 18761) (by norm_num)
theorem B200141 : Blo 131789 200141 := bbase (se 3 (by rfl) ⟨37526, by rfl⟩ : syracuseStep 200141 = 75053) (by norm_num)
theorem B200165 : Blo 131789 200165 := bbase (se 4 (by rfl) ⟨18765, by rfl⟩ : syracuseStep 200165 = 37531) (by norm_num)
theorem B298493 : Blo 131789 298493 := bbase (se 3 (by rfl) ⟨55967, by rfl⟩ : syracuseStep 298493 = 111935) (by norm_num)
theorem B200189 : Blo 131789 200189 := bbase (se 3 (by rfl) ⟨37535, by rfl⟩ : syracuseStep 200189 = 75071) (by norm_num)
theorem B167437 : Blo 131789 167437 := bbase (se 3 (by rfl) ⟨31394, by rfl⟩ : syracuseStep 167437 = 62789) (by norm_num)
theorem B134677 : Blo 131789 134677 := bbase (se 6 (by rfl) ⟨3156, by rfl⟩ : syracuseStep 134677 = 6313) (by norm_num)
theorem B200213 : Blo 131789 200213 := bbase (se 6 (by rfl) ⟨4692, by rfl⟩ : syracuseStep 200213 = 9385) (by norm_num)
theorem B200237 : Blo 131789 200237 := bbase (se 3 (by rfl) ⟨37544, by rfl⟩ : syracuseStep 200237 = 75089) (by norm_num)
theorem B298565 : Blo 131789 298565 := bbase (se 4 (by rfl) ⟨27990, by rfl⟩ : syracuseStep 298565 = 55981) (by norm_num)
theorem B200261 : Blo 131789 200261 := bbase (se 4 (by rfl) ⟨18774, by rfl⟩ : syracuseStep 200261 = 37549) (by norm_num)
theorem B200285 : Blo 131789 200285 := bbase (se 3 (by rfl) ⟨37553, by rfl⟩ : syracuseStep 200285 = 75107) (by norm_num)
theorem B200309 : Blo 131789 200309 := bbase (se 5 (by rfl) ⟨9389, by rfl⟩ : syracuseStep 200309 = 18779) (by norm_num)
theorem B298637 : Blo 131789 298637 := bbase (se 3 (by rfl) ⟨55994, by rfl⟩ : syracuseStep 298637 = 111989) (by norm_num)
theorem B200333 : Blo 131789 200333 := bbase (se 3 (by rfl) ⟨37562, by rfl⟩ : syracuseStep 200333 = 75125) (by norm_num)
theorem B200357 : Blo 131789 200357 := bbase (se 4 (by rfl) ⟨18783, by rfl⟩ : syracuseStep 200357 = 37567) (by norm_num)
theorem B167609 : Blo 131789 167609 := bbase (se 2 (by rfl) ⟨62853, by rfl⟩ : syracuseStep 167609 = 125707) (by norm_num)
theorem B200381 : Blo 131789 200381 := bbase (se 3 (by rfl) ⟨37571, by rfl⟩ : syracuseStep 200381 = 75143) (by norm_num)
theorem B298709 : Blo 131789 298709 := bbase (se 7 (by rfl) ⟨3500, by rfl⟩ : syracuseStep 298709 = 7001) (by norm_num)
theorem B200405 : Blo 131789 200405 := bbase (se 7 (by rfl) ⟨2348, by rfl⟩ : syracuseStep 200405 = 4697) (by norm_num)
theorem B200429 : Blo 131789 200429 := bbase (se 3 (by rfl) ⟨37580, by rfl⟩ : syracuseStep 200429 = 75161) (by norm_num)
theorem B167665 : Blo 131789 167665 := bbase (se 2 (by rfl) ⟨62874, by rfl⟩ : syracuseStep 167665 = 125749) (by norm_num)
theorem B200453 : Blo 131789 200453 := bbase (se 4 (by rfl) ⟨18792, by rfl⟩ : syracuseStep 200453 = 37585) (by norm_num)
theorem B298781 : Blo 131789 298781 := bbase (se 3 (by rfl) ⟨56021, by rfl⟩ : syracuseStep 298781 = 112043) (by norm_num)
theorem B200477 : Blo 131789 200477 := bbase (se 3 (by rfl) ⟨37589, by rfl⟩ : syracuseStep 200477 = 75179) (by norm_num)
theorem B200501 : Blo 131789 200501 := bbase (se 5 (by rfl) ⟨9398, by rfl⟩ : syracuseStep 200501 = 18797) (by norm_num)
theorem B200525 : Blo 131789 200525 := bbase (se 3 (by rfl) ⟨37598, by rfl⟩ : syracuseStep 200525 = 75197) (by norm_num)
theorem B167761 : Blo 131789 167761 := bbase (se 2 (by rfl) ⟨62910, by rfl⟩ : syracuseStep 167761 = 125821) (by norm_num)
theorem B560981 : Blo 131789 560981 := bbase (se 9 (by rfl) ⟨1643, by rfl⟩ : syracuseStep 560981 = 3287) (by norm_num)
theorem B1544021 : Blo 131789 1544021 := bbase (se 9 (by rfl) ⟨4523, by rfl⟩ : syracuseStep 1544021 = 9047) (by norm_num)
theorem B298853 : Blo 131789 298853 := bbase (se 4 (by rfl) ⟨28017, by rfl⟩ : syracuseStep 298853 = 56035) (by norm_num)
theorem B200549 : Blo 131789 200549 := bbase (se 4 (by rfl) ⟨18801, by rfl⟩ : syracuseStep 200549 = 37603) (by norm_num)
theorem B200573 : Blo 131789 200573 := bbase (se 3 (by rfl) ⟨37607, by rfl⟩ : syracuseStep 200573 = 75215) (by norm_num)
theorem B200597 : Blo 131789 200597 := bbase (se 6 (by rfl) ⟨4701, by rfl⟩ : syracuseStep 200597 = 9403) (by norm_num)
theorem B298925 : Blo 131789 298925 := bbase (se 3 (by rfl) ⟨56048, by rfl⟩ : syracuseStep 298925 = 112097) (by norm_num)
theorem B200621 : Blo 131789 200621 := bbase (se 3 (by rfl) ⟨37616, by rfl⟩ : syracuseStep 200621 = 75233) (by norm_num)
theorem B200645 : Blo 131789 200645 := bbase (se 4 (by rfl) ⟨18810, by rfl⟩ : syracuseStep 200645 = 37621) (by norm_num)
theorem B200669 : Blo 131789 200669 := bbase (se 3 (by rfl) ⟨37625, by rfl⟩ : syracuseStep 200669 = 75251) (by norm_num)
theorem B298997 : Blo 131789 298997 := bbase (se 5 (by rfl) ⟨14015, by rfl⟩ : syracuseStep 298997 = 28031) (by norm_num)
theorem B200693 : Blo 131789 200693 := bbase (se 5 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 200693 = 18815) (by norm_num)
theorem B167933 : Blo 131789 167933 := bbase (se 3 (by rfl) ⟨31487, by rfl⟩ : syracuseStep 167933 = 62975) (by norm_num)
theorem B200717 : Blo 131789 200717 := bbase (se 3 (by rfl) ⟨37634, by rfl⟩ : syracuseStep 200717 = 75269) (by norm_num)
theorem B200741 : Blo 131789 200741 := bbase (se 4 (by rfl) ⟨18819, by rfl⟩ : syracuseStep 200741 = 37639) (by norm_num)
theorem B167989 : Blo 131789 167989 := bbase (se 5 (by rfl) ⟨7874, by rfl⟩ : syracuseStep 167989 = 15749) (by norm_num)
theorem B299069 : Blo 131789 299069 := bbase (se 3 (by rfl) ⟨56075, by rfl⟩ : syracuseStep 299069 = 112151) (by norm_num)
theorem B200765 : Blo 131789 200765 := bbase (se 3 (by rfl) ⟨37643, by rfl⟩ : syracuseStep 200765 = 75287) (by norm_num)
theorem B200789 : Blo 131789 200789 := bbase (se 8 (by rfl) ⟨1176, by rfl⟩ : syracuseStep 200789 = 2353) (by norm_num)
theorem B200813 : Blo 131789 200813 := bbase (se 3 (by rfl) ⟨37652, by rfl⟩ : syracuseStep 200813 = 75305) (by norm_num)
theorem B299141 : Blo 131789 299141 := bbase (se 4 (by rfl) ⟨28044, by rfl⟩ : syracuseStep 299141 = 56089) (by norm_num)
theorem B200837 : Blo 131789 200837 := bbase (se 4 (by rfl) ⟨18828, by rfl⟩ : syracuseStep 200837 = 37657) (by norm_num)
theorem B168085 : Blo 131789 168085 := bbase (se 6 (by rfl) ⟨3939, by rfl⟩ : syracuseStep 168085 = 7879) (by norm_num)
theorem B200861 : Blo 131789 200861 := bbase (se 3 (by rfl) ⟨37661, by rfl⟩ : syracuseStep 200861 = 75323) (by norm_num)
theorem B200885 : Blo 131789 200885 := bbase (se 5 (by rfl) ⟨9416, by rfl⟩ : syracuseStep 200885 = 18833) (by norm_num)
theorem B299213 : Blo 131789 299213 := bbase (se 3 (by rfl) ⟨56102, by rfl⟩ : syracuseStep 299213 = 112205) (by norm_num)
theorem B200909 : Blo 131789 200909 := bbase (se 3 (by rfl) ⟨37670, by rfl⟩ : syracuseStep 200909 = 75341) (by norm_num)
theorem B200933 : Blo 131789 200933 := bbase (se 4 (by rfl) ⟨18837, by rfl⟩ : syracuseStep 200933 = 37675) (by norm_num)
theorem B200957 : Blo 131789 200957 := bbase (se 3 (by rfl) ⟨37679, by rfl⟩ : syracuseStep 200957 = 75359) (by norm_num)
theorem B299285 : Blo 131789 299285 := bbase (se 6 (by rfl) ⟨7014, by rfl⟩ : syracuseStep 299285 = 14029) (by norm_num)
theorem B200981 : Blo 131789 200981 := bbase (se 6 (by rfl) ⟨4710, by rfl⟩ : syracuseStep 200981 = 9421) (by norm_num)
theorem B200989 : Blo 131789 200989 := bbase (se 3 (by rfl) ⟨37685, by rfl⟩ : syracuseStep 200989 = 75371) (by norm_num)
theorem B201005 : Blo 131789 201005 := bbase (se 3 (by rfl) ⟨37688, by rfl⟩ : syracuseStep 201005 = 75377) (by norm_num)
theorem B758069 : Blo 131789 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B168257 : Blo 131789 168257 := bbase (se 2 (by rfl) ⟨63096, by rfl⟩ : syracuseStep 168257 = 126193) (by norm_num)
theorem B201029 : Blo 131789 201029 := bbase (se 4 (by rfl) ⟨18846, by rfl⟩ : syracuseStep 201029 = 37693) (by norm_num)
theorem B233813 : Blo 131789 233813 := bbase (se 10 (by rfl) ⟨342, by rfl⟩ : syracuseStep 233813 = 685) (by norm_num)
theorem B299357 : Blo 131789 299357 := bbase (se 3 (by rfl) ⟨56129, by rfl⟩ : syracuseStep 299357 = 112259) (by norm_num)
theorem B201053 : Blo 131789 201053 := bbase (se 3 (by rfl) ⟨37697, by rfl⟩ : syracuseStep 201053 = 75395) (by norm_num)
theorem B201077 : Blo 131789 201077 := bbase (se 5 (by rfl) ⟨9425, by rfl⟩ : syracuseStep 201077 = 18851) (by norm_num)
theorem B168313 : Blo 131789 168313 := bbase (se 2 (by rfl) ⟨63117, by rfl⟩ : syracuseStep 168313 = 126235) (by norm_num)
theorem B201101 : Blo 131789 201101 := bbase (se 3 (by rfl) ⟨37706, by rfl⟩ : syracuseStep 201101 = 75413) (by norm_num)
theorem B299429 : Blo 131789 299429 := bbase (se 4 (by rfl) ⟨28071, by rfl⟩ : syracuseStep 299429 = 56143) (by norm_num)
theorem B201125 : Blo 131789 201125 := bbase (se 4 (by rfl) ⟨18855, by rfl⟩ : syracuseStep 201125 = 37711) (by norm_num)
theorem B201149 : Blo 131789 201149 := bbase (se 3 (by rfl) ⟨37715, by rfl⟩ : syracuseStep 201149 = 75431) (by norm_num)
theorem B201173 : Blo 131789 201173 := bbase (se 7 (by rfl) ⟨2357, by rfl⟩ : syracuseStep 201173 = 4715) (by norm_num)
theorem B168409 : Blo 131789 168409 := bbase (se 2 (by rfl) ⟨63153, by rfl⟩ : syracuseStep 168409 = 126307) (by norm_num)
theorem B299501 : Blo 131789 299501 := bbase (se 3 (by rfl) ⟨56156, by rfl⟩ : syracuseStep 299501 = 112313) (by norm_num)
theorem B201197 : Blo 131789 201197 := bbase (se 3 (by rfl) ⟨37724, by rfl⟩ : syracuseStep 201197 = 75449) (by norm_num)
theorem B201221 : Blo 131789 201221 := bbase (se 4 (by rfl) ⟨18864, by rfl⟩ : syracuseStep 201221 = 37729) (by norm_num)
theorem B201245 : Blo 131789 201245 := bbase (se 3 (by rfl) ⟨37733, by rfl⟩ : syracuseStep 201245 = 75467) (by norm_num)
theorem B299573 : Blo 131789 299573 := bbase (se 5 (by rfl) ⟨14042, by rfl⟩ : syracuseStep 299573 = 28085) (by norm_num)
theorem B201269 : Blo 131789 201269 := bbase (se 5 (by rfl) ⟨9434, by rfl⟩ : syracuseStep 201269 = 18869) (by norm_num)
theorem B201293 : Blo 131789 201293 := bbase (se 3 (by rfl) ⟨37742, by rfl⟩ : syracuseStep 201293 = 75485) (by norm_num)
theorem B201317 : Blo 131789 201317 := bbase (se 4 (by rfl) ⟨18873, by rfl⟩ : syracuseStep 201317 = 37747) (by norm_num)
theorem B299645 : Blo 131789 299645 := bbase (se 3 (by rfl) ⟨56183, by rfl⟩ : syracuseStep 299645 = 112367) (by norm_num)
theorem B201341 : Blo 131789 201341 := bbase (se 3 (by rfl) ⟨37751, by rfl⟩ : syracuseStep 201341 = 75503) (by norm_num)
theorem B168581 : Blo 131789 168581 := bbase (se 4 (by rfl) ⟨15804, by rfl⟩ : syracuseStep 168581 = 31609) (by norm_num)
theorem B201365 : Blo 131789 201365 := bbase (se 6 (by rfl) ⟨4719, by rfl⟩ : syracuseStep 201365 = 9439) (by norm_num)
theorem B201389 : Blo 131789 201389 := bbase (se 3 (by rfl) ⟨37760, by rfl⟩ : syracuseStep 201389 = 75521) (by norm_num)
theorem B168637 : Blo 131789 168637 := bbase (se 3 (by rfl) ⟨31619, by rfl⟩ : syracuseStep 168637 = 63239) (by norm_num)
theorem B299717 : Blo 131789 299717 := bbase (se 4 (by rfl) ⟨28098, by rfl⟩ : syracuseStep 299717 = 56197) (by norm_num)
theorem B201413 : Blo 131789 201413 := bbase (se 4 (by rfl) ⟨18882, by rfl⟩ : syracuseStep 201413 = 37765) (by norm_num)
theorem B824021 : Blo 131789 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B201437 : Blo 131789 201437 := bbase (se 3 (by rfl) ⟨37769, by rfl⟩ : syracuseStep 201437 = 75539) (by norm_num)
theorem B201461 : Blo 131789 201461 := bbase (se 5 (by rfl) ⟨9443, by rfl⟩ : syracuseStep 201461 = 18887) (by norm_num)
theorem B135941 : Blo 131789 135941 := bbase (se 4 (by rfl) ⟨12744, by rfl⟩ : syracuseStep 135941 = 25489) (by norm_num)
theorem B299789 : Blo 131789 299789 := bbase (se 3 (by rfl) ⟨56210, by rfl⟩ : syracuseStep 299789 = 112421) (by norm_num)
theorem B201485 : Blo 131789 201485 := bbase (se 3 (by rfl) ⟨37778, by rfl⟩ : syracuseStep 201485 = 75557) (by norm_num)
theorem B168733 : Blo 131789 168733 := bbase (se 3 (by rfl) ⟨31637, by rfl⟩ : syracuseStep 168733 = 63275) (by norm_num)
theorem B201509 : Blo 131789 201509 := bbase (se 4 (by rfl) ⟨18891, by rfl⟩ : syracuseStep 201509 = 37783) (by norm_num)
theorem B201533 : Blo 131789 201533 := bbase (se 3 (by rfl) ⟨37787, by rfl⟩ : syracuseStep 201533 = 75575) (by norm_num)
theorem B299861 : Blo 131789 299861 := bbase (se 9 (by rfl) ⟨878, by rfl⟩ : syracuseStep 299861 = 1757) (by norm_num)
theorem B201557 : Blo 131789 201557 := bbase (se 9 (by rfl) ⟨590, by rfl⟩ : syracuseStep 201557 = 1181) (by norm_num)
theorem B201581 : Blo 131789 201581 := bbase (se 3 (by rfl) ⟨37796, by rfl⟩ : syracuseStep 201581 = 75593) (by norm_num)
theorem B201605 : Blo 131789 201605 := bbase (se 4 (by rfl) ⟨18900, by rfl⟩ : syracuseStep 201605 = 37801) (by norm_num)
theorem B299933 : Blo 131789 299933 := bbase (se 3 (by rfl) ⟨56237, by rfl⟩ : syracuseStep 299933 = 112475) (by norm_num)
theorem B201629 : Blo 131789 201629 := bbase (se 3 (by rfl) ⟨37805, by rfl⟩ : syracuseStep 201629 = 75611) (by norm_num)
theorem B201653 : Blo 131789 201653 := bbase (se 5 (by rfl) ⟨9452, by rfl⟩ : syracuseStep 201653 = 18905) (by norm_num)
theorem B168905 : Blo 131789 168905 := bbase (se 2 (by rfl) ⟨63339, by rfl⟩ : syracuseStep 168905 = 126679) (by norm_num)
theorem B201677 : Blo 131789 201677 := bbase (se 3 (by rfl) ⟨37814, by rfl⟩ : syracuseStep 201677 = 75629) (by norm_num)
theorem B300005 : Blo 131789 300005 := bbase (se 4 (by rfl) ⟨28125, by rfl⟩ : syracuseStep 300005 = 56251) (by norm_num)
theorem B201701 : Blo 131789 201701 := bbase (se 4 (by rfl) ⟨18909, by rfl⟩ : syracuseStep 201701 = 37819) (by norm_num)
theorem B201725 : Blo 131789 201725 := bbase (se 3 (by rfl) ⟨37823, by rfl⟩ : syracuseStep 201725 = 75647) (by norm_num)
theorem B168961 : Blo 131789 168961 := bbase (se 2 (by rfl) ⟨63360, by rfl⟩ : syracuseStep 168961 = 126721) (by norm_num)
theorem B201749 : Blo 131789 201749 := bbase (se 6 (by rfl) ⟨4728, by rfl⟩ : syracuseStep 201749 = 9457) (by norm_num)
theorem B300077 : Blo 131789 300077 := bbase (se 3 (by rfl) ⟨56264, by rfl⟩ : syracuseStep 300077 = 112529) (by norm_num)
theorem B201773 : Blo 131789 201773 := bbase (se 3 (by rfl) ⟨37832, by rfl⟩ : syracuseStep 201773 = 75665) (by norm_num)
theorem B201797 : Blo 131789 201797 := bbase (se 4 (by rfl) ⟨18918, by rfl⟩ : syracuseStep 201797 = 37837) (by norm_num)
theorem B201821 : Blo 131789 201821 := bbase (se 3 (by rfl) ⟨37841, by rfl⟩ : syracuseStep 201821 = 75683) (by norm_num)
theorem B169057 : Blo 131789 169057 := bbase (se 2 (by rfl) ⟨63396, by rfl⟩ : syracuseStep 169057 = 126793) (by norm_num)
theorem B300149 : Blo 131789 300149 := bbase (se 5 (by rfl) ⟨14069, by rfl⟩ : syracuseStep 300149 = 28139) (by norm_num)
theorem B201845 : Blo 131789 201845 := bbase (se 5 (by rfl) ⟨9461, by rfl⟩ : syracuseStep 201845 = 18923) (by norm_num)
theorem B201869 : Blo 131789 201869 := bbase (se 3 (by rfl) ⟨37850, by rfl⟩ : syracuseStep 201869 = 75701) (by norm_num)
theorem B201893 : Blo 131789 201893 := bbase (se 4 (by rfl) ⟨18927, by rfl⟩ : syracuseStep 201893 = 37855) (by norm_num)
theorem B300221 : Blo 131789 300221 := bbase (se 3 (by rfl) ⟨56291, by rfl⟩ : syracuseStep 300221 = 112583) (by norm_num)
theorem B201917 : Blo 131789 201917 := bbase (se 3 (by rfl) ⟨37859, by rfl⟩ : syracuseStep 201917 = 75719) (by norm_num)
theorem B201941 : Blo 131789 201941 := bbase (se 7 (by rfl) ⟨2366, by rfl⟩ : syracuseStep 201941 = 4733) (by norm_num)
theorem B201965 : Blo 131789 201965 := bbase (se 3 (by rfl) ⟨37868, by rfl⟩ : syracuseStep 201965 = 75737) (by norm_num)
theorem B300293 : Blo 131789 300293 := bbase (se 4 (by rfl) ⟨28152, by rfl⟩ : syracuseStep 300293 = 56305) (by norm_num)
theorem B201989 : Blo 131789 201989 := bbase (se 4 (by rfl) ⟨18936, by rfl⟩ : syracuseStep 201989 = 37873) (by norm_num)
theorem B169229 : Blo 131789 169229 := bbase (se 3 (by rfl) ⟨31730, by rfl⟩ : syracuseStep 169229 = 63461) (by norm_num)
theorem B202013 : Blo 131789 202013 := bbase (se 3 (by rfl) ⟨37877, by rfl⟩ : syracuseStep 202013 = 75755) (by norm_num)
theorem B202037 : Blo 131789 202037 := bbase (se 5 (by rfl) ⟨9470, by rfl⟩ : syracuseStep 202037 = 18941) (by norm_num)
theorem B333125 : Blo 131789 333125 := bbase (se 4 (by rfl) ⟨31230, by rfl⟩ : syracuseStep 333125 = 62461) (by norm_num)
theorem B169285 : Blo 131789 169285 := bbase (se 4 (by rfl) ⟨15870, by rfl⟩ : syracuseStep 169285 = 31741) (by norm_num)
theorem B300365 : Blo 131789 300365 := bbase (se 3 (by rfl) ⟨56318, by rfl⟩ : syracuseStep 300365 = 112637) (by norm_num)
theorem B202061 : Blo 131789 202061 := bbase (se 3 (by rfl) ⟨37886, by rfl⟩ : syracuseStep 202061 = 75773) (by norm_num)
theorem B202085 : Blo 131789 202085 := bbase (se 4 (by rfl) ⟨18945, by rfl⟩ : syracuseStep 202085 = 37891) (by norm_num)
theorem B431477 : Blo 131789 431477 := bbase (se 5 (by rfl) ⟨20225, by rfl⟩ : syracuseStep 431477 = 40451) (by norm_num)
theorem B202109 : Blo 131789 202109 := bbase (se 3 (by rfl) ⟨37895, by rfl⟩ : syracuseStep 202109 = 75791) (by norm_num)
theorem B300437 : Blo 131789 300437 := bbase (se 6 (by rfl) ⟨7041, by rfl⟩ : syracuseStep 300437 = 14083) (by norm_num)
theorem B202133 : Blo 131789 202133 := bbase (se 6 (by rfl) ⟨4737, by rfl⟩ : syracuseStep 202133 = 9475) (by norm_num)
theorem B169381 : Blo 131789 169381 := bbase (se 4 (by rfl) ⟨15879, by rfl⟩ : syracuseStep 169381 = 31759) (by norm_num)
theorem B202157 : Blo 131789 202157 := bbase (se 3 (by rfl) ⟨37904, by rfl⟩ : syracuseStep 202157 = 75809) (by norm_num)
theorem B202181 : Blo 131789 202181 := bbase (se 4 (by rfl) ⟨18954, by rfl⟩ : syracuseStep 202181 = 37909) (by norm_num)
theorem B267733 : Blo 131789 267733 := bbase (se 7 (by rfl) ⟨3137, by rfl⟩ : syracuseStep 267733 = 6275) (by norm_num)
theorem B759253 : Blo 131789 759253 := bbase (se 7 (by rfl) ⟨8897, by rfl⟩ : syracuseStep 759253 = 17795) (by norm_num)
theorem B300509 : Blo 131789 300509 := bbase (se 3 (by rfl) ⟨56345, by rfl⟩ : syracuseStep 300509 = 112691) (by norm_num)
theorem B202205 : Blo 131789 202205 := bbase (se 3 (by rfl) ⟨37913, by rfl⟩ : syracuseStep 202205 = 75827) (by norm_num)
theorem B202229 : Blo 131789 202229 := bbase (se 5 (by rfl) ⟨9479, by rfl⟩ : syracuseStep 202229 = 18959) (by norm_num)
theorem B202253 : Blo 131789 202253 := bbase (se 3 (by rfl) ⟨37922, by rfl⟩ : syracuseStep 202253 = 75845) (by norm_num)
theorem B267797 : Blo 131789 267797 := bbase (se 6 (by rfl) ⟨6276, by rfl⟩ : syracuseStep 267797 = 12553) (by norm_num)
theorem B300581 : Blo 131789 300581 := bbase (se 4 (by rfl) ⟨28179, by rfl⟩ : syracuseStep 300581 = 56359) (by norm_num)
theorem B202277 : Blo 131789 202277 := bbase (se 4 (by rfl) ⟨18963, by rfl⟩ : syracuseStep 202277 = 37927) (by norm_num)
theorem B202301 : Blo 131789 202301 := bbase (se 3 (by rfl) ⟨37931, by rfl⟩ : syracuseStep 202301 = 75863) (by norm_num)
theorem B169553 : Blo 131789 169553 := bbase (se 2 (by rfl) ⟨63582, by rfl⟩ : syracuseStep 169553 = 127165) (by norm_num)
theorem B202325 : Blo 131789 202325 := bbase (se 8 (by rfl) ⟨1185, by rfl⟩ : syracuseStep 202325 = 2371) (by norm_num)
theorem B300653 : Blo 131789 300653 := bbase (se 3 (by rfl) ⟨56372, by rfl⟩ : syracuseStep 300653 = 112745) (by norm_num)
theorem B202349 : Blo 131789 202349 := bbase (se 3 (by rfl) ⟨37940, by rfl⟩ : syracuseStep 202349 = 75881) (by norm_num)
theorem B1283701 : Blo 131789 1283701 := bbase (se 5 (by rfl) ⟨60173, by rfl⟩ : syracuseStep 1283701 = 120347) (by norm_num)
theorem B202373 : Blo 131789 202373 := bbase (se 4 (by rfl) ⟨18972, by rfl⟩ : syracuseStep 202373 = 37945) (by norm_num)
theorem B169609 : Blo 131789 169609 := bbase (se 2 (by rfl) ⟨63603, by rfl⟩ : syracuseStep 169609 = 127207) (by norm_num)
theorem B857749 : Blo 131789 857749 := bbase (se 6 (by rfl) ⟨20103, by rfl⟩ : syracuseStep 857749 = 40207) (by norm_num)
theorem B202397 : Blo 131789 202397 := bbase (se 3 (by rfl) ⟨37949, by rfl⟩ : syracuseStep 202397 = 75899) (by norm_num)
theorem B300725 : Blo 131789 300725 := bbase (se 5 (by rfl) ⟨14096, by rfl⟩ : syracuseStep 300725 = 28193) (by norm_num)
theorem B202421 : Blo 131789 202421 := bbase (se 5 (by rfl) ⟨9488, by rfl⟩ : syracuseStep 202421 = 18977) (by norm_num)
theorem B202445 : Blo 131789 202445 := bbase (se 3 (by rfl) ⟨37958, by rfl⟩ : syracuseStep 202445 = 75917) (by norm_num)
theorem B202469 : Blo 131789 202469 := bbase (se 4 (by rfl) ⟨18981, by rfl⟩ : syracuseStep 202469 = 37963) (by norm_num)
theorem B169705 : Blo 131789 169705 := bbase (se 2 (by rfl) ⟨63639, by rfl⟩ : syracuseStep 169705 = 127279) (by norm_num)
theorem B300797 : Blo 131789 300797 := bbase (se 3 (by rfl) ⟨56399, by rfl⟩ : syracuseStep 300797 = 112799) (by norm_num)
theorem B202493 : Blo 131789 202493 := bbase (se 3 (by rfl) ⟨37967, by rfl⟩ : syracuseStep 202493 = 75935) (by norm_num)
theorem B562949 : Blo 131789 562949 := bbase (se 4 (by rfl) ⟨52776, by rfl⟩ : syracuseStep 562949 = 105553) (by norm_num)
theorem B202517 : Blo 131789 202517 := bbase (se 6 (by rfl) ⟨4746, by rfl⟩ : syracuseStep 202517 = 9493) (by norm_num)
theorem B202541 : Blo 131789 202541 := bbase (se 3 (by rfl) ⟨37976, by rfl⟩ : syracuseStep 202541 = 75953) (by norm_num)
theorem B333629 : Blo 131789 333629 := bbase (se 3 (by rfl) ⟨62555, by rfl⟩ : syracuseStep 333629 = 125111) (by norm_num)
theorem B300869 : Blo 131789 300869 := bbase (se 4 (by rfl) ⟨28206, by rfl⟩ : syracuseStep 300869 = 56413) (by norm_num)
theorem B202565 : Blo 131789 202565 := bbase (se 4 (by rfl) ⟨18990, by rfl⟩ : syracuseStep 202565 = 37981) (by norm_num)
theorem B202589 : Blo 131789 202589 := bbase (se 3 (by rfl) ⟨37985, by rfl⟩ : syracuseStep 202589 = 75971) (by norm_num)
theorem B202613 : Blo 131789 202613 := bbase (se 5 (by rfl) ⟨9497, by rfl⟩ : syracuseStep 202613 = 18995) (by norm_num)
theorem B300941 : Blo 131789 300941 := bbase (se 3 (by rfl) ⟨56426, by rfl⟩ : syracuseStep 300941 = 112853) (by norm_num)
theorem B202637 : Blo 131789 202637 := bbase (se 3 (by rfl) ⟨37994, by rfl⟩ : syracuseStep 202637 = 75989) (by norm_num)
theorem B169877 : Blo 131789 169877 := bbase (se 6 (by rfl) ⟨3981, by rfl⟩ : syracuseStep 169877 = 7963) (by norm_num)
theorem B202661 : Blo 131789 202661 := bbase (se 4 (by rfl) ⟨18999, by rfl⟩ : syracuseStep 202661 = 37999) (by norm_num)
theorem B202685 : Blo 131789 202685 := bbase (se 3 (by rfl) ⟨38003, by rfl⟩ : syracuseStep 202685 = 76007) (by norm_num)
theorem B169933 : Blo 131789 169933 := bbase (se 3 (by rfl) ⟨31862, by rfl⟩ : syracuseStep 169933 = 63725) (by norm_num)
theorem B301013 : Blo 131789 301013 := bbase (se 7 (by rfl) ⟨3527, by rfl⟩ : syracuseStep 301013 = 7055) (by norm_num)
theorem B202709 : Blo 131789 202709 := bbase (se 7 (by rfl) ⟨2375, by rfl⟩ : syracuseStep 202709 = 4751) (by norm_num)
theorem B202733 : Blo 131789 202733 := bbase (se 3 (by rfl) ⟨38012, by rfl⟩ : syracuseStep 202733 = 76025) (by norm_num)
theorem B333821 : Blo 131789 333821 := bbase (se 3 (by rfl) ⟨62591, by rfl⟩ : syracuseStep 333821 = 125183) (by norm_num)
theorem B202757 : Blo 131789 202757 := bbase (se 4 (by rfl) ⟨19008, by rfl⟩ : syracuseStep 202757 = 38017) (by norm_num)
theorem B301085 : Blo 131789 301085 := bbase (se 3 (by rfl) ⟨56453, by rfl⟩ : syracuseStep 301085 = 112907) (by norm_num)
theorem B202781 : Blo 131789 202781 := bbase (se 3 (by rfl) ⟨38021, by rfl⟩ : syracuseStep 202781 = 76043) (by norm_num)
theorem B170029 : Blo 131789 170029 := bbase (se 3 (by rfl) ⟨31880, by rfl⟩ : syracuseStep 170029 = 63761) (by norm_num)
theorem B202805 : Blo 131789 202805 := bbase (se 5 (by rfl) ⟨9506, by rfl⟩ : syracuseStep 202805 = 19013) (by norm_num)
theorem B202829 : Blo 131789 202829 := bbase (se 3 (by rfl) ⟨38030, by rfl⟩ : syracuseStep 202829 = 76061) (by norm_num)
theorem B301157 : Blo 131789 301157 := bbase (se 4 (by rfl) ⟨28233, by rfl⟩ : syracuseStep 301157 = 56467) (by norm_num)
theorem B202853 : Blo 131789 202853 := bbase (se 4 (by rfl) ⟨19017, by rfl⟩ : syracuseStep 202853 = 38035) (by norm_num)
theorem B202877 : Blo 131789 202877 := bbase (se 3 (by rfl) ⟨38039, by rfl⟩ : syracuseStep 202877 = 76079) (by norm_num)
theorem B202901 : Blo 131789 202901 := bbase (se 6 (by rfl) ⟨4755, by rfl⟩ : syracuseStep 202901 = 9511) (by norm_num)
theorem B301229 : Blo 131789 301229 := bbase (se 3 (by rfl) ⟨56480, by rfl⟩ : syracuseStep 301229 = 112961) (by norm_num)
theorem B202925 : Blo 131789 202925 := bbase (se 3 (by rfl) ⟨38048, by rfl⟩ : syracuseStep 202925 = 76097) (by norm_num)
theorem B202949 : Blo 131789 202949 := bbase (se 4 (by rfl) ⟨19026, by rfl⟩ : syracuseStep 202949 = 38053) (by norm_num)
theorem B170201 : Blo 131789 170201 := bbase (se 2 (by rfl) ⟨63825, by rfl⟩ : syracuseStep 170201 = 127651) (by norm_num)
theorem B202973 : Blo 131789 202973 := bbase (se 3 (by rfl) ⟨38057, by rfl⟩ : syracuseStep 202973 = 76115) (by norm_num)
theorem B301301 : Blo 131789 301301 := bbase (se 5 (by rfl) ⟨14123, by rfl⟩ : syracuseStep 301301 = 28247) (by norm_num)
theorem B202997 : Blo 131789 202997 := bbase (se 5 (by rfl) ⟨9515, by rfl⟩ : syracuseStep 202997 = 19031) (by norm_num)
theorem B203021 : Blo 131789 203021 := bbase (se 3 (by rfl) ⟨38066, by rfl⟩ : syracuseStep 203021 = 76133) (by norm_num)
theorem B170257 : Blo 131789 170257 := bbase (se 2 (by rfl) ⟨63846, by rfl⟩ : syracuseStep 170257 = 127693) (by norm_num)
theorem B203045 : Blo 131789 203045 := bbase (se 4 (by rfl) ⟨19035, by rfl⟩ : syracuseStep 203045 = 38071) (by norm_num)
theorem B301373 : Blo 131789 301373 := bbase (se 3 (by rfl) ⟨56507, by rfl⟩ : syracuseStep 301373 = 113015) (by norm_num)
theorem B203069 : Blo 131789 203069 := bbase (se 3 (by rfl) ⟨38075, by rfl⟩ : syracuseStep 203069 = 76151) (by norm_num)
theorem B334165 : Blo 131789 334165 := bbase (se 10 (by rfl) ⟨489, by rfl⟩ : syracuseStep 334165 = 979) (by norm_num)
theorem B203093 : Blo 131789 203093 := bbase (se 10 (by rfl) ⟨297, by rfl⟩ : syracuseStep 203093 = 595) (by norm_num)
theorem B203117 : Blo 131789 203117 := bbase (se 3 (by rfl) ⟨38084, by rfl⟩ : syracuseStep 203117 = 76169) (by norm_num)
theorem B170353 : Blo 131789 170353 := bbase (se 2 (by rfl) ⟨63882, by rfl⟩ : syracuseStep 170353 = 127765) (by norm_num)
theorem B301445 : Blo 131789 301445 := bbase (se 4 (by rfl) ⟨28260, by rfl⟩ : syracuseStep 301445 = 56521) (by norm_num)
theorem B203141 : Blo 131789 203141 := bbase (se 4 (by rfl) ⟨19044, by rfl⟩ : syracuseStep 203141 = 38089) (by norm_num)
theorem B203165 : Blo 131789 203165 := bbase (se 3 (by rfl) ⟨38093, by rfl⟩ : syracuseStep 203165 = 76187) (by norm_num)
theorem B203189 : Blo 131789 203189 := bbase (se 5 (by rfl) ⟨9524, by rfl⟩ : syracuseStep 203189 = 19049) (by norm_num)
theorem B334277 : Blo 131789 334277 := bbase (se 4 (by rfl) ⟨31338, by rfl⟩ : syracuseStep 334277 = 62677) (by norm_num)
theorem B301517 : Blo 131789 301517 := bbase (se 3 (by rfl) ⟨56534, by rfl⟩ : syracuseStep 301517 = 113069) (by norm_num)
theorem B203213 : Blo 131789 203213 := bbase (se 3 (by rfl) ⟨38102, by rfl⟩ : syracuseStep 203213 = 76205) (by norm_num)
theorem B203237 : Blo 131789 203237 := bbase (se 4 (by rfl) ⟨19053, by rfl⟩ : syracuseStep 203237 = 38107) (by norm_num)
theorem B203261 : Blo 131789 203261 := bbase (se 3 (by rfl) ⟨38111, by rfl⟩ : syracuseStep 203261 = 76223) (by norm_num)
theorem B301589 : Blo 131789 301589 := bbase (se 6 (by rfl) ⟨7068, by rfl⟩ : syracuseStep 301589 = 14137) (by norm_num)
theorem B203285 : Blo 131789 203285 := bbase (se 6 (by rfl) ⟨4764, by rfl⟩ : syracuseStep 203285 = 9529) (by norm_num)
theorem B170525 : Blo 131789 170525 := bbase (se 3 (by rfl) ⟨31973, by rfl⟩ : syracuseStep 170525 = 63947) (by norm_num)
theorem B203309 : Blo 131789 203309 := bbase (se 3 (by rfl) ⟨38120, by rfl⟩ : syracuseStep 203309 = 76241) (by norm_num)
theorem B203333 : Blo 131789 203333 := bbase (se 4 (by rfl) ⟨19062, by rfl⟩ : syracuseStep 203333 = 38125) (by norm_num)
theorem B170581 : Blo 131789 170581 := bbase (se 8 (by rfl) ⟨999, by rfl⟩ : syracuseStep 170581 = 1999) (by norm_num)
theorem B301661 : Blo 131789 301661 := bbase (se 3 (by rfl) ⟨56561, by rfl⟩ : syracuseStep 301661 = 113123) (by norm_num)
theorem B203357 : Blo 131789 203357 := bbase (se 3 (by rfl) ⟨38129, by rfl⟩ : syracuseStep 203357 = 76259) (by norm_num)
theorem B203381 : Blo 131789 203381 := bbase (se 5 (by rfl) ⟨9533, by rfl⟩ : syracuseStep 203381 = 19067) (by norm_num)
theorem B334469 : Blo 131789 334469 := bbase (se 4 (by rfl) ⟨31356, by rfl⟩ : syracuseStep 334469 = 62713) (by norm_num)
theorem B203405 : Blo 131789 203405 := bbase (se 3 (by rfl) ⟨38138, by rfl⟩ : syracuseStep 203405 = 76277) (by norm_num)
theorem B301733 : Blo 131789 301733 := bbase (se 4 (by rfl) ⟨28287, by rfl⟩ : syracuseStep 301733 = 56575) (by norm_num)
theorem B203429 : Blo 131789 203429 := bbase (se 4 (by rfl) ⟨19071, by rfl⟩ : syracuseStep 203429 = 38143) (by norm_num)
theorem B170677 : Blo 131789 170677 := bbase (se 5 (by rfl) ⟨8000, by rfl⟩ : syracuseStep 170677 = 16001) (by norm_num)
theorem B432821 : Blo 131789 432821 := bbase (se 5 (by rfl) ⟨20288, by rfl⟩ : syracuseStep 432821 = 40577) (by norm_num)
theorem B203453 : Blo 131789 203453 := bbase (se 3 (by rfl) ⟨38147, by rfl⟩ : syracuseStep 203453 = 76295) (by norm_num)
theorem B203477 : Blo 131789 203477 := bbase (se 7 (by rfl) ⟨2384, by rfl⟩ : syracuseStep 203477 = 4769) (by norm_num)
theorem B301805 : Blo 131789 301805 := bbase (se 3 (by rfl) ⟨56588, by rfl⟩ : syracuseStep 301805 = 113177) (by norm_num)
theorem B203501 : Blo 131789 203501 := bbase (se 3 (by rfl) ⟨38156, by rfl⟩ : syracuseStep 203501 = 76313) (by norm_num)
theorem B203525 : Blo 131789 203525 := bbase (se 4 (by rfl) ⟨19080, by rfl⟩ : syracuseStep 203525 = 38161) (by norm_num)
theorem B203549 : Blo 131789 203549 := bbase (se 3 (by rfl) ⟨38165, by rfl⟩ : syracuseStep 203549 = 76331) (by norm_num)
theorem B138029 : Blo 131789 138029 := bbase (se 3 (by rfl) ⟨25880, by rfl⟩ : syracuseStep 138029 = 51761) (by norm_num)
theorem B203573 : Blo 131789 203573 := bbase (se 5 (by rfl) ⟨9542, by rfl⟩ : syracuseStep 203573 = 19085) (by norm_num)
theorem B301877 : Blo 131789 301877 := bbase (se 5 (by rfl) ⟨14150, by rfl⟩ : syracuseStep 301877 = 28301) (by norm_num)
theorem B203597 : Blo 131789 203597 := bbase (se 3 (by rfl) ⟨38174, by rfl⟩ : syracuseStep 203597 = 76349) (by norm_num)
theorem B170849 : Blo 131789 170849 := bbase (se 2 (by rfl) ⟨64068, by rfl⟩ : syracuseStep 170849 = 128137) (by norm_num)
theorem B203621 : Blo 131789 203621 := bbase (se 4 (by rfl) ⟨19089, by rfl⟩ : syracuseStep 203621 = 38179) (by norm_num)
theorem B301949 : Blo 131789 301949 := bbase (se 3 (by rfl) ⟨56615, by rfl⟩ : syracuseStep 301949 = 113231) (by norm_num)
theorem B203645 : Blo 131789 203645 := bbase (se 3 (by rfl) ⟨38183, by rfl⟩ : syracuseStep 203645 = 76367) (by norm_num)
theorem B203669 : Blo 131789 203669 := bbase (se 6 (by rfl) ⟨4773, by rfl⟩ : syracuseStep 203669 = 9547) (by norm_num)
theorem B170905 : Blo 131789 170905 := bbase (se 2 (by rfl) ⟨64089, by rfl⟩ : syracuseStep 170905 = 128179) (by norm_num)
theorem B302021 : Blo 131789 302021 := bbase (se 4 (by rfl) ⟨28314, by rfl⟩ : syracuseStep 302021 = 56629) (by norm_num)
theorem B334813 : Blo 131789 334813 := bbase (se 3 (by rfl) ⟨62777, by rfl⟩ : syracuseStep 334813 = 125555) (by norm_num)
theorem B171001 : Blo 131789 171001 := bbase (se 2 (by rfl) ⟨64125, by rfl⟩ : syracuseStep 171001 = 128251) (by norm_num)
theorem B302093 : Blo 131789 302093 := bbase (se 3 (by rfl) ⟨56642, by rfl⟩ : syracuseStep 302093 = 113285) (by norm_num)
theorem B1023029 : Blo 131789 1023029 := bbase (se 5 (by rfl) ⟨47954, by rfl⟩ : syracuseStep 1023029 = 95909) (by norm_num)
theorem B334925 : Blo 131789 334925 := bbase (se 3 (by rfl) ⟨62798, by rfl⟩ : syracuseStep 334925 = 125597) (by norm_num)
theorem B302165 : Blo 131789 302165 := bbase (se 8 (by rfl) ⟨1770, by rfl⟩ : syracuseStep 302165 = 3541) (by norm_num)
theorem B302221 : Blo 131789 302221 := bbase (se 3 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 302221 = 113333) (by norm_num)
theorem B302237 : Blo 131789 302237 := bbase (se 3 (by rfl) ⟨56669, by rfl⟩ : syracuseStep 302237 = 113339) (by norm_num)
theorem B171173 : Blo 131789 171173 := bbase (se 4 (by rfl) ⟨16047, by rfl⟩ : syracuseStep 171173 = 32095) (by norm_num)
theorem B302293 : Blo 131789 302293 := bbase (se 7 (by rfl) ⟨3542, by rfl⟩ : syracuseStep 302293 = 7085) (by norm_num)
theorem B171229 : Blo 131789 171229 := bbase (se 3 (by rfl) ⟨32105, by rfl⟩ : syracuseStep 171229 = 64211) (by norm_num)
theorem B204005 : Blo 131789 204005 := bbase (se 4 (by rfl) ⟨19125, by rfl⟩ : syracuseStep 204005 = 38251) (by norm_num)
theorem B302309 : Blo 131789 302309 := bbase (se 4 (by rfl) ⟨28341, by rfl⟩ : syracuseStep 302309 = 56683) (by norm_num)
theorem B335117 : Blo 131789 335117 := bbase (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) (by norm_num)
theorem B302381 : Blo 131789 302381 := bbase (se 3 (by rfl) ⟨56696, by rfl⟩ : syracuseStep 302381 = 113393) (by norm_num)
theorem B171325 : Blo 131789 171325 := bbase (se 3 (by rfl) ⟨32123, by rfl⟩ : syracuseStep 171325 = 64247) (by norm_num)
theorem B204133 : Blo 131789 204133 := bbase (se 4 (by rfl) ⟨19137, by rfl⟩ : syracuseStep 204133 = 38275) (by norm_num)
theorem B302453 : Blo 131789 302453 := bbase (se 5 (by rfl) ⟨14177, by rfl⟩ : syracuseStep 302453 = 28355) (by norm_num)
theorem B761237 : Blo 131789 761237 := bbase (se 6 (by rfl) ⟨17841, by rfl⟩ : syracuseStep 761237 = 35683) (by norm_num)
theorem B171433 : Blo 131789 171433 := bbase (se 2 (by rfl) ⟨64287, by rfl⟩ : syracuseStep 171433 = 128575) (by norm_num)
theorem B204205 : Blo 131789 204205 := bbase (se 3 (by rfl) ⟨38288, by rfl⟩ : syracuseStep 204205 = 76577) (by norm_num)
theorem B302525 : Blo 131789 302525 := bbase (se 3 (by rfl) ⟨56723, by rfl⟩ : syracuseStep 302525 = 113447) (by norm_num)
theorem B171497 : Blo 131789 171497 := bbase (se 2 (by rfl) ⟨64311, by rfl⟩ : syracuseStep 171497 = 128623) (by norm_num)
theorem B564725 : Blo 131789 564725 := bbase (se 5 (by rfl) ⟨26471, by rfl⟩ : syracuseStep 564725 = 52943) (by norm_num)
theorem B302597 : Blo 131789 302597 := bbase (se 4 (by rfl) ⟨28368, by rfl⟩ : syracuseStep 302597 = 56737) (by norm_num)
theorem B171553 : Blo 131789 171553 := bbase (se 2 (by rfl) ⟨64332, by rfl⟩ : syracuseStep 171553 = 128665) (by norm_num)
theorem B302669 : Blo 131789 302669 := bbase (se 3 (by rfl) ⟨56750, by rfl⟩ : syracuseStep 302669 = 113501) (by norm_num)
theorem B335461 : Blo 131789 335461 := bbase (se 4 (by rfl) ⟨31449, by rfl⟩ : syracuseStep 335461 = 62899) (by norm_num)
theorem B171649 : Blo 131789 171649 := bbase (se 2 (by rfl) ⟨64368, by rfl⟩ : syracuseStep 171649 = 128737) (by norm_num)
theorem B302741 : Blo 131789 302741 := bbase (se 6 (by rfl) ⟨7095, by rfl⟩ : syracuseStep 302741 = 14191) (by norm_num)
theorem B335573 : Blo 131789 335573 := bbase (se 7 (by rfl) ⟨3932, by rfl⟩ : syracuseStep 335573 = 7865) (by norm_num)
theorem B302813 : Blo 131789 302813 := bbase (se 3 (by rfl) ⟨56777, by rfl⟩ : syracuseStep 302813 = 113555) (by norm_num)
theorem B564965 : Blo 131789 564965 := bbase (se 4 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 564965 = 105931) (by norm_num)
theorem B270101 : Blo 131789 270101 := bbase (se 6 (by rfl) ⟨6330, by rfl⟩ : syracuseStep 270101 = 12661) (by norm_num)
theorem B1154837 : Blo 131789 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B302885 : Blo 131789 302885 := bbase (se 4 (by rfl) ⟨28395, by rfl⟩ : syracuseStep 302885 = 56791) (by norm_num)
theorem B171821 : Blo 131789 171821 := bbase (se 3 (by rfl) ⟨32216, by rfl⟩ : syracuseStep 171821 = 64433) (by norm_num)
theorem B302957 : Blo 131789 302957 := bbase (se 3 (by rfl) ⟨56804, by rfl⟩ : syracuseStep 302957 = 113609) (by norm_num)
theorem B761717 : Blo 131789 761717 := bbase (se 5 (by rfl) ⟨35705, by rfl⟩ : syracuseStep 761717 = 71411) (by norm_num)
theorem B270197 : Blo 131789 270197 := bbase (se 5 (by rfl) ⟨12665, by rfl⟩ : syracuseStep 270197 = 25331) (by norm_num)
theorem B434069 : Blo 131789 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B335765 : Blo 131789 335765 := bbase (se 6 (by rfl) ⟨7869, by rfl⟩ : syracuseStep 335765 = 15739) (by norm_num)
theorem B368533 : Blo 131789 368533 := bbase (se 6 (by rfl) ⟨8637, by rfl⟩ : syracuseStep 368533 = 17275) (by norm_num)
theorem B303029 : Blo 131789 303029 := bbase (se 5 (by rfl) ⟨14204, by rfl⟩ : syracuseStep 303029 = 28409) (by norm_num)
theorem B303101 : Blo 131789 303101 := bbase (se 3 (by rfl) ⟨56831, by rfl⟩ : syracuseStep 303101 = 113663) (by norm_num)
theorem B172093 : Blo 131789 172093 := bbase (se 3 (by rfl) ⟨32267, by rfl⟩ : syracuseStep 172093 = 64535) (by norm_num)
theorem B303173 : Blo 131789 303173 := bbase (se 4 (by rfl) ⟨28422, by rfl⟩ : syracuseStep 303173 = 56845) (by norm_num)
theorem B303245 : Blo 131789 303245 := bbase (se 3 (by rfl) ⟨56858, by rfl⟩ : syracuseStep 303245 = 113717) (by norm_num)
theorem B303317 : Blo 131789 303317 := bbase (se 7 (by rfl) ⟨3554, by rfl⟩ : syracuseStep 303317 = 7109) (by norm_num)
theorem B336109 : Blo 131789 336109 := bbase (se 3 (by rfl) ⟨63020, by rfl⟩ : syracuseStep 336109 = 126041) (by norm_num)
theorem B303389 : Blo 131789 303389 := bbase (se 3 (by rfl) ⟨56885, by rfl⟩ : syracuseStep 303389 = 113771) (by norm_num)
theorem B1089845 : Blo 131789 1089845 := bbase (se 5 (by rfl) ⟨51086, by rfl⟩ : syracuseStep 1089845 = 102173) (by norm_num)
theorem B336221 : Blo 131789 336221 := bbase (se 3 (by rfl) ⟨63041, by rfl⟩ : syracuseStep 336221 = 126083) (by norm_num)
theorem B303461 : Blo 131789 303461 := bbase (se 4 (by rfl) ⟨28449, by rfl⟩ : syracuseStep 303461 = 56899) (by norm_num)
theorem B1286549 : Blo 131789 1286549 := bbase (se 6 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 1286549 = 60307) (by norm_num)
theorem B303533 : Blo 131789 303533 := bbase (se 3 (by rfl) ⟨56912, by rfl⟩ : syracuseStep 303533 = 113825) (by norm_num)
theorem B303605 : Blo 131789 303605 := bbase (se 5 (by rfl) ⟨14231, by rfl⟩ : syracuseStep 303605 = 28463) (by norm_num)
theorem B205301 : Blo 131789 205301 := bbase (se 5 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 205301 = 19247) (by norm_num)
theorem B336413 : Blo 131789 336413 := bbase (se 3 (by rfl) ⟨63077, by rfl⟩ : syracuseStep 336413 = 126155) (by norm_num)
theorem B303677 : Blo 131789 303677 := bbase (se 3 (by rfl) ⟨56939, by rfl⟩ : syracuseStep 303677 = 113879) (by norm_num)
theorem B205373 : Blo 131789 205373 := bbase (se 3 (by rfl) ⟨38507, by rfl⟩ : syracuseStep 205373 = 77015) (by norm_num)
theorem B303749 : Blo 131789 303749 := bbase (se 4 (by rfl) ⟨28476, by rfl⟩ : syracuseStep 303749 = 56953) (by norm_num)
theorem B434821 : Blo 131789 434821 := bbase (se 4 (by rfl) ⟨40764, by rfl⟩ : syracuseStep 434821 = 81529) (by norm_num)
theorem B303821 : Blo 131789 303821 := bbase (se 3 (by rfl) ⟨56966, by rfl⟩ : syracuseStep 303821 = 113933) (by norm_num)
theorem B303845 : Blo 131789 303845 := bbase (se 4 (by rfl) ⟨28485, by rfl⟩ : syracuseStep 303845 = 56971) (by norm_num)
theorem B1155829 : Blo 131789 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B303893 : Blo 131789 303893 := bbase (se 6 (by rfl) ⟨7122, by rfl⟩ : syracuseStep 303893 = 14245) (by norm_num)
theorem B303965 : Blo 131789 303965 := bbase (se 3 (by rfl) ⟨56993, by rfl⟩ : syracuseStep 303965 = 113987) (by norm_num)
theorem B336757 : Blo 131789 336757 := bbase (se 5 (by rfl) ⟨15785, by rfl⟩ : syracuseStep 336757 = 31571) (by norm_num)
theorem B304037 : Blo 131789 304037 := bbase (se 4 (by rfl) ⟨28503, by rfl⟩ : syracuseStep 304037 = 57007) (by norm_num)
theorem B336869 : Blo 131789 336869 := bbase (se 4 (by rfl) ⟨31581, by rfl⟩ : syracuseStep 336869 = 63163) (by norm_num)
theorem B304109 : Blo 131789 304109 := bbase (se 3 (by rfl) ⟨57020, by rfl⟩ : syracuseStep 304109 = 114041) (by norm_num)
theorem B304181 : Blo 131789 304181 := bbase (se 5 (by rfl) ⟨14258, by rfl⟩ : syracuseStep 304181 = 28517) (by norm_num)
theorem B304253 : Blo 131789 304253 := bbase (se 3 (by rfl) ⟨57047, by rfl⟩ : syracuseStep 304253 = 114095) (by norm_num)
theorem B271517 : Blo 131789 271517 := bbase (se 3 (by rfl) ⟨50909, by rfl⟩ : syracuseStep 271517 = 101819) (by norm_num)
theorem B337061 : Blo 131789 337061 := bbase (se 4 (by rfl) ⟨31599, by rfl⟩ : syracuseStep 337061 = 63199) (by norm_num)
theorem B304325 : Blo 131789 304325 := bbase (se 4 (by rfl) ⟨28530, by rfl⟩ : syracuseStep 304325 = 57061) (by norm_num)
theorem B304397 : Blo 131789 304397 := bbase (se 3 (by rfl) ⟨57074, by rfl⟩ : syracuseStep 304397 = 114149) (by norm_num)
theorem B304469 : Blo 131789 304469 := bbase (se 12 (by rfl) ⟨111, by rfl⟩ : syracuseStep 304469 = 223) (by norm_num)
theorem B304541 : Blo 131789 304541 := bbase (se 3 (by rfl) ⟨57101, by rfl⟩ : syracuseStep 304541 = 114203) (by norm_num)
theorem B501173 : Blo 131789 501173 := bbase (se 5 (by rfl) ⟨23492, by rfl⟩ : syracuseStep 501173 = 46985) (by norm_num)
theorem B304613 : Blo 131789 304613 := bbase (se 4 (by rfl) ⟨28557, by rfl⟩ : syracuseStep 304613 = 57115) (by norm_num)
theorem B337405 : Blo 131789 337405 := bbase (se 3 (by rfl) ⟨63263, by rfl⟩ : syracuseStep 337405 = 126527) (by norm_num)
theorem B304685 : Blo 131789 304685 := bbase (se 3 (by rfl) ⟨57128, by rfl⟩ : syracuseStep 304685 = 114257) (by norm_num)
theorem B763445 : Blo 131789 763445 := bbase (se 5 (by rfl) ⟨35786, by rfl⟩ : syracuseStep 763445 = 71573) (by norm_num)
theorem B337517 : Blo 131789 337517 := bbase (se 3 (by rfl) ⟨63284, by rfl⟩ : syracuseStep 337517 = 126569) (by norm_num)
theorem B304757 : Blo 131789 304757 := bbase (se 5 (by rfl) ⟨14285, by rfl⟩ : syracuseStep 304757 = 28571) (by norm_num)
theorem B304829 : Blo 131789 304829 := bbase (se 3 (by rfl) ⟨57155, by rfl⟩ : syracuseStep 304829 = 114311) (by norm_num)
theorem B501461 : Blo 131789 501461 := bbase (se 7 (by rfl) ⟨5876, by rfl⟩ : syracuseStep 501461 = 11753) (by norm_num)
theorem B403157 : Blo 131789 403157 := bbase (se 7 (by rfl) ⟨4724, by rfl⟩ : syracuseStep 403157 = 9449) (by norm_num)
theorem B304901 : Blo 131789 304901 := bbase (se 4 (by rfl) ⟨28584, by rfl⟩ : syracuseStep 304901 = 57169) (by norm_num)
theorem B337709 : Blo 131789 337709 := bbase (se 3 (by rfl) ⟨63320, by rfl⟩ : syracuseStep 337709 = 126641) (by norm_num)
theorem B141113 : Blo 131789 141113 := bbase (se 2 (by rfl) ⟨52917, by rfl⟩ : syracuseStep 141113 = 105835) (by norm_num)
theorem B304973 : Blo 131789 304973 := bbase (se 3 (by rfl) ⟨57182, by rfl⟩ : syracuseStep 304973 = 114365) (by norm_num)
theorem B305045 : Blo 131789 305045 := bbase (se 6 (by rfl) ⟨7149, by rfl⟩ : syracuseStep 305045 = 14299) (by norm_num)
theorem B239557 : Blo 131789 239557 := bbase (se 4 (by rfl) ⟨22458, by rfl⟩ : syracuseStep 239557 = 44917) (by norm_num)
theorem B567253 : Blo 131789 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B305117 : Blo 131789 305117 := bbase (se 3 (by rfl) ⟨57209, by rfl⟩ : syracuseStep 305117 = 114419) (by norm_num)
theorem B141301 : Blo 131789 141301 := bbase (se 5 (by rfl) ⟨6623, by rfl⟩ : syracuseStep 141301 = 13247) (by norm_num)
theorem B305189 : Blo 131789 305189 := bbase (se 4 (by rfl) ⟨28611, by rfl⟩ : syracuseStep 305189 = 57223) (by norm_num)
theorem B305213 : Blo 131789 305213 := bbase (se 3 (by rfl) ⟨57227, by rfl⟩ : syracuseStep 305213 = 114455) (by norm_num)
theorem B305261 : Blo 131789 305261 := bbase (se 3 (by rfl) ⟨57236, by rfl⟩ : syracuseStep 305261 = 114473) (by norm_num)
theorem B338053 : Blo 131789 338053 := bbase (se 4 (by rfl) ⟨31692, by rfl⟩ : syracuseStep 338053 = 63385) (by norm_num)
theorem B305333 : Blo 131789 305333 := bbase (se 5 (by rfl) ⟨14312, by rfl⟩ : syracuseStep 305333 = 28625) (by norm_num)
theorem B338165 : Blo 131789 338165 := bbase (se 5 (by rfl) ⟨15851, by rfl⟩ : syracuseStep 338165 = 31703) (by norm_num)
theorem B305405 : Blo 131789 305405 := bbase (se 3 (by rfl) ⟨57263, by rfl⟩ : syracuseStep 305405 = 114527) (by norm_num)
theorem B305477 : Blo 131789 305477 := bbase (se 4 (by rfl) ⟨28638, by rfl⟩ : syracuseStep 305477 = 57277) (by norm_num)
theorem B338357 : Blo 131789 338357 := bbase (se 5 (by rfl) ⟨15860, by rfl⟩ : syracuseStep 338357 = 31721) (by norm_num)
theorem B502213 : Blo 131789 502213 := bbase (se 4 (by rfl) ⟨47082, by rfl⟩ : syracuseStep 502213 = 94165) (by norm_num)
theorem B305797 : Blo 131789 305797 := bbase (se 4 (by rfl) ⟨28668, by rfl⟩ : syracuseStep 305797 = 57337) (by norm_num)
theorem B273053 : Blo 131789 273053 := bbase (se 3 (by rfl) ⟨51197, by rfl⟩ : syracuseStep 273053 = 102395) (by norm_num)
theorem B1157813 : Blo 131789 1157813 := bbase (se 5 (by rfl) ⟨54272, by rfl⟩ : syracuseStep 1157813 = 108545) (by norm_num)
theorem B731861 : Blo 131789 731861 := bbase (se 7 (by rfl) ⟨8576, by rfl⟩ : syracuseStep 731861 = 17153) (by norm_num)
theorem B338701 : Blo 131789 338701 := bbase (se 3 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 338701 = 127013) (by norm_num)
theorem B142121 : Blo 131789 142121 := bbase (se 2 (by rfl) ⟨53295, by rfl⟩ : syracuseStep 142121 = 106591) (by norm_num)
theorem B502645 : Blo 131789 502645 := bbase (se 5 (by rfl) ⟨23561, by rfl⟩ : syracuseStep 502645 = 47123) (by norm_num)
theorem B338813 : Blo 131789 338813 := bbase (se 3 (by rfl) ⟨63527, by rfl⟩ : syracuseStep 338813 = 127055) (by norm_num)
theorem B306125 : Blo 131789 306125 := bbase (se 3 (by rfl) ⟨57398, by rfl⟩ : syracuseStep 306125 = 114797) (by norm_num)
theorem B240637 : Blo 131789 240637 := bbase (se 3 (by rfl) ⟨45119, by rfl⟩ : syracuseStep 240637 = 90239) (by norm_num)
theorem B339005 : Blo 131789 339005 := bbase (se 3 (by rfl) ⟨63563, by rfl⟩ : syracuseStep 339005 = 127127) (by norm_num)
theorem B240725 : Blo 131789 240725 := bbase (se 8 (by rfl) ⟨1410, by rfl⟩ : syracuseStep 240725 = 2821) (by norm_num)
theorem B207973 : Blo 131789 207973 := bbase (se 4 (by rfl) ⟨19497, by rfl⟩ : syracuseStep 207973 = 38995) (by norm_num)
theorem B240781 : Blo 131789 240781 := bbase (se 3 (by rfl) ⟨45146, by rfl⟩ : syracuseStep 240781 = 90293) (by norm_num)
theorem B502949 : Blo 131789 502949 := bbase (se 4 (by rfl) ⟨47151, by rfl⟩ : syracuseStep 502949 = 94303) (by norm_num)
theorem B142565 : Blo 131789 142565 := bbase (se 4 (by rfl) ⟨13365, by rfl⟩ : syracuseStep 142565 = 26731) (by norm_num)
theorem B437653 : Blo 131789 437653 := bbase (se 6 (by rfl) ⟨10257, by rfl⟩ : syracuseStep 437653 = 20515) (by norm_num)
theorem B339349 : Blo 131789 339349 := bbase (se 6 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 339349 = 15907) (by norm_num)
theorem B568741 : Blo 131789 568741 := bbase (se 4 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 568741 = 106639) (by norm_num)
theorem B568757 : Blo 131789 568757 := bbase (se 5 (by rfl) ⟨26660, by rfl⟩ : syracuseStep 568757 = 53321) (by norm_num)
theorem B142813 : Blo 131789 142813 := bbase (se 3 (by rfl) ⟨26777, by rfl⟩ : syracuseStep 142813 = 53555) (by norm_num)
theorem B339461 : Blo 131789 339461 := bbase (se 4 (by rfl) ⟨31824, by rfl⟩ : syracuseStep 339461 = 63649) (by norm_num)
theorem B863797 : Blo 131789 863797 := bbase (se 5 (by rfl) ⟨40490, by rfl⟩ : syracuseStep 863797 = 80981) (by norm_num)
theorem B339653 : Blo 131789 339653 := bbase (se 4 (by rfl) ⟨31842, by rfl⟩ : syracuseStep 339653 = 63685) (by norm_num)
theorem B306965 : Blo 131789 306965 := bbase (se 6 (by rfl) ⟨7194, by rfl⟩ : syracuseStep 306965 = 14389) (by norm_num)
theorem B438053 : Blo 131789 438053 := bbase (se 4 (by rfl) ⟨41067, by rfl⟩ : syracuseStep 438053 = 82135) (by norm_num)
theorem B143245 : Blo 131789 143245 := bbase (se 3 (by rfl) ⟨26858, by rfl⟩ : syracuseStep 143245 = 53717) (by norm_num)
theorem B274349 : Blo 131789 274349 := bbase (se 3 (by rfl) ⟨51440, by rfl⟩ : syracuseStep 274349 = 102881) (by norm_num)
theorem B405445 : Blo 131789 405445 := bbase (se 4 (by rfl) ⟨38010, by rfl⟩ : syracuseStep 405445 = 76021) (by norm_num)
theorem B143317 : Blo 131789 143317 := bbase (se 7 (by rfl) ⟨1679, by rfl⟩ : syracuseStep 143317 = 3359) (by norm_num)
theorem B339997 : Blo 131789 339997 := bbase (se 3 (by rfl) ⟨63749, by rfl⟩ : syracuseStep 339997 = 127499) (by norm_num)
theorem B340109 : Blo 131789 340109 := bbase (se 3 (by rfl) ⟨63770, by rfl⟩ : syracuseStep 340109 = 127541) (by norm_num)
theorem B667925 : Blo 131789 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B143689 : Blo 131789 143689 := bbase (se 2 (by rfl) ⟨53883, by rfl⟩ : syracuseStep 143689 = 107767) (by norm_num)
theorem B340301 : Blo 131789 340301 := bbase (se 3 (by rfl) ⟨63806, by rfl⟩ : syracuseStep 340301 = 127613) (by norm_num)
theorem B242309 : Blo 131789 242309 := bbase (se 4 (by rfl) ⟨22716, by rfl⟩ : syracuseStep 242309 = 45433) (by norm_num)
theorem B340645 : Blo 131789 340645 := bbase (se 4 (by rfl) ⟨31935, by rfl⟩ : syracuseStep 340645 = 63871) (by norm_num)
theorem B144065 : Blo 131789 144065 := bbase (se 2 (by rfl) ⟨54024, by rfl⟩ : syracuseStep 144065 = 108049) (by norm_num)
theorem B1913557 : Blo 131789 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B144137 : Blo 131789 144137 := bbase (se 2 (by rfl) ⟨54051, by rfl⟩ : syracuseStep 144137 = 108103) (by norm_num)
theorem B340757 : Blo 131789 340757 := bbase (se 6 (by rfl) ⟨7986, by rfl⟩ : syracuseStep 340757 = 15973) (by norm_num)
theorem B144325 : Blo 131789 144325 := bbase (se 4 (by rfl) ⟨13530, by rfl⟩ : syracuseStep 144325 = 27061) (by norm_num)
theorem B340949 : Blo 131789 340949 := bbase (se 7 (by rfl) ⟨3995, by rfl⟩ : syracuseStep 340949 = 7991) (by norm_num)
theorem B144509 : Blo 131789 144509 := bbase (se 3 (by rfl) ⟨27095, by rfl⟩ : syracuseStep 144509 = 54191) (by norm_num)
theorem B505061 : Blo 131789 505061 := bbase (se 4 (by rfl) ⟨47349, by rfl⟩ : syracuseStep 505061 = 94699) (by norm_num)
theorem B144649 : Blo 131789 144649 := bbase (se 2 (by rfl) ⟨54243, by rfl⟩ : syracuseStep 144649 = 108487) (by norm_num)
theorem B341293 : Blo 131789 341293 := bbase (se 3 (by rfl) ⟨63992, by rfl⟩ : syracuseStep 341293 = 127985) (by norm_num)
theorem B341405 : Blo 131789 341405 := bbase (se 3 (by rfl) ⟨64013, by rfl⟩ : syracuseStep 341405 = 128027) (by norm_num)
theorem B603605 : Blo 131789 603605 := bbase (se 7 (by rfl) ⟨7073, by rfl⟩ : syracuseStep 603605 = 14147) (by norm_num)
theorem B505349 : Blo 131789 505349 := bbase (se 4 (by rfl) ⟨47376, by rfl⟩ : syracuseStep 505349 = 94753) (by norm_num)
theorem B669221 : Blo 131789 669221 := bbase (se 4 (by rfl) ⟨62739, by rfl⟩ : syracuseStep 669221 = 125479) (by norm_num)
theorem B341597 : Blo 131789 341597 := bbase (se 3 (by rfl) ⟨64049, by rfl⟩ : syracuseStep 341597 = 128099) (by norm_num)
theorem B308861 : Blo 131789 308861 := bbase (se 3 (by rfl) ⟨57911, by rfl⟩ : syracuseStep 308861 = 115823) (by norm_num)
theorem B571013 : Blo 131789 571013 := bbase (se 4 (by rfl) ⟨53532, by rfl⟩ : syracuseStep 571013 = 107065) (by norm_num)
theorem B276245 : Blo 131789 276245 := bbase (se 6 (by rfl) ⟨6474, by rfl⟩ : syracuseStep 276245 = 12949) (by norm_num)
theorem B243629 : Blo 131789 243629 := bbase (se 3 (by rfl) ⟨45680, by rfl⟩ : syracuseStep 243629 = 91361) (by norm_num)
theorem B341941 : Blo 131789 341941 := bbase (se 5 (by rfl) ⟨16028, by rfl⟩ : syracuseStep 341941 = 32057) (by norm_num)
theorem B538613 : Blo 131789 538613 := bbase (se 5 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 538613 = 50495) (by norm_num)
theorem B342053 : Blo 131789 342053 := bbase (se 4 (by rfl) ⟨32067, by rfl⟩ : syracuseStep 342053 = 64135) (by norm_num)
theorem B342245 : Blo 131789 342245 := bbase (se 4 (by rfl) ⟨32085, by rfl⟩ : syracuseStep 342245 = 64171) (by norm_num)
theorem B440549 : Blo 131789 440549 := bbase (se 4 (by rfl) ⟨41301, by rfl⟩ : syracuseStep 440549 = 82603) (by norm_num)
theorem B637237 : Blo 131789 637237 := bbase (se 5 (by rfl) ⟨29870, by rfl⟩ : syracuseStep 637237 = 59741) (by norm_num)
theorem B211285 : Blo 131789 211285 := bbase (se 10 (by rfl) ⟨309, by rfl⟩ : syracuseStep 211285 = 619) (by norm_num)
theorem B866645 : Blo 131789 866645 := bbase (se 10 (by rfl) ⟨1269, by rfl⟩ : syracuseStep 866645 = 2539) (by norm_num)
theorem B342589 : Blo 131789 342589 := bbase (se 3 (by rfl) ⟨64235, by rfl⟩ : syracuseStep 342589 = 128471) (by norm_num)
theorem B1030805 : Blo 131789 1030805 := bbase (se 6 (by rfl) ⟨24159, by rfl⟩ : syracuseStep 1030805 = 48319) (by norm_num)
theorem B506533 : Blo 131789 506533 := bbase (se 4 (by rfl) ⟨47487, by rfl⟩ : syracuseStep 506533 = 94975) (by norm_num)
theorem B342701 : Blo 131789 342701 := bbase (se 3 (by rfl) ⟨64256, by rfl⟩ : syracuseStep 342701 = 128513) (by norm_num)
theorem B211709 : Blo 131789 211709 := bbase (se 3 (by rfl) ⟨39695, by rfl⟩ : syracuseStep 211709 = 79391) (by norm_num)
theorem B670517 : Blo 131789 670517 := bbase (se 5 (by rfl) ⟨31430, by rfl⟩ : syracuseStep 670517 = 62861) (by norm_num)
theorem B342893 : Blo 131789 342893 := bbase (se 3 (by rfl) ⟨64292, by rfl⟩ : syracuseStep 342893 = 128585) (by norm_num)
theorem B277453 : Blo 131789 277453 := bbase (se 3 (by rfl) ⟨52022, by rfl⟩ : syracuseStep 277453 = 104045) (by norm_num)
theorem B506837 : Blo 131789 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B211997 : Blo 131789 211997 := bbase (se 3 (by rfl) ⟨39749, by rfl⟩ : syracuseStep 211997 = 79499) (by norm_num)
theorem B343237 : Blo 131789 343237 := bbase (se 4 (by rfl) ⟨32178, by rfl⟩ : syracuseStep 343237 = 64357) (by norm_num)
theorem B343349 : Blo 131789 343349 := bbase (se 5 (by rfl) ⟨16094, by rfl⟩ : syracuseStep 343349 = 32189) (by norm_num)
theorem B1457621 : Blo 131789 1457621 := bbase (se 7 (by rfl) ⟨17081, by rfl⟩ : syracuseStep 1457621 = 34163) (by norm_num)
theorem B277997 : Blo 131789 277997 := bbase (se 3 (by rfl) ⟨52124, by rfl⟩ : syracuseStep 277997 = 104249) (by norm_num)
theorem B343541 : Blo 131789 343541 := bbase (se 5 (by rfl) ⟨16103, by rfl⟩ : syracuseStep 343541 = 32207) (by norm_num)
theorem B245413 : Blo 131789 245413 := bbase (se 4 (by rfl) ⟨23007, by rfl⟩ : syracuseStep 245413 = 46015) (by norm_num)
theorem B212797 : Blo 131789 212797 := bbase (se 3 (by rfl) ⟨39899, by rfl⟩ : syracuseStep 212797 = 79799) (by norm_num)
theorem B376757 : Blo 131789 376757 := bbase (se 5 (by rfl) ⟨17660, by rfl⟩ : syracuseStep 376757 = 35321) (by norm_num)
theorem B671813 : Blo 131789 671813 := bbase (se 4 (by rfl) ⟨62982, by rfl⟩ : syracuseStep 671813 = 125965) (by norm_num)
theorem B278621 : Blo 131789 278621 := bbase (se 3 (by rfl) ⟨52241, by rfl⟩ : syracuseStep 278621 = 104483) (by norm_num)
theorem B311597 : Blo 131789 311597 := bbase (se 3 (by rfl) ⟨58424, by rfl⟩ : syracuseStep 311597 = 116849) (by norm_num)
theorem B213349 : Blo 131789 213349 := bbase (se 4 (by rfl) ⟨20001, by rfl⟩ : syracuseStep 213349 = 40003) (by norm_num)
theorem B180733 : Blo 131789 180733 := bbase (se 3 (by rfl) ⟨33887, by rfl⟩ : syracuseStep 180733 = 67775) (by norm_num)
theorem B213605 : Blo 131789 213605 := bbase (se 4 (by rfl) ⟨20025, by rfl⟩ : syracuseStep 213605 = 40051) (by norm_num)
theorem B180949 : Blo 131789 180949 := bbase (se 7 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 180949 = 4241) (by norm_num)
theorem B148297 : Blo 131789 148297 := bbase (se 2 (by rfl) ⟨55611, by rfl⟩ : syracuseStep 148297 = 111223) (by norm_num)
theorem B148333 : Blo 131789 148333 := bbase (se 3 (by rfl) ⟨27812, by rfl⟩ : syracuseStep 148333 = 55625) (by norm_num)
theorem B148369 : Blo 131789 148369 := bbase (se 2 (by rfl) ⟨55638, by rfl⟩ : syracuseStep 148369 = 111277) (by norm_num)
theorem B574373 : Blo 131789 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B148405 : Blo 131789 148405 := bbase (se 5 (by rfl) ⟨6956, by rfl⟩ : syracuseStep 148405 = 13913) (by norm_num)
theorem B148441 : Blo 131789 148441 := bbase (se 2 (by rfl) ⟨55665, by rfl⟩ : syracuseStep 148441 = 111331) (by norm_num)
theorem B148477 : Blo 131789 148477 := bbase (se 3 (by rfl) ⟨27839, by rfl⟩ : syracuseStep 148477 = 55679) (by norm_num)
theorem B508949 : Blo 131789 508949 := bbase (se 6 (by rfl) ⟨11928, by rfl⟩ : syracuseStep 508949 = 23857) (by norm_num)
theorem B148513 : Blo 131789 148513 := bbase (se 2 (by rfl) ⟨55692, by rfl⟩ : syracuseStep 148513 = 111385) (by norm_num)
theorem B148549 : Blo 131789 148549 := bbase (se 4 (by rfl) ⟨13926, by rfl⟩ : syracuseStep 148549 = 27853) (by norm_num)
theorem B377941 : Blo 131789 377941 := bbase (se 8 (by rfl) ⟨2214, by rfl⟩ : syracuseStep 377941 = 4429) (by norm_num)
theorem B148585 : Blo 131789 148585 := bbase (se 2 (by rfl) ⟨55719, by rfl⟩ : syracuseStep 148585 = 111439) (by norm_num)
theorem B148621 : Blo 131789 148621 := bbase (se 3 (by rfl) ⟨27866, by rfl⟩ : syracuseStep 148621 = 55733) (by norm_num)
theorem B148657 : Blo 131789 148657 := bbase (se 2 (by rfl) ⟨55746, by rfl⟩ : syracuseStep 148657 = 111493) (by norm_num)
theorem B148693 : Blo 131789 148693 := bbase (se 7 (by rfl) ⟨1742, by rfl⟩ : syracuseStep 148693 = 3485) (by norm_num)
theorem B378101 : Blo 131789 378101 := bbase (se 5 (by rfl) ⟨17723, by rfl⟩ : syracuseStep 378101 = 35447) (by norm_num)
theorem B148729 : Blo 131789 148729 := bbase (se 2 (by rfl) ⟨55773, by rfl⟩ : syracuseStep 148729 = 111547) (by norm_num)
theorem B1525013 : Blo 131789 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B148765 : Blo 131789 148765 := bbase (se 3 (by rfl) ⟨27893, by rfl⟩ : syracuseStep 148765 = 55787) (by norm_num)
theorem B214309 : Blo 131789 214309 := bbase (se 4 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 214309 = 40183) (by norm_num)
theorem B509237 : Blo 131789 509237 := bbase (se 5 (by rfl) ⟨23870, by rfl⟩ : syracuseStep 509237 = 47741) (by norm_num)
theorem B148801 : Blo 131789 148801 := bbase (se 2 (by rfl) ⟨55800, by rfl⟩ : syracuseStep 148801 = 111601) (by norm_num)
theorem B673109 : Blo 131789 673109 := bbase (se 12 (by rfl) ⟨246, by rfl⟩ : syracuseStep 673109 = 493) (by norm_num)
theorem B148837 : Blo 131789 148837 := bbase (se 4 (by rfl) ⟨13953, by rfl⟩ : syracuseStep 148837 = 27907) (by norm_num)
theorem B148873 : Blo 131789 148873 := bbase (se 2 (by rfl) ⟨55827, by rfl⟩ : syracuseStep 148873 = 111655) (by norm_num)
theorem B181645 : Blo 131789 181645 := bbase (se 3 (by rfl) ⟨34058, by rfl⟩ : syracuseStep 181645 = 68117) (by norm_num)
theorem B607637 : Blo 131789 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B148909 : Blo 131789 148909 := bbase (se 3 (by rfl) ⟨27920, by rfl⟩ : syracuseStep 148909 = 55841) (by norm_num)
theorem B148945 : Blo 131789 148945 := bbase (se 2 (by rfl) ⟨55854, by rfl⟩ : syracuseStep 148945 = 111709) (by norm_num)
theorem B378341 : Blo 131789 378341 := bbase (se 4 (by rfl) ⟨35469, by rfl⟩ : syracuseStep 378341 = 70939) (by norm_num)
theorem B148981 : Blo 131789 148981 := bbase (se 5 (by rfl) ⟨6983, by rfl⟩ : syracuseStep 148981 = 13967) (by norm_num)
theorem B149017 : Blo 131789 149017 := bbase (se 2 (by rfl) ⟨55881, by rfl⟩ : syracuseStep 149017 = 111763) (by norm_num)
theorem B149053 : Blo 131789 149053 := bbase (se 3 (by rfl) ⟨27947, by rfl⟩ : syracuseStep 149053 = 55895) (by norm_num)
theorem B575045 : Blo 131789 575045 := bbase (se 4 (by rfl) ⟨53910, by rfl⟩ : syracuseStep 575045 = 107821) (by norm_num)
theorem B149089 : Blo 131789 149089 := bbase (se 2 (by rfl) ⟨55908, by rfl⟩ : syracuseStep 149089 = 111817) (by norm_num)
theorem B149125 : Blo 131789 149125 := bbase (se 4 (by rfl) ⟨13980, by rfl⟩ : syracuseStep 149125 = 27961) (by norm_num)
theorem B378533 : Blo 131789 378533 := bbase (se 4 (by rfl) ⟨35487, by rfl⟩ : syracuseStep 378533 = 70975) (by norm_num)
theorem B149161 : Blo 131789 149161 := bbase (se 2 (by rfl) ⟨55935, by rfl⟩ : syracuseStep 149161 = 111871) (by norm_num)
theorem B149197 : Blo 131789 149197 := bbase (se 3 (by rfl) ⟨27974, by rfl⟩ : syracuseStep 149197 = 55949) (by norm_num)
theorem B214733 : Blo 131789 214733 := bbase (se 3 (by rfl) ⟨40262, by rfl⟩ : syracuseStep 214733 = 80525) (by norm_num)
theorem B149233 : Blo 131789 149233 := bbase (se 2 (by rfl) ⟨55962, by rfl⟩ : syracuseStep 149233 = 111925) (by norm_num)
theorem B149269 : Blo 131789 149269 := bbase (se 6 (by rfl) ⟨3498, by rfl⟩ : syracuseStep 149269 = 6997) (by norm_num)
theorem B149305 : Blo 131789 149305 := bbase (se 2 (by rfl) ⟨55989, by rfl⟩ : syracuseStep 149305 = 111979) (by norm_num)
theorem B149341 : Blo 131789 149341 := bbase (se 3 (by rfl) ⟨28001, by rfl⟩ : syracuseStep 149341 = 56003) (by norm_num)
theorem B149377 : Blo 131789 149377 := bbase (se 2 (by rfl) ⟨56016, by rfl⟩ : syracuseStep 149377 = 112033) (by norm_num)
theorem B149413 : Blo 131789 149413 := bbase (se 4 (by rfl) ⟨14007, by rfl⟩ : syracuseStep 149413 = 28015) (by norm_num)
theorem B149449 : Blo 131789 149449 := bbase (se 2 (by rfl) ⟨56043, by rfl⟩ : syracuseStep 149449 = 112087) (by norm_num)
theorem B149485 : Blo 131789 149485 := bbase (se 3 (by rfl) ⟨28028, by rfl⟩ : syracuseStep 149485 = 56057) (by norm_num)
theorem B215021 : Blo 131789 215021 := bbase (se 3 (by rfl) ⟨40316, by rfl⟩ : syracuseStep 215021 = 80633) (by norm_num)
theorem B870389 : Blo 131789 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B149521 : Blo 131789 149521 := bbase (se 2 (by rfl) ⟨56070, by rfl⟩ : syracuseStep 149521 = 112141) (by norm_num)
theorem B149557 : Blo 131789 149557 := bbase (se 5 (by rfl) ⟨7010, by rfl⟩ : syracuseStep 149557 = 14021) (by norm_num)
theorem B149593 : Blo 131789 149593 := bbase (se 2 (by rfl) ⟨56097, by rfl⟩ : syracuseStep 149593 = 112195) (by norm_num)
theorem B149629 : Blo 131789 149629 := bbase (se 3 (by rfl) ⟨28055, by rfl⟩ : syracuseStep 149629 = 56111) (by norm_num)
theorem B149665 : Blo 131789 149665 := bbase (se 2 (by rfl) ⟨56124, by rfl⟩ : syracuseStep 149665 = 112249) (by norm_num)
theorem B149701 : Blo 131789 149701 := bbase (se 4 (by rfl) ⟨14034, by rfl⟩ : syracuseStep 149701 = 28069) (by norm_num)
theorem B215245 : Blo 131789 215245 := bbase (se 3 (by rfl) ⟨40358, by rfl⟩ : syracuseStep 215245 = 80717) (by norm_num)
theorem B149737 : Blo 131789 149737 := bbase (se 2 (by rfl) ⟨56151, by rfl⟩ : syracuseStep 149737 = 112303) (by norm_num)
theorem B149773 : Blo 131789 149773 := bbase (se 3 (by rfl) ⟨28082, by rfl⟩ : syracuseStep 149773 = 56165) (by norm_num)
theorem B149809 : Blo 131789 149809 := bbase (se 2 (by rfl) ⟨56178, by rfl⟩ : syracuseStep 149809 = 112357) (by norm_num)
theorem B149845 : Blo 131789 149845 := bbase (se 10 (by rfl) ⟨219, by rfl⟩ : syracuseStep 149845 = 439) (by norm_num)
theorem B149881 : Blo 131789 149881 := bbase (se 2 (by rfl) ⟨56205, by rfl⟩ : syracuseStep 149881 = 112411) (by norm_num)
theorem B412037 : Blo 131789 412037 := bbase (se 4 (by rfl) ⟨38628, by rfl⟩ : syracuseStep 412037 = 77257) (by norm_num)
theorem B641429 : Blo 131789 641429 := bbase (se 6 (by rfl) ⟨15033, by rfl⟩ : syracuseStep 641429 = 30067) (by norm_num)
theorem B149917 : Blo 131789 149917 := bbase (se 3 (by rfl) ⟨28109, by rfl⟩ : syracuseStep 149917 = 56219) (by norm_num)
theorem B149953 : Blo 131789 149953 := bbase (se 2 (by rfl) ⟨56232, by rfl⟩ : syracuseStep 149953 = 112465) (by norm_num)
theorem B510421 : Blo 131789 510421 := bbase (se 7 (by rfl) ⟨5981, by rfl⟩ : syracuseStep 510421 = 11963) (by norm_num)
theorem B182749 : Blo 131789 182749 := bbase (se 3 (by rfl) ⟨34265, by rfl⟩ : syracuseStep 182749 = 68531) (by norm_num)
theorem B149989 : Blo 131789 149989 := bbase (se 4 (by rfl) ⟨14061, by rfl⟩ : syracuseStep 149989 = 28123) (by norm_num)
theorem B150025 : Blo 131789 150025 := bbase (se 2 (by rfl) ⟨56259, by rfl⟩ : syracuseStep 150025 = 112519) (by norm_num)
theorem B150061 : Blo 131789 150061 := bbase (se 3 (by rfl) ⟨28136, by rfl⟩ : syracuseStep 150061 = 56273) (by norm_num)
theorem B150097 : Blo 131789 150097 := bbase (se 2 (by rfl) ⟨56286, by rfl⟩ : syracuseStep 150097 = 112573) (by norm_num)
theorem B445013 : Blo 131789 445013 := bbase (se 8 (by rfl) ⟨2607, by rfl⟩ : syracuseStep 445013 = 5215) (by norm_num)
theorem B674405 : Blo 131789 674405 := bbase (se 4 (by rfl) ⟨63225, by rfl⟩ : syracuseStep 674405 = 126451) (by norm_num)
theorem B150133 : Blo 131789 150133 := bbase (se 5 (by rfl) ⟨7037, by rfl⟩ : syracuseStep 150133 = 14075) (by norm_num)
theorem B379525 : Blo 131789 379525 := bbase (se 4 (by rfl) ⟨35580, by rfl⟩ : syracuseStep 379525 = 71161) (by norm_num)
theorem B477845 : Blo 131789 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B1493653 : Blo 131789 1493653 := bbase (se 6 (by rfl) ⟨35007, by rfl⟩ : syracuseStep 1493653 = 70015) (by norm_num)
theorem B150169 : Blo 131789 150169 := bbase (se 2 (by rfl) ⟨56313, by rfl⟩ : syracuseStep 150169 = 112627) (by norm_num)
theorem B150205 : Blo 131789 150205 := bbase (se 3 (by rfl) ⟨28163, by rfl⟩ : syracuseStep 150205 = 56327) (by norm_num)
theorem B150241 : Blo 131789 150241 := bbase (se 2 (by rfl) ⟨56340, by rfl⟩ : syracuseStep 150241 = 112681) (by norm_num)
theorem B150277 : Blo 131789 150277 := bbase (se 4 (by rfl) ⟨14088, by rfl⟩ : syracuseStep 150277 = 28177) (by norm_num)
theorem B510725 : Blo 131789 510725 := bbase (se 4 (by rfl) ⟨47880, by rfl⟩ : syracuseStep 510725 = 95761) (by norm_num)
theorem B150313 : Blo 131789 150313 := bbase (se 2 (by rfl) ⟨56367, by rfl⟩ : syracuseStep 150313 = 112735) (by norm_num)
theorem B150341 : Blo 131789 150341 := bbase (se 4 (by rfl) ⟨14094, by rfl⟩ : syracuseStep 150341 = 28189) (by norm_num)
theorem B150349 : Blo 131789 150349 := bbase (se 3 (by rfl) ⟨28190, by rfl⟩ : syracuseStep 150349 = 56381) (by norm_num)
theorem B150385 : Blo 131789 150385 := bbase (se 2 (by rfl) ⟨56394, by rfl⟩ : syracuseStep 150385 = 112789) (by norm_num)
theorem B150421 : Blo 131789 150421 := bbase (se 6 (by rfl) ⟨3525, by rfl⟩ : syracuseStep 150421 = 7051) (by norm_num)
theorem B150457 : Blo 131789 150457 := bbase (se 2 (by rfl) ⟨56421, by rfl⟩ : syracuseStep 150457 = 112843) (by norm_num)
theorem B150493 : Blo 131789 150493 := bbase (se 3 (by rfl) ⟨28217, by rfl⟩ : syracuseStep 150493 = 56435) (by norm_num)
theorem B150529 : Blo 131789 150529 := bbase (se 2 (by rfl) ⟨56448, by rfl⟩ : syracuseStep 150529 = 112897) (by norm_num)
theorem B445445 : Blo 131789 445445 := bbase (se 4 (by rfl) ⟨41760, by rfl⟩ : syracuseStep 445445 = 83521) (by norm_num)
theorem B150565 : Blo 131789 150565 := bbase (se 4 (by rfl) ⟨14115, by rfl⟩ : syracuseStep 150565 = 28231) (by norm_num)
theorem B281645 : Blo 131789 281645 := bbase (se 3 (by rfl) ⟨52808, by rfl⟩ : syracuseStep 281645 = 105617) (by norm_num)
theorem B150601 : Blo 131789 150601 := bbase (se 2 (by rfl) ⟨56475, by rfl⟩ : syracuseStep 150601 = 112951) (by norm_num)
theorem B150637 : Blo 131789 150637 := bbase (se 3 (by rfl) ⟨28244, by rfl⟩ : syracuseStep 150637 = 56489) (by norm_num)
theorem B150673 : Blo 131789 150673 := bbase (se 2 (by rfl) ⟨56502, by rfl⟩ : syracuseStep 150673 = 113005) (by norm_num)
theorem B183461 : Blo 131789 183461 := bbase (se 4 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 183461 = 34399) (by norm_num)
theorem B150709 : Blo 131789 150709 := bbase (se 5 (by rfl) ⟨7064, by rfl⟩ : syracuseStep 150709 = 14129) (by norm_num)
theorem B773333 : Blo 131789 773333 := bbase (se 7 (by rfl) ⟨9062, by rfl⟩ : syracuseStep 773333 = 18125) (by norm_num)
theorem B150745 : Blo 131789 150745 := bbase (se 2 (by rfl) ⟨56529, by rfl⟩ : syracuseStep 150745 = 113059) (by norm_num)
theorem B150781 : Blo 131789 150781 := bbase (se 3 (by rfl) ⟨28271, by rfl⟩ : syracuseStep 150781 = 56543) (by norm_num)
theorem B150817 : Blo 131789 150817 := bbase (se 2 (by rfl) ⟨56556, by rfl⟩ : syracuseStep 150817 = 113113) (by norm_num)
theorem B576821 : Blo 131789 576821 := bbase (se 5 (by rfl) ⟨27038, by rfl⟩ : syracuseStep 576821 = 54077) (by norm_num)
theorem B216373 : Blo 131789 216373 := bbase (se 5 (by rfl) ⟨10142, by rfl⟩ : syracuseStep 216373 = 20285) (by norm_num)
theorem B150853 : Blo 131789 150853 := bbase (se 4 (by rfl) ⟨14142, by rfl⟩ : syracuseStep 150853 = 28285) (by norm_num)
theorem B150889 : Blo 131789 150889 := bbase (se 2 (by rfl) ⟨56583, by rfl⟩ : syracuseStep 150889 = 113167) (by norm_num)
theorem B150925 : Blo 131789 150925 := bbase (se 3 (by rfl) ⟨28298, by rfl⟩ : syracuseStep 150925 = 56597) (by norm_num)
theorem B150961 : Blo 131789 150961 := bbase (se 2 (by rfl) ⟨56610, by rfl⟩ : syracuseStep 150961 = 113221) (by norm_num)
theorem B445877 : Blo 131789 445877 := bbase (se 5 (by rfl) ⟨20900, by rfl⟩ : syracuseStep 445877 = 41801) (by norm_num)
theorem B150997 : Blo 131789 150997 := bbase (se 7 (by rfl) ⟨1769, by rfl⟩ : syracuseStep 150997 = 3539) (by norm_num)
theorem B151033 : Blo 131789 151033 := bbase (se 2 (by rfl) ⟨56637, by rfl⟩ : syracuseStep 151033 = 113275) (by norm_num)
theorem B151069 : Blo 131789 151069 := bbase (se 3 (by rfl) ⟨28325, by rfl⟩ : syracuseStep 151069 = 56651) (by norm_num)
theorem B151105 : Blo 131789 151105 := bbase (se 2 (by rfl) ⟨56664, by rfl⟩ : syracuseStep 151105 = 113329) (by norm_num)
theorem B216677 : Blo 131789 216677 := bbase (se 4 (by rfl) ⟨20313, by rfl⟩ : syracuseStep 216677 = 40627) (by norm_num)
theorem B151141 : Blo 131789 151141 := bbase (se 4 (by rfl) ⟨14169, by rfl⟩ : syracuseStep 151141 = 28339) (by norm_num)
theorem B151177 : Blo 131789 151177 := bbase (se 2 (by rfl) ⟨56691, by rfl⟩ : syracuseStep 151177 = 113383) (by norm_num)
theorem B151213 : Blo 131789 151213 := bbase (se 3 (by rfl) ⟨28352, by rfl⟩ : syracuseStep 151213 = 56705) (by norm_num)
theorem B151249 : Blo 131789 151249 := bbase (se 2 (by rfl) ⟨56718, by rfl⟩ : syracuseStep 151249 = 113437) (by norm_num)
theorem B380629 : Blo 131789 380629 := bbase (se 7 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 380629 = 8921) (by norm_num)
theorem B642773 : Blo 131789 642773 := bbase (se 7 (by rfl) ⟨7532, by rfl⟩ : syracuseStep 642773 = 15065) (by norm_num)
theorem B151285 : Blo 131789 151285 := bbase (se 5 (by rfl) ⟨7091, by rfl⟩ : syracuseStep 151285 = 14183) (by norm_num)
theorem B216821 : Blo 131789 216821 := bbase (se 5 (by rfl) ⟨10163, by rfl⟩ : syracuseStep 216821 = 20327) (by norm_num)
theorem B151321 : Blo 131789 151321 := bbase (se 2 (by rfl) ⟨56745, by rfl⟩ : syracuseStep 151321 = 113491) (by norm_num)
theorem B151357 : Blo 131789 151357 := bbase (se 3 (by rfl) ⟨28379, by rfl⟩ : syracuseStep 151357 = 56759) (by norm_num)
theorem B151393 : Blo 131789 151393 := bbase (se 2 (by rfl) ⟨56772, by rfl⟩ : syracuseStep 151393 = 113545) (by norm_num)
theorem B446309 : Blo 131789 446309 := bbase (se 4 (by rfl) ⟨41841, by rfl⟩ : syracuseStep 446309 = 83683) (by norm_num)
theorem B675701 : Blo 131789 675701 := bbase (se 5 (by rfl) ⟨31673, by rfl⟩ : syracuseStep 675701 = 63347) (by norm_num)
theorem B151429 : Blo 131789 151429 := bbase (se 4 (by rfl) ⟨14196, by rfl⟩ : syracuseStep 151429 = 28393) (by norm_num)
theorem B282533 : Blo 131789 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B151465 : Blo 131789 151465 := bbase (se 2 (by rfl) ⟨56799, by rfl⟩ : syracuseStep 151465 = 113599) (by norm_num)
theorem B151501 : Blo 131789 151501 := bbase (se 3 (by rfl) ⟨28406, by rfl⟩ : syracuseStep 151501 = 56813) (by norm_num)
theorem B151537 : Blo 131789 151537 := bbase (se 2 (by rfl) ⟨56826, by rfl⟩ : syracuseStep 151537 = 113653) (by norm_num)
theorem B151573 : Blo 131789 151573 := bbase (se 6 (by rfl) ⟨3552, by rfl⟩ : syracuseStep 151573 = 7105) (by norm_num)
theorem B151609 : Blo 131789 151609 := bbase (se 2 (by rfl) ⟨56853, by rfl⟩ : syracuseStep 151609 = 113707) (by norm_num)
theorem B151645 : Blo 131789 151645 := bbase (se 3 (by rfl) ⟨28433, by rfl⟩ : syracuseStep 151645 = 56867) (by norm_num)
theorem B151681 : Blo 131789 151681 := bbase (se 2 (by rfl) ⟨56880, by rfl⟩ : syracuseStep 151681 = 113761) (by norm_num)
theorem B282773 : Blo 131789 282773 := bbase (se 6 (by rfl) ⟨6627, by rfl⟩ : syracuseStep 282773 = 13255) (by norm_num)
theorem B151717 : Blo 131789 151717 := bbase (se 4 (by rfl) ⟨14223, by rfl⟩ : syracuseStep 151717 = 28447) (by norm_num)
theorem B479429 : Blo 131789 479429 := bbase (se 4 (by rfl) ⟨44946, by rfl⟩ : syracuseStep 479429 = 89893) (by norm_num)
theorem B151753 : Blo 131789 151753 := bbase (se 2 (by rfl) ⟨56907, by rfl⟩ : syracuseStep 151753 = 113815) (by norm_num)
theorem B184541 : Blo 131789 184541 := bbase (se 3 (by rfl) ⟨34601, by rfl⟩ : syracuseStep 184541 = 69203) (by norm_num)
theorem B151789 : Blo 131789 151789 := bbase (se 3 (by rfl) ⟨28460, by rfl⟩ : syracuseStep 151789 = 56921) (by norm_num)
theorem B151825 : Blo 131789 151825 := bbase (se 2 (by rfl) ⟨56934, by rfl⟩ : syracuseStep 151825 = 113869) (by norm_num)
theorem B446741 : Blo 131789 446741 := bbase (se 6 (by rfl) ⟨10470, by rfl⟩ : syracuseStep 446741 = 20941) (by norm_num)
theorem B577813 : Blo 131789 577813 := bbase (se 6 (by rfl) ⟨13542, by rfl⟩ : syracuseStep 577813 = 27085) (by norm_num)
theorem B151861 : Blo 131789 151861 := bbase (se 5 (by rfl) ⟨7118, by rfl⟩ : syracuseStep 151861 = 14237) (by norm_num)
theorem B151877 : Blo 131789 151877 := bbase (se 4 (by rfl) ⟨14238, by rfl⟩ : syracuseStep 151877 = 28477) (by norm_num)
theorem B151897 : Blo 131789 151897 := bbase (se 2 (by rfl) ⟨56961, by rfl⟩ : syracuseStep 151897 = 113923) (by norm_num)
theorem B250229 : Blo 131789 250229 := bbase (se 5 (by rfl) ⟨11729, by rfl⟩ : syracuseStep 250229 = 23459) (by norm_num)
theorem B151933 : Blo 131789 151933 := bbase (se 3 (by rfl) ⟨28487, by rfl⟩ : syracuseStep 151933 = 56975) (by norm_num)
theorem B151969 : Blo 131789 151969 := bbase (se 2 (by rfl) ⟨56988, by rfl⟩ : syracuseStep 151969 = 113977) (by norm_num)
theorem B152005 : Blo 131789 152005 := bbase (se 4 (by rfl) ⟨14250, by rfl⟩ : syracuseStep 152005 = 28501) (by norm_num)
theorem B152041 : Blo 131789 152041 := bbase (se 2 (by rfl) ⟨57015, by rfl⟩ : syracuseStep 152041 = 114031) (by norm_num)
theorem B250381 : Blo 131789 250381 := bbase (se 3 (by rfl) ⟨46946, by rfl⟩ : syracuseStep 250381 = 93893) (by norm_num)
theorem B152077 : Blo 131789 152077 := bbase (se 3 (by rfl) ⟨28514, by rfl⟩ : syracuseStep 152077 = 57029) (by norm_num)
theorem B152113 : Blo 131789 152113 := bbase (se 2 (by rfl) ⟨57042, by rfl⟩ : syracuseStep 152113 = 114085) (by norm_num)
theorem B152149 : Blo 131789 152149 := bbase (se 8 (by rfl) ⟨891, by rfl⟩ : syracuseStep 152149 = 1783) (by norm_num)
theorem B152185 : Blo 131789 152185 := bbase (se 2 (by rfl) ⟨57069, by rfl⟩ : syracuseStep 152185 = 114139) (by norm_num)
theorem B283277 : Blo 131789 283277 := bbase (se 3 (by rfl) ⟨53114, by rfl⟩ : syracuseStep 283277 = 106229) (by norm_num)
theorem B283285 : Blo 131789 283285 := bbase (se 6 (by rfl) ⟨6639, by rfl⟩ : syracuseStep 283285 = 13279) (by norm_num)
theorem B152221 : Blo 131789 152221 := bbase (se 3 (by rfl) ⟨28541, by rfl⟩ : syracuseStep 152221 = 57083) (by norm_num)
theorem B152257 : Blo 131789 152257 := bbase (se 2 (by rfl) ⟨57096, by rfl⟩ : syracuseStep 152257 = 114193) (by norm_num)
theorem B447173 : Blo 131789 447173 := bbase (se 4 (by rfl) ⟨41922, by rfl⟩ : syracuseStep 447173 = 83845) (by norm_num)
theorem B152293 : Blo 131789 152293 := bbase (se 4 (by rfl) ⟨14277, by rfl⟩ : syracuseStep 152293 = 28555) (by norm_num)
theorem B152329 : Blo 131789 152329 := bbase (se 2 (by rfl) ⟨57123, by rfl⟩ : syracuseStep 152329 = 114247) (by norm_num)
theorem B152365 : Blo 131789 152365 := bbase (se 3 (by rfl) ⟨28568, by rfl⟩ : syracuseStep 152365 = 57137) (by norm_num)
theorem B250685 : Blo 131789 250685 := bbase (se 3 (by rfl) ⟨47003, by rfl⟩ : syracuseStep 250685 = 94007) (by norm_num)
theorem B512837 : Blo 131789 512837 := bbase (se 4 (by rfl) ⟨48078, by rfl⟩ : syracuseStep 512837 = 96157) (by norm_num)
theorem B152401 : Blo 131789 152401 := bbase (se 2 (by rfl) ⟨57150, by rfl⟩ : syracuseStep 152401 = 114301) (by norm_num)
theorem B152437 : Blo 131789 152437 := bbase (se 5 (by rfl) ⟨7145, by rfl⟩ : syracuseStep 152437 = 14291) (by norm_num)
theorem B152473 : Blo 131789 152473 := bbase (se 2 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 152473 = 114355) (by norm_num)
theorem B152509 : Blo 131789 152509 := bbase (se 3 (by rfl) ⟨28595, by rfl⟩ : syracuseStep 152509 = 57191) (by norm_num)
theorem B152545 : Blo 131789 152545 := bbase (se 2 (by rfl) ⟨57204, by rfl⟩ : syracuseStep 152545 = 114409) (by norm_num)
theorem B152581 : Blo 131789 152581 := bbase (se 4 (by rfl) ⟨14304, by rfl⟩ : syracuseStep 152581 = 28609) (by norm_num)
theorem B152617 : Blo 131789 152617 := bbase (se 2 (by rfl) ⟨57231, by rfl⟩ : syracuseStep 152617 = 114463) (by norm_num)
theorem B152653 : Blo 131789 152653 := bbase (se 3 (by rfl) ⟨28622, by rfl⟩ : syracuseStep 152653 = 57245) (by norm_num)
theorem B513125 : Blo 131789 513125 := bbase (se 4 (by rfl) ⟨48105, by rfl⟩ : syracuseStep 513125 = 96211) (by norm_num)
theorem B152689 : Blo 131789 152689 := bbase (se 2 (by rfl) ⟨57258, by rfl⟩ : syracuseStep 152689 = 114517) (by norm_num)
theorem B447605 : Blo 131789 447605 := bbase (se 5 (by rfl) ⟨20981, by rfl⟩ : syracuseStep 447605 = 41963) (by norm_num)
theorem B676997 : Blo 131789 676997 := bbase (se 4 (by rfl) ⟨63468, by rfl⟩ : syracuseStep 676997 = 126937) (by norm_num)
theorem B152725 : Blo 131789 152725 := bbase (se 6 (by rfl) ⟨3579, by rfl⟩ : syracuseStep 152725 = 7159) (by norm_num)
theorem B382133 : Blo 131789 382133 := bbase (se 5 (by rfl) ⟨17912, by rfl⟩ : syracuseStep 382133 = 35825) (by norm_num)
theorem B152761 : Blo 131789 152761 := bbase (se 2 (by rfl) ⟨57285, by rfl⟩ : syracuseStep 152761 = 114571) (by norm_num)
theorem B1267093 : Blo 131789 1267093 := bbase (se 6 (by rfl) ⟨29697, by rfl⟩ : syracuseStep 1267093 = 59395) (by norm_num)
theorem B448037 : Blo 131789 448037 := bbase (se 4 (by rfl) ⟨42003, by rfl⟩ : syracuseStep 448037 = 84007) (by norm_num)
theorem B251437 : Blo 131789 251437 := bbase (se 3 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 251437 = 94289) (by norm_num)
theorem B874037 : Blo 131789 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B316997 : Blo 131789 316997 := bbase (se 4 (by rfl) ⟨29718, by rfl⟩ : syracuseStep 316997 = 59437) (by norm_num)
theorem B644773 : Blo 131789 644773 := bbase (se 4 (by rfl) ⟨60447, by rfl⟩ : syracuseStep 644773 = 120895) (by norm_num)
theorem B251581 : Blo 131789 251581 := bbase (se 3 (by rfl) ⟨47171, by rfl⟩ : syracuseStep 251581 = 94343) (by norm_num)
theorem B906997 : Blo 131789 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B284413 : Blo 131789 284413 := bbase (se 3 (by rfl) ⟨53327, by rfl⟩ : syracuseStep 284413 = 106655) (by norm_num)
theorem B251741 : Blo 131789 251741 := bbase (se 3 (by rfl) ⟨47201, by rfl⟩ : syracuseStep 251741 = 94403) (by norm_num)
theorem B448469 : Blo 131789 448469 := bbase (se 7 (by rfl) ⟨5255, by rfl⟩ : syracuseStep 448469 = 10511) (by norm_num)
theorem B251885 : Blo 131789 251885 := bbase (se 3 (by rfl) ⟨47228, by rfl⟩ : syracuseStep 251885 = 94457) (by norm_num)
theorem B1136693 : Blo 131789 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B284789 : Blo 131789 284789 := bbase (se 5 (by rfl) ⟨13349, by rfl⟩ : syracuseStep 284789 = 26699) (by norm_num)
theorem B153793 : Blo 131789 153793 := bbase (se 2 (by rfl) ⟨57672, by rfl⟩ : syracuseStep 153793 = 115345) (by norm_num)
theorem B514309 : Blo 131789 514309 := bbase (se 4 (by rfl) ⟨48216, by rfl⟩ : syracuseStep 514309 = 96433) (by norm_num)
theorem B252173 : Blo 131789 252173 := bbase (se 3 (by rfl) ⟨47282, by rfl⟩ : syracuseStep 252173 = 94565) (by norm_num)
theorem B481589 : Blo 131789 481589 := bbase (se 5 (by rfl) ⟨22574, by rfl⟩ : syracuseStep 481589 = 45149) (by norm_num)
theorem B317765 : Blo 131789 317765 := bbase (se 4 (by rfl) ⟨29790, by rfl⟩ : syracuseStep 317765 = 59581) (by norm_num)
theorem B317773 : Blo 131789 317773 := bbase (se 3 (by rfl) ⟨59582, by rfl⟩ : syracuseStep 317773 = 119165) (by norm_num)
theorem B448901 : Blo 131789 448901 := bbase (se 4 (by rfl) ⟨42084, by rfl⟩ : syracuseStep 448901 = 84169) (by norm_num)
theorem B678293 : Blo 131789 678293 := bbase (se 6 (by rfl) ⟨15897, by rfl⟩ : syracuseStep 678293 = 31795) (by norm_num)
theorem B252325 : Blo 131789 252325 := bbase (se 4 (by rfl) ⟨23655, by rfl⟩ : syracuseStep 252325 = 47311) (by norm_num)
theorem B514613 : Blo 131789 514613 := bbase (se 5 (by rfl) ⟨24122, by rfl⟩ : syracuseStep 514613 = 48245) (by norm_num)
theorem B252629 : Blo 131789 252629 := bbase (se 7 (by rfl) ⟨2960, by rfl⟩ : syracuseStep 252629 = 5921) (by norm_num)
theorem B383717 : Blo 131789 383717 := bbase (se 4 (by rfl) ⟨35973, by rfl⟩ : syracuseStep 383717 = 71947) (by norm_num)
theorem B449333 : Blo 131789 449333 := bbase (se 5 (by rfl) ⟨21062, by rfl⟩ : syracuseStep 449333 = 42125) (by norm_num)
theorem B318581 : Blo 131789 318581 := bbase (se 5 (by rfl) ⟨14933, by rfl⟩ : syracuseStep 318581 = 29867) (by norm_num)
theorem B154829 : Blo 131789 154829 := bbase (se 3 (by rfl) ⟨29030, by rfl⟩ : syracuseStep 154829 = 58061) (by norm_num)
theorem B449765 : Blo 131789 449765 := bbase (se 4 (by rfl) ⟨42165, by rfl⟩ : syracuseStep 449765 = 84331) (by norm_num)
theorem B384389 : Blo 131789 384389 := bbase (se 4 (by rfl) ⟨36036, by rfl⟩ : syracuseStep 384389 = 72073) (by norm_num)
theorem B253381 : Blo 131789 253381 := bbase (se 4 (by rfl) ⟨23754, by rfl⟩ : syracuseStep 253381 = 47509) (by norm_num)
theorem B482773 : Blo 131789 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B187877 : Blo 131789 187877 := bbase (se 4 (by rfl) ⟨17613, by rfl⟩ : syracuseStep 187877 = 35227) (by norm_num)
theorem B187957 : Blo 131789 187957 := bbase (se 5 (by rfl) ⟨8810, by rfl⟩ : syracuseStep 187957 = 17621) (by norm_num)
theorem B253525 : Blo 131789 253525 := bbase (se 8 (by rfl) ⟨1485, by rfl⟩ : syracuseStep 253525 = 2971) (by norm_num)
theorem B482917 : Blo 131789 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B450197 : Blo 131789 450197 := bbase (se 6 (by rfl) ⟨10551, by rfl⟩ : syracuseStep 450197 = 21103) (by norm_num)
theorem B679589 : Blo 131789 679589 := bbase (se 4 (by rfl) ⟨63711, by rfl⟩ : syracuseStep 679589 = 127423) (by norm_num)
theorem B188077 : Blo 131789 188077 := bbase (se 3 (by rfl) ⟨35264, by rfl⟩ : syracuseStep 188077 = 70529) (by norm_num)
theorem B286429 : Blo 131789 286429 := bbase (se 3 (by rfl) ⟨53705, by rfl⟩ : syracuseStep 286429 = 107411) (by norm_num)
theorem B253685 : Blo 131789 253685 := bbase (se 5 (by rfl) ⟨11891, by rfl⟩ : syracuseStep 253685 = 23783) (by norm_num)
theorem B351989 : Blo 131789 351989 := bbase (se 5 (by rfl) ⟨16499, by rfl⟩ : syracuseStep 351989 = 32999) (by norm_num)
theorem B188173 : Blo 131789 188173 := bbase (se 3 (by rfl) ⟨35282, by rfl⟩ : syracuseStep 188173 = 70565) (by norm_num)
theorem B384821 : Blo 131789 384821 := bbase (se 5 (by rfl) ⟨18038, by rfl⟩ : syracuseStep 384821 = 36077) (by norm_num)
theorem B1007477 : Blo 131789 1007477 := bbase (se 5 (by rfl) ⟨47225, by rfl⟩ : syracuseStep 1007477 = 94451) (by norm_num)
theorem B253829 : Blo 131789 253829 := bbase (se 4 (by rfl) ⟨23796, by rfl⟩ : syracuseStep 253829 = 47593) (by norm_num)
theorem B450629 : Blo 131789 450629 := bbase (se 4 (by rfl) ⟨42246, by rfl⟩ : syracuseStep 450629 = 84493) (by norm_num)
theorem B286805 : Blo 131789 286805 := bbase (se 8 (by rfl) ⟨1680, by rfl⟩ : syracuseStep 286805 = 3361) (by norm_num)
theorem B647317 : Blo 131789 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B254117 : Blo 131789 254117 := bbase (se 4 (by rfl) ⟨23823, by rfl⟩ : syracuseStep 254117 = 47647) (by norm_num)
theorem B188669 : Blo 131789 188669 := bbase (se 3 (by rfl) ⟨35375, by rfl⟩ : syracuseStep 188669 = 70751) (by norm_num)
theorem B254269 : Blo 131789 254269 := bbase (se 3 (by rfl) ⟨47675, by rfl⟩ : syracuseStep 254269 = 95351) (by norm_num)
theorem B451061 : Blo 131789 451061 := bbase (se 5 (by rfl) ⟨21143, by rfl⟩ : syracuseStep 451061 = 42287) (by norm_num)
theorem B1237493 : Blo 131789 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B385573 : Blo 131789 385573 := bbase (se 4 (by rfl) ⟨36147, by rfl⟩ : syracuseStep 385573 = 72295) (by norm_num)
theorem B287317 : Blo 131789 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B254573 : Blo 131789 254573 := bbase (se 3 (by rfl) ⟨47732, by rfl⟩ : syracuseStep 254573 = 95465) (by norm_num)
theorem B221869 : Blo 131789 221869 := bbase (se 3 (by rfl) ⟨41600, by rfl⟩ : syracuseStep 221869 = 83201) (by norm_num)
theorem B1237781 : Blo 131789 1237781 := bbase (se 6 (by rfl) ⟨29010, by rfl⟩ : syracuseStep 1237781 = 58021) (by norm_num)
theorem B189221 : Blo 131789 189221 := bbase (se 4 (by rfl) ⟨17739, by rfl⟩ : syracuseStep 189221 = 35479) (by norm_num)
theorem B451493 : Blo 131789 451493 := bbase (se 4 (by rfl) ⟨42327, by rfl⟩ : syracuseStep 451493 = 84655) (by norm_num)
theorem B680885 : Blo 131789 680885 := bbase (se 5 (by rfl) ⟨31916, by rfl⟩ : syracuseStep 680885 = 63833) (by norm_num)
theorem B1139669 : Blo 131789 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B287813 : Blo 131789 287813 := bbase (se 4 (by rfl) ⟨26982, by rfl⟩ : syracuseStep 287813 = 53965) (by norm_num)
theorem B222493 : Blo 131789 222493 := bbase (se 3 (by rfl) ⟨41717, by rfl⟩ : syracuseStep 222493 = 83435) (by norm_num)
theorem B451925 : Blo 131789 451925 := bbase (se 12 (by rfl) ⟨165, by rfl⟩ : syracuseStep 451925 = 331) (by norm_num)
theorem B255325 : Blo 131789 255325 := bbase (se 3 (by rfl) ⟨47873, by rfl⟩ : syracuseStep 255325 = 95747) (by norm_num)
theorem B222581 : Blo 131789 222581 := bbase (se 5 (by rfl) ⟨10433, by rfl⟩ : syracuseStep 222581 = 20867) (by norm_num)
theorem B255469 : Blo 131789 255469 := bbase (se 3 (by rfl) ⟨47900, by rfl⟩ : syracuseStep 255469 = 95801) (by norm_num)
theorem B222709 : Blo 131789 222709 := bbase (se 5 (by rfl) ⟨10439, by rfl⟩ : syracuseStep 222709 = 20879) (by norm_num)
theorem B189973 : Blo 131789 189973 := bbase (se 6 (by rfl) ⟨4452, by rfl⟩ : syracuseStep 189973 = 8905) (by norm_num)
theorem B222797 : Blo 131789 222797 := bbase (se 3 (by rfl) ⟨41774, by rfl⟩ : syracuseStep 222797 = 83549) (by norm_num)
theorem B255629 : Blo 131789 255629 := bbase (se 3 (by rfl) ⟨47930, by rfl⟩ : syracuseStep 255629 = 95861) (by norm_num)
theorem B222925 : Blo 131789 222925 := bbase (se 3 (by rfl) ⟨41798, by rfl⟩ : syracuseStep 222925 = 83597) (by norm_num)
theorem B452357 : Blo 131789 452357 := bbase (se 4 (by rfl) ⟨42408, by rfl⟩ : syracuseStep 452357 = 84817) (by norm_num)
theorem B255773 : Blo 131789 255773 := bbase (se 3 (by rfl) ⟨47957, by rfl⟩ : syracuseStep 255773 = 95915) (by norm_num)
theorem B223013 : Blo 131789 223013 := bbase (se 4 (by rfl) ⟨20907, by rfl⟩ : syracuseStep 223013 = 41815) (by norm_num)
theorem B321349 : Blo 131789 321349 := bbase (se 4 (by rfl) ⟨30126, by rfl⟩ : syracuseStep 321349 = 60253) (by norm_num)
theorem B223141 : Blo 131789 223141 := bbase (se 4 (by rfl) ⟨20919, by rfl⟩ : syracuseStep 223141 = 41839) (by norm_num)
theorem B288677 : Blo 131789 288677 := bbase (se 4 (by rfl) ⟨27063, by rfl⟩ : syracuseStep 288677 = 54127) (by norm_num)
theorem B223229 : Blo 131789 223229 := bbase (se 3 (by rfl) ⟨41855, by rfl⟩ : syracuseStep 223229 = 83711) (by norm_num)
theorem B288821 : Blo 131789 288821 := bbase (se 5 (by rfl) ⟨13538, by rfl⟩ : syracuseStep 288821 = 27077) (by norm_num)
theorem B256061 : Blo 131789 256061 := bbase (se 3 (by rfl) ⟨48011, by rfl⟩ : syracuseStep 256061 = 96023) (by norm_num)
theorem B223357 : Blo 131789 223357 := bbase (se 3 (by rfl) ⟨41879, by rfl⟩ : syracuseStep 223357 = 83759) (by norm_num)
theorem B452789 : Blo 131789 452789 := bbase (se 5 (by rfl) ⟨21224, by rfl⟩ : syracuseStep 452789 = 42449) (by norm_num)
theorem B682181 : Blo 131789 682181 := bbase (se 4 (by rfl) ⟨63954, by rfl⟩ : syracuseStep 682181 = 127909) (by norm_num)
theorem B223445 : Blo 131789 223445 := bbase (se 7 (by rfl) ⟨2618, by rfl⟩ : syracuseStep 223445 = 5237) (by norm_num)
theorem B256213 : Blo 131789 256213 := bbase (se 7 (by rfl) ⟨3002, by rfl⟩ : syracuseStep 256213 = 6005) (by norm_num)
theorem B190765 : Blo 131789 190765 := bbase (se 3 (by rfl) ⟨35768, by rfl⟩ : syracuseStep 190765 = 71537) (by norm_num)
theorem B321869 : Blo 131789 321869 := bbase (se 3 (by rfl) ⟨60350, by rfl⟩ : syracuseStep 321869 = 120701) (by norm_num)
theorem B223573 : Blo 131789 223573 := bbase (se 10 (by rfl) ⟨327, by rfl⟩ : syracuseStep 223573 = 655) (by norm_num)
theorem B223661 : Blo 131789 223661 := bbase (se 3 (by rfl) ⟨41936, by rfl⟩ : syracuseStep 223661 = 83873) (by norm_num)
theorem B321965 : Blo 131789 321965 := bbase (se 3 (by rfl) ⟨60368, by rfl⟩ : syracuseStep 321965 = 120737) (by norm_num)
theorem B256493 : Blo 131789 256493 := bbase (se 3 (by rfl) ⟨48092, by rfl⟩ : syracuseStep 256493 = 96185) (by norm_num)
theorem B256517 : Blo 131789 256517 := bbase (se 4 (by rfl) ⟨24048, by rfl⟩ : syracuseStep 256517 = 48097) (by norm_num)
theorem B223789 : Blo 131789 223789 := bbase (se 3 (by rfl) ⟨41960, by rfl⟩ : syracuseStep 223789 = 83921) (by norm_num)
theorem B453221 : Blo 131789 453221 := bbase (se 4 (by rfl) ⟨42489, by rfl⟩ : syracuseStep 453221 = 84979) (by norm_num)
theorem B813685 : Blo 131789 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B191101 : Blo 131789 191101 := bbase (se 3 (by rfl) ⟨35831, by rfl⟩ : syracuseStep 191101 = 71663) (by norm_num)
theorem B223877 : Blo 131789 223877 := bbase (se 4 (by rfl) ⟨20988, by rfl⟩ : syracuseStep 223877 = 41977) (by norm_num)
theorem B224005 : Blo 131789 224005 := bbase (se 4 (by rfl) ⟨21000, by rfl⟩ : syracuseStep 224005 = 42001) (by norm_num)
theorem B289565 : Blo 131789 289565 := bbase (se 3 (by rfl) ⟨54293, by rfl⟩ : syracuseStep 289565 = 108587) (by norm_num)
theorem B191317 : Blo 131789 191317 := bbase (se 9 (by rfl) ⟨560, by rfl⟩ : syracuseStep 191317 = 1121) (by norm_num)
theorem B224093 : Blo 131789 224093 := bbase (se 3 (by rfl) ⟨42017, by rfl⟩ : syracuseStep 224093 = 84035) (by norm_num)
theorem B224221 : Blo 131789 224221 := bbase (se 3 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 224221 = 84083) (by norm_num)
theorem B453653 : Blo 131789 453653 := bbase (se 6 (by rfl) ⟨10632, by rfl⟩ : syracuseStep 453653 = 21265) (by norm_num)
theorem B224309 : Blo 131789 224309 := bbase (se 5 (by rfl) ⟨10514, by rfl⟩ : syracuseStep 224309 = 21029) (by norm_num)
theorem B224437 : Blo 131789 224437 := bbase (se 5 (by rfl) ⟨10520, by rfl⟩ : syracuseStep 224437 = 21041) (by norm_num)
theorem B191693 : Blo 131789 191693 := bbase (se 3 (by rfl) ⟨35942, by rfl⟩ : syracuseStep 191693 = 71885) (by norm_num)
theorem B257269 : Blo 131789 257269 := bbase (se 5 (by rfl) ⟨12059, by rfl⟩ : syracuseStep 257269 = 24119) (by norm_num)
theorem B224525 : Blo 131789 224525 := bbase (se 3 (by rfl) ⟨42098, by rfl⟩ : syracuseStep 224525 = 84197) (by norm_num)
theorem B847189 : Blo 131789 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B159089 : Blo 131789 159089 := bbase (se 2 (by rfl) ⟨59658, by rfl⟩ : syracuseStep 159089 = 119317) (by norm_num)
theorem B257413 : Blo 131789 257413 := bbase (se 4 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 257413 = 48265) (by norm_num)
theorem B224653 : Blo 131789 224653 := bbase (se 3 (by rfl) ⟨42122, by rfl⟩ : syracuseStep 224653 = 84245) (by norm_num)
theorem B454085 : Blo 131789 454085 := bbase (se 4 (by rfl) ⟨42570, by rfl⟩ : syracuseStep 454085 = 85141) (by norm_num)
theorem B650693 : Blo 131789 650693 := bbase (se 4 (by rfl) ⟨61002, by rfl⟩ : syracuseStep 650693 = 122005) (by norm_num)
theorem B683477 : Blo 131789 683477 := bbase (se 7 (by rfl) ⟨8009, by rfl⟩ : syracuseStep 683477 = 16019) (by norm_num)
theorem B224741 : Blo 131789 224741 := bbase (se 4 (by rfl) ⟨21069, by rfl⟩ : syracuseStep 224741 = 42139) (by norm_num)
theorem B257573 : Blo 131789 257573 := bbase (se 4 (by rfl) ⟨24147, by rfl⟩ : syracuseStep 257573 = 48295) (by norm_num)
theorem B224869 : Blo 131789 224869 := bbase (se 4 (by rfl) ⟨21081, by rfl⟩ : syracuseStep 224869 = 42163) (by norm_num)
theorem B257717 : Blo 131789 257717 := bbase (se 5 (by rfl) ⟨12080, by rfl⟩ : syracuseStep 257717 = 24161) (by norm_num)
theorem B159421 : Blo 131789 159421 := bbase (se 3 (by rfl) ⟨29891, by rfl⟩ : syracuseStep 159421 = 59783) (by norm_num)
theorem B224957 : Blo 131789 224957 := bbase (se 3 (by rfl) ⟨42179, by rfl⟩ : syracuseStep 224957 = 84359) (by norm_num)
theorem B323309 : Blo 131789 323309 := bbase (se 3 (by rfl) ⟨60620, by rfl⟩ : syracuseStep 323309 = 121241) (by norm_num)
theorem B323357 : Blo 131789 323357 := bbase (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) (by norm_num)
theorem B225085 : Blo 131789 225085 := bbase (se 3 (by rfl) ⟨42203, by rfl⟩ : syracuseStep 225085 = 84407) (by norm_num)
theorem B454517 : Blo 131789 454517 := bbase (se 5 (by rfl) ⟨21305, by rfl⟩ : syracuseStep 454517 = 42611) (by norm_num)
theorem B225173 : Blo 131789 225173 := bbase (se 6 (by rfl) ⟨5277, by rfl⟩ : syracuseStep 225173 = 10555) (by norm_num)
theorem B225301 : Blo 131789 225301 := bbase (se 6 (by rfl) ⟨5280, by rfl⟩ : syracuseStep 225301 = 10561) (by norm_num)
theorem B225389 : Blo 131789 225389 := bbase (se 3 (by rfl) ⟨42260, by rfl⟩ : syracuseStep 225389 = 84521) (by norm_num)
theorem B258221 : Blo 131789 258221 := bbase (se 3 (by rfl) ⟨48416, by rfl⟩ : syracuseStep 258221 = 96833) (by norm_num)
theorem B225517 : Blo 131789 225517 := bbase (se 3 (by rfl) ⟨42284, by rfl⟩ : syracuseStep 225517 = 84569) (by norm_num)
theorem B454949 : Blo 131789 454949 := bbase (se 4 (by rfl) ⟨42651, by rfl⟩ : syracuseStep 454949 = 85303) (by norm_num)
theorem B520501 : Blo 131789 520501 := bbase (se 5 (by rfl) ⟨24398, by rfl⟩ : syracuseStep 520501 = 48797) (by norm_num)
theorem B225605 : Blo 131789 225605 := bbase (se 4 (by rfl) ⟨21150, by rfl⟩ : syracuseStep 225605 = 42301) (by norm_num)
theorem B225733 : Blo 131789 225733 := bbase (se 4 (by rfl) ⟨21162, by rfl⟩ : syracuseStep 225733 = 42325) (by norm_num)
theorem B225821 : Blo 131789 225821 := bbase (se 3 (by rfl) ⟨42341, by rfl⟩ : syracuseStep 225821 = 84683) (by norm_num)
theorem B225845 : Blo 131789 225845 := bbase (se 5 (by rfl) ⟨10586, by rfl⟩ : syracuseStep 225845 = 21173) (by norm_num)
theorem B160309 : Blo 131789 160309 := bbase (se 5 (by rfl) ⟨7514, by rfl⟩ : syracuseStep 160309 = 15029) (by norm_num)
theorem B193117 : Blo 131789 193117 := bbase (se 3 (by rfl) ⟨36209, by rfl⟩ : syracuseStep 193117 = 72419) (by norm_num)
theorem B225949 : Blo 131789 225949 := bbase (se 3 (by rfl) ⟨42365, by rfl⟩ : syracuseStep 225949 = 84731) (by norm_num)
theorem B422597 : Blo 131789 422597 := bbase (se 4 (by rfl) ⟨39618, by rfl⟩ : syracuseStep 422597 = 79237) (by norm_num)
theorem B455381 : Blo 131789 455381 := bbase (se 7 (by rfl) ⟨5336, by rfl⟩ : syracuseStep 455381 = 10673) (by norm_num)
theorem B684773 : Blo 131789 684773 := bbase (se 4 (by rfl) ⟨64197, by rfl⟩ : syracuseStep 684773 = 128395) (by norm_num)
theorem B226037 : Blo 131789 226037 := bbase (se 5 (by rfl) ⟨10595, by rfl⟩ : syracuseStep 226037 = 21191) (by norm_num)
theorem B226133 : Blo 131789 226133 := bbase (se 9 (by rfl) ⟨662, by rfl⟩ : syracuseStep 226133 = 1325) (by norm_num)
theorem B226165 : Blo 131789 226165 := bbase (se 5 (by rfl) ⟨10601, by rfl⟩ : syracuseStep 226165 = 21203) (by norm_num)
theorem B226253 : Blo 131789 226253 := bbase (se 3 (by rfl) ⟨42422, by rfl⟩ : syracuseStep 226253 = 84845) (by norm_num)
theorem B226381 : Blo 131789 226381 := bbase (se 3 (by rfl) ⟨42446, by rfl⟩ : syracuseStep 226381 = 84893) (by norm_num)
theorem B455813 : Blo 131789 455813 := bbase (se 4 (by rfl) ⟨42732, by rfl⟩ : syracuseStep 455813 = 85465) (by norm_num)
theorem B226469 : Blo 131789 226469 := bbase (se 4 (by rfl) ⟨21231, by rfl⟩ : syracuseStep 226469 = 42463) (by norm_num)
theorem B292069 : Blo 131789 292069 := bbase (se 4 (by rfl) ⟨27381, by rfl⟩ : syracuseStep 292069 = 54763) (by norm_num)
theorem B226597 : Blo 131789 226597 := bbase (se 4 (by rfl) ⟨21243, by rfl⟩ : syracuseStep 226597 = 42487) (by norm_num)
theorem B3437909 : Blo 131789 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B226685 : Blo 131789 226685 := bbase (se 3 (by rfl) ⟨42503, by rfl⟩ : syracuseStep 226685 = 85007) (by norm_num)
theorem B226813 : Blo 131789 226813 := bbase (se 3 (by rfl) ⟨42527, by rfl⟩ : syracuseStep 226813 = 85055) (by norm_num)
theorem B292405 : Blo 131789 292405 := bbase (se 5 (by rfl) ⟨13706, by rfl⟩ : syracuseStep 292405 = 27413) (by norm_num)
theorem B456245 : Blo 131789 456245 := bbase (se 5 (by rfl) ⟨21386, by rfl⟩ : syracuseStep 456245 = 42773) (by norm_num)
theorem B161357 : Blo 131789 161357 := bbase (se 3 (by rfl) ⟨30254, by rfl⟩ : syracuseStep 161357 = 60509) (by norm_num)
theorem B226901 : Blo 131789 226901 := bbase (se 8 (by rfl) ⟨1329, by rfl⟩ : syracuseStep 226901 = 2659) (by norm_num)
theorem B358037 : Blo 131789 358037 := bbase (se 6 (by rfl) ⟨8391, by rfl⟩ : syracuseStep 358037 = 16783) (by norm_num)
theorem B325309 : Blo 131789 325309 := bbase (se 3 (by rfl) ⟨60995, by rfl⟩ : syracuseStep 325309 = 121991) (by norm_num)
theorem B227029 : Blo 131789 227029 := bbase (se 7 (by rfl) ⟨2660, by rfl⟩ : syracuseStep 227029 = 5321) (by norm_num)
theorem B227117 : Blo 131789 227117 := bbase (se 3 (by rfl) ⟨42584, by rfl⟩ : syracuseStep 227117 = 85169) (by norm_num)
theorem B325453 : Blo 131789 325453 := bbase (se 3 (by rfl) ⟨61022, by rfl⟩ : syracuseStep 325453 = 122045) (by norm_num)
theorem B227245 : Blo 131789 227245 := bbase (se 3 (by rfl) ⟨42608, by rfl⟩ : syracuseStep 227245 = 85217) (by norm_num)
theorem B161713 : Blo 131789 161713 := bbase (se 2 (by rfl) ⟨60642, by rfl⟩ : syracuseStep 161713 = 121285) (by norm_num)
theorem B456677 : Blo 131789 456677 := bbase (se 4 (by rfl) ⟨42813, by rfl⟩ : syracuseStep 456677 = 85627) (by norm_num)
theorem B686069 : Blo 131789 686069 := bbase (se 5 (by rfl) ⟨32159, by rfl⟩ : syracuseStep 686069 = 64319) (by norm_num)
theorem B227333 : Blo 131789 227333 := bbase (se 4 (by rfl) ⟨21312, by rfl⟩ : syracuseStep 227333 = 42625) (by norm_num)
theorem B161905 : Blo 131789 161905 := bbase (se 2 (by rfl) ⟨60714, by rfl⟩ : syracuseStep 161905 = 121429) (by norm_num)
theorem B227461 : Blo 131789 227461 := bbase (se 4 (by rfl) ⟨21324, by rfl⟩ : syracuseStep 227461 = 42649) (by norm_num)
theorem B227549 : Blo 131789 227549 := bbase (se 3 (by rfl) ⟨42665, by rfl⟩ : syracuseStep 227549 = 85331) (by norm_num)
theorem B162049 : Blo 131789 162049 := bbase (se 2 (by rfl) ⟨60768, by rfl⟩ : syracuseStep 162049 = 121537) (by norm_num)
theorem B391493 : Blo 131789 391493 := bbase (se 4 (by rfl) ⟨36702, by rfl⟩ : syracuseStep 391493 = 73405) (by norm_num)
theorem B719189 : Blo 131789 719189 := bbase (se 10 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 719189 = 2107) (by norm_num)
theorem B1603925 : Blo 131789 1603925 := bbase (se 10 (by rfl) ⟨2349, by rfl⟩ : syracuseStep 1603925 = 4699) (by norm_num)
theorem B227677 : Blo 131789 227677 := bbase (se 3 (by rfl) ⟨42689, by rfl⟩ : syracuseStep 227677 = 85379) (by norm_num)
theorem B227701 : Blo 131789 227701 := bbase (se 5 (by rfl) ⟨10673, by rfl⟩ : syracuseStep 227701 = 21347) (by norm_num)
theorem B457109 : Blo 131789 457109 := bbase (se 6 (by rfl) ⟨10713, by rfl⟩ : syracuseStep 457109 = 21427) (by norm_num)
theorem B293285 : Blo 131789 293285 := bbase (se 4 (by rfl) ⟨27495, by rfl⟩ : syracuseStep 293285 = 54991) (by norm_num)
theorem B227765 : Blo 131789 227765 := bbase (se 5 (by rfl) ⟨10676, by rfl⟩ : syracuseStep 227765 = 21353) (by norm_num)
theorem B326069 : Blo 131789 326069 := bbase (se 5 (by rfl) ⟨15284, by rfl⟩ : syracuseStep 326069 = 30569) (by norm_num)
theorem B260597 : Blo 131789 260597 := bbase (se 5 (by rfl) ⟨12215, by rfl⟩ : syracuseStep 260597 = 24431) (by norm_num)
theorem B2423317 : Blo 131789 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B227893 : Blo 131789 227893 := bbase (se 5 (by rfl) ⟨10682, by rfl⟩ : syracuseStep 227893 = 21365) (by norm_num)
theorem B227981 : Blo 131789 227981 := bbase (se 3 (by rfl) ⟨42746, by rfl⟩ : syracuseStep 227981 = 85493) (by norm_num)
theorem B228109 : Blo 131789 228109 := bbase (se 3 (by rfl) ⟨42770, by rfl⟩ : syracuseStep 228109 = 85541) (by norm_num)
theorem B1178389 : Blo 131789 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B457541 : Blo 131789 457541 := bbase (se 4 (by rfl) ⟨42894, by rfl⟩ : syracuseStep 457541 = 85789) (by norm_num)
theorem B228197 : Blo 131789 228197 := bbase (se 4 (by rfl) ⟨21393, by rfl⟩ : syracuseStep 228197 = 42787) (by norm_num)
theorem B228325 : Blo 131789 228325 := bbase (se 4 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 228325 = 42811) (by norm_num)
theorem B326669 : Blo 131789 326669 := bbase (se 3 (by rfl) ⟨61250, by rfl⟩ : syracuseStep 326669 = 122501) (by norm_num)
theorem B228413 : Blo 131789 228413 := bbase (se 3 (by rfl) ⟨42827, by rfl⟩ : syracuseStep 228413 = 85655) (by norm_num)
theorem B326741 : Blo 131789 326741 := bbase (se 8 (by rfl) ⟨1914, by rfl⟩ : syracuseStep 326741 = 3829) (by norm_num)
theorem B228541 : Blo 131789 228541 := bbase (se 3 (by rfl) ⟨42851, by rfl⟩ : syracuseStep 228541 = 85703) (by norm_num)
theorem B457973 : Blo 131789 457973 := bbase (se 5 (by rfl) ⟨21467, by rfl⟩ : syracuseStep 457973 = 42935) (by norm_num)
theorem B687365 : Blo 131789 687365 := bbase (se 4 (by rfl) ⟨64440, by rfl⟩ : syracuseStep 687365 = 128881) (by norm_num)
theorem B228629 : Blo 131789 228629 := bbase (se 6 (by rfl) ⟨5358, by rfl⟩ : syracuseStep 228629 = 10717) (by norm_num)
theorem B228757 : Blo 131789 228757 := bbase (se 6 (by rfl) ⟨5361, by rfl⟩ : syracuseStep 228757 = 10723) (by norm_num)
theorem B1015253 : Blo 131789 1015253 := bbase (se 7 (by rfl) ⟨11897, by rfl⟩ : syracuseStep 1015253 = 23795) (by norm_num)
theorem B228845 : Blo 131789 228845 := bbase (se 3 (by rfl) ⟨42908, by rfl⟩ : syracuseStep 228845 = 85817) (by norm_num)
theorem B228973 : Blo 131789 228973 := bbase (se 3 (by rfl) ⟨42932, by rfl⟩ : syracuseStep 228973 = 85865) (by norm_num)
theorem B327293 : Blo 131789 327293 := bbase (se 3 (by rfl) ⟨61367, by rfl⟩ : syracuseStep 327293 = 122735) (by norm_num)
theorem B229061 : Blo 131789 229061 := bbase (se 4 (by rfl) ⟨21474, by rfl⟩ : syracuseStep 229061 = 42949) (by norm_num)
theorem B1408853 : Blo 131789 1408853 := bbase (se 9 (by rfl) ⟨4127, by rfl⟩ : syracuseStep 1408853 = 8255) (by norm_num)
theorem B229457 : Blo 131789 229457 := bstep (se 2 (by rfl) ⟨86046, by rfl⟩ : syracuseStep 229457 = 172093) B172093
theorem B688589 : Blo 131789 688589 := bstep (se 3 (by rfl) ⟨129110, by rfl⟩ : syracuseStep 688589 = 258221) B258221
theorem B131795 : Blo 131789 131795 := bstep (se 1 (by rfl) ⟨98846, by rfl⟩ : syracuseStep 131795 = 197693) B197693
theorem B131811 : Blo 131789 131811 := bstep (se 1 (by rfl) ⟨98858, by rfl⟩ : syracuseStep 131811 = 197717) B197717
theorem B131827 : Blo 131789 131827 := bstep (se 1 (by rfl) ⟨98870, by rfl⟩ : syracuseStep 131827 = 197741) B197741
theorem B131843 : Blo 131789 131843 := bstep (se 1 (by rfl) ⟨98882, by rfl⟩ : syracuseStep 131843 = 197765) B197765
theorem B131859 : Blo 131789 131859 := bstep (se 1 (by rfl) ⟨98894, by rfl⟩ : syracuseStep 131859 = 197789) B197789
theorem B131875 : Blo 131789 131875 := bstep (se 1 (by rfl) ⟨98906, by rfl⟩ : syracuseStep 131875 = 197813) B197813
theorem B131891 : Blo 131789 131891 := bstep (se 1 (by rfl) ⟨98918, by rfl⟩ : syracuseStep 131891 = 197837) B197837
theorem B131907 : Blo 131789 131907 := bstep (se 1 (by rfl) ⟨98930, by rfl⟩ : syracuseStep 131907 = 197861) B197861
theorem B131923 : Blo 131789 131923 := bstep (se 1 (by rfl) ⟨98942, by rfl⟩ : syracuseStep 131923 = 197885) B197885
theorem B131939 : Blo 131789 131939 := bstep (se 1 (by rfl) ⟨98954, by rfl⟩ : syracuseStep 131939 = 197909) B197909
theorem B1016675 : Blo 131789 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B131955 : Blo 131789 131955 := bstep (se 1 (by rfl) ⟨98966, by rfl⟩ : syracuseStep 131955 = 197933) B197933
theorem B131971 : Blo 131789 131971 := bstep (se 1 (by rfl) ⟨98978, by rfl⟩ : syracuseStep 131971 = 197957) B197957
theorem B623501 : Blo 131789 623501 := bstep (se 3 (by rfl) ⟨116906, by rfl⟩ : syracuseStep 623501 = 233813) B233813
theorem B295825 : Blo 131789 295825 := bstep (se 2 (by rfl) ⟨110934, by rfl⟩ : syracuseStep 295825 = 221869) B221869
theorem B131987 : Blo 131789 131987 := bstep (se 1 (by rfl) ⟨98990, by rfl⟩ : syracuseStep 131987 = 197981) B197981
theorem B132003 : Blo 131789 132003 := bstep (se 1 (by rfl) ⟨99002, by rfl⟩ : syracuseStep 132003 = 198005) B198005
theorem B132019 : Blo 131789 132019 := bstep (se 1 (by rfl) ⟨99014, by rfl⟩ : syracuseStep 132019 = 198029) B198029
theorem B132035 : Blo 131789 132035 := bstep (se 1 (by rfl) ⟨99026, by rfl⟩ : syracuseStep 132035 = 198053) B198053
theorem B1573829 : Blo 131789 1573829 := bstep (se 4 (by rfl) ⟨147546, by rfl⟩ : syracuseStep 1573829 = 295093) B295093
theorem B132051 : Blo 131789 132051 := bstep (se 1 (by rfl) ⟨99038, by rfl⟩ : syracuseStep 132051 = 198077) B198077
theorem B132067 : Blo 131789 132067 := bstep (se 1 (by rfl) ⟨99050, by rfl⟩ : syracuseStep 132067 = 198101) B198101
theorem B1541105 : Blo 131789 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B132083 : Blo 131789 132083 := bstep (se 1 (by rfl) ⟨99062, by rfl⟩ : syracuseStep 132083 = 198125) B198125
theorem B132099 : Blo 131789 132099 := bstep (se 1 (by rfl) ⟨99074, by rfl⟩ : syracuseStep 132099 = 198149) B198149
theorem B132115 : Blo 131789 132115 := bstep (se 1 (by rfl) ⟨99086, by rfl⟩ : syracuseStep 132115 = 198173) B198173
theorem B132131 : Blo 131789 132131 := bstep (se 1 (by rfl) ⟨99098, by rfl⟩ : syracuseStep 132131 = 198197) B198197
theorem B132147 : Blo 131789 132147 := bstep (se 1 (by rfl) ⟨99110, by rfl⟩ : syracuseStep 132147 = 198221) B198221
theorem B197699 : Blo 131789 197699 := bstep (se 1 (by rfl) ⟨148274, by rfl⟩ : syracuseStep 197699 = 296549) B296549
theorem B132163 : Blo 131789 132163 := bstep (se 1 (by rfl) ⟨99122, by rfl⟩ : syracuseStep 132163 = 198245) B198245
theorem B132179 : Blo 131789 132179 := bstep (se 1 (by rfl) ⟨99134, by rfl⟩ : syracuseStep 132179 = 198269) B198269
theorem B197729 : Blo 131789 197729 := bstep (se 2 (by rfl) ⟨74148, by rfl⟩ : syracuseStep 197729 = 148297) B148297
theorem B132195 : Blo 131789 132195 := bstep (se 1 (by rfl) ⟨99146, by rfl⟩ : syracuseStep 132195 = 198293) B198293
theorem B197747 : Blo 131789 197747 := bstep (se 1 (by rfl) ⟨148310, by rfl⟩ : syracuseStep 197747 = 296621) B296621
theorem B132211 : Blo 131789 132211 := bstep (se 1 (by rfl) ⟨99158, by rfl⟩ : syracuseStep 132211 = 198317) B198317
theorem B132227 : Blo 131789 132227 := bstep (se 1 (by rfl) ⟨99170, by rfl⟩ : syracuseStep 132227 = 198341) B198341
theorem B197777 : Blo 131789 197777 := bstep (se 2 (by rfl) ⟨74166, by rfl⟩ : syracuseStep 197777 = 148333) B148333
theorem B132243 : Blo 131789 132243 := bstep (se 1 (by rfl) ⟨99182, by rfl⟩ : syracuseStep 132243 = 198365) B198365
theorem B197795 : Blo 131789 197795 := bstep (se 1 (by rfl) ⟨148346, by rfl⟩ : syracuseStep 197795 = 296693) B296693
theorem B132259 : Blo 131789 132259 := bstep (se 1 (by rfl) ⟨99194, by rfl⟩ : syracuseStep 132259 = 198389) B198389
theorem B132275 : Blo 131789 132275 := bstep (se 1 (by rfl) ⟨99206, by rfl⟩ : syracuseStep 132275 = 198413) B198413
theorem B197825 : Blo 131789 197825 := bstep (se 2 (by rfl) ⟨74184, by rfl⟩ : syracuseStep 197825 = 148369) B148369
theorem B132291 : Blo 131789 132291 := bstep (se 1 (by rfl) ⟨99218, by rfl⟩ : syracuseStep 132291 = 198437) B198437
theorem B197843 : Blo 131789 197843 := bstep (se 1 (by rfl) ⟨148382, by rfl⟩ : syracuseStep 197843 = 296765) B296765
theorem B132307 : Blo 131789 132307 := bstep (se 1 (by rfl) ⟨99230, by rfl⟩ : syracuseStep 132307 = 198461) B198461
theorem B132323 : Blo 131789 132323 := bstep (se 1 (by rfl) ⟨99242, by rfl⟩ : syracuseStep 132323 = 198485) B198485
theorem B197873 : Blo 131789 197873 := bstep (se 2 (by rfl) ⟨74202, by rfl⟩ : syracuseStep 197873 = 148405) B148405
theorem B132339 : Blo 131789 132339 := bstep (se 1 (by rfl) ⟨99254, by rfl⟩ : syracuseStep 132339 = 198509) B198509
theorem B197891 : Blo 131789 197891 := bstep (se 1 (by rfl) ⟨148418, by rfl⟩ : syracuseStep 197891 = 296837) B296837
theorem B132355 : Blo 131789 132355 := bstep (se 1 (by rfl) ⟨99266, by rfl⟩ : syracuseStep 132355 = 198533) B198533
theorem B132371 : Blo 131789 132371 := bstep (se 1 (by rfl) ⟨99278, by rfl⟩ : syracuseStep 132371 = 198557) B198557
theorem B197921 : Blo 131789 197921 := bstep (se 2 (by rfl) ⟨74220, by rfl⟩ : syracuseStep 197921 = 148441) B148441
theorem B132387 : Blo 131789 132387 := bstep (se 1 (by rfl) ⟨99290, by rfl⟩ : syracuseStep 132387 = 198581) B198581
theorem B197939 : Blo 131789 197939 := bstep (se 1 (by rfl) ⟨148454, by rfl⟩ : syracuseStep 197939 = 296909) B296909
theorem B132403 : Blo 131789 132403 := bstep (se 1 (by rfl) ⟨99302, by rfl⟩ : syracuseStep 132403 = 198605) B198605
theorem B132419 : Blo 131789 132419 := bstep (se 1 (by rfl) ⟨99314, by rfl⟩ : syracuseStep 132419 = 198629) B198629
theorem B197969 : Blo 131789 197969 := bstep (se 2 (by rfl) ⟨74238, by rfl⟩ : syracuseStep 197969 = 148477) B148477
theorem B132435 : Blo 131789 132435 := bstep (se 1 (by rfl) ⟨99326, by rfl⟩ : syracuseStep 132435 = 198653) B198653
theorem B197987 : Blo 131789 197987 := bstep (se 1 (by rfl) ⟨148490, by rfl⟩ : syracuseStep 197987 = 296981) B296981
theorem B132451 : Blo 131789 132451 := bstep (se 1 (by rfl) ⟨99338, by rfl⟩ : syracuseStep 132451 = 198677) B198677
theorem B132467 : Blo 131789 132467 := bstep (se 1 (by rfl) ⟨99350, by rfl⟩ : syracuseStep 132467 = 198701) B198701
theorem B198017 : Blo 131789 198017 := bstep (se 2 (by rfl) ⟨74256, by rfl⟩ : syracuseStep 198017 = 148513) B148513
theorem B132483 : Blo 131789 132483 := bstep (se 1 (by rfl) ⟨99362, by rfl⟩ : syracuseStep 132483 = 198725) B198725
theorem B198035 : Blo 131789 198035 := bstep (se 1 (by rfl) ⟨148526, by rfl⟩ : syracuseStep 198035 = 297053) B297053
theorem B132499 : Blo 131789 132499 := bstep (se 1 (by rfl) ⟨99374, by rfl⟩ : syracuseStep 132499 = 198749) B198749
theorem B132515 : Blo 131789 132515 := bstep (se 1 (by rfl) ⟨99386, by rfl⟩ : syracuseStep 132515 = 198773) B198773
theorem B198065 : Blo 131789 198065 := bstep (se 2 (by rfl) ⟨74274, by rfl⟩ : syracuseStep 198065 = 148549) B148549
theorem B132531 : Blo 131789 132531 := bstep (se 1 (by rfl) ⟨99398, by rfl⟩ : syracuseStep 132531 = 198797) B198797
theorem B198083 : Blo 131789 198083 := bstep (se 1 (by rfl) ⟨148562, by rfl⟩ : syracuseStep 198083 = 297125) B297125
theorem B132547 : Blo 131789 132547 := bstep (se 1 (by rfl) ⟨99410, by rfl⟩ : syracuseStep 132547 = 198821) B198821
theorem B132563 : Blo 131789 132563 := bstep (se 1 (by rfl) ⟨99422, by rfl⟩ : syracuseStep 132563 = 198845) B198845
theorem B198113 : Blo 131789 198113 := bstep (se 2 (by rfl) ⟨74292, by rfl⟩ : syracuseStep 198113 = 148585) B148585
theorem B132579 : Blo 131789 132579 := bstep (se 1 (by rfl) ⟨99434, by rfl⟩ : syracuseStep 132579 = 198869) B198869
theorem B198131 : Blo 131789 198131 := bstep (se 1 (by rfl) ⟨148598, by rfl⟩ : syracuseStep 198131 = 297197) B297197
theorem B132595 : Blo 131789 132595 := bstep (se 1 (by rfl) ⟨99446, by rfl⟩ : syracuseStep 132595 = 198893) B198893
theorem B132611 : Blo 131789 132611 := bstep (se 1 (by rfl) ⟨99458, by rfl⟩ : syracuseStep 132611 = 198917) B198917
theorem B198161 : Blo 131789 198161 := bstep (se 2 (by rfl) ⟨74310, by rfl⟩ : syracuseStep 198161 = 148621) B148621
theorem B132627 : Blo 131789 132627 := bstep (se 1 (by rfl) ⟨99470, by rfl⟩ : syracuseStep 132627 = 198941) B198941
theorem B198179 : Blo 131789 198179 := bstep (se 1 (by rfl) ⟨148634, by rfl⟩ : syracuseStep 198179 = 297269) B297269
theorem B132643 : Blo 131789 132643 := bstep (se 1 (by rfl) ⟨99482, by rfl⟩ : syracuseStep 132643 = 198965) B198965
theorem B132659 : Blo 131789 132659 := bstep (se 1 (by rfl) ⟨99494, by rfl⟩ : syracuseStep 132659 = 198989) B198989
theorem B198209 : Blo 131789 198209 := bstep (se 2 (by rfl) ⟨74328, by rfl⟩ : syracuseStep 198209 = 148657) B148657
theorem B132675 : Blo 131789 132675 := bstep (se 1 (by rfl) ⟨99506, by rfl⟩ : syracuseStep 132675 = 199013) B199013
theorem B198227 : Blo 131789 198227 := bstep (se 1 (by rfl) ⟨148670, by rfl⟩ : syracuseStep 198227 = 297341) B297341
theorem B132691 : Blo 131789 132691 := bstep (se 1 (by rfl) ⟨99518, by rfl⟩ : syracuseStep 132691 = 199037) B199037
theorem B132707 : Blo 131789 132707 := bstep (se 1 (by rfl) ⟨99530, by rfl⟩ : syracuseStep 132707 = 199061) B199061
theorem B427619 : Blo 131789 427619 := bstep (se 1 (by rfl) ⟨320714, by rfl⟩ : syracuseStep 427619 = 641429) B641429
theorem B198257 : Blo 131789 198257 := bstep (se 2 (by rfl) ⟨74346, by rfl⟩ : syracuseStep 198257 = 148693) B148693
theorem B132723 : Blo 131789 132723 := bstep (se 1 (by rfl) ⟨99542, by rfl⟩ : syracuseStep 132723 = 199085) B199085
theorem B198275 : Blo 131789 198275 := bstep (se 1 (by rfl) ⟨148706, by rfl⟩ : syracuseStep 198275 = 297413) B297413
theorem B132739 : Blo 131789 132739 := bstep (se 1 (by rfl) ⟨99554, by rfl⟩ : syracuseStep 132739 = 199109) B199109
theorem B132755 : Blo 131789 132755 := bstep (se 1 (by rfl) ⟨99566, by rfl⟩ : syracuseStep 132755 = 199133) B199133
theorem B198305 : Blo 131789 198305 := bstep (se 2 (by rfl) ⟨74364, by rfl⟩ : syracuseStep 198305 = 148729) B148729
theorem B132771 : Blo 131789 132771 := bstep (se 1 (by rfl) ⟨99578, by rfl⟩ : syracuseStep 132771 = 199157) B199157
theorem B198323 : Blo 131789 198323 := bstep (se 1 (by rfl) ⟨148742, by rfl⟩ : syracuseStep 198323 = 297485) B297485
theorem B132787 : Blo 131789 132787 := bstep (se 1 (by rfl) ⟨99590, by rfl⟩ : syracuseStep 132787 = 199181) B199181
theorem B132803 : Blo 131789 132803 := bstep (se 1 (by rfl) ⟨99602, by rfl⟩ : syracuseStep 132803 = 199205) B199205
theorem B755405 : Blo 131789 755405 := bstep (se 3 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 755405 = 283277) B283277
theorem B296657 : Blo 131789 296657 := bstep (se 2 (by rfl) ⟨111246, by rfl⟩ : syracuseStep 296657 = 222493) B222493
theorem B198353 : Blo 131789 198353 := bstep (se 2 (by rfl) ⟨74382, by rfl⟩ : syracuseStep 198353 = 148765) B148765
theorem B132819 : Blo 131789 132819 := bstep (se 1 (by rfl) ⟨99614, by rfl⟩ : syracuseStep 132819 = 199229) B199229
theorem B296675 : Blo 131789 296675 := bstep (se 1 (by rfl) ⟨222506, by rfl⟩ : syracuseStep 296675 = 445013) B445013
theorem B198371 : Blo 131789 198371 := bstep (se 1 (by rfl) ⟨148778, by rfl⟩ : syracuseStep 198371 = 297557) B297557
theorem B132835 : Blo 131789 132835 := bstep (se 1 (by rfl) ⟨99626, by rfl⟩ : syracuseStep 132835 = 199253) B199253
theorem B132851 : Blo 131789 132851 := bstep (se 1 (by rfl) ⟨99638, by rfl⟩ : syracuseStep 132851 = 199277) B199277
theorem B198401 : Blo 131789 198401 := bstep (se 2 (by rfl) ⟨74400, by rfl⟩ : syracuseStep 198401 = 148801) B148801
theorem B132867 : Blo 131789 132867 := bstep (se 1 (by rfl) ⟨99650, by rfl⟩ : syracuseStep 132867 = 199301) B199301
theorem B198419 : Blo 131789 198419 := bstep (se 1 (by rfl) ⟨148814, by rfl⟩ : syracuseStep 198419 = 297629) B297629
theorem B132883 : Blo 131789 132883 := bstep (se 1 (by rfl) ⟨99662, by rfl⟩ : syracuseStep 132883 = 199325) B199325
theorem B132899 : Blo 131789 132899 := bstep (se 1 (by rfl) ⟨99674, by rfl⟩ : syracuseStep 132899 = 199349) B199349
theorem B198449 : Blo 131789 198449 := bstep (se 2 (by rfl) ⟨74418, by rfl⟩ : syracuseStep 198449 = 148837) B148837
theorem B132915 : Blo 131789 132915 := bstep (se 1 (by rfl) ⟨99686, by rfl⟩ : syracuseStep 132915 = 199373) B199373
theorem B198467 : Blo 131789 198467 := bstep (se 1 (by rfl) ⟨148850, by rfl⟩ : syracuseStep 198467 = 297701) B297701
theorem B132931 : Blo 131789 132931 := bstep (se 1 (by rfl) ⟨99698, by rfl⟩ : syracuseStep 132931 = 199397) B199397
theorem B132947 : Blo 131789 132947 := bstep (se 1 (by rfl) ⟨99710, by rfl⟩ : syracuseStep 132947 = 199421) B199421
theorem B198497 : Blo 131789 198497 := bstep (se 2 (by rfl) ⟨74436, by rfl⟩ : syracuseStep 198497 = 148873) B148873
theorem B132963 : Blo 131789 132963 := bstep (se 1 (by rfl) ⟨99722, by rfl⟩ : syracuseStep 132963 = 199445) B199445
theorem B198515 : Blo 131789 198515 := bstep (se 1 (by rfl) ⟨148886, by rfl⟩ : syracuseStep 198515 = 297773) B297773
theorem B132979 : Blo 131789 132979 := bstep (se 1 (by rfl) ⟨99734, by rfl⟩ : syracuseStep 132979 = 199469) B199469
theorem B132995 : Blo 131789 132995 := bstep (se 1 (by rfl) ⟨99746, by rfl⟩ : syracuseStep 132995 = 199493) B199493
theorem B198545 : Blo 131789 198545 := bstep (se 2 (by rfl) ⟨74454, by rfl⟩ : syracuseStep 198545 = 148909) B148909
theorem B133011 : Blo 131789 133011 := bstep (se 1 (by rfl) ⟨99758, by rfl⟩ : syracuseStep 133011 = 199517) B199517
theorem B198563 : Blo 131789 198563 := bstep (se 1 (by rfl) ⟨148922, by rfl⟩ : syracuseStep 198563 = 297845) B297845
theorem B133027 : Blo 131789 133027 := bstep (se 1 (by rfl) ⟨99770, by rfl⟩ : syracuseStep 133027 = 199541) B199541
theorem B133043 : Blo 131789 133043 := bstep (se 1 (by rfl) ⟨99782, by rfl⟩ : syracuseStep 133043 = 199565) B199565
theorem B198593 : Blo 131789 198593 := bstep (se 2 (by rfl) ⟨74472, by rfl⟩ : syracuseStep 198593 = 148945) B148945
theorem B133059 : Blo 131789 133059 := bstep (se 1 (by rfl) ⟨99794, by rfl⟩ : syracuseStep 133059 = 199589) B199589
theorem B198611 : Blo 131789 198611 := bstep (se 1 (by rfl) ⟨148958, by rfl⟩ : syracuseStep 198611 = 297917) B297917
theorem B133075 : Blo 131789 133075 := bstep (se 1 (by rfl) ⟨99806, by rfl⟩ : syracuseStep 133075 = 199613) B199613
theorem B133091 : Blo 131789 133091 := bstep (se 1 (by rfl) ⟨99818, by rfl⟩ : syracuseStep 133091 = 199637) B199637
theorem B296945 : Blo 131789 296945 := bstep (se 2 (by rfl) ⟨111354, by rfl⟩ : syracuseStep 296945 = 222709) B222709
theorem B198641 : Blo 131789 198641 := bstep (se 2 (by rfl) ⟨74490, by rfl⟩ : syracuseStep 198641 = 148981) B148981
theorem B133107 : Blo 131789 133107 := bstep (se 1 (by rfl) ⟨99830, by rfl⟩ : syracuseStep 133107 = 199661) B199661
theorem B296963 : Blo 131789 296963 := bstep (se 1 (by rfl) ⟨222722, by rfl⟩ : syracuseStep 296963 = 445445) B445445
theorem B198659 : Blo 131789 198659 := bstep (se 1 (by rfl) ⟨148994, by rfl⟩ : syracuseStep 198659 = 297989) B297989
theorem B133123 : Blo 131789 133123 := bstep (se 1 (by rfl) ⟨99842, by rfl⟩ : syracuseStep 133123 = 199685) B199685
theorem B133139 : Blo 131789 133139 := bstep (se 1 (by rfl) ⟨99854, by rfl⟩ : syracuseStep 133139 = 199709) B199709
theorem B198689 : Blo 131789 198689 := bstep (se 2 (by rfl) ⟨74508, by rfl⟩ : syracuseStep 198689 = 149017) B149017
theorem B133155 : Blo 131789 133155 := bstep (se 1 (by rfl) ⟨99866, by rfl⟩ : syracuseStep 133155 = 199733) B199733
theorem B198707 : Blo 131789 198707 := bstep (se 1 (by rfl) ⟨149030, by rfl⟩ : syracuseStep 198707 = 298061) B298061
theorem B133171 : Blo 131789 133171 := bstep (se 1 (by rfl) ⟨99878, by rfl⟩ : syracuseStep 133171 = 199757) B199757
theorem B133187 : Blo 131789 133187 := bstep (se 1 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 133187 = 199781) B199781
theorem B198737 : Blo 131789 198737 := bstep (se 2 (by rfl) ⟨74526, by rfl⟩ : syracuseStep 198737 = 149053) B149053
theorem B133203 : Blo 131789 133203 := bstep (se 1 (by rfl) ⟨99902, by rfl⟩ : syracuseStep 133203 = 199805) B199805
theorem B198755 : Blo 131789 198755 := bstep (se 1 (by rfl) ⟨149066, by rfl⟩ : syracuseStep 198755 = 298133) B298133
theorem B133219 : Blo 131789 133219 := bstep (se 1 (by rfl) ⟨99914, by rfl⟩ : syracuseStep 133219 = 199829) B199829
theorem B133235 : Blo 131789 133235 := bstep (se 1 (by rfl) ⟨99926, by rfl⟩ : syracuseStep 133235 = 199853) B199853
theorem B198785 : Blo 131789 198785 := bstep (se 2 (by rfl) ⟨74544, by rfl⟩ : syracuseStep 198785 = 149089) B149089
theorem B133251 : Blo 131789 133251 := bstep (se 1 (by rfl) ⟨99938, by rfl⟩ : syracuseStep 133251 = 199877) B199877
theorem B198803 : Blo 131789 198803 := bstep (se 1 (by rfl) ⟨149102, by rfl⟩ : syracuseStep 198803 = 298205) B298205
theorem B133267 : Blo 131789 133267 := bstep (se 1 (by rfl) ⟨99950, by rfl⟩ : syracuseStep 133267 = 199901) B199901
theorem B133283 : Blo 131789 133283 := bstep (se 1 (by rfl) ⟨99962, by rfl⟩ : syracuseStep 133283 = 199925) B199925
theorem B198833 : Blo 131789 198833 := bstep (se 2 (by rfl) ⟨74562, by rfl⟩ : syracuseStep 198833 = 149125) B149125
theorem B133299 : Blo 131789 133299 := bstep (se 1 (by rfl) ⟨99974, by rfl⟩ : syracuseStep 133299 = 199949) B199949
theorem B198851 : Blo 131789 198851 := bstep (se 1 (by rfl) ⟨149138, by rfl⟩ : syracuseStep 198851 = 298277) B298277
theorem B133315 : Blo 131789 133315 := bstep (se 1 (by rfl) ⟨99986, by rfl⟩ : syracuseStep 133315 = 199973) B199973
theorem B133331 : Blo 131789 133331 := bstep (se 1 (by rfl) ⟨99998, by rfl⟩ : syracuseStep 133331 = 199997) B199997
theorem B198881 : Blo 131789 198881 := bstep (se 2 (by rfl) ⟨74580, by rfl⟩ : syracuseStep 198881 = 149161) B149161
theorem B133347 : Blo 131789 133347 := bstep (se 1 (by rfl) ⟨100010, by rfl⟩ : syracuseStep 133347 = 200021) B200021
theorem B198899 : Blo 131789 198899 := bstep (se 1 (by rfl) ⟨149174, by rfl⟩ : syracuseStep 198899 = 298349) B298349
theorem B133363 : Blo 131789 133363 := bstep (se 1 (by rfl) ⟨100022, by rfl⟩ : syracuseStep 133363 = 200045) B200045
theorem B133379 : Blo 131789 133379 := bstep (se 1 (by rfl) ⟨100034, by rfl⟩ : syracuseStep 133379 = 200069) B200069
theorem B297233 : Blo 131789 297233 := bstep (se 2 (by rfl) ⟨111462, by rfl⟩ : syracuseStep 297233 = 222925) B222925
theorem B198929 : Blo 131789 198929 := bstep (se 2 (by rfl) ⟨74598, by rfl⟩ : syracuseStep 198929 = 149197) B149197
theorem B133395 : Blo 131789 133395 := bstep (se 1 (by rfl) ⟨100046, by rfl⟩ : syracuseStep 133395 = 200093) B200093
theorem B297251 : Blo 131789 297251 := bstep (se 1 (by rfl) ⟨222938, by rfl⟩ : syracuseStep 297251 = 445877) B445877
theorem B198947 : Blo 131789 198947 := bstep (se 1 (by rfl) ⟨149210, by rfl⟩ : syracuseStep 198947 = 298421) B298421
theorem B133411 : Blo 131789 133411 := bstep (se 1 (by rfl) ⟨100058, by rfl⟩ : syracuseStep 133411 = 200117) B200117
theorem B133427 : Blo 131789 133427 := bstep (se 1 (by rfl) ⟨100070, by rfl⟩ : syracuseStep 133427 = 200141) B200141
theorem B1968437 : Blo 131789 1968437 := bstep (se 5 (by rfl) ⟨92270, by rfl⟩ : syracuseStep 1968437 = 184541) B184541
theorem B198977 : Blo 131789 198977 := bstep (se 2 (by rfl) ⟨74616, by rfl⟩ : syracuseStep 198977 = 149233) B149233
theorem B133443 : Blo 131789 133443 := bstep (se 1 (by rfl) ⟨100082, by rfl⟩ : syracuseStep 133443 = 200165) B200165
theorem B198995 : Blo 131789 198995 := bstep (se 1 (by rfl) ⟨149246, by rfl⟩ : syracuseStep 198995 = 298493) B298493
theorem B133459 : Blo 131789 133459 := bstep (se 1 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 133459 = 200189) B200189
theorem B133475 : Blo 131789 133475 := bstep (se 1 (by rfl) ⟨100106, by rfl⟩ : syracuseStep 133475 = 200213) B200213
theorem B199025 : Blo 131789 199025 := bstep (se 2 (by rfl) ⟨74634, by rfl⟩ : syracuseStep 199025 = 149269) B149269
theorem B133491 : Blo 131789 133491 := bstep (se 1 (by rfl) ⟨100118, by rfl⟩ : syracuseStep 133491 = 200237) B200237
theorem B199043 : Blo 131789 199043 := bstep (se 1 (by rfl) ⟨149282, by rfl⟩ : syracuseStep 199043 = 298565) B298565
theorem B133507 : Blo 131789 133507 := bstep (se 1 (by rfl) ⟨100130, by rfl⟩ : syracuseStep 133507 = 200261) B200261
theorem B133523 : Blo 131789 133523 := bstep (se 1 (by rfl) ⟨100142, by rfl⟩ : syracuseStep 133523 = 200285) B200285
theorem B199073 : Blo 131789 199073 := bstep (se 2 (by rfl) ⟨74652, by rfl⟩ : syracuseStep 199073 = 149305) B149305
theorem B133539 : Blo 131789 133539 := bstep (se 1 (by rfl) ⟨100154, by rfl⟩ : syracuseStep 133539 = 200309) B200309
theorem B428465 : Blo 131789 428465 := bstep (se 2 (by rfl) ⟨160674, by rfl⟩ : syracuseStep 428465 = 321349) B321349
theorem B199091 : Blo 131789 199091 := bstep (se 1 (by rfl) ⟨149318, by rfl⟩ : syracuseStep 199091 = 298637) B298637
theorem B133555 : Blo 131789 133555 := bstep (se 1 (by rfl) ⟨100166, by rfl⟩ : syracuseStep 133555 = 200333) B200333
theorem B133571 : Blo 131789 133571 := bstep (se 1 (by rfl) ⟨100178, by rfl⟩ : syracuseStep 133571 = 200357) B200357
theorem B199121 : Blo 131789 199121 := bstep (se 2 (by rfl) ⟨74670, by rfl⟩ : syracuseStep 199121 = 149341) B149341
theorem B133587 : Blo 131789 133587 := bstep (se 1 (by rfl) ⟨100190, by rfl⟩ : syracuseStep 133587 = 200381) B200381
theorem B199139 : Blo 131789 199139 := bstep (se 1 (by rfl) ⟨149354, by rfl⟩ : syracuseStep 199139 = 298709) B298709
theorem B133603 : Blo 131789 133603 := bstep (se 1 (by rfl) ⟨100202, by rfl⟩ : syracuseStep 133603 = 200405) B200405
theorem B133619 : Blo 131789 133619 := bstep (se 1 (by rfl) ⟨100214, by rfl⟩ : syracuseStep 133619 = 200429) B200429
theorem B199169 : Blo 131789 199169 := bstep (se 2 (by rfl) ⟨74688, by rfl⟩ : syracuseStep 199169 = 149377) B149377
theorem B133635 : Blo 131789 133635 := bstep (se 1 (by rfl) ⟨100226, by rfl⟩ : syracuseStep 133635 = 200453) B200453
theorem B199187 : Blo 131789 199187 := bstep (se 1 (by rfl) ⟨149390, by rfl⟩ : syracuseStep 199187 = 298781) B298781
theorem B133651 : Blo 131789 133651 := bstep (se 1 (by rfl) ⟨100238, by rfl⟩ : syracuseStep 133651 = 200477) B200477
theorem B133667 : Blo 131789 133667 := bstep (se 1 (by rfl) ⟨100250, by rfl⟩ : syracuseStep 133667 = 200501) B200501
theorem B297521 : Blo 131789 297521 := bstep (se 2 (by rfl) ⟨111570, by rfl⟩ : syracuseStep 297521 = 223141) B223141
theorem B199217 : Blo 131789 199217 := bstep (se 2 (by rfl) ⟨74706, by rfl⟩ : syracuseStep 199217 = 149413) B149413
theorem B133683 : Blo 131789 133683 := bstep (se 1 (by rfl) ⟨100262, by rfl⟩ : syracuseStep 133683 = 200525) B200525
theorem B297539 : Blo 131789 297539 := bstep (se 1 (by rfl) ⟨223154, by rfl⟩ : syracuseStep 297539 = 446309) B446309
theorem B199235 : Blo 131789 199235 := bstep (se 1 (by rfl) ⟨149426, by rfl⟩ : syracuseStep 199235 = 298853) B298853
theorem B133699 : Blo 131789 133699 := bstep (se 1 (by rfl) ⟨100274, by rfl⟩ : syracuseStep 133699 = 200549) B200549
theorem B133715 : Blo 131789 133715 := bstep (se 1 (by rfl) ⟨100286, by rfl⟩ : syracuseStep 133715 = 200573) B200573
theorem B199265 : Blo 131789 199265 := bstep (se 2 (by rfl) ⟨74724, by rfl⟩ : syracuseStep 199265 = 149449) B149449
theorem B133731 : Blo 131789 133731 := bstep (se 1 (by rfl) ⟨100298, by rfl⟩ : syracuseStep 133731 = 200597) B200597
theorem B756337 : Blo 131789 756337 := bstep (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) B567253
theorem B199283 : Blo 131789 199283 := bstep (se 1 (by rfl) ⟨149462, by rfl⟩ : syracuseStep 199283 = 298925) B298925
theorem B133747 : Blo 131789 133747 := bstep (se 1 (by rfl) ⟨100310, by rfl⟩ : syracuseStep 133747 = 200621) B200621
theorem B133763 : Blo 131789 133763 := bstep (se 1 (by rfl) ⟨100322, by rfl⟩ : syracuseStep 133763 = 200645) B200645
theorem B199313 : Blo 131789 199313 := bstep (se 2 (by rfl) ⟨74742, by rfl⟩ : syracuseStep 199313 = 149485) B149485
theorem B133779 : Blo 131789 133779 := bstep (se 1 (by rfl) ⟨100334, by rfl⟩ : syracuseStep 133779 = 200669) B200669
theorem B199331 : Blo 131789 199331 := bstep (se 1 (by rfl) ⟨149498, by rfl⟩ : syracuseStep 199331 = 298997) B298997
theorem B133795 : Blo 131789 133795 := bstep (se 1 (by rfl) ⟨100346, by rfl⟩ : syracuseStep 133795 = 200693) B200693
theorem B133811 : Blo 131789 133811 := bstep (se 1 (by rfl) ⟨100358, by rfl⟩ : syracuseStep 133811 = 200717) B200717
theorem B199361 : Blo 131789 199361 := bstep (se 2 (by rfl) ⟨74760, by rfl⟩ : syracuseStep 199361 = 149521) B149521
theorem B133827 : Blo 131789 133827 := bstep (se 1 (by rfl) ⟨100370, by rfl⟩ : syracuseStep 133827 = 200741) B200741
theorem B199379 : Blo 131789 199379 := bstep (se 1 (by rfl) ⟨149534, by rfl⟩ : syracuseStep 199379 = 299069) B299069
theorem B133843 : Blo 131789 133843 := bstep (se 1 (by rfl) ⟨100382, by rfl⟩ : syracuseStep 133843 = 200765) B200765
theorem B133859 : Blo 131789 133859 := bstep (se 1 (by rfl) ⟨100394, by rfl⟩ : syracuseStep 133859 = 200789) B200789
theorem B199409 : Blo 131789 199409 := bstep (se 2 (by rfl) ⟨74778, by rfl⟩ : syracuseStep 199409 = 149557) B149557
theorem B133875 : Blo 131789 133875 := bstep (se 1 (by rfl) ⟨100406, by rfl⟩ : syracuseStep 133875 = 200813) B200813
theorem B199427 : Blo 131789 199427 := bstep (se 1 (by rfl) ⟨149570, by rfl⟩ : syracuseStep 199427 = 299141) B299141
theorem B133891 : Blo 131789 133891 := bstep (se 1 (by rfl) ⟨100418, by rfl⟩ : syracuseStep 133891 = 200837) B200837
theorem B133907 : Blo 131789 133907 := bstep (se 1 (by rfl) ⟨100430, by rfl⟩ : syracuseStep 133907 = 200861) B200861
theorem B199457 : Blo 131789 199457 := bstep (se 2 (by rfl) ⟨74796, by rfl⟩ : syracuseStep 199457 = 149593) B149593
theorem B133923 : Blo 131789 133923 := bstep (se 1 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 133923 = 200885) B200885
theorem B199475 : Blo 131789 199475 := bstep (se 1 (by rfl) ⟨149606, by rfl⟩ : syracuseStep 199475 = 299213) B299213
theorem B133939 : Blo 131789 133939 := bstep (se 1 (by rfl) ⟨100454, by rfl⟩ : syracuseStep 133939 = 200909) B200909
theorem B133955 : Blo 131789 133955 := bstep (se 1 (by rfl) ⟨100466, by rfl⟩ : syracuseStep 133955 = 200933) B200933
theorem B297809 : Blo 131789 297809 := bstep (se 2 (by rfl) ⟨111678, by rfl⟩ : syracuseStep 297809 = 223357) B223357
theorem B199505 : Blo 131789 199505 := bstep (se 2 (by rfl) ⟨74814, by rfl⟩ : syracuseStep 199505 = 149629) B149629
theorem B133971 : Blo 131789 133971 := bstep (se 1 (by rfl) ⟨100478, by rfl⟩ : syracuseStep 133971 = 200957) B200957
theorem B297827 : Blo 131789 297827 := bstep (se 1 (by rfl) ⟨223370, by rfl⟩ : syracuseStep 297827 = 446741) B446741
theorem B199523 : Blo 131789 199523 := bstep (se 1 (by rfl) ⟨149642, by rfl⟩ : syracuseStep 199523 = 299285) B299285
theorem B133987 : Blo 131789 133987 := bstep (se 1 (by rfl) ⟨100490, by rfl⟩ : syracuseStep 133987 = 200981) B200981
theorem B134003 : Blo 131789 134003 := bstep (se 1 (by rfl) ⟨100502, by rfl⟩ : syracuseStep 134003 = 201005) B201005
theorem B199553 : Blo 131789 199553 := bstep (se 2 (by rfl) ⟨74832, by rfl⟩ : syracuseStep 199553 = 149665) B149665
theorem B134019 : Blo 131789 134019 := bstep (se 1 (by rfl) ⟨100514, by rfl⟩ : syracuseStep 134019 = 201029) B201029
theorem B199571 : Blo 131789 199571 := bstep (se 1 (by rfl) ⟨149678, by rfl⟩ : syracuseStep 199571 = 299357) B299357
theorem B134035 : Blo 131789 134035 := bstep (se 1 (by rfl) ⟨100526, by rfl⟩ : syracuseStep 134035 = 201053) B201053
theorem B134051 : Blo 131789 134051 := bstep (se 1 (by rfl) ⟨100538, by rfl⟩ : syracuseStep 134051 = 201077) B201077
theorem B199601 : Blo 131789 199601 := bstep (se 2 (by rfl) ⟨74850, by rfl⟩ : syracuseStep 199601 = 149701) B149701
theorem B134067 : Blo 131789 134067 := bstep (se 1 (by rfl) ⟨100550, by rfl⟩ : syracuseStep 134067 = 201101) B201101
theorem B199619 : Blo 131789 199619 := bstep (se 1 (by rfl) ⟨149714, by rfl⟩ : syracuseStep 199619 = 299429) B299429
theorem B134083 : Blo 131789 134083 := bstep (se 1 (by rfl) ⟨100562, by rfl⟩ : syracuseStep 134083 = 201125) B201125
theorem B854981 : Blo 131789 854981 := bstep (se 4 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 854981 = 160309) B160309
theorem B134099 : Blo 131789 134099 := bstep (se 1 (by rfl) ⟨100574, by rfl⟩ : syracuseStep 134099 = 201149) B201149
theorem B199649 : Blo 131789 199649 := bstep (se 2 (by rfl) ⟨74868, by rfl⟩ : syracuseStep 199649 = 149737) B149737
theorem B134115 : Blo 131789 134115 := bstep (se 1 (by rfl) ⟨100586, by rfl⟩ : syracuseStep 134115 = 201173) B201173
theorem B199667 : Blo 131789 199667 := bstep (se 1 (by rfl) ⟨149750, by rfl⟩ : syracuseStep 199667 = 299501) B299501
theorem B134131 : Blo 131789 134131 := bstep (se 1 (by rfl) ⟨100598, by rfl⟩ : syracuseStep 134131 = 201197) B201197
theorem B134147 : Blo 131789 134147 := bstep (se 1 (by rfl) ⟨100610, by rfl⟩ : syracuseStep 134147 = 201221) B201221
theorem B199697 : Blo 131789 199697 := bstep (se 2 (by rfl) ⟨74886, by rfl⟩ : syracuseStep 199697 = 149773) B149773
theorem B134163 : Blo 131789 134163 := bstep (se 1 (by rfl) ⟨100622, by rfl⟩ : syracuseStep 134163 = 201245) B201245
theorem B199715 : Blo 131789 199715 := bstep (se 1 (by rfl) ⟨149786, by rfl⟩ : syracuseStep 199715 = 299573) B299573
theorem B134179 : Blo 131789 134179 := bstep (se 1 (by rfl) ⟨100634, by rfl⟩ : syracuseStep 134179 = 201269) B201269
theorem B134195 : Blo 131789 134195 := bstep (se 1 (by rfl) ⟨100646, by rfl⟩ : syracuseStep 134195 = 201293) B201293
theorem B199745 : Blo 131789 199745 := bstep (se 2 (by rfl) ⟨74904, by rfl⟩ : syracuseStep 199745 = 149809) B149809
theorem B134211 : Blo 131789 134211 := bstep (se 1 (by rfl) ⟨100658, by rfl⟩ : syracuseStep 134211 = 201317) B201317
theorem B199763 : Blo 131789 199763 := bstep (se 1 (by rfl) ⟨149822, by rfl⟩ : syracuseStep 199763 = 299645) B299645
theorem B134227 : Blo 131789 134227 := bstep (se 1 (by rfl) ⟨100670, by rfl⟩ : syracuseStep 134227 = 201341) B201341
theorem B134243 : Blo 131789 134243 := bstep (se 1 (by rfl) ⟨100682, by rfl⟩ : syracuseStep 134243 = 201365) B201365
theorem B298097 : Blo 131789 298097 := bstep (se 2 (by rfl) ⟨111786, by rfl⟩ : syracuseStep 298097 = 223573) B223573
theorem B199793 : Blo 131789 199793 := bstep (se 2 (by rfl) ⟨74922, by rfl⟩ : syracuseStep 199793 = 149845) B149845
theorem B134259 : Blo 131789 134259 := bstep (se 1 (by rfl) ⟨100694, by rfl⟩ : syracuseStep 134259 = 201389) B201389
theorem B298115 : Blo 131789 298115 := bstep (se 1 (by rfl) ⟨223586, by rfl⟩ : syracuseStep 298115 = 447173) B447173
theorem B199811 : Blo 131789 199811 := bstep (se 1 (by rfl) ⟨149858, by rfl⟩ : syracuseStep 199811 = 299717) B299717
theorem B134275 : Blo 131789 134275 := bstep (se 1 (by rfl) ⟨100706, by rfl⟩ : syracuseStep 134275 = 201413) B201413
theorem B134291 : Blo 131789 134291 := bstep (se 1 (by rfl) ⟨100718, by rfl⟩ : syracuseStep 134291 = 201437) B201437
theorem B199841 : Blo 131789 199841 := bstep (se 2 (by rfl) ⟨74940, by rfl⟩ : syracuseStep 199841 = 149881) B149881
theorem B134307 : Blo 131789 134307 := bstep (se 1 (by rfl) ⟨100730, by rfl⟩ : syracuseStep 134307 = 201461) B201461
theorem B199859 : Blo 131789 199859 := bstep (se 1 (by rfl) ⟨149894, by rfl⟩ : syracuseStep 199859 = 299789) B299789
theorem B134323 : Blo 131789 134323 := bstep (se 1 (by rfl) ⟨100742, by rfl⟩ : syracuseStep 134323 = 201485) B201485
theorem B134339 : Blo 131789 134339 := bstep (se 1 (by rfl) ⟨100754, by rfl⟩ : syracuseStep 134339 = 201509) B201509
theorem B199889 : Blo 131789 199889 := bstep (se 2 (by rfl) ⟨74958, by rfl⟩ : syracuseStep 199889 = 149917) B149917
theorem B167123 : Blo 131789 167123 := bstep (se 1 (by rfl) ⟨125342, by rfl⟩ : syracuseStep 167123 = 250685) B250685
theorem B134355 : Blo 131789 134355 := bstep (se 1 (by rfl) ⟨100766, by rfl⟩ : syracuseStep 134355 = 201533) B201533
theorem B199907 : Blo 131789 199907 := bstep (se 1 (by rfl) ⟨149930, by rfl⟩ : syracuseStep 199907 = 299861) B299861
theorem B134371 : Blo 131789 134371 := bstep (se 1 (by rfl) ⟨100778, by rfl⟩ : syracuseStep 134371 = 201557) B201557
theorem B134387 : Blo 131789 134387 := bstep (se 1 (by rfl) ⟨100790, by rfl⟩ : syracuseStep 134387 = 201581) B201581
theorem B199937 : Blo 131789 199937 := bstep (se 2 (by rfl) ⟨74976, by rfl⟩ : syracuseStep 199937 = 149953) B149953
theorem B134403 : Blo 131789 134403 := bstep (se 1 (by rfl) ⟨100802, by rfl⟩ : syracuseStep 134403 = 201605) B201605
theorem B199955 : Blo 131789 199955 := bstep (se 1 (by rfl) ⟨149966, by rfl⟩ : syracuseStep 199955 = 299933) B299933
theorem B134419 : Blo 131789 134419 := bstep (se 1 (by rfl) ⟨100814, by rfl⟩ : syracuseStep 134419 = 201629) B201629
theorem B134435 : Blo 131789 134435 := bstep (se 1 (by rfl) ⟨100826, by rfl⟩ : syracuseStep 134435 = 201653) B201653
theorem B199985 : Blo 131789 199985 := bstep (se 2 (by rfl) ⟨74994, by rfl⟩ : syracuseStep 199985 = 149989) B149989
theorem B134451 : Blo 131789 134451 := bstep (se 1 (by rfl) ⟨100838, by rfl⟩ : syracuseStep 134451 = 201677) B201677
theorem B200003 : Blo 131789 200003 := bstep (se 1 (by rfl) ⟨150002, by rfl⟩ : syracuseStep 200003 = 300005) B300005
theorem B134467 : Blo 131789 134467 := bstep (se 1 (by rfl) ⟨100850, by rfl⟩ : syracuseStep 134467 = 201701) B201701
theorem B134483 : Blo 131789 134483 := bstep (se 1 (by rfl) ⟨100862, by rfl⟩ : syracuseStep 134483 = 201725) B201725
theorem B200033 : Blo 131789 200033 := bstep (se 2 (by rfl) ⟨75012, by rfl⟩ : syracuseStep 200033 = 150025) B150025
theorem B134499 : Blo 131789 134499 := bstep (se 1 (by rfl) ⟨100874, by rfl⟩ : syracuseStep 134499 = 201749) B201749
theorem B200051 : Blo 131789 200051 := bstep (se 1 (by rfl) ⟨150038, by rfl⟩ : syracuseStep 200051 = 300077) B300077
theorem B134515 : Blo 131789 134515 := bstep (se 1 (by rfl) ⟨100886, by rfl⟩ : syracuseStep 134515 = 201773) B201773
theorem B134531 : Blo 131789 134531 := bstep (se 1 (by rfl) ⟨100898, by rfl⟩ : syracuseStep 134531 = 201797) B201797
theorem B298385 : Blo 131789 298385 := bstep (se 2 (by rfl) ⟨111894, by rfl⟩ : syracuseStep 298385 = 223789) B223789
theorem B200081 : Blo 131789 200081 := bstep (se 2 (by rfl) ⟨75030, by rfl⟩ : syracuseStep 200081 = 150061) B150061
theorem B134547 : Blo 131789 134547 := bstep (se 1 (by rfl) ⟨100910, by rfl⟩ : syracuseStep 134547 = 201821) B201821
theorem B298403 : Blo 131789 298403 := bstep (se 1 (by rfl) ⟨223802, by rfl⟩ : syracuseStep 298403 = 447605) B447605
theorem B200099 : Blo 131789 200099 := bstep (se 1 (by rfl) ⟨150074, by rfl⟩ : syracuseStep 200099 = 300149) B300149
theorem B134563 : Blo 131789 134563 := bstep (se 1 (by rfl) ⟨100922, by rfl⟩ : syracuseStep 134563 = 201845) B201845
theorem B134579 : Blo 131789 134579 := bstep (se 1 (by rfl) ⟨100934, by rfl⟩ : syracuseStep 134579 = 201869) B201869
theorem B200129 : Blo 131789 200129 := bstep (se 2 (by rfl) ⟨75048, by rfl⟩ : syracuseStep 200129 = 150097) B150097
theorem B134595 : Blo 131789 134595 := bstep (se 1 (by rfl) ⟨100946, by rfl⟩ : syracuseStep 134595 = 201893) B201893
theorem B200147 : Blo 131789 200147 := bstep (se 1 (by rfl) ⟨150110, by rfl⟩ : syracuseStep 200147 = 300221) B300221
theorem B134611 : Blo 131789 134611 := bstep (se 1 (by rfl) ⟨100958, by rfl⟩ : syracuseStep 134611 = 201917) B201917
theorem B134627 : Blo 131789 134627 := bstep (se 1 (by rfl) ⟨100970, by rfl⟩ : syracuseStep 134627 = 201941) B201941
theorem B200177 : Blo 131789 200177 := bstep (se 2 (by rfl) ⟨75066, by rfl⟩ : syracuseStep 200177 = 150133) B150133
theorem B1084913 : Blo 131789 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B134643 : Blo 131789 134643 := bstep (se 1 (by rfl) ⟨100982, by rfl⟩ : syracuseStep 134643 = 201965) B201965
theorem B200195 : Blo 131789 200195 := bstep (se 1 (by rfl) ⟨150146, by rfl⟩ : syracuseStep 200195 = 300293) B300293
theorem B134659 : Blo 131789 134659 := bstep (se 1 (by rfl) ⟨100994, by rfl⟩ : syracuseStep 134659 = 201989) B201989
theorem B134675 : Blo 131789 134675 := bstep (se 1 (by rfl) ⟨101006, by rfl⟩ : syracuseStep 134675 = 202013) B202013
theorem B200225 : Blo 131789 200225 := bstep (se 2 (by rfl) ⟨75084, by rfl⟩ : syracuseStep 200225 = 150169) B150169
theorem B134691 : Blo 131789 134691 := bstep (se 1 (by rfl) ⟨101018, by rfl⟩ : syracuseStep 134691 = 202037) B202037
theorem B200243 : Blo 131789 200243 := bstep (se 1 (by rfl) ⟨150182, by rfl⟩ : syracuseStep 200243 = 300365) B300365
theorem B134707 : Blo 131789 134707 := bstep (se 1 (by rfl) ⟨101030, by rfl⟩ : syracuseStep 134707 = 202061) B202061
theorem B134723 : Blo 131789 134723 := bstep (se 1 (by rfl) ⟨101042, by rfl⟩ : syracuseStep 134723 = 202085) B202085
theorem B200273 : Blo 131789 200273 := bstep (se 2 (by rfl) ⟨75102, by rfl⟩ : syracuseStep 200273 = 150205) B150205
theorem B134739 : Blo 131789 134739 := bstep (se 1 (by rfl) ⟨101054, by rfl⟩ : syracuseStep 134739 = 202109) B202109
theorem B200291 : Blo 131789 200291 := bstep (se 1 (by rfl) ⟨150218, by rfl⟩ : syracuseStep 200291 = 300437) B300437
theorem B134755 : Blo 131789 134755 := bstep (se 1 (by rfl) ⟨101066, by rfl⟩ : syracuseStep 134755 = 202133) B202133
theorem B134771 : Blo 131789 134771 := bstep (se 1 (by rfl) ⟨101078, by rfl⟩ : syracuseStep 134771 = 202157) B202157
theorem B200321 : Blo 131789 200321 := bstep (se 2 (by rfl) ⟨75120, by rfl⟩ : syracuseStep 200321 = 150241) B150241
theorem B134787 : Blo 131789 134787 := bstep (se 1 (by rfl) ⟨101090, by rfl⟩ : syracuseStep 134787 = 202181) B202181
theorem B200339 : Blo 131789 200339 := bstep (se 1 (by rfl) ⟨150254, by rfl⟩ : syracuseStep 200339 = 300509) B300509
theorem B134803 : Blo 131789 134803 := bstep (se 1 (by rfl) ⟨101102, by rfl⟩ : syracuseStep 134803 = 202205) B202205
theorem B134819 : Blo 131789 134819 := bstep (se 1 (by rfl) ⟨101114, by rfl⟩ : syracuseStep 134819 = 202229) B202229
theorem B298673 : Blo 131789 298673 := bstep (se 2 (by rfl) ⟨112002, by rfl⟩ : syracuseStep 298673 = 224005) B224005
theorem B200369 : Blo 131789 200369 := bstep (se 2 (by rfl) ⟨75138, by rfl⟩ : syracuseStep 200369 = 150277) B150277
theorem B134835 : Blo 131789 134835 := bstep (se 1 (by rfl) ⟨101126, by rfl⟩ : syracuseStep 134835 = 202253) B202253
theorem B298691 : Blo 131789 298691 := bstep (se 1 (by rfl) ⟨224018, by rfl⟩ : syracuseStep 298691 = 448037) B448037
theorem B200387 : Blo 131789 200387 := bstep (se 1 (by rfl) ⟨150290, by rfl⟩ : syracuseStep 200387 = 300581) B300581
theorem B134851 : Blo 131789 134851 := bstep (se 1 (by rfl) ⟨101138, by rfl⟩ : syracuseStep 134851 = 202277) B202277
theorem B134867 : Blo 131789 134867 := bstep (se 1 (by rfl) ⟨101150, by rfl⟩ : syracuseStep 134867 = 202301) B202301
theorem B200417 : Blo 131789 200417 := bstep (se 2 (by rfl) ⟨75156, by rfl⟩ : syracuseStep 200417 = 150313) B150313
theorem B134883 : Blo 131789 134883 := bstep (se 1 (by rfl) ⟨101162, by rfl⟩ : syracuseStep 134883 = 202325) B202325
theorem B200435 : Blo 131789 200435 := bstep (se 1 (by rfl) ⟨150326, by rfl⟩ : syracuseStep 200435 = 300653) B300653
theorem B134899 : Blo 131789 134899 := bstep (se 1 (by rfl) ⟨101174, by rfl⟩ : syracuseStep 134899 = 202349) B202349
theorem B134915 : Blo 131789 134915 := bstep (se 1 (by rfl) ⟨101186, by rfl⟩ : syracuseStep 134915 = 202373) B202373
theorem B200465 : Blo 131789 200465 := bstep (se 2 (by rfl) ⟨75174, by rfl⟩ : syracuseStep 200465 = 150349) B150349
theorem B134931 : Blo 131789 134931 := bstep (se 1 (by rfl) ⟨101198, by rfl⟩ : syracuseStep 134931 = 202397) B202397
theorem B200483 : Blo 131789 200483 := bstep (se 1 (by rfl) ⟨150362, by rfl⟩ : syracuseStep 200483 = 300725) B300725
theorem B134947 : Blo 131789 134947 := bstep (se 1 (by rfl) ⟨101210, by rfl⟩ : syracuseStep 134947 = 202421) B202421
theorem B134963 : Blo 131789 134963 := bstep (se 1 (by rfl) ⟨101222, by rfl⟩ : syracuseStep 134963 = 202445) B202445
theorem B200513 : Blo 131789 200513 := bstep (se 2 (by rfl) ⟨75192, by rfl⟩ : syracuseStep 200513 = 150385) B150385
theorem B134979 : Blo 131789 134979 := bstep (se 1 (by rfl) ⟨101234, by rfl⟩ : syracuseStep 134979 = 202469) B202469
theorem B200531 : Blo 131789 200531 := bstep (se 1 (by rfl) ⟨150398, by rfl⟩ : syracuseStep 200531 = 300797) B300797
theorem B134995 : Blo 131789 134995 := bstep (se 1 (by rfl) ⟨101246, by rfl⟩ : syracuseStep 134995 = 202493) B202493
theorem B135011 : Blo 131789 135011 := bstep (se 1 (by rfl) ⟨101258, by rfl⟩ : syracuseStep 135011 = 202517) B202517
theorem B200561 : Blo 131789 200561 := bstep (se 2 (by rfl) ⟨75210, by rfl⟩ : syracuseStep 200561 = 150421) B150421
theorem B135027 : Blo 131789 135027 := bstep (se 1 (by rfl) ⟨101270, by rfl⟩ : syracuseStep 135027 = 202541) B202541
theorem B200579 : Blo 131789 200579 := bstep (se 1 (by rfl) ⟨150434, by rfl⟩ : syracuseStep 200579 = 300869) B300869
theorem B135043 : Blo 131789 135043 := bstep (se 1 (by rfl) ⟨101282, by rfl⟩ : syracuseStep 135043 = 202565) B202565
theorem B167827 : Blo 131789 167827 := bstep (se 1 (by rfl) ⟨125870, by rfl⟩ : syracuseStep 167827 = 251741) B251741
theorem B135059 : Blo 131789 135059 := bstep (se 1 (by rfl) ⟨101294, by rfl⟩ : syracuseStep 135059 = 202589) B202589
theorem B200609 : Blo 131789 200609 := bstep (se 2 (by rfl) ⟨75228, by rfl⟩ : syracuseStep 200609 = 150457) B150457
theorem B135075 : Blo 131789 135075 := bstep (se 1 (by rfl) ⟨101306, by rfl⟩ : syracuseStep 135075 = 202613) B202613
theorem B200627 : Blo 131789 200627 := bstep (se 1 (by rfl) ⟨150470, by rfl⟩ : syracuseStep 200627 = 300941) B300941
theorem B135091 : Blo 131789 135091 := bstep (se 1 (by rfl) ⟨101318, by rfl⟩ : syracuseStep 135091 = 202637) B202637
theorem B135107 : Blo 131789 135107 := bstep (se 1 (by rfl) ⟨101330, by rfl⟩ : syracuseStep 135107 = 202661) B202661
theorem B298961 : Blo 131789 298961 := bstep (se 2 (by rfl) ⟨112110, by rfl⟩ : syracuseStep 298961 = 224221) B224221
theorem B200657 : Blo 131789 200657 := bstep (se 2 (by rfl) ⟨75246, by rfl⟩ : syracuseStep 200657 = 150493) B150493
theorem B135123 : Blo 131789 135123 := bstep (se 1 (by rfl) ⟨101342, by rfl⟩ : syracuseStep 135123 = 202685) B202685
theorem B298979 : Blo 131789 298979 := bstep (se 1 (by rfl) ⟨224234, by rfl⟩ : syracuseStep 298979 = 448469) B448469
theorem B200675 : Blo 131789 200675 := bstep (se 1 (by rfl) ⟨150506, by rfl⟩ : syracuseStep 200675 = 301013) B301013
theorem B135139 : Blo 131789 135139 := bstep (se 1 (by rfl) ⟨101354, by rfl⟩ : syracuseStep 135139 = 202709) B202709
theorem B167923 : Blo 131789 167923 := bstep (se 1 (by rfl) ⟨125942, by rfl⟩ : syracuseStep 167923 = 251885) B251885
theorem B135155 : Blo 131789 135155 := bstep (se 1 (by rfl) ⟨101366, by rfl⟩ : syracuseStep 135155 = 202733) B202733
theorem B200705 : Blo 131789 200705 := bstep (se 2 (by rfl) ⟨75264, by rfl⟩ : syracuseStep 200705 = 150529) B150529
theorem B135171 : Blo 131789 135171 := bstep (se 1 (by rfl) ⟨101378, by rfl⟩ : syracuseStep 135171 = 202757) B202757
theorem B200723 : Blo 131789 200723 := bstep (se 1 (by rfl) ⟨150542, by rfl⟩ : syracuseStep 200723 = 301085) B301085
theorem B135187 : Blo 131789 135187 := bstep (se 1 (by rfl) ⟨101390, by rfl⟩ : syracuseStep 135187 = 202781) B202781
theorem B757795 : Blo 131789 757795 := bstep (se 1 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 757795 = 1136693) B1136693
theorem B135203 : Blo 131789 135203 := bstep (se 1 (by rfl) ⟨101402, by rfl⟩ : syracuseStep 135203 = 202805) B202805
theorem B200753 : Blo 131789 200753 := bstep (se 2 (by rfl) ⟨75282, by rfl⟩ : syracuseStep 200753 = 150565) B150565
theorem B135219 : Blo 131789 135219 := bstep (se 1 (by rfl) ⟨101414, by rfl⟩ : syracuseStep 135219 = 202829) B202829
theorem B200771 : Blo 131789 200771 := bstep (se 1 (by rfl) ⟨150578, by rfl⟩ : syracuseStep 200771 = 301157) B301157
theorem B135235 : Blo 131789 135235 := bstep (se 1 (by rfl) ⟨101426, by rfl⟩ : syracuseStep 135235 = 202853) B202853
theorem B135251 : Blo 131789 135251 := bstep (se 1 (by rfl) ⟨101438, by rfl⟩ : syracuseStep 135251 = 202877) B202877
theorem B200801 : Blo 131789 200801 := bstep (se 2 (by rfl) ⟨75300, by rfl⟩ : syracuseStep 200801 = 150601) B150601
theorem B135267 : Blo 131789 135267 := bstep (se 1 (by rfl) ⟨101450, by rfl⟩ : syracuseStep 135267 = 202901) B202901
theorem B200819 : Blo 131789 200819 := bstep (se 1 (by rfl) ⟨150614, by rfl⟩ : syracuseStep 200819 = 301229) B301229
theorem B135283 : Blo 131789 135283 := bstep (se 1 (by rfl) ⟨101462, by rfl⟩ : syracuseStep 135283 = 202925) B202925
theorem B135299 : Blo 131789 135299 := bstep (se 1 (by rfl) ⟨101474, by rfl⟩ : syracuseStep 135299 = 202949) B202949
theorem B2330765 : Blo 131789 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B200849 : Blo 131789 200849 := bstep (se 2 (by rfl) ⟨75318, by rfl⟩ : syracuseStep 200849 = 150637) B150637
theorem B135315 : Blo 131789 135315 := bstep (se 1 (by rfl) ⟨101486, by rfl⟩ : syracuseStep 135315 = 202973) B202973
theorem B200867 : Blo 131789 200867 := bstep (se 1 (by rfl) ⟨150650, by rfl⟩ : syracuseStep 200867 = 301301) B301301
theorem B135331 : Blo 131789 135331 := bstep (se 1 (by rfl) ⟨101498, by rfl⟩ : syracuseStep 135331 = 202997) B202997
theorem B135347 : Blo 131789 135347 := bstep (se 1 (by rfl) ⟨101510, by rfl⟩ : syracuseStep 135347 = 203021) B203021
theorem B200897 : Blo 131789 200897 := bstep (se 2 (by rfl) ⟨75336, by rfl⟩ : syracuseStep 200897 = 150673) B150673
theorem B135363 : Blo 131789 135363 := bstep (se 1 (by rfl) ⟨101522, by rfl⟩ : syracuseStep 135363 = 203045) B203045
theorem B430285 : Blo 131789 430285 := bstep (se 3 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 430285 = 161357) B161357
theorem B200915 : Blo 131789 200915 := bstep (se 1 (by rfl) ⟨150686, by rfl⟩ : syracuseStep 200915 = 301373) B301373
theorem B135379 : Blo 131789 135379 := bstep (se 1 (by rfl) ⟨101534, by rfl⟩ : syracuseStep 135379 = 203069) B203069
theorem B135395 : Blo 131789 135395 := bstep (se 1 (by rfl) ⟨101546, by rfl⟩ : syracuseStep 135395 = 203093) B203093
theorem B299249 : Blo 131789 299249 := bstep (se 2 (by rfl) ⟨112218, by rfl⟩ : syracuseStep 299249 = 224437) B224437
theorem B200945 : Blo 131789 200945 := bstep (se 2 (by rfl) ⟨75354, by rfl⟩ : syracuseStep 200945 = 150709) B150709
theorem B135411 : Blo 131789 135411 := bstep (se 1 (by rfl) ⟨101558, by rfl⟩ : syracuseStep 135411 = 203117) B203117
theorem B299267 : Blo 131789 299267 := bstep (se 1 (by rfl) ⟨224450, by rfl⟩ : syracuseStep 299267 = 448901) B448901
theorem B200963 : Blo 131789 200963 := bstep (se 1 (by rfl) ⟨150722, by rfl⟩ : syracuseStep 200963 = 301445) B301445
theorem B135427 : Blo 131789 135427 := bstep (se 1 (by rfl) ⟨101570, by rfl⟩ : syracuseStep 135427 = 203141) B203141
theorem B135443 : Blo 131789 135443 := bstep (se 1 (by rfl) ⟨101582, by rfl⟩ : syracuseStep 135443 = 203165) B203165
theorem B200993 : Blo 131789 200993 := bstep (se 2 (by rfl) ⟨75372, by rfl⟩ : syracuseStep 200993 = 150745) B150745
theorem B135459 : Blo 131789 135459 := bstep (se 1 (by rfl) ⟨101594, by rfl⟩ : syracuseStep 135459 = 203189) B203189
theorem B201011 : Blo 131789 201011 := bstep (se 1 (by rfl) ⟨150758, by rfl⟩ : syracuseStep 201011 = 301517) B301517
theorem B135475 : Blo 131789 135475 := bstep (se 1 (by rfl) ⟨101606, by rfl⟩ : syracuseStep 135475 = 203213) B203213
theorem B135491 : Blo 131789 135491 := bstep (se 1 (by rfl) ⟨101618, by rfl⟩ : syracuseStep 135491 = 203237) B203237
theorem B201041 : Blo 131789 201041 := bstep (se 2 (by rfl) ⟨75390, by rfl⟩ : syracuseStep 201041 = 150781) B150781
theorem B135507 : Blo 131789 135507 := bstep (se 1 (by rfl) ⟨101630, by rfl⟩ : syracuseStep 135507 = 203261) B203261
theorem B201059 : Blo 131789 201059 := bstep (se 1 (by rfl) ⟨150794, by rfl⟩ : syracuseStep 201059 = 301589) B301589
theorem B135523 : Blo 131789 135523 := bstep (se 1 (by rfl) ⟨101642, by rfl⟩ : syracuseStep 135523 = 203285) B203285
theorem B135539 : Blo 131789 135539 := bstep (se 1 (by rfl) ⟨101654, by rfl⟩ : syracuseStep 135539 = 203309) B203309
theorem B201089 : Blo 131789 201089 := bstep (se 2 (by rfl) ⟨75408, by rfl⟩ : syracuseStep 201089 = 150817) B150817
theorem B135555 : Blo 131789 135555 := bstep (se 1 (by rfl) ⟨101666, by rfl⟩ : syracuseStep 135555 = 203333) B203333
theorem B201107 : Blo 131789 201107 := bstep (se 1 (by rfl) ⟨150830, by rfl⟩ : syracuseStep 201107 = 301661) B301661
theorem B135571 : Blo 131789 135571 := bstep (se 1 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 135571 = 203357) B203357
theorem B135587 : Blo 131789 135587 := bstep (se 1 (by rfl) ⟨101690, by rfl⟩ : syracuseStep 135587 = 203381) B203381
theorem B201137 : Blo 131789 201137 := bstep (se 2 (by rfl) ⟨75426, by rfl⟩ : syracuseStep 201137 = 150853) B150853
theorem B135603 : Blo 131789 135603 := bstep (se 1 (by rfl) ⟨101702, by rfl⟩ : syracuseStep 135603 = 203405) B203405
theorem B201155 : Blo 131789 201155 := bstep (se 1 (by rfl) ⟨150866, by rfl⟩ : syracuseStep 201155 = 301733) B301733
theorem B135619 : Blo 131789 135619 := bstep (se 1 (by rfl) ⟨101714, by rfl⟩ : syracuseStep 135619 = 203429) B203429
theorem B135635 : Blo 131789 135635 := bstep (se 1 (by rfl) ⟨101726, by rfl⟩ : syracuseStep 135635 = 203453) B203453
theorem B201185 : Blo 131789 201185 := bstep (se 2 (by rfl) ⟨75444, by rfl⟩ : syracuseStep 201185 = 150889) B150889
theorem B168419 : Blo 131789 168419 := bstep (se 1 (by rfl) ⟨126314, by rfl⟩ : syracuseStep 168419 = 252629) B252629
theorem B135651 : Blo 131789 135651 := bstep (se 1 (by rfl) ⟨101738, by rfl⟩ : syracuseStep 135651 = 203477) B203477
theorem B201203 : Blo 131789 201203 := bstep (se 1 (by rfl) ⟨150902, by rfl⟩ : syracuseStep 201203 = 301805) B301805
theorem B135667 : Blo 131789 135667 := bstep (se 1 (by rfl) ⟨101750, by rfl⟩ : syracuseStep 135667 = 203501) B203501
theorem B135683 : Blo 131789 135683 := bstep (se 1 (by rfl) ⟨101762, by rfl⟩ : syracuseStep 135683 = 203525) B203525
theorem B299537 : Blo 131789 299537 := bstep (se 2 (by rfl) ⟨112326, by rfl⟩ : syracuseStep 299537 = 224653) B224653
theorem B201233 : Blo 131789 201233 := bstep (se 2 (by rfl) ⟨75462, by rfl⟩ : syracuseStep 201233 = 150925) B150925
theorem B135699 : Blo 131789 135699 := bstep (se 1 (by rfl) ⟨101774, by rfl⟩ : syracuseStep 135699 = 203549) B203549
theorem B299555 : Blo 131789 299555 := bstep (se 1 (by rfl) ⟨224666, by rfl⟩ : syracuseStep 299555 = 449333) B449333
theorem B201251 : Blo 131789 201251 := bstep (se 1 (by rfl) ⟨150938, by rfl⟩ : syracuseStep 201251 = 301877) B301877
theorem B135715 : Blo 131789 135715 := bstep (se 1 (by rfl) ⟨101786, by rfl⟩ : syracuseStep 135715 = 203573) B203573
theorem B758321 : Blo 131789 758321 := bstep (se 2 (by rfl) ⟨284370, by rfl⟩ : syracuseStep 758321 = 568741) B568741
theorem B135731 : Blo 131789 135731 := bstep (se 1 (by rfl) ⟨101798, by rfl⟩ : syracuseStep 135731 = 203597) B203597
theorem B201281 : Blo 131789 201281 := bstep (se 2 (by rfl) ⟨75480, by rfl⟩ : syracuseStep 201281 = 150961) B150961
theorem B135747 : Blo 131789 135747 := bstep (se 1 (by rfl) ⟨101810, by rfl⟩ : syracuseStep 135747 = 203621) B203621
theorem B201299 : Blo 131789 201299 := bstep (se 1 (by rfl) ⟨150974, by rfl⟩ : syracuseStep 201299 = 301949) B301949
theorem B135763 : Blo 131789 135763 := bstep (se 1 (by rfl) ⟨101822, by rfl⟩ : syracuseStep 135763 = 203645) B203645
theorem B135779 : Blo 131789 135779 := bstep (se 1 (by rfl) ⟨101834, by rfl⟩ : syracuseStep 135779 = 203669) B203669
theorem B201329 : Blo 131789 201329 := bstep (se 2 (by rfl) ⟨75498, by rfl⟩ : syracuseStep 201329 = 150997) B150997
theorem B201347 : Blo 131789 201347 := bstep (se 1 (by rfl) ⟨151010, by rfl⟩ : syracuseStep 201347 = 302021) B302021
theorem B201377 : Blo 131789 201377 := bstep (se 2 (by rfl) ⟨75516, by rfl⟩ : syracuseStep 201377 = 151033) B151033
theorem B201395 : Blo 131789 201395 := bstep (se 1 (by rfl) ⟨151046, by rfl⟩ : syracuseStep 201395 = 302093) B302093
theorem B201425 : Blo 131789 201425 := bstep (se 2 (by rfl) ⟨75534, by rfl⟩ : syracuseStep 201425 = 151069) B151069
theorem B201443 : Blo 131789 201443 := bstep (se 1 (by rfl) ⟨151082, by rfl⟩ : syracuseStep 201443 = 302165) B302165
theorem B1151729 : Blo 131789 1151729 := bstep (se 2 (by rfl) ⟨431898, by rfl⟩ : syracuseStep 1151729 = 863797) B863797
theorem B201473 : Blo 131789 201473 := bstep (se 2 (by rfl) ⟨75552, by rfl⟩ : syracuseStep 201473 = 151105) B151105
theorem B201491 : Blo 131789 201491 := bstep (se 1 (by rfl) ⟨151118, by rfl⟩ : syracuseStep 201491 = 302237) B302237
theorem B299825 : Blo 131789 299825 := bstep (se 2 (by rfl) ⟨112434, by rfl⟩ : syracuseStep 299825 = 224869) B224869
theorem B201521 : Blo 131789 201521 := bstep (se 2 (by rfl) ⟨75570, by rfl⟩ : syracuseStep 201521 = 151141) B151141
theorem B299843 : Blo 131789 299843 := bstep (se 1 (by rfl) ⟨224882, by rfl⟩ : syracuseStep 299843 = 449765) B449765
theorem B201539 : Blo 131789 201539 := bstep (se 1 (by rfl) ⟨151154, by rfl⟩ : syracuseStep 201539 = 302309) B302309
theorem B201569 : Blo 131789 201569 := bstep (se 2 (by rfl) ⟨75588, by rfl⟩ : syracuseStep 201569 = 151177) B151177
theorem B201587 : Blo 131789 201587 := bstep (se 1 (by rfl) ⟨151190, by rfl⟩ : syracuseStep 201587 = 302381) B302381
theorem B201617 : Blo 131789 201617 := bstep (se 2 (by rfl) ⟨75606, by rfl⟩ : syracuseStep 201617 = 151213) B151213
theorem B201635 : Blo 131789 201635 := bstep (se 1 (by rfl) ⟨151226, by rfl⟩ : syracuseStep 201635 = 302453) B302453
theorem B201665 : Blo 131789 201665 := bstep (se 2 (by rfl) ⟨75624, by rfl⟩ : syracuseStep 201665 = 151249) B151249
theorem B201683 : Blo 131789 201683 := bstep (se 1 (by rfl) ⟨151262, by rfl⟩ : syracuseStep 201683 = 302525) B302525
theorem B201713 : Blo 131789 201713 := bstep (se 2 (by rfl) ⟨75642, by rfl⟩ : syracuseStep 201713 = 151285) B151285
theorem B201731 : Blo 131789 201731 := bstep (se 1 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 201731 = 302597) B302597
theorem B201761 : Blo 131789 201761 := bstep (se 2 (by rfl) ⟨75660, by rfl⟩ : syracuseStep 201761 = 151321) B151321
theorem B201779 : Blo 131789 201779 := bstep (se 1 (by rfl) ⟨151334, by rfl⟩ : syracuseStep 201779 = 302669) B302669
theorem B300113 : Blo 131789 300113 := bstep (se 2 (by rfl) ⟨112542, by rfl⟩ : syracuseStep 300113 = 225085) B225085
theorem B201809 : Blo 131789 201809 := bstep (se 2 (by rfl) ⟨75678, by rfl⟩ : syracuseStep 201809 = 151357) B151357
theorem B300131 : Blo 131789 300131 := bstep (se 1 (by rfl) ⟨225098, by rfl⟩ : syracuseStep 300131 = 450197) B450197
theorem B201827 : Blo 131789 201827 := bstep (se 1 (by rfl) ⟨151370, by rfl⟩ : syracuseStep 201827 = 302741) B302741
theorem B201857 : Blo 131789 201857 := bstep (se 2 (by rfl) ⟨75696, by rfl⟩ : syracuseStep 201857 = 151393) B151393
theorem B201875 : Blo 131789 201875 := bstep (se 1 (by rfl) ⟨151406, by rfl⟩ : syracuseStep 201875 = 302813) B302813
theorem B169123 : Blo 131789 169123 := bstep (se 1 (by rfl) ⟨126842, by rfl⟩ : syracuseStep 169123 = 253685) B253685
theorem B234659 : Blo 131789 234659 := bstep (se 1 (by rfl) ⟨175994, by rfl⟩ : syracuseStep 234659 = 351989) B351989
theorem B201905 : Blo 131789 201905 := bstep (se 2 (by rfl) ⟨75714, by rfl⟩ : syracuseStep 201905 = 151429) B151429
theorem B201923 : Blo 131789 201923 := bstep (se 1 (by rfl) ⟨151442, by rfl⟩ : syracuseStep 201923 = 302885) B302885
theorem B201953 : Blo 131789 201953 := bstep (se 2 (by rfl) ⟨75732, by rfl⟩ : syracuseStep 201953 = 151465) B151465
theorem B201971 : Blo 131789 201971 := bstep (se 1 (by rfl) ⟨151478, by rfl⟩ : syracuseStep 201971 = 302957) B302957
theorem B169219 : Blo 131789 169219 := bstep (se 1 (by rfl) ⟨126914, by rfl⟩ : syracuseStep 169219 = 253829) B253829
theorem B202001 : Blo 131789 202001 := bstep (se 2 (by rfl) ⟨75750, by rfl⟩ : syracuseStep 202001 = 151501) B151501
theorem B202019 : Blo 131789 202019 := bstep (se 1 (by rfl) ⟨151514, by rfl⟩ : syracuseStep 202019 = 303029) B303029
theorem B202049 : Blo 131789 202049 := bstep (se 2 (by rfl) ⟨75768, by rfl⟩ : syracuseStep 202049 = 151537) B151537
theorem B202067 : Blo 131789 202067 := bstep (se 1 (by rfl) ⟨151550, by rfl⟩ : syracuseStep 202067 = 303101) B303101
theorem B300401 : Blo 131789 300401 := bstep (se 2 (by rfl) ⟨112650, by rfl⟩ : syracuseStep 300401 = 225301) B225301
theorem B202097 : Blo 131789 202097 := bstep (se 2 (by rfl) ⟨75786, by rfl⟩ : syracuseStep 202097 = 151573) B151573
theorem B300419 : Blo 131789 300419 := bstep (se 1 (by rfl) ⟨225314, by rfl⟩ : syracuseStep 300419 = 450629) B450629
theorem B202115 : Blo 131789 202115 := bstep (se 1 (by rfl) ⟨151586, by rfl⟩ : syracuseStep 202115 = 303173) B303173
theorem B202145 : Blo 131789 202145 := bstep (se 2 (by rfl) ⟨75804, by rfl⟩ : syracuseStep 202145 = 151609) B151609
theorem B202163 : Blo 131789 202163 := bstep (se 1 (by rfl) ⟨151622, by rfl⟩ : syracuseStep 202163 = 303245) B303245
theorem B202193 : Blo 131789 202193 := bstep (se 2 (by rfl) ⟨75822, by rfl⟩ : syracuseStep 202193 = 151645) B151645
theorem B202211 : Blo 131789 202211 := bstep (se 1 (by rfl) ⟨151658, by rfl⟩ : syracuseStep 202211 = 303317) B303317
theorem B202241 : Blo 131789 202241 := bstep (se 2 (by rfl) ⟨75840, by rfl⟩ : syracuseStep 202241 = 151681) B151681
theorem B202259 : Blo 131789 202259 := bstep (se 1 (by rfl) ⟨151694, by rfl⟩ : syracuseStep 202259 = 303389) B303389
theorem B726563 : Blo 131789 726563 := bstep (se 1 (by rfl) ⟨544922, by rfl⟩ : syracuseStep 726563 = 1089845) B1089845
theorem B202289 : Blo 131789 202289 := bstep (se 2 (by rfl) ⟨75858, by rfl⟩ : syracuseStep 202289 = 151717) B151717
theorem B202307 : Blo 131789 202307 := bstep (se 1 (by rfl) ⟨151730, by rfl⟩ : syracuseStep 202307 = 303461) B303461
theorem B202337 : Blo 131789 202337 := bstep (se 2 (by rfl) ⟨75876, by rfl⟩ : syracuseStep 202337 = 151753) B151753
theorem B857699 : Blo 131789 857699 := bstep (se 1 (by rfl) ⟨643274, by rfl⟩ : syracuseStep 857699 = 1286549) B1286549
theorem B202355 : Blo 131789 202355 := bstep (se 1 (by rfl) ⟨151766, by rfl⟩ : syracuseStep 202355 = 303533) B303533
theorem B300689 : Blo 131789 300689 := bstep (se 2 (by rfl) ⟨112758, by rfl⟩ : syracuseStep 300689 = 225517) B225517
theorem B202385 : Blo 131789 202385 := bstep (se 2 (by rfl) ⟨75894, by rfl⟩ : syracuseStep 202385 = 151789) B151789
theorem B300707 : Blo 131789 300707 := bstep (se 1 (by rfl) ⟨225530, by rfl⟩ : syracuseStep 300707 = 451061) B451061
theorem B202403 : Blo 131789 202403 := bstep (se 1 (by rfl) ⟨151802, by rfl⟩ : syracuseStep 202403 = 303605) B303605
theorem B824995 : Blo 131789 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B202433 : Blo 131789 202433 := bstep (se 2 (by rfl) ⟨75912, by rfl⟩ : syracuseStep 202433 = 151825) B151825
theorem B267985 : Blo 131789 267985 := bstep (se 2 (by rfl) ⟨100494, by rfl⟩ : syracuseStep 267985 = 200989) B200989
theorem B202451 : Blo 131789 202451 := bstep (se 1 (by rfl) ⟨151838, by rfl⟩ : syracuseStep 202451 = 303677) B303677
theorem B202481 : Blo 131789 202481 := bstep (se 2 (by rfl) ⟨75930, by rfl⟩ : syracuseStep 202481 = 151861) B151861
theorem B694001 : Blo 131789 694001 := bstep (se 2 (by rfl) ⟨260250, by rfl⟩ : syracuseStep 694001 = 520501) B520501
theorem B169715 : Blo 131789 169715 := bstep (se 1 (by rfl) ⟨127286, by rfl⟩ : syracuseStep 169715 = 254573) B254573
theorem B202499 : Blo 131789 202499 := bstep (se 1 (by rfl) ⟨151874, by rfl⟩ : syracuseStep 202499 = 303749) B303749
theorem B202529 : Blo 131789 202529 := bstep (se 2 (by rfl) ⟨75948, by rfl⟩ : syracuseStep 202529 = 151897) B151897
theorem B202547 : Blo 131789 202547 := bstep (se 1 (by rfl) ⟨151910, by rfl⟩ : syracuseStep 202547 = 303821) B303821
theorem B202577 : Blo 131789 202577 := bstep (se 2 (by rfl) ⟨75966, by rfl⟩ : syracuseStep 202577 = 151933) B151933
theorem B202595 : Blo 131789 202595 := bstep (se 1 (by rfl) ⟨151946, by rfl⟩ : syracuseStep 202595 = 303893) B303893
theorem B202625 : Blo 131789 202625 := bstep (se 2 (by rfl) ⟨75984, by rfl⟩ : syracuseStep 202625 = 151969) B151969
theorem B202643 : Blo 131789 202643 := bstep (se 1 (by rfl) ⟨151982, by rfl⟩ : syracuseStep 202643 = 303965) B303965
theorem B300977 : Blo 131789 300977 := bstep (se 2 (by rfl) ⟨112866, by rfl⟩ : syracuseStep 300977 = 225733) B225733
theorem B202673 : Blo 131789 202673 := bstep (se 2 (by rfl) ⟨76002, by rfl⟩ : syracuseStep 202673 = 152005) B152005
theorem B300995 : Blo 131789 300995 := bstep (se 1 (by rfl) ⟨225746, by rfl⟩ : syracuseStep 300995 = 451493) B451493
theorem B202691 : Blo 131789 202691 := bstep (se 1 (by rfl) ⟨152018, by rfl⟩ : syracuseStep 202691 = 304037) B304037
theorem B202721 : Blo 131789 202721 := bstep (se 2 (by rfl) ⟨76020, by rfl⟩ : syracuseStep 202721 = 152041) B152041
theorem B759779 : Blo 131789 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B202739 : Blo 131789 202739 := bstep (se 1 (by rfl) ⟨152054, by rfl⟩ : syracuseStep 202739 = 304109) B304109
theorem B333841 : Blo 131789 333841 := bstep (se 2 (by rfl) ⟨125190, by rfl⟩ : syracuseStep 333841 = 250381) B250381
theorem B202769 : Blo 131789 202769 := bstep (se 2 (by rfl) ⟨76038, by rfl⟩ : syracuseStep 202769 = 152077) B152077
theorem B202787 : Blo 131789 202787 := bstep (se 1 (by rfl) ⟨152090, by rfl⟩ : syracuseStep 202787 = 304181) B304181
theorem B202817 : Blo 131789 202817 := bstep (se 2 (by rfl) ⟨76056, by rfl⟩ : syracuseStep 202817 = 152113) B152113
theorem B202835 : Blo 131789 202835 := bstep (se 1 (by rfl) ⟨152126, by rfl⟩ : syracuseStep 202835 = 304253) B304253
theorem B202865 : Blo 131789 202865 := bstep (se 2 (by rfl) ⟨76074, by rfl⟩ : syracuseStep 202865 = 152149) B152149
theorem B202883 : Blo 131789 202883 := bstep (se 1 (by rfl) ⟨152162, by rfl⟩ : syracuseStep 202883 = 304325) B304325
theorem B202913 : Blo 131789 202913 := bstep (se 2 (by rfl) ⟨76092, by rfl⟩ : syracuseStep 202913 = 152185) B152185
theorem B202931 : Blo 131789 202931 := bstep (se 1 (by rfl) ⟨152198, by rfl⟩ : syracuseStep 202931 = 304397) B304397
theorem B301265 : Blo 131789 301265 := bstep (se 2 (by rfl) ⟨112974, by rfl⟩ : syracuseStep 301265 = 225949) B225949
theorem B202961 : Blo 131789 202961 := bstep (se 2 (by rfl) ⟨76110, by rfl⟩ : syracuseStep 202961 = 152221) B152221
theorem B301283 : Blo 131789 301283 := bstep (se 1 (by rfl) ⟨225962, by rfl⟩ : syracuseStep 301283 = 451925) B451925
theorem B202979 : Blo 131789 202979 := bstep (se 1 (by rfl) ⟨152234, by rfl⟩ : syracuseStep 202979 = 304469) B304469
theorem B203009 : Blo 131789 203009 := bstep (se 2 (by rfl) ⟨76128, by rfl⟩ : syracuseStep 203009 = 152257) B152257
theorem B203027 : Blo 131789 203027 := bstep (se 1 (by rfl) ⟨152270, by rfl⟩ : syracuseStep 203027 = 304541) B304541
theorem B334115 : Blo 131789 334115 := bstep (se 1 (by rfl) ⟨250586, by rfl⟩ : syracuseStep 334115 = 501173) B501173
theorem B203057 : Blo 131789 203057 := bstep (se 2 (by rfl) ⟨76146, by rfl⟩ : syracuseStep 203057 = 152293) B152293
theorem B203075 : Blo 131789 203075 := bstep (se 1 (by rfl) ⟨152306, by rfl⟩ : syracuseStep 203075 = 304613) B304613
theorem B203105 : Blo 131789 203105 := bstep (se 2 (by rfl) ⟨76164, by rfl⟩ : syracuseStep 203105 = 152329) B152329
theorem B203123 : Blo 131789 203123 := bstep (se 1 (by rfl) ⟨152342, by rfl⟩ : syracuseStep 203123 = 304685) B304685
theorem B203153 : Blo 131789 203153 := bstep (se 2 (by rfl) ⟨76182, by rfl⟩ : syracuseStep 203153 = 152365) B152365
theorem B203171 : Blo 131789 203171 := bstep (se 1 (by rfl) ⟨152378, by rfl⟩ : syracuseStep 203171 = 304757) B304757
theorem B170419 : Blo 131789 170419 := bstep (se 1 (by rfl) ⟨127814, by rfl⟩ : syracuseStep 170419 = 255629) B255629
theorem B203201 : Blo 131789 203201 := bstep (se 2 (by rfl) ⟨76200, by rfl⟩ : syracuseStep 203201 = 152401) B152401
theorem B1612229 : Blo 131789 1612229 := bstep (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) B302293
theorem B203219 : Blo 131789 203219 := bstep (se 1 (by rfl) ⟨152414, by rfl⟩ : syracuseStep 203219 = 304829) B304829
theorem B334307 : Blo 131789 334307 := bstep (se 1 (by rfl) ⟨250730, by rfl⟩ : syracuseStep 334307 = 501461) B501461
theorem B268771 : Blo 131789 268771 := bstep (se 1 (by rfl) ⟨201578, by rfl⟩ : syracuseStep 268771 = 403157) B403157
theorem B301553 : Blo 131789 301553 := bstep (se 2 (by rfl) ⟨113082, by rfl⟩ : syracuseStep 301553 = 226165) B226165
theorem B203249 : Blo 131789 203249 := bstep (se 2 (by rfl) ⟨76218, by rfl⟩ : syracuseStep 203249 = 152437) B152437
theorem B301571 : Blo 131789 301571 := bstep (se 1 (by rfl) ⟨226178, by rfl⟩ : syracuseStep 301571 = 452357) B452357
theorem B203267 : Blo 131789 203267 := bstep (se 1 (by rfl) ⟨152450, by rfl⟩ : syracuseStep 203267 = 304901) B304901
theorem B170515 : Blo 131789 170515 := bstep (se 1 (by rfl) ⟨127886, by rfl⟩ : syracuseStep 170515 = 255773) B255773
theorem B203297 : Blo 131789 203297 := bstep (se 2 (by rfl) ⟨76236, by rfl⟩ : syracuseStep 203297 = 152473) B152473
theorem B203315 : Blo 131789 203315 := bstep (se 1 (by rfl) ⟨152486, by rfl⟩ : syracuseStep 203315 = 304973) B304973
theorem B203345 : Blo 131789 203345 := bstep (se 2 (by rfl) ⟨76254, by rfl⟩ : syracuseStep 203345 = 152509) B152509
theorem B203363 : Blo 131789 203363 := bstep (se 1 (by rfl) ⟨152522, by rfl⟩ : syracuseStep 203363 = 305045) B305045
theorem B203393 : Blo 131789 203393 := bstep (se 2 (by rfl) ⟨76272, by rfl⟩ : syracuseStep 203393 = 152545) B152545
theorem B694925 : Blo 131789 694925 := bstep (se 3 (by rfl) ⟨130298, by rfl⟩ : syracuseStep 694925 = 260597) B260597
theorem B203411 : Blo 131789 203411 := bstep (se 1 (by rfl) ⟨152558, by rfl⟩ : syracuseStep 203411 = 305117) B305117
theorem B203441 : Blo 131789 203441 := bstep (se 2 (by rfl) ⟨76290, by rfl⟩ : syracuseStep 203441 = 152581) B152581
theorem B203459 : Blo 131789 203459 := bstep (se 1 (by rfl) ⟨152594, by rfl⟩ : syracuseStep 203459 = 305189) B305189
theorem B203489 : Blo 131789 203489 := bstep (se 2 (by rfl) ⟨76308, by rfl⟩ : syracuseStep 203489 = 152617) B152617
theorem B203507 : Blo 131789 203507 := bstep (se 1 (by rfl) ⟨152630, by rfl⟩ : syracuseStep 203507 = 305261) B305261
theorem B301841 : Blo 131789 301841 := bstep (se 2 (by rfl) ⟨113190, by rfl⟩ : syracuseStep 301841 = 226381) B226381
theorem B203537 : Blo 131789 203537 := bstep (se 2 (by rfl) ⟨76326, by rfl⟩ : syracuseStep 203537 = 152653) B152653
theorem B301859 : Blo 131789 301859 := bstep (se 1 (by rfl) ⟨226394, by rfl⟩ : syracuseStep 301859 = 452789) B452789
theorem B203555 : Blo 131789 203555 := bstep (se 1 (by rfl) ⟨152666, by rfl⟩ : syracuseStep 203555 = 305333) B305333
theorem B203585 : Blo 131789 203585 := bstep (se 2 (by rfl) ⟨76344, by rfl⟩ : syracuseStep 203585 = 152689) B152689
theorem B203603 : Blo 131789 203603 := bstep (se 1 (by rfl) ⟨152702, by rfl⟩ : syracuseStep 203603 = 305405) B305405
theorem B203633 : Blo 131789 203633 := bstep (se 2 (by rfl) ⟨76362, by rfl⟩ : syracuseStep 203633 = 152725) B152725
theorem B203651 : Blo 131789 203651 := bstep (se 1 (by rfl) ⟨152738, by rfl⟩ : syracuseStep 203651 = 305477) B305477
theorem B203681 : Blo 131789 203681 := bstep (se 2 (by rfl) ⟨76380, by rfl⟩ : syracuseStep 203681 = 152761) B152761
theorem B171011 : Blo 131789 171011 := bstep (se 1 (by rfl) ⟨128258, by rfl⟩ : syracuseStep 171011 = 256517) B256517
theorem B302129 : Blo 131789 302129 := bstep (se 2 (by rfl) ⟨113298, by rfl⟩ : syracuseStep 302129 = 226597) B226597
theorem B302147 : Blo 131789 302147 := bstep (se 1 (by rfl) ⟨226610, by rfl⟩ : syracuseStep 302147 = 453221) B453221
theorem B1154189 : Blo 131789 1154189 := bstep (se 3 (by rfl) ⟨216410, by rfl⟩ : syracuseStep 1154189 = 432821) B432821
theorem B204083 : Blo 131789 204083 := bstep (se 1 (by rfl) ⟨153062, by rfl⟩ : syracuseStep 204083 = 306125) B306125
theorem B302417 : Blo 131789 302417 := bstep (se 2 (by rfl) ⟨113406, by rfl⟩ : syracuseStep 302417 = 226813) B226813
theorem B302435 : Blo 131789 302435 := bstep (se 1 (by rfl) ⟨226826, by rfl⟩ : syracuseStep 302435 = 453653) B453653
theorem B335249 : Blo 131789 335249 := bstep (se 2 (by rfl) ⟨125718, by rfl⟩ : syracuseStep 335249 = 251437) B251437
theorem B335299 : Blo 131789 335299 := bstep (se 1 (by rfl) ⟨251474, by rfl⟩ : syracuseStep 335299 = 502949) B502949
theorem B368077 : Blo 131789 368077 := bstep (se 3 (by rfl) ⟨69014, by rfl⟩ : syracuseStep 368077 = 138029) B138029
theorem B1711601 : Blo 131789 1711601 := bstep (se 2 (by rfl) ⟨641850, by rfl⟩ : syracuseStep 1711601 = 1283701) B1283701
theorem B400909 : Blo 131789 400909 := bstep (se 3 (by rfl) ⟨75170, by rfl⟩ : syracuseStep 400909 = 150341) B150341
theorem B859697 : Blo 131789 859697 := bstep (se 2 (by rfl) ⟨322386, by rfl⟩ : syracuseStep 859697 = 644773) B644773
theorem B335441 : Blo 131789 335441 := bstep (se 2 (by rfl) ⟨125790, by rfl⟩ : syracuseStep 335441 = 251581) B251581
theorem B433745 : Blo 131789 433745 := bstep (se 2 (by rfl) ⟨162654, by rfl⟩ : syracuseStep 433745 = 325309) B325309
theorem B302705 : Blo 131789 302705 := bstep (se 2 (by rfl) ⟨113514, by rfl⟩ : syracuseStep 302705 = 227029) B227029
theorem B302723 : Blo 131789 302723 := bstep (se 1 (by rfl) ⟨227042, by rfl⟩ : syracuseStep 302723 = 454085) B454085
theorem B171715 : Blo 131789 171715 := bstep (se 1 (by rfl) ⟨128786, by rfl⟩ : syracuseStep 171715 = 257573) B257573
theorem B433937 : Blo 131789 433937 := bstep (se 2 (by rfl) ⟨162726, by rfl⟩ : syracuseStep 433937 = 325453) B325453
theorem B171811 : Blo 131789 171811 := bstep (se 1 (by rfl) ⟨128858, by rfl⟩ : syracuseStep 171811 = 257717) B257717
theorem B761669 : Blo 131789 761669 := bstep (se 4 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 761669 = 142813) B142813
theorem B204643 : Blo 131789 204643 := bstep (se 1 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 204643 = 306965) B306965
theorem B302993 : Blo 131789 302993 := bstep (se 2 (by rfl) ⟨113622, by rfl⟩ : syracuseStep 302993 = 227245) B227245
theorem B303011 : Blo 131789 303011 := bstep (se 1 (by rfl) ⟨227258, by rfl⟩ : syracuseStep 303011 = 454517) B454517
theorem B1450037 : Blo 131789 1450037 := bstep (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) B135941
theorem B565325 : Blo 131789 565325 := bstep (se 3 (by rfl) ⟨105998, by rfl⟩ : syracuseStep 565325 = 211997) B211997
theorem B303281 : Blo 131789 303281 := bstep (se 2 (by rfl) ⟨113730, by rfl⟩ : syracuseStep 303281 = 227461) B227461
theorem B303299 : Blo 131789 303299 := bstep (se 1 (by rfl) ⟨227474, by rfl⟩ : syracuseStep 303299 = 454949) B454949
theorem B205057 : Blo 131789 205057 := bstep (se 2 (by rfl) ⟨76896, by rfl⟩ : syracuseStep 205057 = 153793) B153793
theorem B3449141 : Blo 131789 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B303569 : Blo 131789 303569 := bstep (se 2 (by rfl) ⟨113838, by rfl⟩ : syracuseStep 303569 = 227677) B227677
theorem B303587 : Blo 131789 303587 := bstep (se 1 (by rfl) ⟨227690, by rfl⟩ : syracuseStep 303587 = 455381) B455381
theorem B303601 : Blo 131789 303601 := bstep (se 2 (by rfl) ⟨113850, by rfl⟩ : syracuseStep 303601 = 227701) B227701
theorem B336433 : Blo 131789 336433 := bstep (se 2 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 336433 = 252325) B252325
theorem B303857 : Blo 131789 303857 := bstep (se 2 (by rfl) ⟨113946, by rfl⟩ : syracuseStep 303857 = 227893) B227893
theorem B303875 : Blo 131789 303875 := bstep (se 1 (by rfl) ⟨227906, by rfl⟩ : syracuseStep 303875 = 455813) B455813
theorem B336707 : Blo 131789 336707 := bstep (se 1 (by rfl) ⟨252530, by rfl⟩ : syracuseStep 336707 = 505061) B505061
theorem B402403 : Blo 131789 402403 := bstep (se 1 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 402403 = 603605) B603605
theorem B336899 : Blo 131789 336899 := bstep (se 1 (by rfl) ⟨252674, by rfl⟩ : syracuseStep 336899 = 505349) B505349
theorem B304145 : Blo 131789 304145 := bstep (se 2 (by rfl) ⟨114054, by rfl⟩ : syracuseStep 304145 = 228109) B228109
theorem B304163 : Blo 131789 304163 := bstep (se 1 (by rfl) ⟨228122, by rfl⟩ : syracuseStep 304163 = 456245) B456245
theorem B205907 : Blo 131789 205907 := bstep (se 1 (by rfl) ⟨154430, by rfl⟩ : syracuseStep 205907 = 308861) B308861
theorem B238691 : Blo 131789 238691 := bstep (se 1 (by rfl) ⟨179018, by rfl⟩ : syracuseStep 238691 = 358037) B358037
theorem B501005 : Blo 131789 501005 := bstep (se 3 (by rfl) ⟨93938, by rfl⟩ : syracuseStep 501005 = 187877) B187877
theorem B369937 : Blo 131789 369937 := bstep (se 2 (by rfl) ⟨138726, by rfl⟩ : syracuseStep 369937 = 277453) B277453
theorem B304433 : Blo 131789 304433 := bstep (se 2 (by rfl) ⟨114162, by rfl⟩ : syracuseStep 304433 = 228325) B228325
theorem B304451 : Blo 131789 304451 := bstep (se 1 (by rfl) ⟨228338, by rfl⟩ : syracuseStep 304451 = 456677) B456677
theorem B402961 : Blo 131789 402961 := bstep (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) B302221
theorem B304721 : Blo 131789 304721 := bstep (se 2 (by rfl) ⟨114270, by rfl⟩ : syracuseStep 304721 = 228541) B228541
theorem B304739 : Blo 131789 304739 := bstep (se 1 (by rfl) ⟨228554, by rfl⟩ : syracuseStep 304739 = 457109) B457109
theorem B272177 : Blo 131789 272177 := bstep (se 2 (by rfl) ⟨102066, by rfl⟩ : syracuseStep 272177 = 204133) B204133
theorem B141139 : Blo 131789 141139 := bstep (se 1 (by rfl) ⟨105854, by rfl⟩ : syracuseStep 141139 = 211709) B211709
theorem B305009 : Blo 131789 305009 := bstep (se 2 (by rfl) ⟨114378, by rfl⟩ : syracuseStep 305009 = 228757) B228757
theorem B305027 : Blo 131789 305027 := bstep (se 1 (by rfl) ⟨228770, by rfl⟩ : syracuseStep 305027 = 457541) B457541
theorem B1714061 : Blo 131789 1714061 := bstep (se 3 (by rfl) ⟨321386, by rfl⟩ : syracuseStep 1714061 = 642773) B642773
theorem B272273 : Blo 131789 272273 := bstep (se 2 (by rfl) ⟨102102, by rfl⟩ : syracuseStep 272273 = 204205) B204205
theorem B337841 : Blo 131789 337841 := bstep (se 2 (by rfl) ⟨126690, by rfl⟩ : syracuseStep 337841 = 253381) B253381
theorem B862157 : Blo 131789 862157 := bstep (se 3 (by rfl) ⟨161654, by rfl⟩ : syracuseStep 862157 = 323309) B323309
theorem B337891 : Blo 131789 337891 := bstep (se 1 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 337891 = 506837) B506837
theorem B338033 : Blo 131789 338033 := bstep (se 2 (by rfl) ⟨126762, by rfl⟩ : syracuseStep 338033 = 253525) B253525
theorem B305297 : Blo 131789 305297 := bstep (se 2 (by rfl) ⟨114486, by rfl⟩ : syracuseStep 305297 = 228973) B228973
theorem B305315 : Blo 131789 305315 := bstep (se 1 (by rfl) ⟨228986, by rfl⟩ : syracuseStep 305315 = 457973) B457973
theorem B731597 : Blo 131789 731597 := bstep (se 3 (by rfl) ⟨137174, by rfl⟩ : syracuseStep 731597 = 274349) B274349
theorem B207731 : Blo 131789 207731 := bstep (se 1 (by rfl) ⟨155798, by rfl⟩ : syracuseStep 207731 = 311597) B311597
theorem B142403 : Blo 131789 142403 := bstep (se 1 (by rfl) ⟨106802, by rfl⟩ : syracuseStep 142403 = 213605) B213605
theorem B339025 : Blo 131789 339025 := bstep (se 2 (by rfl) ⟨127134, by rfl⟩ : syracuseStep 339025 = 254269) B254269
theorem B11775203 : Blo 131789 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B503117 : Blo 131789 503117 := bstep (se 3 (by rfl) ⟨94334, by rfl⟩ : syracuseStep 503117 = 188669) B188669
theorem B240977 : Blo 131789 240977 := bstep (se 2 (by rfl) ⟨90366, by rfl⟩ : syracuseStep 240977 = 180733) B180733
theorem B339299 : Blo 131789 339299 := bstep (se 1 (by rfl) ⟨254474, by rfl⟩ : syracuseStep 339299 = 508949) B508949
theorem B3452357 : Blo 131789 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B405005 : Blo 131789 405005 := bstep (se 3 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 405005 = 151877) B151877
theorem B339491 : Blo 131789 339491 := bstep (se 1 (by rfl) ⟨254618, by rfl⟩ : syracuseStep 339491 = 509237) B509237
theorem B405091 : Blo 131789 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B241265 : Blo 131789 241265 := bstep (se 2 (by rfl) ⟨90474, by rfl⟩ : syracuseStep 241265 = 180949) B180949
theorem B667277 : Blo 131789 667277 := bstep (se 3 (by rfl) ⟨125114, by rfl⟩ : syracuseStep 667277 = 250229) B250229
theorem B143155 : Blo 131789 143155 := bstep (se 1 (by rfl) ⟨107366, by rfl⟩ : syracuseStep 143155 = 214733) B214733
theorem B503921 : Blo 131789 503921 := bstep (se 2 (by rfl) ⟨188970, by rfl⟩ : syracuseStep 503921 = 377941) B377941
theorem B1290467 : Blo 131789 1290467 := bstep (se 1 (by rfl) ⟨967850, by rfl⟩ : syracuseStep 1290467 = 1935701) B1935701
theorem B274691 : Blo 131789 274691 := bstep (se 1 (by rfl) ⟨206018, by rfl⟩ : syracuseStep 274691 = 412037) B412037
theorem B2896181 : Blo 131789 2896181 := bstep (se 5 (by rfl) ⟨135758, by rfl⟩ : syracuseStep 2896181 = 271517) B271517
theorem B569699 : Blo 131789 569699 := bstep (se 1 (by rfl) ⟨427274, by rfl⟩ : syracuseStep 569699 = 854549) B854549
theorem B340433 : Blo 131789 340433 := bstep (se 2 (by rfl) ⟨127662, by rfl⟩ : syracuseStep 340433 = 255325) B255325
theorem B340483 : Blo 131789 340483 := bstep (se 1 (by rfl) ⟨255362, by rfl⟩ : syracuseStep 340483 = 510725) B510725
theorem B340625 : Blo 131789 340625 := bstep (se 2 (by rfl) ⟨127734, by rfl⟩ : syracuseStep 340625 = 255469) B255469
theorem B307907 : Blo 131789 307907 := bstep (se 1 (by rfl) ⟨230930, by rfl⟩ : syracuseStep 307907 = 461861) B461861
theorem B504589 : Blo 131789 504589 := bstep (se 3 (by rfl) ⟨94610, by rfl⟩ : syracuseStep 504589 = 189221) B189221
theorem B1520693 : Blo 131789 1520693 := bstep (se 5 (by rfl) ⟨71282, by rfl⟩ : syracuseStep 1520693 = 142565) B142565
theorem B144451 : Blo 131789 144451 := bstep (se 1 (by rfl) ⟨108338, by rfl⟩ : syracuseStep 144451 = 216677) B216677
theorem B144547 : Blo 131789 144547 := bstep (se 1 (by rfl) ⟨108410, by rfl⟩ : syracuseStep 144547 = 216821) B216821
theorem B373987 : Blo 131789 373987 := bstep (se 1 (by rfl) ⟨280490, by rfl⟩ : syracuseStep 373987 = 560981) B560981
theorem B1029347 : Blo 131789 1029347 := bstep (se 1 (by rfl) ⟨772010, by rfl⟩ : syracuseStep 1029347 = 1544021) B1544021
theorem B767501 : Blo 131789 767501 := bstep (se 3 (by rfl) ⟨143906, by rfl⟩ : syracuseStep 767501 = 287813) B287813
theorem B505379 : Blo 131789 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B341617 : Blo 131789 341617 := bstep (se 2 (by rfl) ⟨128106, by rfl⟩ : syracuseStep 341617 = 256213) B256213
theorem B341891 : Blo 131789 341891 := bstep (se 1 (by rfl) ⟨256418, by rfl⟩ : syracuseStep 341891 = 512837) B512837
theorem B669617 : Blo 131789 669617 := bstep (se 2 (by rfl) ⟨251106, by rfl⟩ : syracuseStep 669617 = 502213) B502213
theorem B243665 : Blo 131789 243665 := bstep (se 2 (by rfl) ⟨91374, by rfl⟩ : syracuseStep 243665 = 182749) B182749
theorem B342083 : Blo 131789 342083 := bstep (se 1 (by rfl) ⟨256562, by rfl⟩ : syracuseStep 342083 = 513125) B513125
theorem B506033 : Blo 131789 506033 := bstep (se 2 (by rfl) ⟨189762, by rfl⟩ : syracuseStep 506033 = 379525) B379525
theorem B407729 : Blo 131789 407729 := bstep (se 2 (by rfl) ⟨152898, by rfl⟩ : syracuseStep 407729 = 305797) B305797
theorem B309521 : Blo 131789 309521 := bstep (se 2 (by rfl) ⟨116070, by rfl⟩ : syracuseStep 309521 = 232141) B232141
theorem B571697 : Blo 131789 571697 := bstep (se 2 (by rfl) ⟨214386, by rfl⟩ : syracuseStep 571697 = 428773) B428773
theorem B178531 : Blo 131789 178531 := bstep (se 1 (by rfl) ⟨133898, by rfl⟩ : syracuseStep 178531 = 267797) B267797
theorem B211331 : Blo 131789 211331 := bstep (se 1 (by rfl) ⟨158498, by rfl⟩ : syracuseStep 211331 = 316997) B316997
theorem B670193 : Blo 131789 670193 := bstep (se 2 (by rfl) ⟨251322, by rfl⟩ : syracuseStep 670193 = 502645) B502645
theorem B375299 : Blo 131789 375299 := bstep (se 1 (by rfl) ⟨281474, by rfl⟩ : syracuseStep 375299 = 562949) B562949
theorem B211843 : Blo 131789 211843 := bstep (se 1 (by rfl) ⟨158882, by rfl⟩ : syracuseStep 211843 = 317765) B317765
theorem B343025 : Blo 131789 343025 := bstep (se 2 (by rfl) ⟨128634, by rfl⟩ : syracuseStep 343025 = 257269) B257269
theorem B343075 : Blo 131789 343075 := bstep (se 1 (by rfl) ⟨257306, by rfl⟩ : syracuseStep 343075 = 514613) B514613
theorem B1129585 : Blo 131789 1129585 := bstep (se 2 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 1129585 = 847189) B847189
theorem B343217 : Blo 131789 343217 := bstep (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) B257413
theorem B179569 : Blo 131789 179569 := bstep (se 2 (by rfl) ⟨67338, by rfl⟩ : syracuseStep 179569 = 134677) B134677
theorem B212387 : Blo 131789 212387 := bstep (se 1 (by rfl) ⟨159290, by rfl⟩ : syracuseStep 212387 = 318581) B318581
theorem B376301 : Blo 131789 376301 := bstep (se 3 (by rfl) ⟨70556, by rfl⟩ : syracuseStep 376301 = 141113) B141113
theorem B212561 : Blo 131789 212561 := bstep (se 2 (by rfl) ⟨79710, by rfl⟩ : syracuseStep 212561 = 159421) B159421
theorem B507491 : Blo 131789 507491 := bstep (se 1 (by rfl) ⟨380618, by rfl⟩ : syracuseStep 507491 = 761237) B761237
theorem B507505 : Blo 131789 507505 := bstep (se 2 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 507505 = 380629) B380629
theorem B376483 : Blo 131789 376483 := bstep (se 1 (by rfl) ⟨282362, by rfl⟩ : syracuseStep 376483 = 564725) B564725
theorem B769733 : Blo 131789 769733 := bstep (se 4 (by rfl) ⟨72162, by rfl⟩ : syracuseStep 769733 = 144325) B144325
theorem B376643 : Blo 131789 376643 := bstep (se 1 (by rfl) ⟨282482, by rfl⟩ : syracuseStep 376643 = 564965) B564965
theorem B180067 : Blo 131789 180067 := bstep (se 1 (by rfl) ⟨135050, by rfl⟩ : syracuseStep 180067 = 270101) B270101
theorem B671651 : Blo 131789 671651 := bstep (se 1 (by rfl) ⟨503738, by rfl⟩ : syracuseStep 671651 = 1007477) B1007477
theorem B540593 : Blo 131789 540593 := bstep (se 2 (by rfl) ⟨202722, by rfl⟩ : syracuseStep 540593 = 405445) B405445
theorem B573389 : Blo 131789 573389 := bstep (se 3 (by rfl) ⟨107510, by rfl⟩ : syracuseStep 573389 = 215021) B215021
theorem B770417 : Blo 131789 770417 := bstep (se 2 (by rfl) ⟨288906, by rfl⟩ : syracuseStep 770417 = 577813) B577813
theorem B672461 : Blo 131789 672461 := bstep (se 3 (by rfl) ⟨126086, by rfl⟩ : syracuseStep 672461 = 252173) B252173
theorem B377713 : Blo 131789 377713 := bstep (se 2 (by rfl) ⟨141642, by rfl⟩ : syracuseStep 377713 = 283285) B283285
theorem B148387 : Blo 131789 148387 := bstep (se 1 (by rfl) ⟨111290, by rfl⟩ : syracuseStep 148387 = 222581) B222581
theorem B508963 : Blo 131789 508963 := bstep (se 1 (by rfl) ⟨381722, by rfl⟩ : syracuseStep 508963 = 763445) B763445
theorem B148531 : Blo 131789 148531 := bstep (se 1 (by rfl) ⟨111398, by rfl⟩ : syracuseStep 148531 = 222797) B222797
theorem B148675 : Blo 131789 148675 := bstep (se 1 (by rfl) ⟨111506, by rfl⟩ : syracuseStep 148675 = 223013) B223013
theorem B1557701 : Blo 131789 1557701 := bstep (se 4 (by rfl) ⟨146034, by rfl⟩ : syracuseStep 1557701 = 292069) B292069
theorem B148819 : Blo 131789 148819 := bstep (se 1 (by rfl) ⟨111614, by rfl⟩ : syracuseStep 148819 = 223229) B223229
theorem B771461 : Blo 131789 771461 := bstep (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) B144649
theorem B2278853 : Blo 131789 2278853 := bstep (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) B427285
theorem B148963 : Blo 131789 148963 := bstep (se 1 (by rfl) ⟨111722, by rfl⟩ : syracuseStep 148963 = 223445) B223445
theorem B214579 : Blo 131789 214579 := bstep (se 1 (by rfl) ⟨160934, by rfl⟩ : syracuseStep 214579 = 321869) B321869
theorem B149107 : Blo 131789 149107 := bstep (se 1 (by rfl) ⟨111830, by rfl⟩ : syracuseStep 149107 = 223661) B223661
theorem B214643 : Blo 131789 214643 := bstep (se 1 (by rfl) ⟨160982, by rfl⟩ : syracuseStep 214643 = 321965) B321965
theorem B149251 : Blo 131789 149251 := bstep (se 1 (by rfl) ⟨111938, by rfl⟩ : syracuseStep 149251 = 223877) B223877
theorem B182035 : Blo 131789 182035 := bstep (se 1 (by rfl) ⟨136526, by rfl⟩ : syracuseStep 182035 = 273053) B273053
theorem B771875 : Blo 131789 771875 := bstep (se 1 (by rfl) ⟨578906, by rfl⟩ : syracuseStep 771875 = 1157813) B1157813
theorem B1689457 : Blo 131789 1689457 := bstep (se 2 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 1689457 = 1267093) B1267093
theorem B149395 : Blo 131789 149395 := bstep (se 1 (by rfl) ⟨112046, by rfl⟩ : syracuseStep 149395 = 224093) B224093
theorem B149539 : Blo 131789 149539 := bstep (se 1 (by rfl) ⟨112154, by rfl⟩ : syracuseStep 149539 = 224309) B224309
theorem B968773 : Blo 131789 968773 := bstep (se 4 (by rfl) ⟨90822, by rfl⟩ : syracuseStep 968773 = 181645) B181645
theorem B378989 : Blo 131789 378989 := bstep (se 3 (by rfl) ⟨71060, by rfl⟩ : syracuseStep 378989 = 142121) B142121
theorem B542861 : Blo 131789 542861 := bstep (se 3 (by rfl) ⟨101786, by rfl⟩ : syracuseStep 542861 = 203573) B203573
theorem B149683 : Blo 131789 149683 := bstep (se 1 (by rfl) ⟨112262, by rfl⟩ : syracuseStep 149683 = 224525) B224525
theorem B379171 : Blo 131789 379171 := bstep (se 1 (by rfl) ⟨284378, by rfl⟩ : syracuseStep 379171 = 568757) B568757
theorem B149827 : Blo 131789 149827 := bstep (se 1 (by rfl) ⟨112370, by rfl⟩ : syracuseStep 149827 = 224741) B224741
theorem B379217 : Blo 131789 379217 := bstep (se 2 (by rfl) ⟨142206, by rfl⟩ : syracuseStep 379217 = 284413) B284413
theorem B149971 : Blo 131789 149971 := bstep (se 1 (by rfl) ⟨112478, by rfl⟩ : syracuseStep 149971 = 224957) B224957
theorem B215617 : Blo 131789 215617 := bstep (se 2 (by rfl) ⟨80856, by rfl⟩ : syracuseStep 215617 = 161713) B161713
theorem B150115 : Blo 131789 150115 := bstep (se 1 (by rfl) ⟨112586, by rfl⟩ : syracuseStep 150115 = 225173) B225173
theorem B871117 : Blo 131789 871117 := bstep (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) B326669
theorem B150259 : Blo 131789 150259 := bstep (se 1 (by rfl) ⟨112694, by rfl⟩ : syracuseStep 150259 = 225389) B225389
theorem B445229 : Blo 131789 445229 := bstep (se 3 (by rfl) ⟨83480, by rfl⟩ : syracuseStep 445229 = 166961) B166961
theorem B215873 : Blo 131789 215873 := bstep (se 2 (by rfl) ⟨80952, by rfl⟩ : syracuseStep 215873 = 161905) B161905
theorem B445283 : Blo 131789 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B150403 : Blo 131789 150403 := bstep (se 1 (by rfl) ⟨112802, by rfl⟩ : syracuseStep 150403 = 225605) B225605
theorem B871309 : Blo 131789 871309 := bstep (se 3 (by rfl) ⟨163370, by rfl⟩ : syracuseStep 871309 = 326741) B326741
theorem B216065 : Blo 131789 216065 := bstep (se 2 (by rfl) ⟨81024, by rfl⟩ : syracuseStep 216065 = 162049) B162049
theorem B150547 : Blo 131789 150547 := bstep (se 1 (by rfl) ⟨112910, by rfl⟩ : syracuseStep 150547 = 225821) B225821
theorem B150563 : Blo 131789 150563 := bstep (se 1 (by rfl) ⟨112922, by rfl⟩ : syracuseStep 150563 = 225845) B225845
theorem B281713 : Blo 131789 281713 := bstep (se 2 (by rfl) ⟨105642, by rfl⟩ : syracuseStep 281713 = 211285) B211285
theorem B445553 : Blo 131789 445553 := bstep (se 2 (by rfl) ⟨167082, by rfl⟩ : syracuseStep 445553 = 334165) B334165
theorem B281731 : Blo 131789 281731 := bstep (se 1 (by rfl) ⟨211298, by rfl⟩ : syracuseStep 281731 = 422597) B422597
theorem B150691 : Blo 131789 150691 := bstep (se 1 (by rfl) ⟨113018, by rfl⟩ : syracuseStep 150691 = 226037) B226037
theorem B511181 : Blo 131789 511181 := bstep (se 3 (by rfl) ⟨95846, by rfl⟩ : syracuseStep 511181 = 191693) B191693
theorem B412877 : Blo 131789 412877 := bstep (se 3 (by rfl) ⟨77414, by rfl⟩ : syracuseStep 412877 = 154829) B154829
theorem B150755 : Blo 131789 150755 := bstep (se 1 (by rfl) ⟨113066, by rfl⟩ : syracuseStep 150755 = 226133) B226133
theorem B544013 : Blo 131789 544013 := bstep (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) B204005
theorem B150835 : Blo 131789 150835 := bstep (se 1 (by rfl) ⟨113126, by rfl⟩ : syracuseStep 150835 = 226253) B226253
theorem B3231089 : Blo 131789 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B150979 : Blo 131789 150979 := bstep (se 1 (by rfl) ⟨113234, by rfl⟩ : syracuseStep 150979 = 226469) B226469
theorem B675377 : Blo 131789 675377 := bstep (se 2 (by rfl) ⟨253266, by rfl⟩ : syracuseStep 675377 = 506533) B506533
theorem B151123 : Blo 131789 151123 := bstep (se 1 (by rfl) ⟨113342, by rfl⟩ : syracuseStep 151123 = 226685) B226685
theorem B446093 : Blo 131789 446093 := bstep (se 3 (by rfl) ⟨83642, by rfl⟩ : syracuseStep 446093 = 167285) B167285
theorem B446147 : Blo 131789 446147 := bstep (se 1 (by rfl) ⟨334610, by rfl⟩ : syracuseStep 446147 = 669221) B669221
theorem B151267 : Blo 131789 151267 := bstep (se 1 (by rfl) ⟨113450, by rfl⟩ : syracuseStep 151267 = 226901) B226901
theorem B380675 : Blo 131789 380675 := bstep (se 1 (by rfl) ⟨285506, by rfl⟩ : syracuseStep 380675 = 571013) B571013
theorem B184163 : Blo 131789 184163 := bstep (se 1 (by rfl) ⟨138122, by rfl⟩ : syracuseStep 184163 = 276245) B276245
theorem B151411 : Blo 131789 151411 := bstep (se 1 (by rfl) ⟨113558, by rfl⟩ : syracuseStep 151411 = 227117) B227117
theorem B741325 : Blo 131789 741325 := bstep (se 3 (by rfl) ⟨138998, by rfl⟩ : syracuseStep 741325 = 277997) B277997
theorem B446417 : Blo 131789 446417 := bstep (se 2 (by rfl) ⟨167406, by rfl⟩ : syracuseStep 446417 = 334813) B334813
theorem B151555 : Blo 131789 151555 := bstep (se 1 (by rfl) ⟨113666, by rfl⟩ : syracuseStep 151555 = 227333) B227333
theorem B1003589 : Blo 131789 1003589 := bstep (se 4 (by rfl) ⟨94086, by rfl⟩ : syracuseStep 1003589 = 188173) B188173
theorem B151699 : Blo 131789 151699 := bstep (se 1 (by rfl) ⟨113774, by rfl⟩ : syracuseStep 151699 = 227549) B227549
theorem B479459 : Blo 131789 479459 := bstep (se 1 (by rfl) ⟨359594, by rfl⟩ : syracuseStep 479459 = 719189) B719189
theorem B1069283 : Blo 131789 1069283 := bstep (se 1 (by rfl) ⟨801962, by rfl⟩ : syracuseStep 1069283 = 1603925) B1603925
theorem B577763 : Blo 131789 577763 := bstep (se 1 (by rfl) ⟨433322, by rfl⟩ : syracuseStep 577763 = 866645) B866645
theorem B151843 : Blo 131789 151843 := bstep (se 1 (by rfl) ⟨113882, by rfl⟩ : syracuseStep 151843 = 227765) B227765
theorem B217379 : Blo 131789 217379 := bstep (se 1 (by rfl) ⟨163034, by rfl⟩ : syracuseStep 217379 = 326069) B326069
theorem B1134917 : Blo 131789 1134917 := bstep (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) B212797
theorem B151987 : Blo 131789 151987 := bstep (se 1 (by rfl) ⟨113990, by rfl⟩ : syracuseStep 151987 = 227981) B227981
theorem B446957 : Blo 131789 446957 := bstep (se 3 (by rfl) ⟨83804, by rfl⟩ : syracuseStep 446957 = 167609) B167609
theorem B447011 : Blo 131789 447011 := bstep (se 1 (by rfl) ⟨335258, by rfl⟩ : syracuseStep 447011 = 670517) B670517
theorem B152131 : Blo 131789 152131 := bstep (se 1 (by rfl) ⟨114098, by rfl⟩ : syracuseStep 152131 = 228197) B228197
theorem B643697 : Blo 131789 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B152275 : Blo 131789 152275 := bstep (se 1 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 152275 = 228413) B228413
theorem B250609 : Blo 131789 250609 := bstep (se 2 (by rfl) ⟨93978, by rfl⟩ : syracuseStep 250609 = 187957) B187957
theorem B1168141 : Blo 131789 1168141 := bstep (se 3 (by rfl) ⟨219026, by rfl⟩ : syracuseStep 1168141 = 438053) B438053
theorem B447281 : Blo 131789 447281 := bstep (se 2 (by rfl) ⟨167730, by rfl⟩ : syracuseStep 447281 = 335461) B335461
theorem B643889 : Blo 131789 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B152419 : Blo 131789 152419 := bstep (se 1 (by rfl) ⟨114314, by rfl⟩ : syracuseStep 152419 = 228629) B228629
theorem B250769 : Blo 131789 250769 := bstep (se 2 (by rfl) ⟨94038, by rfl⟩ : syracuseStep 250769 = 188077) B188077
theorem B381905 : Blo 131789 381905 := bstep (se 2 (by rfl) ⟨143214, by rfl⟩ : syracuseStep 381905 = 286429) B286429
theorem B676835 : Blo 131789 676835 := bstep (se 1 (by rfl) ⟨507626, by rfl⟩ : syracuseStep 676835 = 1015253) B1015253
theorem B971747 : Blo 131789 971747 := bstep (se 1 (by rfl) ⟨728810, by rfl⟩ : syracuseStep 971747 = 1457621) B1457621
theorem B152563 : Blo 131789 152563 := bstep (se 1 (by rfl) ⟨114422, by rfl⟩ : syracuseStep 152563 = 228845) B228845
theorem B218195 : Blo 131789 218195 := bstep (se 1 (by rfl) ⟨163646, by rfl⟩ : syracuseStep 218195 = 327293) B327293
theorem B152707 : Blo 131789 152707 := bstep (se 1 (by rfl) ⟨114530, by rfl⟩ : syracuseStep 152707 = 229061) B229061
theorem B939235 : Blo 131789 939235 := bstep (se 1 (by rfl) ⟨704426, by rfl⟩ : syracuseStep 939235 = 1408853) B1408853
theorem B251171 : Blo 131789 251171 := bstep (se 1 (by rfl) ⟨188378, by rfl⟩ : syracuseStep 251171 = 376757) B376757
theorem B447821 : Blo 131789 447821 := bstep (se 3 (by rfl) ⟨83966, by rfl⟩ : syracuseStep 447821 = 167933) B167933
theorem B284003 : Blo 131789 284003 := bstep (se 1 (by rfl) ⟨213002, by rfl⟩ : syracuseStep 284003 = 426005) B426005
theorem B447875 : Blo 131789 447875 := bstep (se 1 (by rfl) ⟨335906, by rfl⟩ : syracuseStep 447875 = 671813) B671813
theorem B185747 : Blo 131789 185747 := bstep (se 1 (by rfl) ⟨139310, by rfl⟩ : syracuseStep 185747 = 278621) B278621
theorem B218611 : Blo 131789 218611 := bstep (se 1 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 218611 = 327917) B327917
theorem B448145 : Blo 131789 448145 := bstep (se 2 (by rfl) ⟨168054, by rfl⟩ : syracuseStep 448145 = 336109) B336109
theorem B677645 : Blo 131789 677645 := bstep (se 3 (by rfl) ⟨127058, by rfl⟩ : syracuseStep 677645 = 254117) B254117
theorem B284465 : Blo 131789 284465 := bstep (se 2 (by rfl) ⟨106674, by rfl⟩ : syracuseStep 284465 = 213349) B213349
theorem B546659 : Blo 131789 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B382915 : Blo 131789 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B219107 : Blo 131789 219107 := bstep (se 1 (by rfl) ⟨164330, by rfl⟩ : syracuseStep 219107 = 328661) B328661
theorem B514097 : Blo 131789 514097 := bstep (se 2 (by rfl) ⟨192786, by rfl⟩ : syracuseStep 514097 = 385573) B385573
theorem B252067 : Blo 131789 252067 := bstep (se 1 (by rfl) ⟨189050, by rfl⟩ : syracuseStep 252067 = 378101) B378101
theorem B448685 : Blo 131789 448685 := bstep (se 3 (by rfl) ⟨84128, by rfl⟩ : syracuseStep 448685 = 168257) B168257
theorem B579761 : Blo 131789 579761 := bstep (se 2 (by rfl) ⟨217410, by rfl⟩ : syracuseStep 579761 = 434821) B434821
theorem B448739 : Blo 131789 448739 := bstep (se 1 (by rfl) ⟨336554, by rfl⟩ : syracuseStep 448739 = 673109) B673109
theorem B252227 : Blo 131789 252227 := bstep (se 1 (by rfl) ⟨189170, by rfl⟩ : syracuseStep 252227 = 378341) B378341
theorem B383363 : Blo 131789 383363 := bstep (se 1 (by rfl) ⟨287522, by rfl⟩ : syracuseStep 383363 = 575045) B575045
theorem B449009 : Blo 131789 449009 := bstep (se 2 (by rfl) ⟨168378, by rfl⟩ : syracuseStep 449009 = 336757) B336757
theorem B547469 : Blo 131789 547469 := bstep (se 3 (by rfl) ⟨102650, by rfl⟩ : syracuseStep 547469 = 205301) B205301
theorem B580259 : Blo 131789 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B547661 : Blo 131789 547661 := bstep (se 3 (by rfl) ⟨102686, by rfl⟩ : syracuseStep 547661 = 205373) B205373
theorem B3398597 : Blo 131789 3398597 := bstep (se 4 (by rfl) ⟨318618, by rfl⟩ : syracuseStep 3398597 = 637237) B637237
theorem B449549 : Blo 131789 449549 := bstep (se 3 (by rfl) ⟨84290, by rfl⟩ : syracuseStep 449549 = 168581) B168581
theorem B646157 : Blo 131789 646157 := bstep (se 3 (by rfl) ⟨121154, by rfl⟩ : syracuseStep 646157 = 242309) B242309
theorem B1956917 : Blo 131789 1956917 := bstep (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) B183461
theorem B449603 : Blo 131789 449603 := bstep (se 1 (by rfl) ⟨337202, by rfl⟩ : syracuseStep 449603 = 674405) B674405
theorem B285763 : Blo 131789 285763 := bstep (se 1 (by rfl) ⟨214322, by rfl⟩ : syracuseStep 285763 = 428645) B428645
theorem B1694789 : Blo 131789 1694789 := bstep (se 4 (by rfl) ⟨158886, by rfl⟩ : syracuseStep 1694789 = 317773) B317773
theorem B318563 : Blo 131789 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B384173 : Blo 131789 384173 := bstep (se 3 (by rfl) ⟨72032, by rfl⟩ : syracuseStep 384173 = 144065) B144065
theorem B810253 : Blo 131789 810253 := bstep (se 3 (by rfl) ⟨151922, by rfl⟩ : syracuseStep 810253 = 303845) B303845
theorem B286019 : Blo 131789 286019 := bstep (se 1 (by rfl) ⟨214514, by rfl⟩ : syracuseStep 286019 = 429029) B429029
theorem B449873 : Blo 131789 449873 := bstep (se 2 (by rfl) ⟨168702, by rfl⟩ : syracuseStep 449873 = 337405) B337405
theorem B384365 : Blo 131789 384365 := bstep (se 3 (by rfl) ⟨72068, by rfl⟩ : syracuseStep 384365 = 144137) B144137
theorem B253297 : Blo 131789 253297 := bstep (se 2 (by rfl) ⟨94986, by rfl⟩ : syracuseStep 253297 = 189973) B189973
theorem B187763 : Blo 131789 187763 := bstep (se 1 (by rfl) ⟨140822, by rfl⟩ : syracuseStep 187763 = 281645) B281645
theorem B3300749 : Blo 131789 3300749 := bstep (se 3 (by rfl) ⟨618890, by rfl⟩ : syracuseStep 3300749 = 1237781) B1237781
theorem B515555 : Blo 131789 515555 := bstep (se 1 (by rfl) ⟨386666, by rfl⟩ : syracuseStep 515555 = 773333) B773333
theorem B450413 : Blo 131789 450413 := bstep (se 3 (by rfl) ⟨84452, by rfl⟩ : syracuseStep 450413 = 168905) B168905
theorem B450467 : Blo 131789 450467 := bstep (se 1 (by rfl) ⟨337850, by rfl⟩ : syracuseStep 450467 = 675701) B675701
theorem B319409 : Blo 131789 319409 := bstep (se 2 (by rfl) ⟨119778, by rfl⟩ : syracuseStep 319409 = 239557) B239557
theorem B188401 : Blo 131789 188401 := bstep (se 2 (by rfl) ⟨70650, by rfl⟩ : syracuseStep 188401 = 141301) B141301
theorem B188515 : Blo 131789 188515 := bstep (se 1 (by rfl) ⟨141386, by rfl⟩ : syracuseStep 188515 = 282773) B282773
theorem B319619 : Blo 131789 319619 := bstep (se 1 (by rfl) ⟨239714, by rfl⟩ : syracuseStep 319619 = 479429) B479429
theorem B450737 : Blo 131789 450737 := bstep (se 2 (by rfl) ⟨169026, by rfl⟩ : syracuseStep 450737 = 338053) B338053
theorem B286993 : Blo 131789 286993 := bstep (se 2 (by rfl) ⟨107622, by rfl⟩ : syracuseStep 286993 = 215245) B215245
theorem B385357 : Blo 131789 385357 := bstep (se 3 (by rfl) ⟨72254, by rfl⟩ : syracuseStep 385357 = 144509) B144509
theorem B254353 : Blo 131789 254353 := bstep (se 2 (by rfl) ⟨95382, by rfl⟩ : syracuseStep 254353 = 190765) B190765
theorem B1532357 : Blo 131789 1532357 := bstep (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) B287317
theorem B549347 : Blo 131789 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B680561 : Blo 131789 680561 := bstep (se 2 (by rfl) ⟨255210, by rfl⟩ : syracuseStep 680561 = 510421) B510421
theorem B451277 : Blo 131789 451277 := bstep (se 3 (by rfl) ⟨84614, by rfl⟩ : syracuseStep 451277 = 169229) B169229
theorem B451331 : Blo 131789 451331 := bstep (se 1 (by rfl) ⟨338498, by rfl⟩ : syracuseStep 451331 = 676997) B676997
theorem B254755 : Blo 131789 254755 := bstep (se 1 (by rfl) ⟨191066, by rfl⟩ : syracuseStep 254755 = 382133) B382133
theorem B254801 : Blo 131789 254801 := bstep (se 2 (by rfl) ⟨95550, by rfl⟩ : syracuseStep 254801 = 191101) B191101
theorem B1991537 : Blo 131789 1991537 := bstep (se 2 (by rfl) ⟨746826, by rfl⟩ : syracuseStep 1991537 = 1493653) B1493653
theorem B222083 : Blo 131789 222083 := bstep (se 1 (by rfl) ⟨166562, by rfl⟩ : syracuseStep 222083 = 333125) B333125
theorem B287651 : Blo 131789 287651 := bstep (se 1 (by rfl) ⟨215738, by rfl⟩ : syracuseStep 287651 = 431477) B431477
theorem B451601 : Blo 131789 451601 := bstep (se 2 (by rfl) ⟨169350, by rfl⟩ : syracuseStep 451601 = 338701) B338701
theorem B255089 : Blo 131789 255089 := bstep (se 2 (by rfl) ⟨95658, by rfl⟩ : syracuseStep 255089 = 191317) B191317
theorem B222419 : Blo 131789 222419 := bstep (se 1 (by rfl) ⟨166814, by rfl⟩ : syracuseStep 222419 = 333629) B333629
theorem B1402181 : Blo 131789 1402181 := bstep (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) B262909
theorem B320849 : Blo 131789 320849 := bstep (se 2 (by rfl) ⟨120318, by rfl⟩ : syracuseStep 320849 = 240637) B240637
theorem B222547 : Blo 131789 222547 := bstep (se 1 (by rfl) ⟨166910, by rfl⟩ : syracuseStep 222547 = 333821) B333821
theorem B189859 : Blo 131789 189859 := bstep (se 1 (by rfl) ⟨142394, by rfl⟩ : syracuseStep 189859 = 284789) B284789
theorem B222689 : Blo 131789 222689 := bstep (se 2 (by rfl) ⟨83508, by rfl⟩ : syracuseStep 222689 = 167017) B167017
theorem B321041 : Blo 131789 321041 := bstep (se 2 (by rfl) ⟨120390, by rfl⟩ : syracuseStep 321041 = 240781) B240781
theorem B321059 : Blo 131789 321059 := bstep (se 1 (by rfl) ⟨240794, by rfl⟩ : syracuseStep 321059 = 481589) B481589
theorem B452141 : Blo 131789 452141 := bstep (se 3 (by rfl) ⟨84776, by rfl⟩ : syracuseStep 452141 = 169553) B169553
theorem B222817 : Blo 131789 222817 := bstep (se 2 (by rfl) ⟨83556, by rfl⟩ : syracuseStep 222817 = 167113) B167113
theorem B452195 : Blo 131789 452195 := bstep (se 1 (by rfl) ⟨339146, by rfl⟩ : syracuseStep 452195 = 678293) B678293
theorem B222851 : Blo 131789 222851 := bstep (se 1 (by rfl) ⟨167138, by rfl⟩ : syracuseStep 222851 = 334277) B334277
theorem B288497 : Blo 131789 288497 := bstep (se 2 (by rfl) ⟨108186, by rfl⟩ : syracuseStep 288497 = 216373) B216373
theorem B222979 : Blo 131789 222979 := bstep (se 1 (by rfl) ⟨167234, by rfl⟩ : syracuseStep 222979 = 334469) B334469
theorem B1009421 : Blo 131789 1009421 := bstep (se 3 (by rfl) ⟨189266, by rfl⟩ : syracuseStep 1009421 = 378533) B378533
theorem B255811 : Blo 131789 255811 := bstep (se 1 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 255811 = 383717) B383717
theorem B583537 : Blo 131789 583537 := bstep (se 2 (by rfl) ⟨218826, by rfl⟩ : syracuseStep 583537 = 437653) B437653
theorem B452465 : Blo 131789 452465 := bstep (se 2 (by rfl) ⟨169674, by rfl⟩ : syracuseStep 452465 = 339349) B339349
theorem B223121 : Blo 131789 223121 := bstep (se 2 (by rfl) ⟨83670, by rfl⟩ : syracuseStep 223121 = 167341) B167341
theorem B223249 : Blo 131789 223249 := bstep (se 2 (by rfl) ⟨83718, by rfl⟩ : syracuseStep 223249 = 167437) B167437
theorem B682019 : Blo 131789 682019 := bstep (se 1 (by rfl) ⟨511514, by rfl⟩ : syracuseStep 682019 = 1023029) B1023029
theorem B223283 : Blo 131789 223283 := bstep (se 1 (by rfl) ⟨167462, by rfl⟩ : syracuseStep 223283 = 334925) B334925
theorem B223411 : Blo 131789 223411 := bstep (se 1 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 223411 = 335117) B335117
theorem B256259 : Blo 131789 256259 := bstep (se 1 (by rfl) ⟨192194, by rfl⟩ : syracuseStep 256259 = 384389) B384389
theorem B223553 : Blo 131789 223553 := bstep (se 2 (by rfl) ⟨83832, by rfl⟩ : syracuseStep 223553 = 167665) B167665
theorem B453005 : Blo 131789 453005 := bstep (se 3 (by rfl) ⟨84938, by rfl⟩ : syracuseStep 453005 = 169877) B169877
theorem B223681 : Blo 131789 223681 := bstep (se 2 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 223681 = 167761) B167761
theorem B453059 : Blo 131789 453059 := bstep (se 1 (by rfl) ⟨339794, by rfl⟩ : syracuseStep 453059 = 679589) B679589
theorem B223715 : Blo 131789 223715 := bstep (se 1 (by rfl) ⟨167786, by rfl⟩ : syracuseStep 223715 = 335573) B335573
theorem B190993 : Blo 131789 190993 := bstep (se 2 (by rfl) ⟨71622, by rfl⟩ : syracuseStep 190993 = 143245) B143245
theorem B256547 : Blo 131789 256547 := bstep (se 1 (by rfl) ⟨192410, by rfl⟩ : syracuseStep 256547 = 384821) B384821
theorem B289379 : Blo 131789 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B223843 : Blo 131789 223843 := bstep (se 1 (by rfl) ⟨167882, by rfl⟩ : syracuseStep 223843 = 335765) B335765
theorem B191089 : Blo 131789 191089 := bstep (se 2 (by rfl) ⟨71658, by rfl⟩ : syracuseStep 191089 = 143317) B143317
theorem B453329 : Blo 131789 453329 := bstep (se 2 (by rfl) ⟨169998, by rfl⟩ : syracuseStep 453329 = 339997) B339997
theorem B191203 : Blo 131789 191203 := bstep (se 1 (by rfl) ⟨143402, by rfl⟩ : syracuseStep 191203 = 286805) B286805
theorem B223985 : Blo 131789 223985 := bstep (se 2 (by rfl) ⟨83994, by rfl⟩ : syracuseStep 223985 = 167989) B167989
theorem B813901 : Blo 131789 813901 := bstep (se 3 (by rfl) ⟨152606, by rfl⟩ : syracuseStep 813901 = 305213) B305213
theorem B682829 : Blo 131789 682829 := bstep (se 3 (by rfl) ⟨128030, by rfl⟩ : syracuseStep 682829 = 256061) B256061
theorem B224113 : Blo 131789 224113 := bstep (se 2 (by rfl) ⟨84042, by rfl⟩ : syracuseStep 224113 = 168085) B168085
theorem B224147 : Blo 131789 224147 := bstep (se 1 (by rfl) ⟨168110, by rfl⟩ : syracuseStep 224147 = 336221) B336221
theorem B224275 : Blo 131789 224275 := bstep (se 1 (by rfl) ⟨168206, by rfl⟩ : syracuseStep 224275 = 336413) B336413
theorem B191585 : Blo 131789 191585 := bstep (se 2 (by rfl) ⟨71844, by rfl⟩ : syracuseStep 191585 = 143689) B143689
theorem B224417 : Blo 131789 224417 := bstep (se 2 (by rfl) ⟨84156, by rfl⟩ : syracuseStep 224417 = 168313) B168313
theorem B1109189 : Blo 131789 1109189 := bstep (se 4 (by rfl) ⟨103986, by rfl⟩ : syracuseStep 1109189 = 207973) B207973
theorem B453869 : Blo 131789 453869 := bstep (se 3 (by rfl) ⟨85100, by rfl⟩ : syracuseStep 453869 = 170201) B170201
theorem B224545 : Blo 131789 224545 := bstep (se 2 (by rfl) ⟨84204, by rfl⟩ : syracuseStep 224545 = 168409) B168409
theorem B453923 : Blo 131789 453923 := bstep (se 1 (by rfl) ⟨340442, by rfl⟩ : syracuseStep 453923 = 680885) B680885
theorem B224579 : Blo 131789 224579 := bstep (se 1 (by rfl) ⟨168434, by rfl⟩ : syracuseStep 224579 = 336869) B336869
theorem B224707 : Blo 131789 224707 := bstep (se 1 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 224707 = 337061) B337061
theorem B257489 : Blo 131789 257489 := bstep (se 2 (by rfl) ⟨96558, by rfl⟩ : syracuseStep 257489 = 193117) B193117
theorem B454193 : Blo 131789 454193 := bstep (se 2 (by rfl) ⟨170322, by rfl⟩ : syracuseStep 454193 = 340645) B340645
theorem B224849 : Blo 131789 224849 := bstep (se 2 (by rfl) ⟨84318, by rfl⟩ : syracuseStep 224849 = 168637) B168637
theorem B2551409 : Blo 131789 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B224977 : Blo 131789 224977 := bstep (se 2 (by rfl) ⟨84366, by rfl⟩ : syracuseStep 224977 = 168733) B168733
theorem B225011 : Blo 131789 225011 := bstep (se 1 (by rfl) ⟨168758, by rfl⟩ : syracuseStep 225011 = 337517) B337517
theorem B225139 : Blo 131789 225139 := bstep (se 1 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 225139 = 337709) B337709
theorem B192451 : Blo 131789 192451 := bstep (se 1 (by rfl) ⟨144338, by rfl⟩ : syracuseStep 192451 = 288677) B288677
theorem B683981 : Blo 131789 683981 := bstep (se 3 (by rfl) ⟨128246, by rfl⟩ : syracuseStep 683981 = 256493) B256493
theorem B225281 : Blo 131789 225281 := bstep (se 2 (by rfl) ⟨84480, by rfl⟩ : syracuseStep 225281 = 168961) B168961
theorem B192547 : Blo 131789 192547 := bstep (se 1 (by rfl) ⟨144410, by rfl⟩ : syracuseStep 192547 = 288821) B288821
theorem B454733 : Blo 131789 454733 := bstep (se 3 (by rfl) ⟨85262, by rfl⟩ : syracuseStep 454733 = 170525) B170525
theorem B225409 : Blo 131789 225409 := bstep (se 2 (by rfl) ⟨84528, by rfl⟩ : syracuseStep 225409 = 169057) B169057
theorem B454787 : Blo 131789 454787 := bstep (se 1 (by rfl) ⟨341090, by rfl⟩ : syracuseStep 454787 = 682181) B682181
theorem B225443 : Blo 131789 225443 := bstep (se 1 (by rfl) ⟨169082, by rfl⟩ : syracuseStep 225443 = 338165) B338165
theorem B1142981 : Blo 131789 1142981 := bstep (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) B214309
theorem B225571 : Blo 131789 225571 := bstep (se 1 (by rfl) ⟨169178, by rfl⟩ : syracuseStep 225571 = 338357) B338357
theorem B356717 : Blo 131789 356717 := bstep (se 3 (by rfl) ⟨66884, by rfl⟩ : syracuseStep 356717 = 133769) B133769
theorem B455057 : Blo 131789 455057 := bstep (se 2 (by rfl) ⟨170646, by rfl⟩ : syracuseStep 455057 = 341293) B341293
theorem B225713 : Blo 131789 225713 := bstep (se 2 (by rfl) ⟨84642, by rfl⟩ : syracuseStep 225713 = 169285) B169285
theorem B487907 : Blo 131789 487907 := bstep (se 1 (by rfl) ⟨365930, by rfl⟩ : syracuseStep 487907 = 731861) B731861
theorem B193043 : Blo 131789 193043 := bstep (se 1 (by rfl) ⟨144782, by rfl⟩ : syracuseStep 193043 = 289565) B289565
theorem B225841 : Blo 131789 225841 := bstep (se 2 (by rfl) ⟨84690, by rfl⟩ : syracuseStep 225841 = 169381) B169381
theorem B225875 : Blo 131789 225875 := bstep (se 1 (by rfl) ⟨169406, by rfl⟩ : syracuseStep 225875 = 338813) B338813
theorem B356977 : Blo 131789 356977 := bstep (se 2 (by rfl) ⟨133866, by rfl⟩ : syracuseStep 356977 = 267733) B267733
theorem B1012337 : Blo 131789 1012337 := bstep (se 2 (by rfl) ⟨379626, by rfl⟩ : syracuseStep 1012337 = 759253) B759253
theorem B226003 : Blo 131789 226003 := bstep (se 1 (by rfl) ⟨169502, by rfl⟩ : syracuseStep 226003 = 339005) B339005
theorem B160483 : Blo 131789 160483 := bstep (se 1 (by rfl) ⟨120362, by rfl⟩ : syracuseStep 160483 = 240725) B240725
theorem B389873 : Blo 131789 389873 := bstep (se 2 (by rfl) ⟨146202, by rfl⟩ : syracuseStep 389873 = 292405) B292405
theorem B226145 : Blo 131789 226145 := bstep (se 2 (by rfl) ⟨84804, by rfl⟩ : syracuseStep 226145 = 169609) B169609
theorem B1143665 : Blo 131789 1143665 := bstep (se 2 (by rfl) ⟨428874, by rfl⟩ : syracuseStep 1143665 = 857749) B857749
theorem B455597 : Blo 131789 455597 := bstep (se 3 (by rfl) ⟨85424, by rfl⟩ : syracuseStep 455597 = 170849) B170849
theorem B226273 : Blo 131789 226273 := bstep (se 2 (by rfl) ⟨84852, by rfl⟩ : syracuseStep 226273 = 169705) B169705
theorem B455651 : Blo 131789 455651 := bstep (se 1 (by rfl) ⟨341738, by rfl⟩ : syracuseStep 455651 = 683477) B683477
theorem B1209329 : Blo 131789 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B226307 : Blo 131789 226307 := bstep (se 1 (by rfl) ⟨169730, by rfl⟩ : syracuseStep 226307 = 339461) B339461
theorem B226435 : Blo 131789 226435 := bstep (se 1 (by rfl) ⟨169826, by rfl⟩ : syracuseStep 226435 = 339653) B339653
theorem B455921 : Blo 131789 455921 := bstep (se 2 (by rfl) ⟨170970, by rfl⟩ : syracuseStep 455921 = 341941) B341941
theorem B226577 : Blo 131789 226577 := bstep (se 2 (by rfl) ⟨84966, by rfl⟩ : syracuseStep 226577 = 169933) B169933
theorem B226705 : Blo 131789 226705 := bstep (se 2 (by rfl) ⟨85014, by rfl⟩ : syracuseStep 226705 = 170029) B170029
theorem B226739 : Blo 131789 226739 := bstep (se 1 (by rfl) ⟨170054, by rfl⟩ : syracuseStep 226739 = 340109) B340109
theorem B226867 : Blo 131789 226867 := bstep (se 1 (by rfl) ⟨170150, by rfl⟩ : syracuseStep 226867 = 340301) B340301
theorem B685745 : Blo 131789 685745 := bstep (se 2 (by rfl) ⟨257154, by rfl⟩ : syracuseStep 685745 = 514309) B514309
theorem B227009 : Blo 131789 227009 := bstep (se 2 (by rfl) ⟨85128, by rfl⟩ : syracuseStep 227009 = 170257) B170257
theorem B456461 : Blo 131789 456461 := bstep (se 3 (by rfl) ⟨85586, by rfl⟩ : syracuseStep 456461 = 171173) B171173
theorem B227137 : Blo 131789 227137 := bstep (se 2 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 227137 = 170353) B170353
theorem B456515 : Blo 131789 456515 := bstep (se 1 (by rfl) ⟨342386, by rfl⟩ : syracuseStep 456515 = 684773) B684773
theorem B227171 : Blo 131789 227171 := bstep (se 1 (by rfl) ⟨170378, by rfl⟩ : syracuseStep 227171 = 340757) B340757
theorem B227299 : Blo 131789 227299 := bstep (se 1 (by rfl) ⟨170474, by rfl⟩ : syracuseStep 227299 = 340949) B340949
theorem B456785 : Blo 131789 456785 := bstep (se 2 (by rfl) ⟨171294, by rfl⟩ : syracuseStep 456785 = 342589) B342589
theorem B227441 : Blo 131789 227441 := bstep (se 2 (by rfl) ⟨85290, by rfl⟩ : syracuseStep 227441 = 170581) B170581
theorem B1538189 : Blo 131789 1538189 := bstep (se 3 (by rfl) ⟨288410, by rfl⟩ : syracuseStep 1538189 = 576821) B576821
theorem B1308869 : Blo 131789 1308869 := bstep (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) B245413
theorem B2291939 : Blo 131789 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B227569 : Blo 131789 227569 := bstep (se 2 (by rfl) ⟨85338, by rfl⟩ : syracuseStep 227569 = 170677) B170677
theorem B227603 : Blo 131789 227603 := bstep (se 1 (by rfl) ⟨170702, by rfl⟩ : syracuseStep 227603 = 341405) B341405
theorem B424237 : Blo 131789 424237 := bstep (se 3 (by rfl) ⟨79544, by rfl⟩ : syracuseStep 424237 = 159089) B159089
theorem B1571185 : Blo 131789 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B227731 : Blo 131789 227731 := bstep (se 1 (by rfl) ⟨170798, by rfl⟩ : syracuseStep 227731 = 341597) B341597
theorem B1735181 : Blo 131789 1735181 := bstep (se 3 (by rfl) ⟨325346, by rfl⟩ : syracuseStep 1735181 = 650693) B650693
theorem B227873 : Blo 131789 227873 := bstep (se 2 (by rfl) ⟨85452, by rfl⟩ : syracuseStep 227873 = 170905) B170905
theorem B2882101 : Blo 131789 2882101 := bstep (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) B270197
theorem B457325 : Blo 131789 457325 := bstep (se 3 (by rfl) ⟨85748, by rfl⟩ : syracuseStep 457325 = 171497) B171497
theorem B162419 : Blo 131789 162419 := bstep (se 1 (by rfl) ⟨121814, by rfl⟩ : syracuseStep 162419 = 243629) B243629
theorem B228001 : Blo 131789 228001 := bstep (se 2 (by rfl) ⟨85500, by rfl⟩ : syracuseStep 228001 = 171001) B171001
theorem B359075 : Blo 131789 359075 := bstep (se 1 (by rfl) ⟨269306, by rfl⟩ : syracuseStep 359075 = 538613) B538613
theorem B457379 : Blo 131789 457379 := bstep (se 1 (by rfl) ⟨343034, by rfl⟩ : syracuseStep 457379 = 686069) B686069
theorem B228035 : Blo 131789 228035 := bstep (se 1 (by rfl) ⟨171026, by rfl⟩ : syracuseStep 228035 = 342053) B342053
theorem B228163 : Blo 131789 228163 := bstep (se 1 (by rfl) ⟨171122, by rfl⟩ : syracuseStep 228163 = 342245) B342245
theorem B293699 : Blo 131789 293699 := bstep (se 1 (by rfl) ⟨220274, by rfl⟩ : syracuseStep 293699 = 440549) B440549
theorem B260995 : Blo 131789 260995 := bstep (se 1 (by rfl) ⟨195746, by rfl⟩ : syracuseStep 260995 = 391493) B391493
theorem B457649 : Blo 131789 457649 := bstep (se 2 (by rfl) ⟨171618, by rfl⟩ : syracuseStep 457649 = 343237) B343237
theorem B195523 : Blo 131789 195523 := bstep (se 1 (by rfl) ⟨146642, by rfl⟩ : syracuseStep 195523 = 293285) B293285
theorem B228305 : Blo 131789 228305 := bstep (se 2 (by rfl) ⟨85614, by rfl⟩ : syracuseStep 228305 = 171229) B171229
theorem B228433 : Blo 131789 228433 := bstep (se 2 (by rfl) ⟨85662, by rfl⟩ : syracuseStep 228433 = 171325) B171325
theorem B687203 : Blo 131789 687203 := bstep (se 1 (by rfl) ⟨515402, by rfl⟩ : syracuseStep 687203 = 1030805) B1030805
theorem B228467 : Blo 131789 228467 := bstep (se 1 (by rfl) ⟨171350, by rfl⟩ : syracuseStep 228467 = 342701) B342701
theorem B228577 : Blo 131789 228577 := bstep (se 2 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 228577 = 171433) B171433
theorem B228595 : Blo 131789 228595 := bstep (se 1 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 228595 = 342893) B342893
theorem B228737 : Blo 131789 228737 := bstep (se 2 (by rfl) ⟨85776, by rfl⟩ : syracuseStep 228737 = 171553) B171553
theorem B3079565 : Blo 131789 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B458189 : Blo 131789 458189 := bstep (se 3 (by rfl) ⟨85910, by rfl⟩ : syracuseStep 458189 = 171821) B171821
theorem B228865 : Blo 131789 228865 := bstep (se 2 (by rfl) ⟨85824, by rfl⟩ : syracuseStep 228865 = 171649) B171649
theorem B458243 : Blo 131789 458243 := bstep (se 1 (by rfl) ⟨343682, by rfl⟩ : syracuseStep 458243 = 687365) B687365
theorem B228899 : Blo 131789 228899 := bstep (se 1 (by rfl) ⟨171674, by rfl⟩ : syracuseStep 228899 = 343349) B343349
theorem B2031245 : Blo 131789 2031245 := bstep (se 3 (by rfl) ⟨380858, by rfl⟩ : syracuseStep 2031245 = 761717) B761717
theorem B229027 : Blo 131789 229027 := bstep (se 1 (by rfl) ⟨171770, by rfl⟩ : syracuseStep 229027 = 343541) B343541
theorem B753421 : Blo 131789 753421 := bstep (se 3 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 753421 = 282533) B282533
theorem B2817845 : Blo 131789 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B491377 : Blo 131789 491377 := bstep (se 2 (by rfl) ⟨184266, by rfl⟩ : syracuseStep 491377 = 368533) B368533
theorem B459059 : Blo 131789 459059 := bstep (se 1 (by rfl) ⟨344294, by rfl⟩ : syracuseStep 459059 = 688589) B688589
theorem B2851421 : Blo 131789 2851421 := bstep (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) B1069283
theorem B1049219 : Blo 131789 1049219 := bstep (se 1 (by rfl) ⟨786914, by rfl⟩ : syracuseStep 1049219 = 1573829) B1573829
theorem B131799 : Blo 131789 131799 := bstep (se 1 (by rfl) ⟨98849, by rfl⟩ : syracuseStep 131799 = 197699) B197699
theorem B131819 : Blo 131789 131819 := bstep (se 1 (by rfl) ⟨98864, by rfl⟩ : syracuseStep 131819 = 197729) B197729
theorem B131831 : Blo 131789 131831 := bstep (se 1 (by rfl) ⟨98873, by rfl⟩ : syracuseStep 131831 = 197747) B197747
theorem B131851 : Blo 131789 131851 := bstep (se 1 (by rfl) ⟨98888, by rfl⟩ : syracuseStep 131851 = 197777) B197777
theorem B131863 : Blo 131789 131863 := bstep (se 1 (by rfl) ⟨98897, by rfl⟩ : syracuseStep 131863 = 197795) B197795
theorem B131883 : Blo 131789 131883 := bstep (se 1 (by rfl) ⟨98912, by rfl⟩ : syracuseStep 131883 = 197825) B197825
theorem B131895 : Blo 131789 131895 := bstep (se 1 (by rfl) ⟨98921, by rfl⟩ : syracuseStep 131895 = 197843) B197843
theorem B131915 : Blo 131789 131915 := bstep (se 1 (by rfl) ⟨98936, by rfl⟩ : syracuseStep 131915 = 197873) B197873
theorem B131927 : Blo 131789 131927 := bstep (se 1 (by rfl) ⟨98945, by rfl⟩ : syracuseStep 131927 = 197891) B197891
theorem B131947 : Blo 131789 131947 := bstep (se 1 (by rfl) ⟨98960, by rfl⟩ : syracuseStep 131947 = 197921) B197921
theorem B2196341 : Blo 131789 2196341 := bstep (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) B205907
theorem B2327413 : Blo 131789 2327413 := bstep (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) B218195
theorem B131959 : Blo 131789 131959 := bstep (se 1 (by rfl) ⟨98969, by rfl⟩ : syracuseStep 131959 = 197939) B197939
theorem B131979 : Blo 131789 131979 := bstep (se 1 (by rfl) ⟨98984, by rfl⟩ : syracuseStep 131979 = 197969) B197969
theorem B131991 : Blo 131789 131991 := bstep (se 1 (by rfl) ⟨98993, by rfl⟩ : syracuseStep 131991 = 197987) B197987
theorem B132011 : Blo 131789 132011 := bstep (se 1 (by rfl) ⟨99008, by rfl⟩ : syracuseStep 132011 = 198017) B198017
theorem B132023 : Blo 131789 132023 := bstep (se 1 (by rfl) ⟨99017, by rfl⟩ : syracuseStep 132023 = 198035) B198035
theorem B132043 : Blo 131789 132043 := bstep (se 1 (by rfl) ⟨99032, by rfl⟩ : syracuseStep 132043 = 198065) B198065
theorem B132055 : Blo 131789 132055 := bstep (se 1 (by rfl) ⟨99041, by rfl⟩ : syracuseStep 132055 = 198083) B198083
theorem B132075 : Blo 131789 132075 := bstep (se 1 (by rfl) ⟨99056, by rfl⟩ : syracuseStep 132075 = 198113) B198113
theorem B132087 : Blo 131789 132087 := bstep (se 1 (by rfl) ⟨99065, by rfl⟩ : syracuseStep 132087 = 198131) B198131
theorem B132107 : Blo 131789 132107 := bstep (se 1 (by rfl) ⟨99080, by rfl⟩ : syracuseStep 132107 = 198161) B198161
theorem B132119 : Blo 131789 132119 := bstep (se 1 (by rfl) ⟨99089, by rfl⟩ : syracuseStep 132119 = 198179) B198179
theorem B132139 : Blo 131789 132139 := bstep (se 1 (by rfl) ⟨99104, by rfl⟩ : syracuseStep 132139 = 198209) B198209
theorem B132151 : Blo 131789 132151 := bstep (se 1 (by rfl) ⟨99113, by rfl⟩ : syracuseStep 132151 = 198227) B198227
theorem B132171 : Blo 131789 132171 := bstep (se 1 (by rfl) ⟨99128, by rfl⟩ : syracuseStep 132171 = 198257) B198257
theorem B132183 : Blo 131789 132183 := bstep (se 1 (by rfl) ⟨99137, by rfl⟩ : syracuseStep 132183 = 198275) B198275
theorem B132203 : Blo 131789 132203 := bstep (se 1 (by rfl) ⟨99152, by rfl⟩ : syracuseStep 132203 = 198305) B198305
theorem B132215 : Blo 131789 132215 := bstep (se 1 (by rfl) ⟨99161, by rfl⟩ : syracuseStep 132215 = 198323) B198323
theorem B197771 : Blo 131789 197771 := bstep (se 1 (by rfl) ⟨148328, by rfl⟩ : syracuseStep 197771 = 296657) B296657
theorem B132235 : Blo 131789 132235 := bstep (se 1 (by rfl) ⟨99176, by rfl⟩ : syracuseStep 132235 = 198353) B198353
theorem B197783 : Blo 131789 197783 := bstep (se 1 (by rfl) ⟨148337, by rfl⟩ : syracuseStep 197783 = 296675) B296675
theorem B132247 : Blo 131789 132247 := bstep (se 1 (by rfl) ⟨99185, by rfl⟩ : syracuseStep 132247 = 198371) B198371
theorem B132267 : Blo 131789 132267 := bstep (se 1 (by rfl) ⟨99200, by rfl⟩ : syracuseStep 132267 = 198401) B198401
theorem B132279 : Blo 131789 132279 := bstep (se 1 (by rfl) ⟨99209, by rfl⟩ : syracuseStep 132279 = 198419) B198419
theorem B394433 : Blo 131789 394433 := bstep (se 2 (by rfl) ⟨147912, by rfl⟩ : syracuseStep 394433 = 295825) B295825
theorem B132299 : Blo 131789 132299 := bstep (se 1 (by rfl) ⟨99224, by rfl⟩ : syracuseStep 132299 = 198449) B198449
theorem B132311 : Blo 131789 132311 := bstep (se 1 (by rfl) ⟨99233, by rfl⟩ : syracuseStep 132311 = 198467) B198467
theorem B197849 : Blo 131789 197849 := bstep (se 2 (by rfl) ⟨74193, by rfl⟩ : syracuseStep 197849 = 148387) B148387
theorem B132331 : Blo 131789 132331 := bstep (se 1 (by rfl) ⟨99248, by rfl⟩ : syracuseStep 132331 = 198497) B198497
theorem B132343 : Blo 131789 132343 := bstep (se 1 (by rfl) ⟨99257, by rfl⟩ : syracuseStep 132343 = 198515) B198515
theorem B132363 : Blo 131789 132363 := bstep (se 1 (by rfl) ⟨99272, by rfl⟩ : syracuseStep 132363 = 198545) B198545
theorem B132375 : Blo 131789 132375 := bstep (se 1 (by rfl) ⟨99281, by rfl⟩ : syracuseStep 132375 = 198563) B198563
theorem B132395 : Blo 131789 132395 := bstep (se 1 (by rfl) ⟨99296, by rfl⟩ : syracuseStep 132395 = 198593) B198593
theorem B132407 : Blo 131789 132407 := bstep (se 1 (by rfl) ⟨99305, by rfl⟩ : syracuseStep 132407 = 198611) B198611
theorem B197963 : Blo 131789 197963 := bstep (se 1 (by rfl) ⟨148472, by rfl⟩ : syracuseStep 197963 = 296945) B296945
theorem B132427 : Blo 131789 132427 := bstep (se 1 (by rfl) ⟨99320, by rfl⟩ : syracuseStep 132427 = 198641) B198641
theorem B197975 : Blo 131789 197975 := bstep (se 1 (by rfl) ⟨148481, by rfl⟩ : syracuseStep 197975 = 296963) B296963
theorem B132439 : Blo 131789 132439 := bstep (se 1 (by rfl) ⟨99329, by rfl⟩ : syracuseStep 132439 = 198659) B198659
theorem B132459 : Blo 131789 132459 := bstep (se 1 (by rfl) ⟨99344, by rfl⟩ : syracuseStep 132459 = 198689) B198689
theorem B132471 : Blo 131789 132471 := bstep (se 1 (by rfl) ⟨99353, by rfl⟩ : syracuseStep 132471 = 198707) B198707
theorem B132491 : Blo 131789 132491 := bstep (se 1 (by rfl) ⟨99368, by rfl⟩ : syracuseStep 132491 = 198737) B198737
theorem B132503 : Blo 131789 132503 := bstep (se 1 (by rfl) ⟨99377, by rfl⟩ : syracuseStep 132503 = 198755) B198755
theorem B198041 : Blo 131789 198041 := bstep (se 2 (by rfl) ⟨74265, by rfl⟩ : syracuseStep 198041 = 148531) B148531
theorem B132523 : Blo 131789 132523 := bstep (se 1 (by rfl) ⟨99392, by rfl⟩ : syracuseStep 132523 = 198785) B198785
theorem B361907 : Blo 131789 361907 := bstep (se 1 (by rfl) ⟨271430, by rfl⟩ : syracuseStep 361907 = 542861) B542861
theorem B132535 : Blo 131789 132535 := bstep (se 1 (by rfl) ⟨99401, by rfl⟩ : syracuseStep 132535 = 198803) B198803
theorem B132555 : Blo 131789 132555 := bstep (se 1 (by rfl) ⟨99416, by rfl⟩ : syracuseStep 132555 = 198833) B198833
theorem B132567 : Blo 131789 132567 := bstep (se 1 (by rfl) ⟨99425, by rfl⟩ : syracuseStep 132567 = 198851) B198851
theorem B132587 : Blo 131789 132587 := bstep (se 1 (by rfl) ⟨99440, by rfl⟩ : syracuseStep 132587 = 198881) B198881
theorem B132599 : Blo 131789 132599 := bstep (se 1 (by rfl) ⟨99449, by rfl⟩ : syracuseStep 132599 = 198899) B198899
theorem B198155 : Blo 131789 198155 := bstep (se 1 (by rfl) ⟨148616, by rfl⟩ : syracuseStep 198155 = 297233) B297233
theorem B132619 : Blo 131789 132619 := bstep (se 1 (by rfl) ⟨99464, by rfl⟩ : syracuseStep 132619 = 198929) B198929
theorem B198167 : Blo 131789 198167 := bstep (se 1 (by rfl) ⟨148625, by rfl⟩ : syracuseStep 198167 = 297251) B297251
theorem B132631 : Blo 131789 132631 := bstep (se 1 (by rfl) ⟨99473, by rfl⟩ : syracuseStep 132631 = 198947) B198947
theorem B1312291 : Blo 131789 1312291 := bstep (se 1 (by rfl) ⟨984218, by rfl⟩ : syracuseStep 1312291 = 1968437) B1968437
theorem B132651 : Blo 131789 132651 := bstep (se 1 (by rfl) ⟨99488, by rfl⟩ : syracuseStep 132651 = 198977) B198977
theorem B132663 : Blo 131789 132663 := bstep (se 1 (by rfl) ⟨99497, by rfl⟩ : syracuseStep 132663 = 198995) B198995
theorem B132683 : Blo 131789 132683 := bstep (se 1 (by rfl) ⟨99512, by rfl⟩ : syracuseStep 132683 = 199025) B199025
theorem B132695 : Blo 131789 132695 := bstep (se 1 (by rfl) ⟨99521, by rfl⟩ : syracuseStep 132695 = 199043) B199043
theorem B198233 : Blo 131789 198233 := bstep (se 2 (by rfl) ⟨74337, by rfl⟩ : syracuseStep 198233 = 148675) B148675
theorem B132715 : Blo 131789 132715 := bstep (se 1 (by rfl) ⟨99536, by rfl⟩ : syracuseStep 132715 = 199073) B199073
theorem B132727 : Blo 131789 132727 := bstep (se 1 (by rfl) ⟨99545, by rfl⟩ : syracuseStep 132727 = 199091) B199091
theorem B132747 : Blo 131789 132747 := bstep (se 1 (by rfl) ⟨99560, by rfl⟩ : syracuseStep 132747 = 199121) B199121
theorem B132759 : Blo 131789 132759 := bstep (se 1 (by rfl) ⟨99569, by rfl⟩ : syracuseStep 132759 = 199139) B199139
theorem B132779 : Blo 131789 132779 := bstep (se 1 (by rfl) ⟨99584, by rfl⟩ : syracuseStep 132779 = 199169) B199169
theorem B132791 : Blo 131789 132791 := bstep (se 1 (by rfl) ⟨99593, by rfl⟩ : syracuseStep 132791 = 199187) B199187
theorem B493249 : Blo 131789 493249 := bstep (se 2 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 493249 = 369937) B369937
theorem B198347 : Blo 131789 198347 := bstep (se 1 (by rfl) ⟨148760, by rfl⟩ : syracuseStep 198347 = 297521) B297521
theorem B132811 : Blo 131789 132811 := bstep (se 1 (by rfl) ⟨99608, by rfl⟩ : syracuseStep 132811 = 199217) B199217
theorem B198359 : Blo 131789 198359 := bstep (se 1 (by rfl) ⟨148769, by rfl⟩ : syracuseStep 198359 = 297539) B297539
theorem B132823 : Blo 131789 132823 := bstep (se 1 (by rfl) ⟨99617, by rfl⟩ : syracuseStep 132823 = 199235) B199235
theorem B132843 : Blo 131789 132843 := bstep (se 1 (by rfl) ⟨99632, by rfl⟩ : syracuseStep 132843 = 199265) B199265
theorem B132855 : Blo 131789 132855 := bstep (se 1 (by rfl) ⟨99641, by rfl⟩ : syracuseStep 132855 = 199283) B199283
theorem B132875 : Blo 131789 132875 := bstep (se 1 (by rfl) ⟨99656, by rfl⟩ : syracuseStep 132875 = 199313) B199313
theorem B132887 : Blo 131789 132887 := bstep (se 1 (by rfl) ⟨99665, by rfl⟩ : syracuseStep 132887 = 199331) B199331
theorem B296729 : Blo 131789 296729 := bstep (se 2 (by rfl) ⟨111273, by rfl⟩ : syracuseStep 296729 = 222547) B222547
theorem B198425 : Blo 131789 198425 := bstep (se 2 (by rfl) ⟨74409, by rfl⟩ : syracuseStep 198425 = 148819) B148819
theorem B132907 : Blo 131789 132907 := bstep (se 1 (by rfl) ⟨99680, by rfl⟩ : syracuseStep 132907 = 199361) B199361
theorem B132919 : Blo 131789 132919 := bstep (se 1 (by rfl) ⟨99689, by rfl⟩ : syracuseStep 132919 = 199379) B199379
theorem B132939 : Blo 131789 132939 := bstep (se 1 (by rfl) ⟨99704, by rfl⟩ : syracuseStep 132939 = 199409) B199409
theorem B132951 : Blo 131789 132951 := bstep (se 1 (by rfl) ⟨99713, by rfl⟩ : syracuseStep 132951 = 199427) B199427
theorem B952165 : Blo 131789 952165 := bstep (se 4 (by rfl) ⟨89265, by rfl⟩ : syracuseStep 952165 = 178531) B178531
theorem B132971 : Blo 131789 132971 := bstep (se 1 (by rfl) ⟨99728, by rfl⟩ : syracuseStep 132971 = 199457) B199457
theorem B296819 : Blo 131789 296819 := bstep (se 1 (by rfl) ⟨222614, by rfl⟩ : syracuseStep 296819 = 445229) B445229
theorem B132983 : Blo 131789 132983 := bstep (se 1 (by rfl) ⟨99737, by rfl⟩ : syracuseStep 132983 = 199475) B199475
theorem B198539 : Blo 131789 198539 := bstep (se 1 (by rfl) ⟨148904, by rfl⟩ : syracuseStep 198539 = 297809) B297809
theorem B133003 : Blo 131789 133003 := bstep (se 1 (by rfl) ⟨99752, by rfl⟩ : syracuseStep 133003 = 199505) B199505
theorem B296855 : Blo 131789 296855 := bstep (se 1 (by rfl) ⟨222641, by rfl⟩ : syracuseStep 296855 = 445283) B445283
theorem B198551 : Blo 131789 198551 := bstep (se 1 (by rfl) ⟨148913, by rfl⟩ : syracuseStep 198551 = 297827) B297827
theorem B133015 : Blo 131789 133015 := bstep (se 1 (by rfl) ⟨99761, by rfl⟩ : syracuseStep 133015 = 199523) B199523
theorem B133035 : Blo 131789 133035 := bstep (se 1 (by rfl) ⟨99776, by rfl⟩ : syracuseStep 133035 = 199553) B199553
theorem B133047 : Blo 131789 133047 := bstep (se 1 (by rfl) ⟨99785, by rfl⟩ : syracuseStep 133047 = 199571) B199571
theorem B133067 : Blo 131789 133067 := bstep (se 1 (by rfl) ⟨99800, by rfl⟩ : syracuseStep 133067 = 199601) B199601
theorem B133079 : Blo 131789 133079 := bstep (se 1 (by rfl) ⟨99809, by rfl⟩ : syracuseStep 133079 = 199619) B199619
theorem B198617 : Blo 131789 198617 := bstep (se 2 (by rfl) ⟨74481, by rfl⟩ : syracuseStep 198617 = 148963) B148963
theorem B133099 : Blo 131789 133099 := bstep (se 1 (by rfl) ⟨99824, by rfl⟩ : syracuseStep 133099 = 199649) B199649
theorem B133111 : Blo 131789 133111 := bstep (se 1 (by rfl) ⟨99833, by rfl⟩ : syracuseStep 133111 = 199667) B199667
theorem B133131 : Blo 131789 133131 := bstep (se 1 (by rfl) ⟨99848, by rfl⟩ : syracuseStep 133131 = 199697) B199697
theorem B133143 : Blo 131789 133143 := bstep (se 1 (by rfl) ⟨99857, by rfl⟩ : syracuseStep 133143 = 199715) B199715
theorem B133163 : Blo 131789 133163 := bstep (se 1 (by rfl) ⟨99872, by rfl⟩ : syracuseStep 133163 = 199745) B199745
theorem B133175 : Blo 131789 133175 := bstep (se 1 (by rfl) ⟨99881, by rfl⟩ : syracuseStep 133175 = 199763) B199763
theorem B297035 : Blo 131789 297035 := bstep (se 1 (by rfl) ⟨222776, by rfl⟩ : syracuseStep 297035 = 445553) B445553
theorem B198731 : Blo 131789 198731 := bstep (se 1 (by rfl) ⟨149048, by rfl⟩ : syracuseStep 198731 = 298097) B298097
theorem B133195 : Blo 131789 133195 := bstep (se 1 (by rfl) ⟨99896, by rfl⟩ : syracuseStep 133195 = 199793) B199793
theorem B198743 : Blo 131789 198743 := bstep (se 1 (by rfl) ⟨149057, by rfl⟩ : syracuseStep 198743 = 298115) B298115
theorem B133207 : Blo 131789 133207 := bstep (se 1 (by rfl) ⟨99905, by rfl⟩ : syracuseStep 133207 = 199811) B199811
theorem B133227 : Blo 131789 133227 := bstep (se 1 (by rfl) ⟨99920, by rfl⟩ : syracuseStep 133227 = 199841) B199841
theorem B133239 : Blo 131789 133239 := bstep (se 1 (by rfl) ⟨99929, by rfl⟩ : syracuseStep 133239 = 199859) B199859
theorem B297089 : Blo 131789 297089 := bstep (se 2 (by rfl) ⟨111408, by rfl⟩ : syracuseStep 297089 = 222817) B222817
theorem B133259 : Blo 131789 133259 := bstep (se 1 (by rfl) ⟨99944, by rfl⟩ : syracuseStep 133259 = 199889) B199889
theorem B133271 : Blo 131789 133271 := bstep (se 1 (by rfl) ⟨99953, by rfl⟩ : syracuseStep 133271 = 199907) B199907
theorem B198809 : Blo 131789 198809 := bstep (se 2 (by rfl) ⟨74553, by rfl⟩ : syracuseStep 198809 = 149107) B149107
theorem B133291 : Blo 131789 133291 := bstep (se 1 (by rfl) ⟨99968, by rfl⟩ : syracuseStep 133291 = 199937) B199937
theorem B362675 : Blo 131789 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B133303 : Blo 131789 133303 := bstep (se 1 (by rfl) ⟨99977, by rfl⟩ : syracuseStep 133303 = 199955) B199955
theorem B133323 : Blo 131789 133323 := bstep (se 1 (by rfl) ⟨99992, by rfl⟩ : syracuseStep 133323 = 199985) B199985
theorem B133335 : Blo 131789 133335 := bstep (se 1 (by rfl) ⟨100001, by rfl⟩ : syracuseStep 133335 = 200003) B200003
theorem B133355 : Blo 131789 133355 := bstep (se 1 (by rfl) ⟨100016, by rfl⟩ : syracuseStep 133355 = 200033) B200033
theorem B133367 : Blo 131789 133367 := bstep (se 1 (by rfl) ⟨100025, by rfl⟩ : syracuseStep 133367 = 200051) B200051
theorem B198923 : Blo 131789 198923 := bstep (se 1 (by rfl) ⟨149192, by rfl⟩ : syracuseStep 198923 = 298385) B298385
theorem B133387 : Blo 131789 133387 := bstep (se 1 (by rfl) ⟨100040, by rfl⟩ : syracuseStep 133387 = 200081) B200081
theorem B198935 : Blo 131789 198935 := bstep (se 1 (by rfl) ⟨149201, by rfl⟩ : syracuseStep 198935 = 298403) B298403
theorem B133399 : Blo 131789 133399 := bstep (se 1 (by rfl) ⟨100049, by rfl⟩ : syracuseStep 133399 = 200099) B200099
theorem B133419 : Blo 131789 133419 := bstep (se 1 (by rfl) ⟨100064, by rfl⟩ : syracuseStep 133419 = 200129) B200129
theorem B133431 : Blo 131789 133431 := bstep (se 1 (by rfl) ⟨100073, by rfl⟩ : syracuseStep 133431 = 200147) B200147
theorem B133451 : Blo 131789 133451 := bstep (se 1 (by rfl) ⟨100088, by rfl⟩ : syracuseStep 133451 = 200177) B200177
theorem B723275 : Blo 131789 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B133463 : Blo 131789 133463 := bstep (se 1 (by rfl) ⟨100097, by rfl⟩ : syracuseStep 133463 = 200195) B200195
theorem B297305 : Blo 131789 297305 := bstep (se 2 (by rfl) ⟨111489, by rfl⟩ : syracuseStep 297305 = 222979) B222979
theorem B199001 : Blo 131789 199001 := bstep (se 2 (by rfl) ⟨74625, by rfl⟩ : syracuseStep 199001 = 149251) B149251
theorem B133483 : Blo 131789 133483 := bstep (se 1 (by rfl) ⟨100112, by rfl⟩ : syracuseStep 133483 = 200225) B200225
theorem B133495 : Blo 131789 133495 := bstep (se 1 (by rfl) ⟨100121, by rfl⟩ : syracuseStep 133495 = 200243) B200243
theorem B133515 : Blo 131789 133515 := bstep (se 1 (by rfl) ⟨100136, by rfl⟩ : syracuseStep 133515 = 200273) B200273
theorem B133527 : Blo 131789 133527 := bstep (se 1 (by rfl) ⟨100145, by rfl⟩ : syracuseStep 133527 = 200291) B200291
theorem B133547 : Blo 131789 133547 := bstep (se 1 (by rfl) ⟨100160, by rfl⟩ : syracuseStep 133547 = 200321) B200321
theorem B297395 : Blo 131789 297395 := bstep (se 1 (by rfl) ⟨223046, by rfl⟩ : syracuseStep 297395 = 446093) B446093
theorem B133559 : Blo 131789 133559 := bstep (se 1 (by rfl) ⟨100169, by rfl⟩ : syracuseStep 133559 = 200339) B200339
theorem B199115 : Blo 131789 199115 := bstep (se 1 (by rfl) ⟨149336, by rfl⟩ : syracuseStep 199115 = 298673) B298673
theorem B133579 : Blo 131789 133579 := bstep (se 1 (by rfl) ⟨100184, by rfl⟩ : syracuseStep 133579 = 200369) B200369
theorem B297431 : Blo 131789 297431 := bstep (se 1 (by rfl) ⟨223073, by rfl⟩ : syracuseStep 297431 = 446147) B446147
theorem B199127 : Blo 131789 199127 := bstep (se 1 (by rfl) ⟨149345, by rfl⟩ : syracuseStep 199127 = 298691) B298691
theorem B133591 : Blo 131789 133591 := bstep (se 1 (by rfl) ⟨100193, by rfl⟩ : syracuseStep 133591 = 200387) B200387
theorem B133611 : Blo 131789 133611 := bstep (se 1 (by rfl) ⟨100208, by rfl⟩ : syracuseStep 133611 = 200417) B200417
theorem B133623 : Blo 131789 133623 := bstep (se 1 (by rfl) ⟨100217, by rfl⟩ : syracuseStep 133623 = 200435) B200435
theorem B133643 : Blo 131789 133643 := bstep (se 1 (by rfl) ⟨100232, by rfl⟩ : syracuseStep 133643 = 200465) B200465
theorem B133655 : Blo 131789 133655 := bstep (se 1 (by rfl) ⟨100241, by rfl⟩ : syracuseStep 133655 = 200483) B200483
theorem B199193 : Blo 131789 199193 := bstep (se 2 (by rfl) ⟨74697, by rfl⟩ : syracuseStep 199193 = 149395) B149395
theorem B133675 : Blo 131789 133675 := bstep (se 1 (by rfl) ⟨100256, by rfl⟩ : syracuseStep 133675 = 200513) B200513
theorem B133687 : Blo 131789 133687 := bstep (se 1 (by rfl) ⟨100265, by rfl⟩ : syracuseStep 133687 = 200531) B200531
theorem B133707 : Blo 131789 133707 := bstep (se 1 (by rfl) ⟨100280, by rfl⟩ : syracuseStep 133707 = 200561) B200561
theorem B133719 : Blo 131789 133719 := bstep (se 1 (by rfl) ⟨100289, by rfl⟩ : syracuseStep 133719 = 200579) B200579
theorem B133739 : Blo 131789 133739 := bstep (se 1 (by rfl) ⟨100304, by rfl⟩ : syracuseStep 133739 = 200609) B200609
theorem B133751 : Blo 131789 133751 := bstep (se 1 (by rfl) ⟨100313, by rfl⟩ : syracuseStep 133751 = 200627) B200627
theorem B297611 : Blo 131789 297611 := bstep (se 1 (by rfl) ⟨223208, by rfl⟩ : syracuseStep 297611 = 446417) B446417
theorem B199307 : Blo 131789 199307 := bstep (se 1 (by rfl) ⟨149480, by rfl⟩ : syracuseStep 199307 = 298961) B298961
theorem B133771 : Blo 131789 133771 := bstep (se 1 (by rfl) ⟨100328, by rfl⟩ : syracuseStep 133771 = 200657) B200657
theorem B199319 : Blo 131789 199319 := bstep (se 1 (by rfl) ⟨149489, by rfl⟩ : syracuseStep 199319 = 298979) B298979
theorem B133783 : Blo 131789 133783 := bstep (se 1 (by rfl) ⟨100337, by rfl⟩ : syracuseStep 133783 = 200675) B200675
theorem B133803 : Blo 131789 133803 := bstep (se 1 (by rfl) ⟨100352, by rfl⟩ : syracuseStep 133803 = 200705) B200705
theorem B133815 : Blo 131789 133815 := bstep (se 1 (by rfl) ⟨100361, by rfl⟩ : syracuseStep 133815 = 200723) B200723
theorem B297665 : Blo 131789 297665 := bstep (se 2 (by rfl) ⟨111624, by rfl⟩ : syracuseStep 297665 = 223249) B223249
theorem B133835 : Blo 131789 133835 := bstep (se 1 (by rfl) ⟨100376, by rfl⟩ : syracuseStep 133835 = 200753) B200753
theorem B133847 : Blo 131789 133847 := bstep (se 1 (by rfl) ⟨100385, by rfl⟩ : syracuseStep 133847 = 200771) B200771
theorem B199385 : Blo 131789 199385 := bstep (se 2 (by rfl) ⟨74769, by rfl⟩ : syracuseStep 199385 = 149539) B149539
theorem B133867 : Blo 131789 133867 := bstep (se 1 (by rfl) ⟨100400, by rfl⟩ : syracuseStep 133867 = 200801) B200801
theorem B133879 : Blo 131789 133879 := bstep (se 1 (by rfl) ⟨100409, by rfl⟩ : syracuseStep 133879 = 200819) B200819
theorem B133899 : Blo 131789 133899 := bstep (se 1 (by rfl) ⟨100424, by rfl⟩ : syracuseStep 133899 = 200849) B200849
theorem B133911 : Blo 131789 133911 := bstep (se 1 (by rfl) ⟨100433, by rfl⟩ : syracuseStep 133911 = 200867) B200867
theorem B133931 : Blo 131789 133931 := bstep (se 1 (by rfl) ⟨100448, by rfl⟩ : syracuseStep 133931 = 200897) B200897
theorem B133943 : Blo 131789 133943 := bstep (se 1 (by rfl) ⟨100457, by rfl⟩ : syracuseStep 133943 = 200915) B200915
theorem B199499 : Blo 131789 199499 := bstep (se 1 (by rfl) ⟨149624, by rfl⟩ : syracuseStep 199499 = 299249) B299249
theorem B133963 : Blo 131789 133963 := bstep (se 1 (by rfl) ⟨100472, by rfl⟩ : syracuseStep 133963 = 200945) B200945
theorem B199511 : Blo 131789 199511 := bstep (se 1 (by rfl) ⟨149633, by rfl⟩ : syracuseStep 199511 = 299267) B299267
theorem B133975 : Blo 131789 133975 := bstep (se 1 (by rfl) ⟨100481, by rfl⟩ : syracuseStep 133975 = 200963) B200963
theorem B133995 : Blo 131789 133995 := bstep (se 1 (by rfl) ⟨100496, by rfl⟩ : syracuseStep 133995 = 200993) B200993
theorem B134007 : Blo 131789 134007 := bstep (se 1 (by rfl) ⟨100505, by rfl⟩ : syracuseStep 134007 = 201011) B201011
theorem B756611 : Blo 131789 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B134027 : Blo 131789 134027 := bstep (se 1 (by rfl) ⟨100520, by rfl⟩ : syracuseStep 134027 = 201041) B201041
theorem B134039 : Blo 131789 134039 := bstep (se 1 (by rfl) ⟨100529, by rfl⟩ : syracuseStep 134039 = 201059) B201059
theorem B297881 : Blo 131789 297881 := bstep (se 2 (by rfl) ⟨111705, by rfl⟩ : syracuseStep 297881 = 223411) B223411
theorem B199577 : Blo 131789 199577 := bstep (se 2 (by rfl) ⟨74841, by rfl⟩ : syracuseStep 199577 = 149683) B149683
theorem B134059 : Blo 131789 134059 := bstep (se 1 (by rfl) ⟨100544, by rfl⟩ : syracuseStep 134059 = 201089) B201089
theorem B134071 : Blo 131789 134071 := bstep (se 1 (by rfl) ⟨100553, by rfl⟩ : syracuseStep 134071 = 201107) B201107
theorem B134091 : Blo 131789 134091 := bstep (se 1 (by rfl) ⟨100568, by rfl⟩ : syracuseStep 134091 = 201137) B201137
theorem B134103 : Blo 131789 134103 := bstep (se 1 (by rfl) ⟨100577, by rfl⟩ : syracuseStep 134103 = 201155) B201155
theorem B134123 : Blo 131789 134123 := bstep (se 1 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 134123 = 201185) B201185
theorem B297971 : Blo 131789 297971 := bstep (se 1 (by rfl) ⟨223478, by rfl⟩ : syracuseStep 297971 = 446957) B446957
theorem B134135 : Blo 131789 134135 := bstep (se 1 (by rfl) ⟨100601, by rfl⟩ : syracuseStep 134135 = 201203) B201203
theorem B199691 : Blo 131789 199691 := bstep (se 1 (by rfl) ⟨149768, by rfl⟩ : syracuseStep 199691 = 299537) B299537
theorem B134155 : Blo 131789 134155 := bstep (se 1 (by rfl) ⟨100616, by rfl⟩ : syracuseStep 134155 = 201233) B201233
theorem B298007 : Blo 131789 298007 := bstep (se 1 (by rfl) ⟨223505, by rfl⟩ : syracuseStep 298007 = 447011) B447011
theorem B199703 : Blo 131789 199703 := bstep (se 1 (by rfl) ⟨149777, by rfl⟩ : syracuseStep 199703 = 299555) B299555
theorem B134167 : Blo 131789 134167 := bstep (se 1 (by rfl) ⟨100625, by rfl⟩ : syracuseStep 134167 = 201251) B201251
theorem B134187 : Blo 131789 134187 := bstep (se 1 (by rfl) ⟨100640, by rfl⟩ : syracuseStep 134187 = 201281) B201281
theorem B134199 : Blo 131789 134199 := bstep (se 1 (by rfl) ⟨100649, by rfl⟩ : syracuseStep 134199 = 201299) B201299
theorem B429131 : Blo 131789 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B134219 : Blo 131789 134219 := bstep (se 1 (by rfl) ⟨100664, by rfl⟩ : syracuseStep 134219 = 201329) B201329
theorem B134231 : Blo 131789 134231 := bstep (se 1 (by rfl) ⟨100673, by rfl⟩ : syracuseStep 134231 = 201347) B201347
theorem B199769 : Blo 131789 199769 := bstep (se 2 (by rfl) ⟨74913, by rfl⟩ : syracuseStep 199769 = 149827) B149827
theorem B134251 : Blo 131789 134251 := bstep (se 1 (by rfl) ⟨100688, by rfl⟩ : syracuseStep 134251 = 201377) B201377
theorem B134263 : Blo 131789 134263 := bstep (se 1 (by rfl) ⟨100697, by rfl⟩ : syracuseStep 134263 = 201395) B201395
theorem B134283 : Blo 131789 134283 := bstep (se 1 (by rfl) ⟨100712, by rfl⟩ : syracuseStep 134283 = 201425) B201425
theorem B134295 : Blo 131789 134295 := bstep (se 1 (by rfl) ⟨100721, by rfl⟩ : syracuseStep 134295 = 201443) B201443
theorem B134315 : Blo 131789 134315 := bstep (se 1 (by rfl) ⟨100736, by rfl⟩ : syracuseStep 134315 = 201473) B201473
theorem B134327 : Blo 131789 134327 := bstep (se 1 (by rfl) ⟨100745, by rfl⟩ : syracuseStep 134327 = 201491) B201491
theorem B298187 : Blo 131789 298187 := bstep (se 1 (by rfl) ⟨223640, by rfl⟩ : syracuseStep 298187 = 447281) B447281
theorem B199883 : Blo 131789 199883 := bstep (se 1 (by rfl) ⟨149912, by rfl⟩ : syracuseStep 199883 = 299825) B299825
theorem B134347 : Blo 131789 134347 := bstep (se 1 (by rfl) ⟨100760, by rfl⟩ : syracuseStep 134347 = 201521) B201521
theorem B199895 : Blo 131789 199895 := bstep (se 1 (by rfl) ⟨149921, by rfl⟩ : syracuseStep 199895 = 299843) B299843
theorem B134359 : Blo 131789 134359 := bstep (se 1 (by rfl) ⟨100769, by rfl⟩ : syracuseStep 134359 = 201539) B201539
theorem B134379 : Blo 131789 134379 := bstep (se 1 (by rfl) ⟨100784, by rfl⟩ : syracuseStep 134379 = 201569) B201569
theorem B134391 : Blo 131789 134391 := bstep (se 1 (by rfl) ⟨100793, by rfl⟩ : syracuseStep 134391 = 201587) B201587
theorem B298241 : Blo 131789 298241 := bstep (se 2 (by rfl) ⟨111840, by rfl⟩ : syracuseStep 298241 = 223681) B223681
theorem B1019141 : Blo 131789 1019141 := bstep (se 4 (by rfl) ⟨95544, by rfl⟩ : syracuseStep 1019141 = 191089) B191089
theorem B167179 : Blo 131789 167179 := bstep (se 1 (by rfl) ⟨125384, by rfl⟩ : syracuseStep 167179 = 250769) B250769
theorem B134411 : Blo 131789 134411 := bstep (se 1 (by rfl) ⟨100808, by rfl⟩ : syracuseStep 134411 = 201617) B201617
theorem B134423 : Blo 131789 134423 := bstep (se 1 (by rfl) ⟨100817, by rfl⟩ : syracuseStep 134423 = 201635) B201635
theorem B199961 : Blo 131789 199961 := bstep (se 2 (by rfl) ⟨74985, by rfl⟩ : syracuseStep 199961 = 149971) B149971
theorem B134443 : Blo 131789 134443 := bstep (se 1 (by rfl) ⟨100832, by rfl⟩ : syracuseStep 134443 = 201665) B201665
theorem B134455 : Blo 131789 134455 := bstep (se 1 (by rfl) ⟨100841, by rfl⟩ : syracuseStep 134455 = 201683) B201683
theorem B134475 : Blo 131789 134475 := bstep (se 1 (by rfl) ⟨100856, by rfl⟩ : syracuseStep 134475 = 201713) B201713
theorem B134487 : Blo 131789 134487 := bstep (se 1 (by rfl) ⟨100865, by rfl⟩ : syracuseStep 134487 = 201731) B201731
theorem B134507 : Blo 131789 134507 := bstep (se 1 (by rfl) ⟨100880, by rfl⟩ : syracuseStep 134507 = 201761) B201761
theorem B134519 : Blo 131789 134519 := bstep (se 1 (by rfl) ⟨100889, by rfl⟩ : syracuseStep 134519 = 201779) B201779
theorem B200075 : Blo 131789 200075 := bstep (se 1 (by rfl) ⟨150056, by rfl⟩ : syracuseStep 200075 = 300113) B300113
theorem B134539 : Blo 131789 134539 := bstep (se 1 (by rfl) ⟨100904, by rfl⟩ : syracuseStep 134539 = 201809) B201809
theorem B200087 : Blo 131789 200087 := bstep (se 1 (by rfl) ⟨150065, by rfl⟩ : syracuseStep 200087 = 300131) B300131
theorem B134551 : Blo 131789 134551 := bstep (se 1 (by rfl) ⟨100913, by rfl⟩ : syracuseStep 134551 = 201827) B201827
theorem B134571 : Blo 131789 134571 := bstep (se 1 (by rfl) ⟨100928, by rfl⟩ : syracuseStep 134571 = 201857) B201857
theorem B134583 : Blo 131789 134583 := bstep (se 1 (by rfl) ⟨100937, by rfl⟩ : syracuseStep 134583 = 201875) B201875
theorem B134603 : Blo 131789 134603 := bstep (se 1 (by rfl) ⟨100952, by rfl⟩ : syracuseStep 134603 = 201905) B201905
theorem B134615 : Blo 131789 134615 := bstep (se 1 (by rfl) ⟨100961, by rfl⟩ : syracuseStep 134615 = 201923) B201923
theorem B298457 : Blo 131789 298457 := bstep (se 2 (by rfl) ⟨111921, by rfl⟩ : syracuseStep 298457 = 223843) B223843
theorem B200153 : Blo 131789 200153 := bstep (se 2 (by rfl) ⟨75057, by rfl⟩ : syracuseStep 200153 = 150115) B150115
theorem B134635 : Blo 131789 134635 := bstep (se 1 (by rfl) ⟨100976, by rfl⟩ : syracuseStep 134635 = 201953) B201953
theorem B134647 : Blo 131789 134647 := bstep (se 1 (by rfl) ⟨100985, by rfl⟩ : syracuseStep 134647 = 201971) B201971
theorem B134667 : Blo 131789 134667 := bstep (se 1 (by rfl) ⟨101000, by rfl⟩ : syracuseStep 134667 = 202001) B202001
theorem B167447 : Blo 131789 167447 := bstep (se 1 (by rfl) ⟨125585, by rfl⟩ : syracuseStep 167447 = 251171) B251171
theorem B134679 : Blo 131789 134679 := bstep (se 1 (by rfl) ⟨101009, by rfl⟩ : syracuseStep 134679 = 202019) B202019
theorem B134699 : Blo 131789 134699 := bstep (se 1 (by rfl) ⟨101024, by rfl⟩ : syracuseStep 134699 = 202049) B202049
theorem B298547 : Blo 131789 298547 := bstep (se 1 (by rfl) ⟨223910, by rfl⟩ : syracuseStep 298547 = 447821) B447821
theorem B134711 : Blo 131789 134711 := bstep (se 1 (by rfl) ⟨101033, by rfl⟩ : syracuseStep 134711 = 202067) B202067
theorem B200267 : Blo 131789 200267 := bstep (se 1 (by rfl) ⟨150200, by rfl⟩ : syracuseStep 200267 = 300401) B300401
theorem B134731 : Blo 131789 134731 := bstep (se 1 (by rfl) ⟨101048, by rfl⟩ : syracuseStep 134731 = 202097) B202097
theorem B298583 : Blo 131789 298583 := bstep (se 1 (by rfl) ⟨223937, by rfl⟩ : syracuseStep 298583 = 447875) B447875
theorem B200279 : Blo 131789 200279 := bstep (se 1 (by rfl) ⟨150209, by rfl⟩ : syracuseStep 200279 = 300419) B300419
theorem B134743 : Blo 131789 134743 := bstep (se 1 (by rfl) ⟨101057, by rfl⟩ : syracuseStep 134743 = 202115) B202115
theorem B134763 : Blo 131789 134763 := bstep (se 1 (by rfl) ⟨101072, by rfl⟩ : syracuseStep 134763 = 202145) B202145
theorem B134775 : Blo 131789 134775 := bstep (se 1 (by rfl) ⟨101081, by rfl⟩ : syracuseStep 134775 = 202163) B202163
theorem B134795 : Blo 131789 134795 := bstep (se 1 (by rfl) ⟨101096, by rfl⟩ : syracuseStep 134795 = 202193) B202193
theorem B134807 : Blo 131789 134807 := bstep (se 1 (by rfl) ⟨101105, by rfl⟩ : syracuseStep 134807 = 202211) B202211
theorem B200345 : Blo 131789 200345 := bstep (se 2 (by rfl) ⟨75129, by rfl⟩ : syracuseStep 200345 = 150259) B150259
theorem B134827 : Blo 131789 134827 := bstep (se 1 (by rfl) ⟨101120, by rfl⟩ : syracuseStep 134827 = 202241) B202241
theorem B134839 : Blo 131789 134839 := bstep (se 1 (by rfl) ⟨101129, by rfl⟩ : syracuseStep 134839 = 202259) B202259
theorem B134859 : Blo 131789 134859 := bstep (se 1 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 134859 = 202289) B202289
theorem B134871 : Blo 131789 134871 := bstep (se 1 (by rfl) ⟨101153, by rfl⟩ : syracuseStep 134871 = 202307) B202307
theorem B495325 : Blo 131789 495325 := bstep (se 3 (by rfl) ⟨92873, by rfl⟩ : syracuseStep 495325 = 185747) B185747
theorem B134891 : Blo 131789 134891 := bstep (se 1 (by rfl) ⟨101168, by rfl⟩ : syracuseStep 134891 = 202337) B202337
theorem B134903 : Blo 131789 134903 := bstep (se 1 (by rfl) ⟨101177, by rfl⟩ : syracuseStep 134903 = 202355) B202355
theorem B298763 : Blo 131789 298763 := bstep (se 1 (by rfl) ⟨224072, by rfl⟩ : syracuseStep 298763 = 448145) B448145
theorem B200459 : Blo 131789 200459 := bstep (se 1 (by rfl) ⟨150344, by rfl⟩ : syracuseStep 200459 = 300689) B300689
theorem B134923 : Blo 131789 134923 := bstep (se 1 (by rfl) ⟨101192, by rfl⟩ : syracuseStep 134923 = 202385) B202385
theorem B1085201 : Blo 131789 1085201 := bstep (se 2 (by rfl) ⟨406950, by rfl⟩ : syracuseStep 1085201 = 813901) B813901
theorem B200471 : Blo 131789 200471 := bstep (se 1 (by rfl) ⟨150353, by rfl⟩ : syracuseStep 200471 = 300707) B300707
theorem B134935 : Blo 131789 134935 := bstep (se 1 (by rfl) ⟨101201, by rfl⟩ : syracuseStep 134935 = 202403) B202403
theorem B134955 : Blo 131789 134955 := bstep (se 1 (by rfl) ⟨101216, by rfl⟩ : syracuseStep 134955 = 202433) B202433
theorem B134967 : Blo 131789 134967 := bstep (se 1 (by rfl) ⟨101225, by rfl⟩ : syracuseStep 134967 = 202451) B202451
theorem B298817 : Blo 131789 298817 := bstep (se 2 (by rfl) ⟨112056, by rfl⟩ : syracuseStep 298817 = 224113) B224113
theorem B134987 : Blo 131789 134987 := bstep (se 1 (by rfl) ⟨101240, by rfl⟩ : syracuseStep 134987 = 202481) B202481
theorem B462667 : Blo 131789 462667 := bstep (se 1 (by rfl) ⟨347000, by rfl⟩ : syracuseStep 462667 = 694001) B694001
theorem B134999 : Blo 131789 134999 := bstep (se 1 (by rfl) ⟨101249, by rfl⟩ : syracuseStep 134999 = 202499) B202499
theorem B200537 : Blo 131789 200537 := bstep (se 2 (by rfl) ⟨75201, by rfl⟩ : syracuseStep 200537 = 150403) B150403
theorem B135019 : Blo 131789 135019 := bstep (se 1 (by rfl) ⟨101264, by rfl⟩ : syracuseStep 135019 = 202529) B202529
theorem B135031 : Blo 131789 135031 := bstep (se 1 (by rfl) ⟨101273, by rfl⟩ : syracuseStep 135031 = 202547) B202547
theorem B135051 : Blo 131789 135051 := bstep (se 1 (by rfl) ⟨101288, by rfl⟩ : syracuseStep 135051 = 202577) B202577
theorem B364439 : Blo 131789 364439 := bstep (se 1 (by rfl) ⟨273329, by rfl⟩ : syracuseStep 364439 = 546659) B546659
theorem B135063 : Blo 131789 135063 := bstep (se 1 (by rfl) ⟨101297, by rfl⟩ : syracuseStep 135063 = 202595) B202595
theorem B135083 : Blo 131789 135083 := bstep (se 1 (by rfl) ⟨101312, by rfl⟩ : syracuseStep 135083 = 202625) B202625
theorem B135095 : Blo 131789 135095 := bstep (se 1 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 135095 = 202643) B202643
theorem B200651 : Blo 131789 200651 := bstep (se 1 (by rfl) ⟨150488, by rfl⟩ : syracuseStep 200651 = 300977) B300977
theorem B135115 : Blo 131789 135115 := bstep (se 1 (by rfl) ⟨101336, by rfl⟩ : syracuseStep 135115 = 202673) B202673
theorem B200663 : Blo 131789 200663 := bstep (se 1 (by rfl) ⟨150497, by rfl⟩ : syracuseStep 200663 = 300995) B300995
theorem B135127 : Blo 131789 135127 := bstep (se 1 (by rfl) ⟨101345, by rfl⟩ : syracuseStep 135127 = 202691) B202691
theorem B135147 : Blo 131789 135147 := bstep (se 1 (by rfl) ⟨101360, by rfl⟩ : syracuseStep 135147 = 202721) B202721
theorem B135159 : Blo 131789 135159 := bstep (se 1 (by rfl) ⟨101369, by rfl⟩ : syracuseStep 135159 = 202739) B202739
theorem B135179 : Blo 131789 135179 := bstep (se 1 (by rfl) ⟨101384, by rfl⟩ : syracuseStep 135179 = 202769) B202769
theorem B135191 : Blo 131789 135191 := bstep (se 1 (by rfl) ⟨101393, by rfl⟩ : syracuseStep 135191 = 202787) B202787
theorem B299033 : Blo 131789 299033 := bstep (se 2 (by rfl) ⟨112137, by rfl⟩ : syracuseStep 299033 = 224275) B224275
theorem B200729 : Blo 131789 200729 := bstep (se 2 (by rfl) ⟨75273, by rfl⟩ : syracuseStep 200729 = 150547) B150547
theorem B856109 : Blo 131789 856109 := bstep (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) B321041
theorem B135211 : Blo 131789 135211 := bstep (se 1 (by rfl) ⟨101408, by rfl⟩ : syracuseStep 135211 = 202817) B202817
theorem B135223 : Blo 131789 135223 := bstep (se 1 (by rfl) ⟨101417, by rfl⟩ : syracuseStep 135223 = 202835) B202835
theorem B135243 : Blo 131789 135243 := bstep (se 1 (by rfl) ⟨101432, by rfl⟩ : syracuseStep 135243 = 202865) B202865
theorem B135255 : Blo 131789 135255 := bstep (se 1 (by rfl) ⟨101441, by rfl⟩ : syracuseStep 135255 = 202883) B202883
theorem B135275 : Blo 131789 135275 := bstep (se 1 (by rfl) ⟨101456, by rfl⟩ : syracuseStep 135275 = 202913) B202913
theorem B299123 : Blo 131789 299123 := bstep (se 1 (by rfl) ⟨224342, by rfl⟩ : syracuseStep 299123 = 448685) B448685
theorem B135287 : Blo 131789 135287 := bstep (se 1 (by rfl) ⟨101465, by rfl⟩ : syracuseStep 135287 = 202931) B202931
theorem B200843 : Blo 131789 200843 := bstep (se 1 (by rfl) ⟨150632, by rfl⟩ : syracuseStep 200843 = 301265) B301265
theorem B135307 : Blo 131789 135307 := bstep (se 1 (by rfl) ⟨101480, by rfl⟩ : syracuseStep 135307 = 202961) B202961
theorem B299159 : Blo 131789 299159 := bstep (se 1 (by rfl) ⟨224369, by rfl⟩ : syracuseStep 299159 = 448739) B448739
theorem B200855 : Blo 131789 200855 := bstep (se 1 (by rfl) ⟨150641, by rfl⟩ : syracuseStep 200855 = 301283) B301283
theorem B135319 : Blo 131789 135319 := bstep (se 1 (by rfl) ⟨101489, by rfl⟩ : syracuseStep 135319 = 202979) B202979
theorem B135339 : Blo 131789 135339 := bstep (se 1 (by rfl) ⟨101504, by rfl⟩ : syracuseStep 135339 = 203009) B203009
theorem B135351 : Blo 131789 135351 := bstep (se 1 (by rfl) ⟨101513, by rfl⟩ : syracuseStep 135351 = 203027) B203027
theorem B135371 : Blo 131789 135371 := bstep (se 1 (by rfl) ⟨101528, by rfl⟩ : syracuseStep 135371 = 203057) B203057
theorem B168151 : Blo 131789 168151 := bstep (se 1 (by rfl) ⟨126113, by rfl⟩ : syracuseStep 168151 = 252227) B252227
theorem B135383 : Blo 131789 135383 := bstep (se 1 (by rfl) ⟨101537, by rfl⟩ : syracuseStep 135383 = 203075) B203075
theorem B200921 : Blo 131789 200921 := bstep (se 2 (by rfl) ⟨75345, by rfl⟩ : syracuseStep 200921 = 150691) B150691
theorem B135403 : Blo 131789 135403 := bstep (se 1 (by rfl) ⟨101552, by rfl⟩ : syracuseStep 135403 = 203105) B203105
theorem B135415 : Blo 131789 135415 := bstep (se 1 (by rfl) ⟨101561, by rfl⟩ : syracuseStep 135415 = 203123) B203123
theorem B135435 : Blo 131789 135435 := bstep (se 1 (by rfl) ⟨101576, by rfl⟩ : syracuseStep 135435 = 203153) B203153
theorem B18583829 : Blo 131789 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B135447 : Blo 131789 135447 := bstep (se 1 (by rfl) ⟨101585, by rfl⟩ : syracuseStep 135447 = 203171) B203171
theorem B135467 : Blo 131789 135467 := bstep (se 1 (by rfl) ⟨101600, by rfl⟩ : syracuseStep 135467 = 203201) B203201
theorem B135479 : Blo 131789 135479 := bstep (se 1 (by rfl) ⟨101609, by rfl⟩ : syracuseStep 135479 = 203219) B203219
theorem B299339 : Blo 131789 299339 := bstep (se 1 (by rfl) ⟨224504, by rfl⟩ : syracuseStep 299339 = 449009) B449009
theorem B201035 : Blo 131789 201035 := bstep (se 1 (by rfl) ⟨150776, by rfl⟩ : syracuseStep 201035 = 301553) B301553
theorem B135499 : Blo 131789 135499 := bstep (se 1 (by rfl) ⟨101624, by rfl⟩ : syracuseStep 135499 = 203249) B203249
theorem B201047 : Blo 131789 201047 := bstep (se 1 (by rfl) ⟨150785, by rfl⟩ : syracuseStep 201047 = 301571) B301571
theorem B135511 : Blo 131789 135511 := bstep (se 1 (by rfl) ⟨101633, by rfl⟩ : syracuseStep 135511 = 203267) B203267
theorem B135531 : Blo 131789 135531 := bstep (se 1 (by rfl) ⟨101648, by rfl⟩ : syracuseStep 135531 = 203297) B203297
theorem B135543 : Blo 131789 135543 := bstep (se 1 (by rfl) ⟨101657, by rfl⟩ : syracuseStep 135543 = 203315) B203315
theorem B299393 : Blo 131789 299393 := bstep (se 2 (by rfl) ⟨112272, by rfl⟩ : syracuseStep 299393 = 224545) B224545
theorem B135563 : Blo 131789 135563 := bstep (se 1 (by rfl) ⟨101672, by rfl⟩ : syracuseStep 135563 = 203345) B203345
theorem B135575 : Blo 131789 135575 := bstep (se 1 (by rfl) ⟨101681, by rfl⟩ : syracuseStep 135575 = 203363) B203363
theorem B201113 : Blo 131789 201113 := bstep (se 2 (by rfl) ⟨75417, by rfl⟩ : syracuseStep 201113 = 150835) B150835
theorem B135595 : Blo 131789 135595 := bstep (se 1 (by rfl) ⟨101696, by rfl⟩ : syracuseStep 135595 = 203393) B203393
theorem B364979 : Blo 131789 364979 := bstep (se 1 (by rfl) ⟨273734, by rfl⟩ : syracuseStep 364979 = 547469) B547469
theorem B463283 : Blo 131789 463283 := bstep (se 1 (by rfl) ⟨347462, by rfl⟩ : syracuseStep 463283 = 694925) B694925
theorem B135607 : Blo 131789 135607 := bstep (se 1 (by rfl) ⟨101705, by rfl⟩ : syracuseStep 135607 = 203411) B203411
theorem B135627 : Blo 131789 135627 := bstep (se 1 (by rfl) ⟨101720, by rfl⟩ : syracuseStep 135627 = 203441) B203441
theorem B135639 : Blo 131789 135639 := bstep (se 1 (by rfl) ⟨101729, by rfl⟩ : syracuseStep 135639 = 203459) B203459
theorem B135659 : Blo 131789 135659 := bstep (se 1 (by rfl) ⟨101744, by rfl⟩ : syracuseStep 135659 = 203489) B203489
theorem B135671 : Blo 131789 135671 := bstep (se 1 (by rfl) ⟨101753, by rfl⟩ : syracuseStep 135671 = 203507) B203507
theorem B201227 : Blo 131789 201227 := bstep (se 1 (by rfl) ⟨150920, by rfl⟩ : syracuseStep 201227 = 301841) B301841
theorem B135691 : Blo 131789 135691 := bstep (se 1 (by rfl) ⟨101768, by rfl⟩ : syracuseStep 135691 = 203537) B203537
theorem B201239 : Blo 131789 201239 := bstep (se 1 (by rfl) ⟨150929, by rfl⟩ : syracuseStep 201239 = 301859) B301859
theorem B135703 : Blo 131789 135703 := bstep (se 1 (by rfl) ⟨101777, by rfl⟩ : syracuseStep 135703 = 203555) B203555
theorem B135723 : Blo 131789 135723 := bstep (se 1 (by rfl) ⟨101792, by rfl⟩ : syracuseStep 135723 = 203585) B203585
theorem B135735 : Blo 131789 135735 := bstep (se 1 (by rfl) ⟨101801, by rfl⟩ : syracuseStep 135735 = 203603) B203603
theorem B135755 : Blo 131789 135755 := bstep (se 1 (by rfl) ⟨101816, by rfl⟩ : syracuseStep 135755 = 203633) B203633
theorem B135767 : Blo 131789 135767 := bstep (se 1 (by rfl) ⟨101825, by rfl⟩ : syracuseStep 135767 = 203651) B203651
theorem B299609 : Blo 131789 299609 := bstep (se 2 (by rfl) ⟨112353, by rfl⟩ : syracuseStep 299609 = 224707) B224707
theorem B201305 : Blo 131789 201305 := bstep (se 2 (by rfl) ⟨75489, by rfl⟩ : syracuseStep 201305 = 150979) B150979
theorem B135787 : Blo 131789 135787 := bstep (se 1 (by rfl) ⟨101840, by rfl⟩ : syracuseStep 135787 = 203681) B203681
theorem B2265731 : Blo 131789 2265731 := bstep (se 1 (by rfl) ⟨1699298, by rfl⟩ : syracuseStep 2265731 = 3398597) B3398597
theorem B299699 : Blo 131789 299699 := bstep (se 1 (by rfl) ⟨224774, by rfl⟩ : syracuseStep 299699 = 449549) B449549
theorem B430771 : Blo 131789 430771 := bstep (se 1 (by rfl) ⟨323078, by rfl⟩ : syracuseStep 430771 = 646157) B646157
theorem B201419 : Blo 131789 201419 := bstep (se 1 (by rfl) ⟨151064, by rfl⟩ : syracuseStep 201419 = 302129) B302129
theorem B299735 : Blo 131789 299735 := bstep (se 1 (by rfl) ⟨224801, by rfl⟩ : syracuseStep 299735 = 449603) B449603
theorem B201431 : Blo 131789 201431 := bstep (se 1 (by rfl) ⟨151073, by rfl⟩ : syracuseStep 201431 = 302147) B302147
theorem B201497 : Blo 131789 201497 := bstep (se 2 (by rfl) ⟨75561, by rfl⟩ : syracuseStep 201497 = 151123) B151123
theorem B299915 : Blo 131789 299915 := bstep (se 1 (by rfl) ⟨224936, by rfl⟩ : syracuseStep 299915 = 449873) B449873
theorem B201611 : Blo 131789 201611 := bstep (se 1 (by rfl) ⟨151208, by rfl⟩ : syracuseStep 201611 = 302417) B302417
theorem B201623 : Blo 131789 201623 := bstep (se 1 (by rfl) ⟨151217, by rfl⟩ : syracuseStep 201623 = 302435) B302435
theorem B2200499 : Blo 131789 2200499 := bstep (se 1 (by rfl) ⟨1650374, by rfl⟩ : syracuseStep 2200499 = 3300749) B3300749
theorem B299969 : Blo 131789 299969 := bstep (se 2 (by rfl) ⟨112488, by rfl⟩ : syracuseStep 299969 = 224977) B224977
theorem B201689 : Blo 131789 201689 := bstep (se 2 (by rfl) ⟨75633, by rfl⟩ : syracuseStep 201689 = 151267) B151267
theorem B201803 : Blo 131789 201803 := bstep (se 1 (by rfl) ⟨151352, by rfl⟩ : syracuseStep 201803 = 302705) B302705
theorem B201815 : Blo 131789 201815 := bstep (se 1 (by rfl) ⟨151361, by rfl⟩ : syracuseStep 201815 = 302723) B302723
theorem B300185 : Blo 131789 300185 := bstep (se 2 (by rfl) ⟨112569, by rfl⟩ : syracuseStep 300185 = 225139) B225139
theorem B201881 : Blo 131789 201881 := bstep (se 2 (by rfl) ⟨75705, by rfl⟩ : syracuseStep 201881 = 151411) B151411
theorem B300275 : Blo 131789 300275 := bstep (se 1 (by rfl) ⟨225206, by rfl⟩ : syracuseStep 300275 = 450413) B450413
theorem B201995 : Blo 131789 201995 := bstep (se 1 (by rfl) ⟨151496, by rfl⟩ : syracuseStep 201995 = 302993) B302993
theorem B988433 : Blo 131789 988433 := bstep (se 2 (by rfl) ⟨370662, by rfl⟩ : syracuseStep 988433 = 741325) B741325
theorem B300311 : Blo 131789 300311 := bstep (se 1 (by rfl) ⟨225233, by rfl⟩ : syracuseStep 300311 = 450467) B450467
theorem B202007 : Blo 131789 202007 := bstep (se 1 (by rfl) ⟨151505, by rfl⟩ : syracuseStep 202007 = 303011) B303011
theorem B202073 : Blo 131789 202073 := bstep (se 2 (by rfl) ⟨75777, by rfl⟩ : syracuseStep 202073 = 151555) B151555
theorem B300491 : Blo 131789 300491 := bstep (se 1 (by rfl) ⟨225368, by rfl⟩ : syracuseStep 300491 = 450737) B450737
theorem B202187 : Blo 131789 202187 := bstep (se 1 (by rfl) ⟨151640, by rfl⟩ : syracuseStep 202187 = 303281) B303281
theorem B202199 : Blo 131789 202199 := bstep (se 1 (by rfl) ⟨151649, by rfl⟩ : syracuseStep 202199 = 303299) B303299
theorem B300545 : Blo 131789 300545 := bstep (se 2 (by rfl) ⟨112704, by rfl⟩ : syracuseStep 300545 = 225409) B225409
theorem B202265 : Blo 131789 202265 := bstep (se 2 (by rfl) ⟨75849, by rfl⟩ : syracuseStep 202265 = 151699) B151699
theorem B2299427 : Blo 131789 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B1021571 : Blo 131789 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B202379 : Blo 131789 202379 := bstep (se 1 (by rfl) ⟨151784, by rfl⟩ : syracuseStep 202379 = 303569) B303569
theorem B202391 : Blo 131789 202391 := bstep (se 1 (by rfl) ⟨151793, by rfl⟩ : syracuseStep 202391 = 303587) B303587
theorem B300761 : Blo 131789 300761 := bstep (se 2 (by rfl) ⟨112785, by rfl⟩ : syracuseStep 300761 = 225571) B225571
theorem B202457 : Blo 131789 202457 := bstep (se 2 (by rfl) ⟨75921, by rfl⟩ : syracuseStep 202457 = 151843) B151843
theorem B300851 : Blo 131789 300851 := bstep (se 1 (by rfl) ⟨225638, by rfl⟩ : syracuseStep 300851 = 451277) B451277
theorem B202571 : Blo 131789 202571 := bstep (se 1 (by rfl) ⟨151928, by rfl⟩ : syracuseStep 202571 = 303857) B303857
theorem B300887 : Blo 131789 300887 := bstep (se 1 (by rfl) ⟨225665, by rfl⟩ : syracuseStep 300887 = 451331) B451331
theorem B202583 : Blo 131789 202583 := bstep (se 1 (by rfl) ⟨151937, by rfl⟩ : syracuseStep 202583 = 303875) B303875
theorem B169867 : Blo 131789 169867 := bstep (se 1 (by rfl) ⟨127400, by rfl⟩ : syracuseStep 169867 = 254801) B254801
theorem B202649 : Blo 131789 202649 := bstep (se 2 (by rfl) ⟨75993, by rfl⟩ : syracuseStep 202649 = 151987) B151987
theorem B301067 : Blo 131789 301067 := bstep (se 1 (by rfl) ⟨225800, by rfl⟩ : syracuseStep 301067 = 451601) B451601
theorem B202763 : Blo 131789 202763 := bstep (se 1 (by rfl) ⟨152072, by rfl⟩ : syracuseStep 202763 = 304145) B304145
theorem B202775 : Blo 131789 202775 := bstep (se 1 (by rfl) ⟨152081, by rfl⟩ : syracuseStep 202775 = 304163) B304163
theorem B825389 : Blo 131789 825389 := bstep (se 3 (by rfl) ⟨154760, by rfl⟩ : syracuseStep 825389 = 309521) B309521
theorem B301121 : Blo 131789 301121 := bstep (se 2 (by rfl) ⟨112920, by rfl⟩ : syracuseStep 301121 = 225841) B225841
theorem B202841 : Blo 131789 202841 := bstep (se 2 (by rfl) ⟨76065, by rfl⟩ : syracuseStep 202841 = 152131) B152131
theorem B334003 : Blo 131789 334003 := bstep (se 1 (by rfl) ⟨250502, by rfl⟩ : syracuseStep 334003 = 501005) B501005
theorem B202955 : Blo 131789 202955 := bstep (se 1 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 202955 = 304433) B304433
theorem B202967 : Blo 131789 202967 := bstep (se 1 (by rfl) ⟨152225, by rfl⟩ : syracuseStep 202967 = 304451) B304451
theorem B301337 : Blo 131789 301337 := bstep (se 2 (by rfl) ⟨113001, by rfl⟩ : syracuseStep 301337 = 226003) B226003
theorem B203033 : Blo 131789 203033 := bstep (se 2 (by rfl) ⟨76137, by rfl⟩ : syracuseStep 203033 = 152275) B152275
theorem B334145 : Blo 131789 334145 := bstep (se 2 (by rfl) ⟨125304, by rfl⟩ : syracuseStep 334145 = 250609) B250609
theorem B301427 : Blo 131789 301427 := bstep (se 1 (by rfl) ⟨226070, by rfl⟩ : syracuseStep 301427 = 452141) B452141
theorem B203147 : Blo 131789 203147 := bstep (se 1 (by rfl) ⟨152360, by rfl⟩ : syracuseStep 203147 = 304721) B304721
theorem B301463 : Blo 131789 301463 := bstep (se 1 (by rfl) ⟨226097, by rfl⟩ : syracuseStep 301463 = 452195) B452195
theorem B203159 : Blo 131789 203159 := bstep (se 1 (by rfl) ⟨152369, by rfl⟩ : syracuseStep 203159 = 304739) B304739
theorem B203225 : Blo 131789 203225 := bstep (se 2 (by rfl) ⟨76209, by rfl⟩ : syracuseStep 203225 = 152419) B152419
theorem B4299277 : Blo 131789 4299277 := bstep (se 3 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 4299277 = 1612229) B1612229
theorem B301643 : Blo 131789 301643 := bstep (se 1 (by rfl) ⟨226232, by rfl⟩ : syracuseStep 301643 = 452465) B452465
theorem B203339 : Blo 131789 203339 := bstep (se 1 (by rfl) ⟨152504, by rfl⟩ : syracuseStep 203339 = 305009) B305009
theorem B203351 : Blo 131789 203351 := bstep (se 1 (by rfl) ⟨152513, by rfl⟩ : syracuseStep 203351 = 305027) B305027
theorem B301697 : Blo 131789 301697 := bstep (se 2 (by rfl) ⟨113136, by rfl⟩ : syracuseStep 301697 = 226273) B226273
theorem B203417 : Blo 131789 203417 := bstep (se 2 (by rfl) ⟨76281, by rfl⟩ : syracuseStep 203417 = 152563) B152563
theorem B203531 : Blo 131789 203531 := bstep (se 1 (by rfl) ⟨152648, by rfl⟩ : syracuseStep 203531 = 305297) B305297
theorem B203543 : Blo 131789 203543 := bstep (se 1 (by rfl) ⟨152657, by rfl⟩ : syracuseStep 203543 = 305315) B305315
theorem B170839 : Blo 131789 170839 := bstep (se 1 (by rfl) ⟨128129, by rfl⟩ : syracuseStep 170839 = 256259) B256259
theorem B301913 : Blo 131789 301913 := bstep (se 2 (by rfl) ⟨113217, by rfl⟩ : syracuseStep 301913 = 226435) B226435
theorem B203609 : Blo 131789 203609 := bstep (se 2 (by rfl) ⟨76353, by rfl⟩ : syracuseStep 203609 = 152707) B152707
theorem B302003 : Blo 131789 302003 := bstep (se 1 (by rfl) ⟨226502, by rfl⟩ : syracuseStep 302003 = 453005) B453005
theorem B302039 : Blo 131789 302039 := bstep (se 1 (by rfl) ⟨226529, by rfl⟩ : syracuseStep 302039 = 453059) B453059
theorem B498649 : Blo 131789 498649 := bstep (se 2 (by rfl) ⟨186993, by rfl⟩ : syracuseStep 498649 = 373987) B373987
theorem B1252313 : Blo 131789 1252313 := bstep (se 2 (by rfl) ⟨469617, by rfl⟩ : syracuseStep 1252313 = 939235) B939235
theorem B433117 : Blo 131789 433117 := bstep (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) B162419
theorem B302219 : Blo 131789 302219 := bstep (se 1 (by rfl) ⟨226664, by rfl⟩ : syracuseStep 302219 = 453329) B453329
theorem B302273 : Blo 131789 302273 := bstep (se 2 (by rfl) ⟨113352, by rfl⟩ : syracuseStep 302273 = 226705) B226705
theorem B957701 : Blo 131789 957701 := bstep (se 4 (by rfl) ⟨89784, by rfl⟩ : syracuseStep 957701 = 179569) B179569
theorem B302489 : Blo 131789 302489 := bstep (se 2 (by rfl) ⟨113433, by rfl⟩ : syracuseStep 302489 = 226867) B226867
theorem B302579 : Blo 131789 302579 := bstep (se 1 (by rfl) ⟨226934, by rfl⟩ : syracuseStep 302579 = 453869) B453869
theorem B302615 : Blo 131789 302615 := bstep (se 1 (by rfl) ⟨226961, by rfl⟩ : syracuseStep 302615 = 453923) B453923
theorem B335411 : Blo 131789 335411 := bstep (se 1 (by rfl) ⟨251558, by rfl⟩ : syracuseStep 335411 = 503117) B503117
theorem B2301571 : Blo 131789 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B171659 : Blo 131789 171659 := bstep (se 1 (by rfl) ⟨128744, by rfl⟩ : syracuseStep 171659 = 257489) B257489
theorem B302795 : Blo 131789 302795 := bstep (se 1 (by rfl) ⟨227096, by rfl⟩ : syracuseStep 302795 = 454193) B454193
theorem B302849 : Blo 131789 302849 := bstep (se 2 (by rfl) ⟨113568, by rfl⟩ : syracuseStep 302849 = 227137) B227137
theorem B303065 : Blo 131789 303065 := bstep (se 2 (by rfl) ⟨113649, by rfl⟩ : syracuseStep 303065 = 227299) B227299
theorem B303155 : Blo 131789 303155 := bstep (se 1 (by rfl) ⟨227366, by rfl⟩ : syracuseStep 303155 = 454733) B454733
theorem B335947 : Blo 131789 335947 := bstep (se 1 (by rfl) ⟨251960, by rfl⟩ : syracuseStep 335947 = 503921) B503921
theorem B303191 : Blo 131789 303191 := bstep (se 1 (by rfl) ⟨227393, by rfl⟩ : syracuseStep 303191 = 454787) B454787
theorem B401501 : Blo 131789 401501 := bstep (se 3 (by rfl) ⟨75281, by rfl⟩ : syracuseStep 401501 = 150563) B150563
theorem B761987 : Blo 131789 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B5218445 : Blo 131789 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B860311 : Blo 131789 860311 := bstep (se 1 (by rfl) ⟨645233, by rfl⟩ : syracuseStep 860311 = 1290467) B1290467
theorem B336089 : Blo 131789 336089 := bstep (se 2 (by rfl) ⟨126033, by rfl⟩ : syracuseStep 336089 = 252067) B252067
theorem B237811 : Blo 131789 237811 := bstep (se 1 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 237811 = 356717) B356717
theorem B303371 : Blo 131789 303371 := bstep (se 1 (by rfl) ⟨227528, by rfl⟩ : syracuseStep 303371 = 455057) B455057
theorem B303425 : Blo 131789 303425 := bstep (se 2 (by rfl) ⟨113784, by rfl⟩ : syracuseStep 303425 = 227569) B227569
theorem B565649 : Blo 131789 565649 := bstep (se 2 (by rfl) ⟨212118, by rfl⟩ : syracuseStep 565649 = 424237) B424237
theorem B205271 : Blo 131789 205271 := bstep (se 1 (by rfl) ⟨153953, by rfl⟩ : syracuseStep 205271 = 307907) B307907
theorem B303641 : Blo 131789 303641 := bstep (se 2 (by rfl) ⟨113865, by rfl⟩ : syracuseStep 303641 = 227731) B227731
theorem B762443 : Blo 131789 762443 := bstep (se 1 (by rfl) ⟨571832, by rfl⟩ : syracuseStep 762443 = 1143665) B1143665
theorem B402013 : Blo 131789 402013 := bstep (se 3 (by rfl) ⟨75377, by rfl⟩ : syracuseStep 402013 = 150755) B150755
theorem B303731 : Blo 131789 303731 := bstep (se 1 (by rfl) ⟨227798, by rfl⟩ : syracuseStep 303731 = 455597) B455597
theorem B303767 : Blo 131789 303767 := bstep (se 1 (by rfl) ⟨227825, by rfl⟩ : syracuseStep 303767 = 455651) B455651
theorem B3842801 : Blo 131789 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B303947 : Blo 131789 303947 := bstep (se 1 (by rfl) ⟨227960, by rfl⟩ : syracuseStep 303947 = 455921) B455921
theorem B304001 : Blo 131789 304001 := bstep (se 2 (by rfl) ⟨114000, by rfl⟩ : syracuseStep 304001 = 228001) B228001
theorem B1024973 : Blo 131789 1024973 := bstep (se 3 (by rfl) ⟨192182, by rfl⟩ : syracuseStep 1024973 = 384365) B384365
theorem B500701 : Blo 131789 500701 := bstep (se 3 (by rfl) ⟨93881, by rfl⟩ : syracuseStep 500701 = 187763) B187763
theorem B336919 : Blo 131789 336919 := bstep (se 1 (by rfl) ⟨252689, by rfl⟩ : syracuseStep 336919 = 505379) B505379
theorem B304217 : Blo 131789 304217 := bstep (se 2 (by rfl) ⟨114081, by rfl⟩ : syracuseStep 304217 = 228163) B228163
theorem B566365 : Blo 131789 566365 := bstep (se 3 (by rfl) ⟨106193, by rfl⟩ : syracuseStep 566365 = 212387) B212387
theorem B304307 : Blo 131789 304307 := bstep (se 1 (by rfl) ⟨228230, by rfl⟩ : syracuseStep 304307 = 456461) B456461
theorem B304343 : Blo 131789 304343 := bstep (se 1 (by rfl) ⟨228257, by rfl⟩ : syracuseStep 304343 = 456515) B456515
theorem B304523 : Blo 131789 304523 := bstep (se 1 (by rfl) ⟨228392, by rfl⟩ : syracuseStep 304523 = 456785) B456785
theorem B1025459 : Blo 131789 1025459 := bstep (se 1 (by rfl) ⟨769094, by rfl⟩ : syracuseStep 1025459 = 1538189) B1538189
theorem B304577 : Blo 131789 304577 := bstep (se 2 (by rfl) ⟨114216, by rfl⟩ : syracuseStep 304577 = 228433) B228433
theorem B337355 : Blo 131789 337355 := bstep (se 1 (by rfl) ⟨253016, by rfl⟩ : syracuseStep 337355 = 506033) B506033
theorem B271819 : Blo 131789 271819 := bstep (se 1 (by rfl) ⟨203864, by rfl⟩ : syracuseStep 271819 = 407729) B407729
theorem B140887 : Blo 131789 140887 := bstep (se 1 (by rfl) ⟨105665, by rfl⟩ : syracuseStep 140887 = 211331) B211331
theorem B304769 : Blo 131789 304769 := bstep (se 2 (by rfl) ⟨114288, by rfl⟩ : syracuseStep 304769 = 228577) B228577
theorem B304793 : Blo 131789 304793 := bstep (se 2 (by rfl) ⟨114297, by rfl⟩ : syracuseStep 304793 = 228595) B228595
theorem B1156787 : Blo 131789 1156787 := bstep (se 1 (by rfl) ⟨867590, by rfl⟩ : syracuseStep 1156787 = 1735181) B1735181
theorem B304883 : Blo 131789 304883 := bstep (se 1 (by rfl) ⟨228662, by rfl⟩ : syracuseStep 304883 = 457325) B457325
theorem B239383 : Blo 131789 239383 := bstep (se 1 (by rfl) ⟨179537, by rfl⟩ : syracuseStep 239383 = 359075) B359075
theorem B304919 : Blo 131789 304919 := bstep (se 1 (by rfl) ⟨228689, by rfl⟩ : syracuseStep 304919 = 457379) B457379
theorem B337729 : Blo 131789 337729 := bstep (se 2 (by rfl) ⟨126648, by rfl⟩ : syracuseStep 337729 = 253297) B253297
theorem B305099 : Blo 131789 305099 := bstep (se 1 (by rfl) ⟨228824, by rfl⟩ : syracuseStep 305099 = 457649) B457649
theorem B305153 : Blo 131789 305153 := bstep (se 2 (by rfl) ⟨114432, by rfl⟩ : syracuseStep 305153 = 228865) B228865
theorem B534545 : Blo 131789 534545 := bstep (se 2 (by rfl) ⟨200454, by rfl⟩ : syracuseStep 534545 = 400909) B400909
theorem B1157165 : Blo 131789 1157165 := bstep (se 3 (by rfl) ⟨216968, by rfl⟩ : syracuseStep 1157165 = 433937) B433937
theorem B501977 : Blo 131789 501977 := bstep (se 2 (by rfl) ⟨188241, by rfl⟩ : syracuseStep 501977 = 376483) B376483
theorem B305369 : Blo 131789 305369 := bstep (se 2 (by rfl) ⟨114513, by rfl⟩ : syracuseStep 305369 = 229027) B229027
theorem B305459 : Blo 131789 305459 := bstep (se 1 (by rfl) ⟨229094, by rfl⟩ : syracuseStep 305459 = 458189) B458189
theorem B305495 : Blo 131789 305495 := bstep (se 1 (by rfl) ⟨229121, by rfl⟩ : syracuseStep 305495 = 458243) B458243
theorem B141707 : Blo 131789 141707 := bstep (se 1 (by rfl) ⟨106280, by rfl⟩ : syracuseStep 141707 = 212561) B212561
theorem B338327 : Blo 131789 338327 := bstep (se 1 (by rfl) ⟨253745, by rfl⟩ : syracuseStep 338327 = 507491) B507491
theorem B1354163 : Blo 131789 1354163 := bstep (se 1 (by rfl) ⟨1015622, by rfl⟩ : syracuseStep 1354163 = 2031245) B2031245
theorem B240089 : Blo 131789 240089 := bstep (se 2 (by rfl) ⟨90033, by rfl⟩ : syracuseStep 240089 = 180067) B180067
theorem B272857 : Blo 131789 272857 := bstep (se 2 (by rfl) ⟨102321, by rfl⟩ : syracuseStep 272857 = 204643) B204643
theorem B1878563 : Blo 131789 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B1026917 : Blo 131789 1026917 := bstep (se 4 (by rfl) ⟨96273, by rfl⟩ : syracuseStep 1026917 = 192547) B192547
theorem B339137 : Blo 131789 339137 := bstep (se 2 (by rfl) ⟨127176, by rfl⟩ : syracuseStep 339137 = 254353) B254353
theorem B404801 : Blo 131789 404801 := bstep (se 2 (by rfl) ⟨151800, by rfl⟩ : syracuseStep 404801 = 303601) B303601
theorem B1027403 : Blo 131789 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B732509 : Blo 131789 732509 := bstep (se 3 (by rfl) ⟨137345, by rfl⟩ : syracuseStep 732509 = 274691) B274691
theorem B1519235 : Blo 131789 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B339673 : Blo 131789 339673 := bstep (se 2 (by rfl) ⟨127377, by rfl⟩ : syracuseStep 339673 = 254755) B254755
theorem B143095 : Blo 131789 143095 := bstep (se 1 (by rfl) ⟨107321, by rfl⟩ : syracuseStep 143095 = 214643) B214643
theorem B503603 : Blo 131789 503603 := bstep (se 1 (by rfl) ⟨377702, by rfl⟩ : syracuseStep 503603 = 755405) B755405
theorem B503617 : Blo 131789 503617 := bstep (se 2 (by rfl) ⟨188856, by rfl⟩ : syracuseStep 503617 = 377713) B377713
theorem B536537 : Blo 131789 536537 := bstep (se 2 (by rfl) ⟨201201, by rfl⟩ : syracuseStep 536537 = 402403) B402403
theorem B1093637 : Blo 131789 1093637 := bstep (se 4 (by rfl) ⟨102528, by rfl⟩ : syracuseStep 1093637 = 205057) B205057
theorem B143915 : Blo 131789 143915 := bstep (se 1 (by rfl) ⟨107936, by rfl⟩ : syracuseStep 143915 = 215873) B215873
theorem B569987 : Blo 131789 569987 := bstep (se 1 (by rfl) ⟨427490, by rfl⟩ : syracuseStep 569987 = 854981) B854981
theorem B537281 : Blo 131789 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B1717037 : Blo 131789 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B340787 : Blo 131789 340787 := bstep (se 1 (by rfl) ⟨255590, by rfl⟩ : syracuseStep 340787 = 511181) B511181
theorem B275251 : Blo 131789 275251 := bstep (se 1 (by rfl) ⟨206438, by rfl⟩ : syracuseStep 275251 = 412877) B412877
theorem B242713 : Blo 131789 242713 := bstep (se 2 (by rfl) ⟨91017, by rfl⟩ : syracuseStep 242713 = 182035) B182035
theorem B341081 : Blo 131789 341081 := bstep (se 2 (by rfl) ⟨127905, by rfl⟩ : syracuseStep 341081 = 255811) B255811
theorem B767069 : Blo 131789 767069 := bstep (se 3 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 767069 = 287651) B287651
theorem B669059 : Blo 131789 669059 := bstep (se 1 (by rfl) ⟨501794, by rfl⟩ : syracuseStep 669059 = 1003589) B1003589
theorem B1291697 : Blo 131789 1291697 := bstep (se 2 (by rfl) ⟨484386, by rfl⟩ : syracuseStep 1291697 = 968773) B968773
theorem B1553843 : Blo 131789 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B144919 : Blo 131789 144919 := bstep (se 1 (by rfl) ⟨108689, by rfl⟩ : syracuseStep 144919 = 217379) B217379
theorem B505547 : Blo 131789 505547 := bstep (se 1 (by rfl) ⟨379160, by rfl⟩ : syracuseStep 505547 = 758321) B758321
theorem B505561 : Blo 131789 505561 := bstep (se 2 (by rfl) ⟨189585, by rfl⟩ : syracuseStep 505561 = 379171) B379171
theorem B767819 : Blo 131789 767819 := bstep (se 1 (by rfl) ⟨575864, by rfl⟩ : syracuseStep 767819 = 1151729) B1151729
theorem B2176885 : Blo 131789 2176885 := bstep (se 5 (by rfl) ⟨102041, by rfl⟩ : syracuseStep 2176885 = 204083) B204083
theorem B14956597 : Blo 131789 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B571799 : Blo 131789 571799 := bstep (se 1 (by rfl) ⟨428849, by rfl⟩ : syracuseStep 571799 = 857699) B857699
theorem B1161745 : Blo 131789 1161745 := bstep (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) B871309
theorem B506519 : Blo 131789 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B146071 : Blo 131789 146071 := bstep (se 1 (by rfl) ⟨109553, by rfl⟩ : syracuseStep 146071 = 219107) B219107
theorem B342731 : Blo 131789 342731 := bstep (se 1 (by rfl) ⟨257048, by rfl⟩ : syracuseStep 342731 = 514097) B514097
theorem B375617 : Blo 131789 375617 := bstep (se 2 (by rfl) ⟨140856, by rfl⟩ : syracuseStep 375617 = 281713) B281713
theorem B375641 : Blo 131789 375641 := bstep (se 2 (by rfl) ⟨140865, by rfl⟩ : syracuseStep 375641 = 281731) B281731
theorem B1129859 : Blo 131789 1129859 := bstep (se 1 (by rfl) ⟨847394, by rfl⟩ : syracuseStep 1129859 = 1694789) B1694789
theorem B4078997 : Blo 131789 4078997 := bstep (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) B191203
theorem B212375 : Blo 131789 212375 := bstep (se 1 (by rfl) ⟨159281, by rfl⟩ : syracuseStep 212375 = 318563) B318563
theorem B769459 : Blo 131789 769459 := bstep (se 1 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 769459 = 1154189) B1154189
theorem B540121 : Blo 131789 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B343703 : Blo 131789 343703 := bstep (se 1 (by rfl) ⟨257777, by rfl⟩ : syracuseStep 343703 = 515555) B515555
theorem B573131 : Blo 131789 573131 := bstep (se 1 (by rfl) ⟨429848, by rfl⟩ : syracuseStep 573131 = 859697) B859697
theorem B507779 : Blo 131789 507779 := bstep (se 1 (by rfl) ⟨380834, by rfl⟩ : syracuseStep 507779 = 761669) B761669
theorem B212939 : Blo 131789 212939 := bstep (se 1 (by rfl) ⟨159704, by rfl⟩ : syracuseStep 212939 = 319409) B319409
theorem B966691 : Blo 131789 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B376883 : Blo 131789 376883 := bstep (se 1 (by rfl) ⟨282662, by rfl⟩ : syracuseStep 376883 = 565325) B565325
theorem B213079 : Blo 131789 213079 := bstep (se 1 (by rfl) ⟨159809, by rfl⟩ : syracuseStep 213079 = 319619) B319619
theorem B573713 : Blo 131789 573713 := bstep (se 2 (by rfl) ⟨215142, by rfl⟩ : syracuseStep 573713 = 430285) B430285
theorem B1327691 : Blo 131789 1327691 := bstep (se 1 (by rfl) ⟨995768, by rfl⟩ : syracuseStep 1327691 = 1991537) B1991537
theorem B148055 : Blo 131789 148055 := bstep (se 1 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 148055 = 222083) B222083
theorem B148279 : Blo 131789 148279 := bstep (se 1 (by rfl) ⟨111209, by rfl⟩ : syracuseStep 148279 = 222419) B222419
theorem B475969 : Blo 131789 475969 := bstep (se 2 (by rfl) ⟨178488, by rfl⟩ : syracuseStep 475969 = 356977) B356977
theorem B770917 : Blo 131789 770917 := bstep (se 4 (by rfl) ⟨72273, by rfl⟩ : syracuseStep 770917 = 144547) B144547
theorem B213899 : Blo 131789 213899 := bstep (se 1 (by rfl) ⟨160424, by rfl⟩ : syracuseStep 213899 = 320849) B320849
theorem B213977 : Blo 131789 213977 := bstep (se 2 (by rfl) ⟨80241, by rfl⟩ : syracuseStep 213977 = 160483) B160483
theorem B148459 : Blo 131789 148459 := bstep (se 1 (by rfl) ⟨111344, by rfl⟩ : syracuseStep 148459 = 222689) B222689
theorem B672785 : Blo 131789 672785 := bstep (se 2 (by rfl) ⟨252294, by rfl⟩ : syracuseStep 672785 = 504589) B504589
theorem B1557521 : Blo 131789 1557521 := bstep (se 2 (by rfl) ⟨584070, by rfl⟩ : syracuseStep 1557521 = 1168141) B1168141
theorem B214039 : Blo 131789 214039 := bstep (se 1 (by rfl) ⟨160529, by rfl⟩ : syracuseStep 214039 = 321059) B321059
theorem B148567 : Blo 131789 148567 := bstep (se 1 (by rfl) ⟨111425, by rfl⟩ : syracuseStep 148567 = 222851) B222851
theorem B672947 : Blo 131789 672947 := bstep (se 1 (by rfl) ⟨504710, by rfl⟩ : syracuseStep 672947 = 1009421) B1009421
theorem B181451 : Blo 131789 181451 := bstep (se 1 (by rfl) ⟨136088, by rfl⟩ : syracuseStep 181451 = 272177) B272177
theorem B1950925 : Blo 131789 1950925 := bstep (se 3 (by rfl) ⟨365798, by rfl⟩ : syracuseStep 1950925 = 731597) B731597
theorem B148747 : Blo 131789 148747 := bstep (se 1 (by rfl) ⟨111560, by rfl⟩ : syracuseStep 148747 = 223121) B223121
theorem B574771 : Blo 131789 574771 := bstep (se 1 (by rfl) ⟨431078, by rfl⟩ : syracuseStep 574771 = 862157) B862157
theorem B148855 : Blo 131789 148855 := bstep (se 1 (by rfl) ⟨111641, by rfl⟩ : syracuseStep 148855 = 223283) B223283
theorem B149035 : Blo 131789 149035 := bstep (se 1 (by rfl) ⟨111776, by rfl⟩ : syracuseStep 149035 = 223553) B223553
theorem B771677 : Blo 131789 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B149143 : Blo 131789 149143 := bstep (se 1 (by rfl) ⟨111857, by rfl⟩ : syracuseStep 149143 = 223715) B223715
theorem B149323 : Blo 131789 149323 := bstep (se 1 (by rfl) ⟨111992, by rfl⟩ : syracuseStep 149323 = 223985) B223985
theorem B149431 : Blo 131789 149431 := bstep (se 1 (by rfl) ⟨112073, by rfl⟩ : syracuseStep 149431 = 224147) B224147
theorem B149611 : Blo 131789 149611 := bstep (se 1 (by rfl) ⟨112208, by rfl⟩ : syracuseStep 149611 = 224417) B224417
theorem B739459 : Blo 131789 739459 := bstep (se 1 (by rfl) ⟨554594, by rfl⟩ : syracuseStep 739459 = 1109189) B1109189
theorem B7850135 : Blo 131789 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B1460429 : Blo 131789 1460429 := bstep (se 3 (by rfl) ⟨273830, by rfl⟩ : syracuseStep 1460429 = 547661) B547661
theorem B149719 : Blo 131789 149719 := bstep (se 1 (by rfl) ⟨112289, by rfl⟩ : syracuseStep 149719 = 224579) B224579
theorem B1099993 : Blo 131789 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B149899 : Blo 131789 149899 := bstep (se 1 (by rfl) ⟨112424, by rfl⟩ : syracuseStep 149899 = 224849) B224849
theorem B444851 : Blo 131789 444851 := bstep (se 1 (by rfl) ⟨333638, by rfl⟩ : syracuseStep 444851 = 667277) B667277
theorem B150007 : Blo 131789 150007 := bstep (se 1 (by rfl) ⟨112505, by rfl⟩ : syracuseStep 150007 = 225011) B225011
theorem B510553 : Blo 131789 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B150187 : Blo 131789 150187 := bstep (se 1 (by rfl) ⟨112640, by rfl⟩ : syracuseStep 150187 = 225281) B225281
theorem B576173 : Blo 131789 576173 := bstep (se 3 (by rfl) ⟨108032, by rfl⟩ : syracuseStep 576173 = 216065) B216065
theorem B445121 : Blo 131789 445121 := bstep (se 2 (by rfl) ⟨166920, by rfl⟩ : syracuseStep 445121 = 333841) B333841
theorem B150295 : Blo 131789 150295 := bstep (se 1 (by rfl) ⟨112721, by rfl⟩ : syracuseStep 150295 = 225443) B225443
theorem B379741 : Blo 131789 379741 := bstep (se 3 (by rfl) ⟨71201, by rfl⟩ : syracuseStep 379741 = 142403) B142403
theorem B379799 : Blo 131789 379799 := bstep (se 1 (by rfl) ⟨284849, by rfl⟩ : syracuseStep 379799 = 569699) B569699
theorem B510893 : Blo 131789 510893 := bstep (se 3 (by rfl) ⟨95792, by rfl⟩ : syracuseStep 510893 = 191585) B191585
theorem B150475 : Blo 131789 150475 := bstep (se 1 (by rfl) ⟨112856, by rfl⟩ : syracuseStep 150475 = 225713) B225713
theorem B150583 : Blo 131789 150583 := bstep (se 1 (by rfl) ⟨112937, by rfl⟩ : syracuseStep 150583 = 225875) B225875
theorem B674891 : Blo 131789 674891 := bstep (se 1 (by rfl) ⟨506168, by rfl⟩ : syracuseStep 674891 = 1012337) B1012337
theorem B445661 : Blo 131789 445661 := bstep (se 3 (by rfl) ⟨83561, by rfl⟩ : syracuseStep 445661 = 167123) B167123
theorem B150763 : Blo 131789 150763 := bstep (se 1 (by rfl) ⟨113072, by rfl⟩ : syracuseStep 150763 = 226145) B226145
theorem B806219 : Blo 131789 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B150871 : Blo 131789 150871 := bstep (se 1 (by rfl) ⟨113153, by rfl⟩ : syracuseStep 150871 = 226307) B226307
theorem B151051 : Blo 131789 151051 := bstep (se 1 (by rfl) ⟨113288, by rfl⟩ : syracuseStep 151051 = 226577) B226577
theorem B151159 : Blo 131789 151159 := bstep (se 1 (by rfl) ⟨113369, by rfl⟩ : syracuseStep 151159 = 226739) B226739
theorem B511667 : Blo 131789 511667 := bstep (se 1 (by rfl) ⟨383750, by rfl⟩ : syracuseStep 511667 = 767501) B767501
theorem B151339 : Blo 131789 151339 := bstep (se 1 (by rfl) ⟨113504, by rfl⟩ : syracuseStep 151339 = 227009) B227009
theorem B347993 : Blo 131789 347993 := bstep (se 2 (by rfl) ⟨130497, by rfl⟩ : syracuseStep 347993 = 260995) B260995
theorem B282457 : Blo 131789 282457 := bstep (se 2 (by rfl) ⟨105921, by rfl⟩ : syracuseStep 282457 = 211843) B211843
theorem B151447 : Blo 131789 151447 := bstep (se 1 (by rfl) ⟨113585, by rfl⟩ : syracuseStep 151447 = 227171) B227171
theorem B446411 : Blo 131789 446411 := bstep (se 1 (by rfl) ⟨334808, by rfl⟩ : syracuseStep 446411 = 669617) B669617
theorem B151627 : Blo 131789 151627 := bstep (se 1 (by rfl) ⟨113720, by rfl⟩ : syracuseStep 151627 = 227441) B227441
theorem B381017 : Blo 131789 381017 := bstep (se 2 (by rfl) ⟨142881, by rfl⟩ : syracuseStep 381017 = 285763) B285763
theorem B872579 : Blo 131789 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B1527959 : Blo 131789 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B2904245 : Blo 131789 2904245 := bstep (se 5 (by rfl) ⟨136136, by rfl⟩ : syracuseStep 2904245 = 272273) B272273
theorem B151735 : Blo 131789 151735 := bstep (se 1 (by rfl) ⟨113801, by rfl⟩ : syracuseStep 151735 = 227603) B227603
theorem B381131 : Blo 131789 381131 := bstep (se 1 (by rfl) ⟨285848, by rfl⟩ : syracuseStep 381131 = 571697) B571697
theorem B643373 : Blo 131789 643373 := bstep (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) B241265
theorem B446795 : Blo 131789 446795 := bstep (se 1 (by rfl) ⟨335096, by rfl⟩ : syracuseStep 446795 = 670193) B670193
theorem B250199 : Blo 131789 250199 := bstep (se 1 (by rfl) ⟨187649, by rfl⟩ : syracuseStep 250199 = 375299) B375299
theorem B151915 : Blo 131789 151915 := bstep (se 1 (by rfl) ⟨113936, by rfl⟩ : syracuseStep 151915 = 227873) B227873
theorem B152023 : Blo 131789 152023 := bstep (se 1 (by rfl) ⟨114017, by rfl⟩ : syracuseStep 152023 = 228035) B228035
theorem B447065 : Blo 131789 447065 := bstep (se 2 (by rfl) ⟨167649, by rfl⟩ : syracuseStep 447065 = 335299) B335299
theorem B152203 : Blo 131789 152203 := bstep (se 1 (by rfl) ⟨114152, by rfl⟩ : syracuseStep 152203 = 228305) B228305
theorem B152311 : Blo 131789 152311 := bstep (se 1 (by rfl) ⟨114233, by rfl⟩ : syracuseStep 152311 = 228467) B228467
theorem B676673 : Blo 131789 676673 := bstep (se 2 (by rfl) ⟨253752, by rfl⟩ : syracuseStep 676673 = 507505) B507505
theorem B152491 : Blo 131789 152491 := bstep (se 1 (by rfl) ⟨114368, by rfl⟩ : syracuseStep 152491 = 228737) B228737
theorem B2053043 : Blo 131789 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B250867 : Blo 131789 250867 := bstep (se 1 (by rfl) ⟨188150, by rfl⟩ : syracuseStep 250867 = 376301) B376301
theorem B1004561 : Blo 131789 1004561 := bstep (se 2 (by rfl) ⟨376710, by rfl⟩ : syracuseStep 1004561 = 753421) B753421
theorem B152599 : Blo 131789 152599 := bstep (se 1 (by rfl) ⟨114449, by rfl⟩ : syracuseStep 152599 = 228899) B228899
theorem B513155 : Blo 131789 513155 := bstep (se 1 (by rfl) ⟨384866, by rfl⟩ : syracuseStep 513155 = 769733) B769733
theorem B251095 : Blo 131789 251095 := bstep (se 1 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 251095 = 376643) B376643
theorem B447767 : Blo 131789 447767 := bstep (se 1 (by rfl) ⟨335825, by rfl⟩ : syracuseStep 447767 = 671651) B671651
theorem B382259 : Blo 131789 382259 := bstep (se 1 (by rfl) ⟨286694, by rfl⟩ : syracuseStep 382259 = 573389) B573389
theorem B251201 : Blo 131789 251201 := bstep (se 2 (by rfl) ⟨94200, by rfl⟩ : syracuseStep 251201 = 188401) B188401
theorem B152971 : Blo 131789 152971 := bstep (se 1 (by rfl) ⟨114728, by rfl⟩ : syracuseStep 152971 = 229457) B229457
theorem B251353 : Blo 131789 251353 := bstep (se 2 (by rfl) ⟨94257, by rfl⟩ : syracuseStep 251353 = 188515) B188515
theorem B513611 : Blo 131789 513611 := bstep (se 1 (by rfl) ⟨385208, by rfl⟩ : syracuseStep 513611 = 770417) B770417
theorem B382657 : Blo 131789 382657 := bstep (se 2 (by rfl) ⟨143496, by rfl⟩ : syracuseStep 382657 = 286993) B286993
theorem B513809 : Blo 131789 513809 := bstep (se 2 (by rfl) ⟨192678, by rfl⟩ : syracuseStep 513809 = 385357) B385357
theorem B448307 : Blo 131789 448307 := bstep (se 1 (by rfl) ⟨336230, by rfl⟩ : syracuseStep 448307 = 672461) B672461
theorem B677783 : Blo 131789 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B415667 : Blo 131789 415667 := bstep (se 1 (by rfl) ⟨311750, by rfl⟩ : syracuseStep 415667 = 623501) B623501
theorem B448577 : Blo 131789 448577 := bstep (se 2 (by rfl) ⟨168216, by rfl⟩ : syracuseStep 448577 = 336433) B336433
theorem B1038467 : Blo 131789 1038467 := bstep (se 1 (by rfl) ⟨778850, by rfl⟩ : syracuseStep 1038467 = 1557701) B1557701
theorem B514307 : Blo 131789 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B514583 : Blo 131789 514583 := bstep (se 1 (by rfl) ⟨385937, by rfl⟩ : syracuseStep 514583 = 771875) B771875
theorem B449117 : Blo 131789 449117 := bstep (se 3 (by rfl) ⟨84209, by rfl⟩ : syracuseStep 449117 = 168419) B168419
theorem B1464925 : Blo 131789 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B678617 : Blo 131789 678617 := bstep (se 2 (by rfl) ⟨254481, by rfl⟩ : syracuseStep 678617 = 508963) B508963
theorem B514781 : Blo 131789 514781 := bstep (se 3 (by rfl) ⟨96521, by rfl⟩ : syracuseStep 514781 = 193043) B193043
theorem B252659 : Blo 131789 252659 := bstep (se 1 (by rfl) ⟨189494, by rfl⟩ : syracuseStep 252659 = 378989) B378989
theorem B252811 : Blo 131789 252811 := bstep (se 1 (by rfl) ⟨189608, by rfl⟩ : syracuseStep 252811 = 379217) B379217
theorem B285643 : Blo 131789 285643 := bstep (se 1 (by rfl) ⟨214232, by rfl⟩ : syracuseStep 285643 = 428465) B428465
theorem B253145 : Blo 131789 253145 := bstep (se 2 (by rfl) ⟨94929, by rfl⟩ : syracuseStep 253145 = 189859) B189859
theorem B1039661 : Blo 131789 1039661 := bstep (se 3 (by rfl) ⟨194936, by rfl⟩ : syracuseStep 1039661 = 389873) B389873
theorem B286105 : Blo 131789 286105 := bstep (se 2 (by rfl) ⟨107289, by rfl⟩ : syracuseStep 286105 = 214579) B214579
theorem B2154059 : Blo 131789 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B450251 : Blo 131789 450251 := bstep (se 1 (by rfl) ⟨337688, by rfl⟩ : syracuseStep 450251 = 675377) B675377
theorem B188185 : Blo 131789 188185 := bstep (se 2 (by rfl) ⟨70569, by rfl⟩ : syracuseStep 188185 = 141139) B141139
theorem B2252609 : Blo 131789 2252609 := bstep (se 2 (by rfl) ⟨844728, by rfl⟩ : syracuseStep 2252609 = 1689457) B1689457
theorem B778049 : Blo 131789 778049 := bstep (se 2 (by rfl) ⟨291768, by rfl⟩ : syracuseStep 778049 = 583537) B583537
theorem B253783 : Blo 131789 253783 := bstep (se 1 (by rfl) ⟨190337, by rfl⟩ : syracuseStep 253783 = 380675) B380675
theorem B450521 : Blo 131789 450521 := bstep (se 2 (by rfl) ⟨168945, by rfl⟩ : syracuseStep 450521 = 337891) B337891
theorem B319639 : Blo 131789 319639 := bstep (se 1 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 319639 = 479459) B479459
theorem B385175 : Blo 131789 385175 := bstep (se 1 (by rfl) ⟨288881, by rfl⟩ : syracuseStep 385175 = 577763) B577763
theorem B680237 : Blo 131789 680237 := bstep (se 3 (by rfl) ⟨127544, by rfl⟩ : syracuseStep 680237 = 255089) B255089
theorem B254603 : Blo 131789 254603 := bstep (se 1 (by rfl) ⟨190952, by rfl⟩ : syracuseStep 254603 = 381905) B381905
theorem B451223 : Blo 131789 451223 := bstep (se 1 (by rfl) ⟨338417, by rfl⟩ : syracuseStep 451223 = 676835) B676835
theorem B647831 : Blo 131789 647831 := bstep (se 1 (by rfl) ⟨485873, by rfl⟩ : syracuseStep 647831 = 971747) B971747
theorem B254657 : Blo 131789 254657 := bstep (se 2 (by rfl) ⟨95496, by rfl⟩ : syracuseStep 254657 = 190993) B190993
theorem B287489 : Blo 131789 287489 := bstep (se 2 (by rfl) ⟨107808, by rfl⟩ : syracuseStep 287489 = 215617) B215617
theorem B156439 : Blo 131789 156439 := bstep (se 1 (by rfl) ⟨117329, by rfl⟩ : syracuseStep 156439 = 234659) B234659
theorem B1008449 : Blo 131789 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B189335 : Blo 131789 189335 := bstep (se 1 (by rfl) ⟨142001, by rfl⟩ : syracuseStep 189335 = 284003) B284003
theorem B484375 : Blo 131789 484375 := bstep (se 1 (by rfl) ⟨363281, by rfl⟩ : syracuseStep 484375 = 726563) B726563
theorem B451763 : Blo 131789 451763 := bstep (se 1 (by rfl) ⟨338822, by rfl⟩ : syracuseStep 451763 = 677645) B677645
theorem B189643 : Blo 131789 189643 := bstep (se 1 (by rfl) ⟨142232, by rfl⟩ : syracuseStep 189643 = 284465) B284465
theorem B452033 : Blo 131789 452033 := bstep (se 2 (by rfl) ⟨169512, by rfl⟩ : syracuseStep 452033 = 339025) B339025
theorem B386507 : Blo 131789 386507 := bstep (se 1 (by rfl) ⟨289880, by rfl⟩ : syracuseStep 386507 = 579761) B579761
theorem B222743 : Blo 131789 222743 := bstep (se 1 (by rfl) ⟨167057, by rfl⟩ : syracuseStep 222743 = 334115) B334115
theorem B255575 : Blo 131789 255575 := bstep (se 1 (by rfl) ⟨191681, by rfl⟩ : syracuseStep 255575 = 383363) B383363
theorem B1140317 : Blo 131789 1140317 := bstep (se 3 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 1140317 = 427619) B427619
theorem B222871 : Blo 131789 222871 := bstep (se 1 (by rfl) ⟨167153, by rfl⟩ : syracuseStep 222871 = 334307) B334307
theorem B386839 : Blo 131789 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B452573 : Blo 131789 452573 := bstep (se 3 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 452573 = 169715) B169715
theorem B256115 : Blo 131789 256115 := bstep (se 1 (by rfl) ⟨192086, by rfl⟩ : syracuseStep 256115 = 384173) B384173
theorem B190679 : Blo 131789 190679 := bstep (se 1 (by rfl) ⟨143009, by rfl⟩ : syracuseStep 190679 = 286019) B286019
theorem B223499 : Blo 131789 223499 := bstep (se 1 (by rfl) ⟨167624, by rfl⟩ : syracuseStep 223499 = 335249) B335249
theorem B1141067 : Blo 131789 1141067 := bstep (se 1 (by rfl) ⟨855800, by rfl⟩ : syracuseStep 1141067 = 1711601) B1711601
theorem B1042789 : Blo 131789 1042789 := bstep (se 4 (by rfl) ⟨97761, by rfl⟩ : syracuseStep 1042789 = 195523) B195523
theorem B223627 : Blo 131789 223627 := bstep (se 1 (by rfl) ⟨167720, by rfl⟩ : syracuseStep 223627 = 335441) B335441
theorem B289163 : Blo 131789 289163 := bstep (se 1 (by rfl) ⟨216872, by rfl⟩ : syracuseStep 289163 = 433745) B433745
theorem B190873 : Blo 131789 190873 := bstep (se 2 (by rfl) ⟨71577, by rfl⟩ : syracuseStep 190873 = 143155) B143155
theorem B223769 : Blo 131789 223769 := bstep (se 2 (by rfl) ⟨83913, by rfl⟩ : syracuseStep 223769 = 167827) B167827
theorem B256601 : Blo 131789 256601 := bstep (se 2 (by rfl) ⟨96225, by rfl⟩ : syracuseStep 256601 = 192451) B192451
theorem B223897 : Blo 131789 223897 := bstep (se 2 (by rfl) ⟨83961, by rfl⟩ : syracuseStep 223897 = 167923) B167923
theorem B1010393 : Blo 131789 1010393 := bstep (se 2 (by rfl) ⟨378897, by rfl⟩ : syracuseStep 1010393 = 757795) B757795
theorem B453707 : Blo 131789 453707 := bstep (se 1 (by rfl) ⟨340280, by rfl⟩ : syracuseStep 453707 = 680561) B680561
theorem B224471 : Blo 131789 224471 := bstep (se 1 (by rfl) ⟨168353, by rfl⟩ : syracuseStep 224471 = 336707) B336707
theorem B224599 : Blo 131789 224599 := bstep (se 1 (by rfl) ⟨168449, by rfl⟩ : syracuseStep 224599 = 336899) B336899
theorem B453977 : Blo 131789 453977 := bstep (se 2 (by rfl) ⟨170241, by rfl⟩ : syracuseStep 453977 = 340483) B340483
theorem B159127 : Blo 131789 159127 := bstep (se 1 (by rfl) ⟨119345, by rfl⟩ : syracuseStep 159127 = 238691) B238691
theorem B192331 : Blo 131789 192331 := bstep (se 1 (by rfl) ⟨144248, by rfl⟩ : syracuseStep 192331 = 288497) B288497
theorem B1142707 : Blo 131789 1142707 := bstep (se 1 (by rfl) ⟨857030, by rfl⟩ : syracuseStep 1142707 = 1714061) B1714061
theorem B225227 : Blo 131789 225227 := bstep (se 1 (by rfl) ⟨168920, by rfl⟩ : syracuseStep 225227 = 337841) B337841
theorem B454679 : Blo 131789 454679 := bstep (se 1 (by rfl) ⟨341009, by rfl⟩ : syracuseStep 454679 = 682019) B682019
theorem B225355 : Blo 131789 225355 := bstep (se 1 (by rfl) ⟨169016, by rfl⟩ : syracuseStep 225355 = 338033) B338033
theorem B192601 : Blo 131789 192601 := bstep (se 2 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 192601 = 144451) B144451
theorem B684125 : Blo 131789 684125 := bstep (se 3 (by rfl) ⟨128273, by rfl⟩ : syracuseStep 684125 = 256547) B256547
theorem B225497 : Blo 131789 225497 := bstep (se 2 (by rfl) ⟨84561, by rfl⟩ : syracuseStep 225497 = 169123) B169123
theorem B225625 : Blo 131789 225625 := bstep (se 2 (by rfl) ⟨84609, by rfl⟩ : syracuseStep 225625 = 169219) B169219
theorem B455219 : Blo 131789 455219 := bstep (se 1 (by rfl) ⟨341414, by rfl⟩ : syracuseStep 455219 = 682829) B682829
theorem B291481 : Blo 131789 291481 := bstep (se 2 (by rfl) ⟨109305, by rfl⟩ : syracuseStep 291481 = 218611) B218611
theorem B455489 : Blo 131789 455489 := bstep (se 2 (by rfl) ⟨170808, by rfl⟩ : syracuseStep 455489 = 341617) B341617
theorem B160651 : Blo 131789 160651 := bstep (se 1 (by rfl) ⟨120488, by rfl⟩ : syracuseStep 160651 = 240977) B240977
theorem B226199 : Blo 131789 226199 := bstep (se 1 (by rfl) ⟨169649, by rfl⟩ : syracuseStep 226199 = 339299) B339299
theorem B357313 : Blo 131789 357313 := bstep (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) B267985
theorem B553949 : Blo 131789 553949 := bstep (se 3 (by rfl) ⟨103865, by rfl⟩ : syracuseStep 553949 = 207731) B207731
theorem B226327 : Blo 131789 226327 := bstep (se 1 (by rfl) ⟨169745, by rfl⟩ : syracuseStep 226327 = 339491) B339491
theorem B1700939 : Blo 131789 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B455987 : Blo 131789 455987 := bstep (se 1 (by rfl) ⟨341990, by rfl⟩ : syracuseStep 455987 = 683981) B683981
theorem B456029 : Blo 131789 456029 := bstep (se 3 (by rfl) ⟨85505, by rfl⟩ : syracuseStep 456029 = 171011) B171011
theorem B1930787 : Blo 131789 1930787 := bstep (se 1 (by rfl) ⟨1448090, by rfl⟩ : syracuseStep 1930787 = 2896181) B2896181
theorem B226955 : Blo 131789 226955 := bstep (se 1 (by rfl) ⟨170216, by rfl⟩ : syracuseStep 226955 = 340433) B340433
theorem B325271 : Blo 131789 325271 := bstep (se 1 (by rfl) ⟨243953, by rfl⟩ : syracuseStep 325271 = 487907) B487907
theorem B227083 : Blo 131789 227083 := bstep (se 1 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 227083 = 340625) B340625
theorem B2094913 : Blo 131789 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B227225 : Blo 131789 227225 := bstep (se 2 (by rfl) ⟨85209, by rfl⟩ : syracuseStep 227225 = 170419) B170419
theorem B358361 : Blo 131789 358361 := bstep (se 2 (by rfl) ⟨134385, by rfl⟩ : syracuseStep 358361 = 268771) B268771
theorem B227353 : Blo 131789 227353 := bstep (se 2 (by rfl) ⟨85257, by rfl⟩ : syracuseStep 227353 = 170515) B170515
theorem B1013795 : Blo 131789 1013795 := bstep (se 1 (by rfl) ⟨760346, by rfl⟩ : syracuseStep 1013795 = 1520693) B1520693
theorem B686231 : Blo 131789 686231 := bstep (se 1 (by rfl) ⟨514673, by rfl⟩ : syracuseStep 686231 = 1029347) B1029347
theorem B1964405 : Blo 131789 1964405 := bstep (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) B184163
theorem B457163 : Blo 131789 457163 := bstep (se 1 (by rfl) ⟨342872, by rfl⟩ : syracuseStep 457163 = 685745) B685745
theorem B227927 : Blo 131789 227927 := bstep (se 1 (by rfl) ⟨170945, by rfl⟩ : syracuseStep 227927 = 341891) B341891
theorem B162443 : Blo 131789 162443 := bstep (se 1 (by rfl) ⟨121832, by rfl⟩ : syracuseStep 162443 = 243665) B243665
theorem B1080013 : Blo 131789 1080013 := bstep (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) B405005
theorem B228055 : Blo 131789 228055 := bstep (se 1 (by rfl) ⟨171041, by rfl⟩ : syracuseStep 228055 = 342083) B342083
theorem B457433 : Blo 131789 457433 := bstep (se 2 (by rfl) ⟨171537, by rfl⟩ : syracuseStep 457433 = 343075) B343075
theorem B1506113 : Blo 131789 1506113 := bstep (se 2 (by rfl) ⟨564792, by rfl⟩ : syracuseStep 1506113 = 1129585) B1129585
theorem B1080337 : Blo 131789 1080337 := bstep (se 2 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 1080337 = 810253) B810253
theorem B195799 : Blo 131789 195799 := bstep (se 1 (by rfl) ⟨146849, by rfl⟩ : syracuseStep 195799 = 293699) B293699
theorem B490769 : Blo 131789 490769 := bstep (se 2 (by rfl) ⟨184038, by rfl⟩ : syracuseStep 490769 = 368077) B368077
theorem B228683 : Blo 131789 228683 := bstep (se 1 (by rfl) ⟨171512, by rfl⟩ : syracuseStep 228683 = 343025) B343025
theorem B458135 : Blo 131789 458135 := bstep (se 1 (by rfl) ⟨343601, by rfl⟩ : syracuseStep 458135 = 687203) B687203
theorem B228811 : Blo 131789 228811 := bstep (se 1 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 228811 = 343217) B343217
theorem B228953 : Blo 131789 228953 := bstep (se 2 (by rfl) ⟨85857, by rfl⟩ : syracuseStep 228953 = 171715) B171715
theorem B229081 : Blo 131789 229081 := bstep (se 2 (by rfl) ⟨85905, by rfl⟩ : syracuseStep 229081 = 171811) B171811
theorem B655169 : Blo 131789 655169 := bstep (se 2 (by rfl) ⟨245688, by rfl⟩ : syracuseStep 655169 = 491377) B491377
theorem B360395 : Blo 131789 360395 := bstep (se 1 (by rfl) ⟨270296, by rfl⟩ : syracuseStep 360395 = 540593) B540593
theorem B426185 : Blo 131789 426185 := bstep (se 2 (by rfl) ⟨159819, by rfl⟩ : syracuseStep 426185 = 319639) B319639
theorem B1147081 : Blo 131789 1147081 := bstep (se 2 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 1147081 = 860311) B860311
theorem B2326877 : Blo 131789 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B885127 : Blo 131789 885127 := bstep (se 1 (by rfl) ⟨663845, by rfl⟩ : syracuseStep 885127 = 1327691) B1327691
theorem B131847 : Blo 131789 131847 := bstep (se 1 (by rfl) ⟨98885, by rfl⟩ : syracuseStep 131847 = 197771) B197771
theorem B131855 : Blo 131789 131855 := bstep (se 1 (by rfl) ⟨98891, by rfl⟩ : syracuseStep 131855 = 197783) B197783
theorem B131899 : Blo 131789 131899 := bstep (se 1 (by rfl) ⟨98924, by rfl⟩ : syracuseStep 131899 = 197849) B197849
theorem B131975 : Blo 131789 131975 := bstep (se 1 (by rfl) ⟨98981, by rfl⟩ : syracuseStep 131975 = 197963) B197963
theorem B131983 : Blo 131789 131983 := bstep (se 1 (by rfl) ⟨98987, by rfl⟩ : syracuseStep 131983 = 197975) B197975
theorem B132027 : Blo 131789 132027 := bstep (se 1 (by rfl) ⟨99020, by rfl⟩ : syracuseStep 132027 = 198041) B198041
theorem B132103 : Blo 131789 132103 := bstep (se 1 (by rfl) ⟨99077, by rfl⟩ : syracuseStep 132103 = 198155) B198155
theorem B132111 : Blo 131789 132111 := bstep (se 1 (by rfl) ⟨99083, by rfl⟩ : syracuseStep 132111 = 198167) B198167
theorem B132155 : Blo 131789 132155 := bstep (se 1 (by rfl) ⟨99116, by rfl⟩ : syracuseStep 132155 = 198233) B198233
theorem B197705 : Blo 131789 197705 := bstep (se 2 (by rfl) ⟨74139, by rfl⟩ : syracuseStep 197705 = 148279) B148279
theorem B132231 : Blo 131789 132231 := bstep (se 1 (by rfl) ⟨99173, by rfl⟩ : syracuseStep 132231 = 198347) B198347
theorem B132239 : Blo 131789 132239 := bstep (se 1 (by rfl) ⟨99179, by rfl⟩ : syracuseStep 132239 = 198359) B198359
theorem B197819 : Blo 131789 197819 := bstep (se 1 (by rfl) ⟨148364, by rfl⟩ : syracuseStep 197819 = 296729) B296729
theorem B132283 : Blo 131789 132283 := bstep (se 1 (by rfl) ⟨99212, by rfl⟩ : syracuseStep 132283 = 198425) B198425
theorem B197879 : Blo 131789 197879 := bstep (se 1 (by rfl) ⟨148409, by rfl⟩ : syracuseStep 197879 = 296819) B296819
theorem B132359 : Blo 131789 132359 := bstep (se 1 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 132359 = 198539) B198539
theorem B197903 : Blo 131789 197903 := bstep (se 1 (by rfl) ⟨148427, by rfl⟩ : syracuseStep 197903 = 296855) B296855
theorem B132367 : Blo 131789 132367 := bstep (se 1 (by rfl) ⟨99275, by rfl⟩ : syracuseStep 132367 = 198551) B198551
theorem B197945 : Blo 131789 197945 := bstep (se 2 (by rfl) ⟨74229, by rfl⟩ : syracuseStep 197945 = 148459) B148459
theorem B132411 : Blo 131789 132411 := bstep (se 1 (by rfl) ⟨99308, by rfl⟩ : syracuseStep 132411 = 198617) B198617
theorem B198023 : Blo 131789 198023 := bstep (se 1 (by rfl) ⟨148517, by rfl⟩ : syracuseStep 198023 = 297035) B297035
theorem B132487 : Blo 131789 132487 := bstep (se 1 (by rfl) ⟨99365, by rfl⟩ : syracuseStep 132487 = 198731) B198731
theorem B132495 : Blo 131789 132495 := bstep (se 1 (by rfl) ⟨99371, by rfl⟩ : syracuseStep 132495 = 198743) B198743
theorem B198059 : Blo 131789 198059 := bstep (se 1 (by rfl) ⟨148544, by rfl⟩ : syracuseStep 198059 = 297089) B297089
theorem B132539 : Blo 131789 132539 := bstep (se 1 (by rfl) ⟨99404, by rfl⟩ : syracuseStep 132539 = 198809) B198809
theorem B198089 : Blo 131789 198089 := bstep (se 2 (by rfl) ⟨74283, by rfl⟩ : syracuseStep 198089 = 148567) B148567
theorem B755153 : Blo 131789 755153 := bstep (se 2 (by rfl) ⟨283182, by rfl⟩ : syracuseStep 755153 = 566365) B566365
theorem B132615 : Blo 131789 132615 := bstep (se 1 (by rfl) ⟨99461, by rfl⟩ : syracuseStep 132615 = 198923) B198923
theorem B132623 : Blo 131789 132623 := bstep (se 1 (by rfl) ⟨99467, by rfl⟩ : syracuseStep 132623 = 198935) B198935
theorem B198203 : Blo 131789 198203 := bstep (se 1 (by rfl) ⟨148652, by rfl⟩ : syracuseStep 198203 = 297305) B297305
theorem B132667 : Blo 131789 132667 := bstep (se 1 (by rfl) ⟨99500, by rfl⟩ : syracuseStep 132667 = 199001) B199001
theorem B394813 : Blo 131789 394813 := bstep (se 3 (by rfl) ⟨74027, by rfl⟩ : syracuseStep 394813 = 148055) B148055
theorem B7603789 : Blo 131789 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B296567 : Blo 131789 296567 := bstep (se 1 (by rfl) ⟨222425, by rfl⟩ : syracuseStep 296567 = 444851) B444851
theorem B198263 : Blo 131789 198263 := bstep (se 1 (by rfl) ⟨148697, by rfl⟩ : syracuseStep 198263 = 297395) B297395
theorem B132743 : Blo 131789 132743 := bstep (se 1 (by rfl) ⟨99557, by rfl⟩ : syracuseStep 132743 = 199115) B199115
theorem B198287 : Blo 131789 198287 := bstep (se 1 (by rfl) ⟨148715, by rfl⟩ : syracuseStep 198287 = 297431) B297431
theorem B132751 : Blo 131789 132751 := bstep (se 1 (by rfl) ⟨99563, by rfl⟩ : syracuseStep 132751 = 199127) B199127
theorem B198329 : Blo 131789 198329 := bstep (se 2 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 198329 = 148747) B148747
theorem B132795 : Blo 131789 132795 := bstep (se 1 (by rfl) ⟨99596, by rfl⟩ : syracuseStep 132795 = 199193) B199193
theorem B198407 : Blo 131789 198407 := bstep (se 1 (by rfl) ⟨148805, by rfl⟩ : syracuseStep 198407 = 297611) B297611
theorem B132871 : Blo 131789 132871 := bstep (se 1 (by rfl) ⟨99653, by rfl⟩ : syracuseStep 132871 = 199307) B199307
theorem B132879 : Blo 131789 132879 := bstep (se 1 (by rfl) ⟨99659, by rfl⟩ : syracuseStep 132879 = 199319) B199319
theorem B296747 : Blo 131789 296747 := bstep (se 1 (by rfl) ⟨222560, by rfl⟩ : syracuseStep 296747 = 445121) B445121
theorem B198443 : Blo 131789 198443 := bstep (se 1 (by rfl) ⟨148832, by rfl⟩ : syracuseStep 198443 = 297665) B297665
theorem B132923 : Blo 131789 132923 := bstep (se 1 (by rfl) ⟨99692, by rfl⟩ : syracuseStep 132923 = 199385) B199385
theorem B198473 : Blo 131789 198473 := bstep (se 2 (by rfl) ⟨74427, by rfl⟩ : syracuseStep 198473 = 148855) B148855
theorem B132999 : Blo 131789 132999 := bstep (se 1 (by rfl) ⟨99749, by rfl⟩ : syracuseStep 132999 = 199499) B199499
theorem B133007 : Blo 131789 133007 := bstep (se 1 (by rfl) ⟨99755, by rfl⟩ : syracuseStep 133007 = 199511) B199511
theorem B198587 : Blo 131789 198587 := bstep (se 1 (by rfl) ⟨148940, by rfl⟩ : syracuseStep 198587 = 297881) B297881
theorem B133051 : Blo 131789 133051 := bstep (se 1 (by rfl) ⟨99788, by rfl⟩ : syracuseStep 133051 = 199577) B199577
theorem B198647 : Blo 131789 198647 := bstep (se 1 (by rfl) ⟨148985, by rfl⟩ : syracuseStep 198647 = 297971) B297971
theorem B133127 : Blo 131789 133127 := bstep (se 1 (by rfl) ⟨99845, by rfl⟩ : syracuseStep 133127 = 199691) B199691
theorem B198671 : Blo 131789 198671 := bstep (se 1 (by rfl) ⟨149003, by rfl⟩ : syracuseStep 198671 = 298007) B298007
theorem B133135 : Blo 131789 133135 := bstep (se 1 (by rfl) ⟨99851, by rfl⟩ : syracuseStep 133135 = 199703) B199703
theorem B198713 : Blo 131789 198713 := bstep (se 2 (by rfl) ⟨74517, by rfl⟩ : syracuseStep 198713 = 149035) B149035
theorem B133179 : Blo 131789 133179 := bstep (se 1 (by rfl) ⟨99884, by rfl⟩ : syracuseStep 133179 = 199769) B199769
theorem B198791 : Blo 131789 198791 := bstep (se 1 (by rfl) ⟨149093, by rfl⟩ : syracuseStep 198791 = 298187) B298187
theorem B133255 : Blo 131789 133255 := bstep (se 1 (by rfl) ⟨99941, by rfl⟩ : syracuseStep 133255 = 199883) B199883
theorem B133263 : Blo 131789 133263 := bstep (se 1 (by rfl) ⟨99947, by rfl⟩ : syracuseStep 133263 = 199895) B199895
theorem B297107 : Blo 131789 297107 := bstep (se 1 (by rfl) ⟨222830, by rfl⟩ : syracuseStep 297107 = 445661) B445661
theorem B198827 : Blo 131789 198827 := bstep (se 1 (by rfl) ⟨149120, by rfl⟩ : syracuseStep 198827 = 298241) B298241
theorem B133307 : Blo 131789 133307 := bstep (se 1 (by rfl) ⟨99980, by rfl⟩ : syracuseStep 133307 = 199961) B199961
theorem B297161 : Blo 131789 297161 := bstep (se 2 (by rfl) ⟨111435, by rfl⟩ : syracuseStep 297161 = 222871) B222871
theorem B198857 : Blo 131789 198857 := bstep (se 2 (by rfl) ⟨74571, by rfl⟩ : syracuseStep 198857 = 149143) B149143
theorem B657665 : Blo 131789 657665 := bstep (se 2 (by rfl) ⟨246624, by rfl⟩ : syracuseStep 657665 = 493249) B493249
theorem B133383 : Blo 131789 133383 := bstep (se 1 (by rfl) ⟨100037, by rfl⟩ : syracuseStep 133383 = 200075) B200075
theorem B133391 : Blo 131789 133391 := bstep (se 1 (by rfl) ⟨100043, by rfl⟩ : syracuseStep 133391 = 200087) B200087
theorem B198971 : Blo 131789 198971 := bstep (se 1 (by rfl) ⟨149228, by rfl⟩ : syracuseStep 198971 = 298457) B298457
theorem B133435 : Blo 131789 133435 := bstep (se 1 (by rfl) ⟨100076, by rfl⟩ : syracuseStep 133435 = 200153) B200153
theorem B199031 : Blo 131789 199031 := bstep (se 1 (by rfl) ⟨149273, by rfl⟩ : syracuseStep 199031 = 298547) B298547
theorem B133511 : Blo 131789 133511 := bstep (se 1 (by rfl) ⟨100133, by rfl⟩ : syracuseStep 133511 = 200267) B200267
theorem B199055 : Blo 131789 199055 := bstep (se 1 (by rfl) ⟨149291, by rfl⟩ : syracuseStep 199055 = 298583) B298583
theorem B133519 : Blo 131789 133519 := bstep (se 1 (by rfl) ⟨100139, by rfl⟩ : syracuseStep 133519 = 200279) B200279
theorem B199097 : Blo 131789 199097 := bstep (se 2 (by rfl) ⟨74661, by rfl⟩ : syracuseStep 199097 = 149323) B149323
theorem B133563 : Blo 131789 133563 := bstep (se 1 (by rfl) ⟨100172, by rfl⟩ : syracuseStep 133563 = 200345) B200345
theorem B199175 : Blo 131789 199175 := bstep (se 1 (by rfl) ⟨149381, by rfl⟩ : syracuseStep 199175 = 298763) B298763
theorem B133639 : Blo 131789 133639 := bstep (se 1 (by rfl) ⟨100229, by rfl⟩ : syracuseStep 133639 = 200459) B200459
theorem B723467 : Blo 131789 723467 := bstep (se 1 (by rfl) ⟨542600, by rfl⟩ : syracuseStep 723467 = 1085201) B1085201
theorem B133647 : Blo 131789 133647 := bstep (se 1 (by rfl) ⟨100235, by rfl⟩ : syracuseStep 133647 = 200471) B200471
theorem B199211 : Blo 131789 199211 := bstep (se 1 (by rfl) ⟨149408, by rfl⟩ : syracuseStep 199211 = 298817) B298817
theorem B231995 : Blo 131789 231995 := bstep (se 1 (by rfl) ⟨173996, by rfl⟩ : syracuseStep 231995 = 347993) B347993
theorem B133691 : Blo 131789 133691 := bstep (se 1 (by rfl) ⟨100268, by rfl⟩ : syracuseStep 133691 = 200537) B200537
theorem B199241 : Blo 131789 199241 := bstep (se 2 (by rfl) ⟨74715, by rfl⟩ : syracuseStep 199241 = 149431) B149431
theorem B133767 : Blo 131789 133767 := bstep (se 1 (by rfl) ⟨100325, by rfl⟩ : syracuseStep 133767 = 200651) B200651
theorem B297607 : Blo 131789 297607 := bstep (se 1 (by rfl) ⟨223205, by rfl⟩ : syracuseStep 297607 = 446411) B446411
theorem B133775 : Blo 131789 133775 := bstep (se 1 (by rfl) ⟨100331, by rfl⟩ : syracuseStep 133775 = 200663) B200663
theorem B199355 : Blo 131789 199355 := bstep (se 1 (by rfl) ⟨149516, by rfl⟩ : syracuseStep 199355 = 299033) B299033
theorem B133819 : Blo 131789 133819 := bstep (se 1 (by rfl) ⟨100364, by rfl⟩ : syracuseStep 133819 = 200729) B200729
theorem B199415 : Blo 131789 199415 := bstep (se 1 (by rfl) ⟨149561, by rfl⟩ : syracuseStep 199415 = 299123) B299123
theorem B6195973 : Blo 131789 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B133895 : Blo 131789 133895 := bstep (se 1 (by rfl) ⟨100421, by rfl⟩ : syracuseStep 133895 = 200843) B200843
theorem B1018639 : Blo 131789 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B199439 : Blo 131789 199439 := bstep (se 1 (by rfl) ⟨149579, by rfl⟩ : syracuseStep 199439 = 299159) B299159
theorem B133903 : Blo 131789 133903 := bstep (se 1 (by rfl) ⟨100427, by rfl⟩ : syracuseStep 133903 = 200855) B200855
theorem B1936163 : Blo 131789 1936163 := bstep (se 1 (by rfl) ⟨1452122, by rfl⟩ : syracuseStep 1936163 = 2904245) B2904245
theorem B199481 : Blo 131789 199481 := bstep (se 2 (by rfl) ⟨74805, by rfl⟩ : syracuseStep 199481 = 149611) B149611
theorem B133947 : Blo 131789 133947 := bstep (se 1 (by rfl) ⟨100460, by rfl⟩ : syracuseStep 133947 = 200921) B200921
theorem B985945 : Blo 131789 985945 := bstep (se 2 (by rfl) ⟨369729, by rfl⟩ : syracuseStep 985945 = 739459) B739459
theorem B12389219 : Blo 131789 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B428915 : Blo 131789 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B297863 : Blo 131789 297863 := bstep (se 1 (by rfl) ⟨223397, by rfl⟩ : syracuseStep 297863 = 446795) B446795
theorem B199559 : Blo 131789 199559 := bstep (se 1 (by rfl) ⟨149669, by rfl⟩ : syracuseStep 199559 = 299339) B299339
theorem B134023 : Blo 131789 134023 := bstep (se 1 (by rfl) ⟨100517, by rfl⟩ : syracuseStep 134023 = 201035) B201035
theorem B166799 : Blo 131789 166799 := bstep (se 1 (by rfl) ⟨125099, by rfl⟩ : syracuseStep 166799 = 250199) B250199
theorem B134031 : Blo 131789 134031 := bstep (se 1 (by rfl) ⟨100523, by rfl⟩ : syracuseStep 134031 = 201047) B201047
theorem B199595 : Blo 131789 199595 := bstep (se 1 (by rfl) ⟨149696, by rfl⟩ : syracuseStep 199595 = 299393) B299393
theorem B134075 : Blo 131789 134075 := bstep (se 1 (by rfl) ⟨100556, by rfl⟩ : syracuseStep 134075 = 201113) B201113
theorem B199625 : Blo 131789 199625 := bstep (se 2 (by rfl) ⟨74859, by rfl⟩ : syracuseStep 199625 = 149719) B149719
theorem B134151 : Blo 131789 134151 := bstep (se 1 (by rfl) ⟨100613, by rfl⟩ : syracuseStep 134151 = 201227) B201227
theorem B134159 : Blo 131789 134159 := bstep (se 1 (by rfl) ⟨100619, by rfl⟩ : syracuseStep 134159 = 201239) B201239
theorem B298043 : Blo 131789 298043 := bstep (se 1 (by rfl) ⟨223532, by rfl⟩ : syracuseStep 298043 = 447065) B447065
theorem B199739 : Blo 131789 199739 := bstep (se 1 (by rfl) ⟨149804, by rfl⟩ : syracuseStep 199739 = 299609) B299609
theorem B134203 : Blo 131789 134203 := bstep (se 1 (by rfl) ⟨100652, by rfl⟩ : syracuseStep 134203 = 201305) B201305
theorem B1510487 : Blo 131789 1510487 := bstep (se 1 (by rfl) ⟨1132865, by rfl⟩ : syracuseStep 1510487 = 2265731) B2265731
theorem B199799 : Blo 131789 199799 := bstep (se 1 (by rfl) ⟨149849, by rfl⟩ : syracuseStep 199799 = 299699) B299699
theorem B134279 : Blo 131789 134279 := bstep (se 1 (by rfl) ⟨100709, by rfl⟩ : syracuseStep 134279 = 201419) B201419
theorem B199823 : Blo 131789 199823 := bstep (se 1 (by rfl) ⟨149867, by rfl⟩ : syracuseStep 199823 = 299735) B299735
theorem B134287 : Blo 131789 134287 := bstep (se 1 (by rfl) ⟨100715, by rfl⟩ : syracuseStep 134287 = 201431) B201431
theorem B298169 : Blo 131789 298169 := bstep (se 2 (by rfl) ⟨111813, by rfl⟩ : syracuseStep 298169 = 223627) B223627
theorem B199865 : Blo 131789 199865 := bstep (se 2 (by rfl) ⟨74949, by rfl⟩ : syracuseStep 199865 = 149899) B149899
theorem B134331 : Blo 131789 134331 := bstep (se 1 (by rfl) ⟨100748, by rfl⟩ : syracuseStep 134331 = 201497) B201497
theorem B199943 : Blo 131789 199943 := bstep (se 1 (by rfl) ⟨149957, by rfl⟩ : syracuseStep 199943 = 299915) B299915
theorem B134407 : Blo 131789 134407 := bstep (se 1 (by rfl) ⟨100805, by rfl⟩ : syracuseStep 134407 = 201611) B201611
theorem B134415 : Blo 131789 134415 := bstep (se 1 (by rfl) ⟨100811, by rfl⟩ : syracuseStep 134415 = 201623) B201623
theorem B363809 : Blo 131789 363809 := bstep (se 2 (by rfl) ⟨136428, by rfl⟩ : syracuseStep 363809 = 272857) B272857
theorem B199979 : Blo 131789 199979 := bstep (se 1 (by rfl) ⟨149984, by rfl⟩ : syracuseStep 199979 = 299969) B299969
theorem B134459 : Blo 131789 134459 := bstep (se 1 (by rfl) ⟨100844, by rfl⟩ : syracuseStep 134459 = 201689) B201689
theorem B200009 : Blo 131789 200009 := bstep (se 2 (by rfl) ⟨75003, by rfl⟩ : syracuseStep 200009 = 150007) B150007
theorem B134535 : Blo 131789 134535 := bstep (se 1 (by rfl) ⟨100901, by rfl⟩ : syracuseStep 134535 = 201803) B201803
theorem B134543 : Blo 131789 134543 := bstep (se 1 (by rfl) ⟨100907, by rfl⟩ : syracuseStep 134543 = 201815) B201815
theorem B200123 : Blo 131789 200123 := bstep (se 1 (by rfl) ⟨150092, by rfl⟩ : syracuseStep 200123 = 300185) B300185
theorem B134587 : Blo 131789 134587 := bstep (se 1 (by rfl) ⟨100940, by rfl⟩ : syracuseStep 134587 = 201881) B201881
theorem B1215965 : Blo 131789 1215965 := bstep (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) B455987
theorem B200183 : Blo 131789 200183 := bstep (se 1 (by rfl) ⟨150137, by rfl⟩ : syracuseStep 200183 = 300275) B300275
theorem B134663 : Blo 131789 134663 := bstep (se 1 (by rfl) ⟨100997, by rfl⟩ : syracuseStep 134663 = 201995) B201995
theorem B658955 : Blo 131789 658955 := bstep (se 1 (by rfl) ⟨494216, by rfl⟩ : syracuseStep 658955 = 988433) B988433
theorem B298511 : Blo 131789 298511 := bstep (se 1 (by rfl) ⟨223883, by rfl⟩ : syracuseStep 298511 = 447767) B447767
theorem B200207 : Blo 131789 200207 := bstep (se 1 (by rfl) ⟨150155, by rfl⟩ : syracuseStep 200207 = 300311) B300311
theorem B134671 : Blo 131789 134671 := bstep (se 1 (by rfl) ⟨101003, by rfl⟩ : syracuseStep 134671 = 202007) B202007
theorem B298529 : Blo 131789 298529 := bstep (se 2 (by rfl) ⟨111948, by rfl⟩ : syracuseStep 298529 = 223897) B223897
theorem B200249 : Blo 131789 200249 := bstep (se 2 (by rfl) ⟨75093, by rfl⟩ : syracuseStep 200249 = 150187) B150187
theorem B134715 : Blo 131789 134715 := bstep (se 1 (by rfl) ⟨101036, by rfl⟩ : syracuseStep 134715 = 202073) B202073
theorem B200327 : Blo 131789 200327 := bstep (se 1 (by rfl) ⟨150245, by rfl⟩ : syracuseStep 200327 = 300491) B300491
theorem B134791 : Blo 131789 134791 := bstep (se 1 (by rfl) ⟨101093, by rfl⟩ : syracuseStep 134791 = 202187) B202187
theorem B134799 : Blo 131789 134799 := bstep (se 1 (by rfl) ⟨101099, by rfl⟩ : syracuseStep 134799 = 202199) B202199
theorem B200363 : Blo 131789 200363 := bstep (se 1 (by rfl) ⟨150272, by rfl⟩ : syracuseStep 200363 = 300545) B300545
theorem B134843 : Blo 131789 134843 := bstep (se 1 (by rfl) ⟨101132, by rfl⟩ : syracuseStep 134843 = 202265) B202265
theorem B200393 : Blo 131789 200393 := bstep (se 2 (by rfl) ⟨75147, by rfl⟩ : syracuseStep 200393 = 150295) B150295
theorem B134919 : Blo 131789 134919 := bstep (se 1 (by rfl) ⟨101189, by rfl⟩ : syracuseStep 134919 = 202379) B202379
theorem B134927 : Blo 131789 134927 := bstep (se 1 (by rfl) ⟨101195, by rfl⟩ : syracuseStep 134927 = 202391) B202391
theorem B200507 : Blo 131789 200507 := bstep (se 1 (by rfl) ⟨150380, by rfl⟩ : syracuseStep 200507 = 300761) B300761
theorem B134971 : Blo 131789 134971 := bstep (se 1 (by rfl) ⟨101228, by rfl⟩ : syracuseStep 134971 = 202457) B202457
theorem B298871 : Blo 131789 298871 := bstep (se 1 (by rfl) ⟨224153, by rfl⟩ : syracuseStep 298871 = 448307) B448307
theorem B200567 : Blo 131789 200567 := bstep (se 1 (by rfl) ⟨150425, by rfl⟩ : syracuseStep 200567 = 300851) B300851
theorem B135047 : Blo 131789 135047 := bstep (se 1 (by rfl) ⟨101285, by rfl⟩ : syracuseStep 135047 = 202571) B202571
theorem B200591 : Blo 131789 200591 := bstep (se 1 (by rfl) ⟨150443, by rfl⟩ : syracuseStep 200591 = 300887) B300887
theorem B135055 : Blo 131789 135055 := bstep (se 1 (by rfl) ⟨101291, by rfl⟩ : syracuseStep 135055 = 202583) B202583
theorem B200633 : Blo 131789 200633 := bstep (se 2 (by rfl) ⟨75237, by rfl⟩ : syracuseStep 200633 = 150475) B150475
theorem B135099 : Blo 131789 135099 := bstep (se 1 (by rfl) ⟨101324, by rfl⟩ : syracuseStep 135099 = 202649) B202649
theorem B200711 : Blo 131789 200711 := bstep (se 1 (by rfl) ⟨150533, by rfl⟩ : syracuseStep 200711 = 301067) B301067
theorem B135175 : Blo 131789 135175 := bstep (se 1 (by rfl) ⟨101381, by rfl⟩ : syracuseStep 135175 = 202763) B202763
theorem B135183 : Blo 131789 135183 := bstep (se 1 (by rfl) ⟨101387, by rfl⟩ : syracuseStep 135183 = 202775) B202775
theorem B299051 : Blo 131789 299051 := bstep (se 1 (by rfl) ⟨224288, by rfl⟩ : syracuseStep 299051 = 448577) B448577
theorem B200747 : Blo 131789 200747 := bstep (se 1 (by rfl) ⟨150560, by rfl⟩ : syracuseStep 200747 = 301121) B301121
theorem B135227 : Blo 131789 135227 := bstep (se 1 (by rfl) ⟨101420, by rfl⟩ : syracuseStep 135227 = 202841) B202841
theorem B200777 : Blo 131789 200777 := bstep (se 2 (by rfl) ⟨75291, by rfl⟩ : syracuseStep 200777 = 150583) B150583
theorem B692311 : Blo 131789 692311 := bstep (se 1 (by rfl) ⟨519233, by rfl⟩ : syracuseStep 692311 = 1038467) B1038467
theorem B135303 : Blo 131789 135303 := bstep (se 1 (by rfl) ⟨101477, by rfl⟩ : syracuseStep 135303 = 202955) B202955
theorem B135311 : Blo 131789 135311 := bstep (se 1 (by rfl) ⟨101483, by rfl⟩ : syracuseStep 135311 = 202967) B202967
theorem B200891 : Blo 131789 200891 := bstep (se 1 (by rfl) ⟨150668, by rfl⟩ : syracuseStep 200891 = 301337) B301337
theorem B135355 : Blo 131789 135355 := bstep (se 1 (by rfl) ⟨101516, by rfl⟩ : syracuseStep 135355 = 203033) B203033
theorem B200951 : Blo 131789 200951 := bstep (se 1 (by rfl) ⟨150713, by rfl⟩ : syracuseStep 200951 = 301427) B301427
theorem B135431 : Blo 131789 135431 := bstep (se 1 (by rfl) ⟨101573, by rfl⟩ : syracuseStep 135431 = 203147) B203147
theorem B200975 : Blo 131789 200975 := bstep (se 1 (by rfl) ⟨150731, by rfl⟩ : syracuseStep 200975 = 301463) B301463
theorem B135439 : Blo 131789 135439 := bstep (se 1 (by rfl) ⟨101579, by rfl⟩ : syracuseStep 135439 = 203159) B203159
theorem B201017 : Blo 131789 201017 := bstep (se 2 (by rfl) ⟨75381, by rfl⟩ : syracuseStep 201017 = 150763) B150763
theorem B135483 : Blo 131789 135483 := bstep (se 1 (by rfl) ⟨101612, by rfl⟩ : syracuseStep 135483 = 203225) B203225
theorem B201095 : Blo 131789 201095 := bstep (se 1 (by rfl) ⟨150821, by rfl⟩ : syracuseStep 201095 = 301643) B301643
theorem B135559 : Blo 131789 135559 := bstep (se 1 (by rfl) ⟨101669, by rfl⟩ : syracuseStep 135559 = 203339) B203339
theorem B135567 : Blo 131789 135567 := bstep (se 1 (by rfl) ⟨101675, by rfl⟩ : syracuseStep 135567 = 203351) B203351
theorem B299411 : Blo 131789 299411 := bstep (se 1 (by rfl) ⟨224558, by rfl⟩ : syracuseStep 299411 = 449117) B449117
theorem B201131 : Blo 131789 201131 := bstep (se 1 (by rfl) ⟨150848, by rfl⟩ : syracuseStep 201131 = 301697) B301697
theorem B135611 : Blo 131789 135611 := bstep (se 1 (by rfl) ⟨101708, by rfl⟩ : syracuseStep 135611 = 203417) B203417
theorem B299465 : Blo 131789 299465 := bstep (se 2 (by rfl) ⟨112299, by rfl⟩ : syracuseStep 299465 = 224599) B224599
theorem B201161 : Blo 131789 201161 := bstep (se 2 (by rfl) ⟨75435, by rfl⟩ : syracuseStep 201161 = 150871) B150871
theorem B135687 : Blo 131789 135687 := bstep (se 1 (by rfl) ⟨101765, by rfl⟩ : syracuseStep 135687 = 203531) B203531
theorem B135695 : Blo 131789 135695 := bstep (se 1 (by rfl) ⟨101771, by rfl⟩ : syracuseStep 135695 = 203543) B203543
theorem B201275 : Blo 131789 201275 := bstep (se 1 (by rfl) ⟨150956, by rfl⟩ : syracuseStep 201275 = 301913) B301913
theorem B135739 : Blo 131789 135739 := bstep (se 1 (by rfl) ⟨101804, by rfl⟩ : syracuseStep 135739 = 203609) B203609
theorem B201335 : Blo 131789 201335 := bstep (se 1 (by rfl) ⟨151001, by rfl⟩ : syracuseStep 201335 = 302003) B302003
theorem B201359 : Blo 131789 201359 := bstep (se 1 (by rfl) ⟨151019, by rfl⟩ : syracuseStep 201359 = 302039) B302039
theorem B201401 : Blo 131789 201401 := bstep (se 2 (by rfl) ⟨75525, by rfl⟩ : syracuseStep 201401 = 151051) B151051
theorem B201479 : Blo 131789 201479 := bstep (se 1 (by rfl) ⟨151109, by rfl⟩ : syracuseStep 201479 = 302219) B302219
theorem B201515 : Blo 131789 201515 := bstep (se 1 (by rfl) ⟨151136, by rfl⟩ : syracuseStep 201515 = 302273) B302273
theorem B201545 : Blo 131789 201545 := bstep (se 2 (by rfl) ⟨75579, by rfl⟩ : syracuseStep 201545 = 151159) B151159
theorem B693107 : Blo 131789 693107 := bstep (se 1 (by rfl) ⟨519830, by rfl⟩ : syracuseStep 693107 = 1039661) B1039661
theorem B201659 : Blo 131789 201659 := bstep (se 1 (by rfl) ⟨151244, by rfl⟩ : syracuseStep 201659 = 302489) B302489
theorem B660433 : Blo 131789 660433 := bstep (se 2 (by rfl) ⟨247662, by rfl⟩ : syracuseStep 660433 = 495325) B495325
theorem B201719 : Blo 131789 201719 := bstep (se 1 (by rfl) ⟨151289, by rfl⟩ : syracuseStep 201719 = 302579) B302579
theorem B201743 : Blo 131789 201743 := bstep (se 1 (by rfl) ⟨151307, by rfl⟩ : syracuseStep 201743 = 302615) B302615
theorem B201785 : Blo 131789 201785 := bstep (se 2 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 201785 = 151339) B151339
theorem B300167 : Blo 131789 300167 := bstep (se 1 (by rfl) ⟨225125, by rfl⟩ : syracuseStep 300167 = 450251) B450251
theorem B201863 : Blo 131789 201863 := bstep (se 1 (by rfl) ⟨151397, by rfl⟩ : syracuseStep 201863 = 302795) B302795
theorem B201899 : Blo 131789 201899 := bstep (se 1 (by rfl) ⟨151424, by rfl⟩ : syracuseStep 201899 = 302849) B302849
theorem B201929 : Blo 131789 201929 := bstep (se 2 (by rfl) ⟨75723, by rfl⟩ : syracuseStep 201929 = 151447) B151447
theorem B300347 : Blo 131789 300347 := bstep (se 1 (by rfl) ⟨225260, by rfl⟩ : syracuseStep 300347 = 450521) B450521
theorem B202043 : Blo 131789 202043 := bstep (se 1 (by rfl) ⟨151532, by rfl⟩ : syracuseStep 202043 = 303065) B303065
theorem B202103 : Blo 131789 202103 := bstep (se 1 (by rfl) ⟨151577, by rfl⟩ : syracuseStep 202103 = 303155) B303155
theorem B202127 : Blo 131789 202127 := bstep (se 1 (by rfl) ⟨151595, by rfl⟩ : syracuseStep 202127 = 303191) B303191
theorem B267667 : Blo 131789 267667 := bstep (se 1 (by rfl) ⟨200750, by rfl⟩ : syracuseStep 267667 = 401501) B401501
theorem B3478963 : Blo 131789 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B300473 : Blo 131789 300473 := bstep (se 2 (by rfl) ⟨112677, by rfl⟩ : syracuseStep 300473 = 225355) B225355
theorem B202169 : Blo 131789 202169 := bstep (se 2 (by rfl) ⟨75813, by rfl⟩ : syracuseStep 202169 = 151627) B151627
theorem B202247 : Blo 131789 202247 := bstep (se 1 (by rfl) ⟨151685, by rfl⟩ : syracuseStep 202247 = 303371) B303371
theorem B202283 : Blo 131789 202283 := bstep (se 1 (by rfl) ⟨151712, by rfl⟩ : syracuseStep 202283 = 303425) B303425
theorem B202313 : Blo 131789 202313 := bstep (se 2 (by rfl) ⟨75867, by rfl⟩ : syracuseStep 202313 = 151735) B151735
theorem B136847 : Blo 131789 136847 := bstep (se 1 (by rfl) ⟨102635, by rfl⟩ : syracuseStep 136847 = 205271) B205271
theorem B202427 : Blo 131789 202427 := bstep (se 1 (by rfl) ⟨151820, by rfl⟩ : syracuseStep 202427 = 303641) B303641
theorem B202487 : Blo 131789 202487 := bstep (se 1 (by rfl) ⟨151865, by rfl⟩ : syracuseStep 202487 = 303731) B303731
theorem B300815 : Blo 131789 300815 := bstep (se 1 (by rfl) ⟨225611, by rfl⟩ : syracuseStep 300815 = 451223) B451223
theorem B431887 : Blo 131789 431887 := bstep (se 1 (by rfl) ⟨323915, by rfl⟩ : syracuseStep 431887 = 647831) B647831
theorem B202511 : Blo 131789 202511 := bstep (se 1 (by rfl) ⟨151883, by rfl⟩ : syracuseStep 202511 = 303767) B303767
theorem B300833 : Blo 131789 300833 := bstep (se 2 (by rfl) ⟨112812, by rfl⟩ : syracuseStep 300833 = 225625) B225625
theorem B169771 : Blo 131789 169771 := bstep (se 1 (by rfl) ⟨127328, by rfl⟩ : syracuseStep 169771 = 254657) B254657
theorem B202553 : Blo 131789 202553 := bstep (se 2 (by rfl) ⟨75957, by rfl⟩ : syracuseStep 202553 = 151915) B151915
theorem B2561867 : Blo 131789 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B202631 : Blo 131789 202631 := bstep (se 1 (by rfl) ⟨151973, by rfl⟩ : syracuseStep 202631 = 303947) B303947
theorem B202667 : Blo 131789 202667 := bstep (se 1 (by rfl) ⟨152000, by rfl⟩ : syracuseStep 202667 = 304001) B304001
theorem B202697 : Blo 131789 202697 := bstep (se 2 (by rfl) ⟨76011, by rfl⟩ : syracuseStep 202697 = 152023) B152023
theorem B202811 : Blo 131789 202811 := bstep (se 1 (by rfl) ⟨152108, by rfl⟩ : syracuseStep 202811 = 304217) B304217
theorem B301175 : Blo 131789 301175 := bstep (se 1 (by rfl) ⟨225881, by rfl⟩ : syracuseStep 301175 = 451763) B451763
theorem B202871 : Blo 131789 202871 := bstep (se 1 (by rfl) ⟨152153, by rfl⟩ : syracuseStep 202871 = 304307) B304307
theorem B202895 : Blo 131789 202895 := bstep (se 1 (by rfl) ⟨152171, by rfl⟩ : syracuseStep 202895 = 304343) B304343
theorem B202937 : Blo 131789 202937 := bstep (se 2 (by rfl) ⟨76101, by rfl⟩ : syracuseStep 202937 = 152203) B152203
theorem B203015 : Blo 131789 203015 := bstep (se 1 (by rfl) ⟨152261, by rfl⟩ : syracuseStep 203015 = 304523) B304523
theorem B301355 : Blo 131789 301355 := bstep (se 1 (by rfl) ⟨226016, by rfl⟩ : syracuseStep 301355 = 452033) B452033
theorem B203051 : Blo 131789 203051 := bstep (se 1 (by rfl) ⟨152288, by rfl⟩ : syracuseStep 203051 = 304577) B304577
theorem B203081 : Blo 131789 203081 := bstep (se 2 (by rfl) ⟨76155, by rfl⟩ : syracuseStep 203081 = 152311) B152311
theorem B760211 : Blo 131789 760211 := bstep (se 1 (by rfl) ⟨570158, by rfl⟩ : syracuseStep 760211 = 1140317) B1140317
theorem B367001 : Blo 131789 367001 := bstep (se 2 (by rfl) ⟨137625, by rfl⟩ : syracuseStep 367001 = 275251) B275251
theorem B203195 : Blo 131789 203195 := bstep (se 1 (by rfl) ⟨152396, by rfl⟩ : syracuseStep 203195 = 304793) B304793
theorem B203255 : Blo 131789 203255 := bstep (se 1 (by rfl) ⟨152441, by rfl⟩ : syracuseStep 203255 = 304883) B304883
theorem B203279 : Blo 131789 203279 := bstep (se 1 (by rfl) ⟨152459, by rfl⟩ : syracuseStep 203279 = 304919) B304919
theorem B203321 : Blo 131789 203321 := bstep (se 2 (by rfl) ⟨76245, by rfl⟩ : syracuseStep 203321 = 152491) B152491
theorem B203399 : Blo 131789 203399 := bstep (se 1 (by rfl) ⟨152549, by rfl⟩ : syracuseStep 203399 = 305099) B305099
theorem B301715 : Blo 131789 301715 := bstep (se 1 (by rfl) ⟨226286, by rfl⟩ : syracuseStep 301715 = 452573) B452573
theorem B334489 : Blo 131789 334489 := bstep (se 2 (by rfl) ⟨125433, by rfl⟩ : syracuseStep 334489 = 250867) B250867
theorem B203435 : Blo 131789 203435 := bstep (se 1 (by rfl) ⟨152576, by rfl⟩ : syracuseStep 203435 = 305153) B305153
theorem B301769 : Blo 131789 301769 := bstep (se 2 (by rfl) ⟨113163, by rfl⟩ : syracuseStep 301769 = 226327) B226327
theorem B203465 : Blo 131789 203465 := bstep (se 2 (by rfl) ⟨76299, by rfl⟩ : syracuseStep 203465 = 152599) B152599
theorem B170743 : Blo 131789 170743 := bstep (se 1 (by rfl) ⟨128057, by rfl⟩ : syracuseStep 170743 = 256115) B256115
theorem B334651 : Blo 131789 334651 := bstep (se 1 (by rfl) ⟨250988, by rfl⟩ : syracuseStep 334651 = 501977) B501977
theorem B203579 : Blo 131789 203579 := bstep (se 1 (by rfl) ⟨152684, by rfl⟩ : syracuseStep 203579 = 305369) B305369
theorem B203639 : Blo 131789 203639 := bstep (se 1 (by rfl) ⟨152729, by rfl⟩ : syracuseStep 203639 = 305459) B305459
theorem B760711 : Blo 131789 760711 := bstep (se 1 (by rfl) ⟨570533, by rfl⟩ : syracuseStep 760711 = 1141067) B1141067
theorem B203663 : Blo 131789 203663 := bstep (se 1 (by rfl) ⟨152747, by rfl⟩ : syracuseStep 203663 = 305495) B305495
theorem B334793 : Blo 131789 334793 := bstep (se 2 (by rfl) ⟨125547, by rfl⟩ : syracuseStep 334793 = 251095) B251095
theorem B433181 : Blo 131789 433181 := bstep (se 3 (by rfl) ⟨81221, by rfl⟩ : syracuseStep 433181 = 162443) B162443
theorem B171067 : Blo 131789 171067 := bstep (se 1 (by rfl) ⟨128300, by rfl⟩ : syracuseStep 171067 = 256601) B256601
theorem B335137 : Blo 131789 335137 := bstep (se 2 (by rfl) ⟨125676, by rfl⟩ : syracuseStep 335137 = 251353) B251353
theorem B302471 : Blo 131789 302471 := bstep (se 1 (by rfl) ⟨226853, by rfl⟩ : syracuseStep 302471 = 453707) B453707
theorem B269867 : Blo 131789 269867 := bstep (se 1 (by rfl) ⟨202400, by rfl⟩ : syracuseStep 269867 = 404801) B404801
theorem B302651 : Blo 131789 302651 := bstep (se 1 (by rfl) ⟨226988, by rfl⟩ : syracuseStep 302651 = 453977) B453977
theorem B302777 : Blo 131789 302777 := bstep (se 2 (by rfl) ⟨113541, by rfl⟩ : syracuseStep 302777 = 227083) B227083
theorem B1449701 : Blo 131789 1449701 := bstep (se 4 (by rfl) ⟨135909, by rfl⟩ : syracuseStep 1449701 = 271819) B271819
theorem B2793217 : Blo 131789 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B335735 : Blo 131789 335735 := bstep (se 1 (by rfl) ⟨251801, by rfl⟩ : syracuseStep 335735 = 503603) B503603
theorem B729091 : Blo 131789 729091 := bstep (se 1 (by rfl) ⟨546818, by rfl⟩ : syracuseStep 729091 = 1093637) B1093637
theorem B303119 : Blo 131789 303119 := bstep (se 1 (by rfl) ⟨227339, by rfl⟩ : syracuseStep 303119 = 454679) B454679
theorem B303137 : Blo 131789 303137 := bstep (se 2 (by rfl) ⟨113676, by rfl⟩ : syracuseStep 303137 = 227353) B227353
theorem B303479 : Blo 131789 303479 := bstep (se 1 (by rfl) ⟨227609, by rfl⟩ : syracuseStep 303479 = 455219) B455219
theorem B303659 : Blo 131789 303659 := bstep (se 1 (by rfl) ⟨227744, by rfl⟩ : syracuseStep 303659 = 455489) B455489
theorem B369299 : Blo 131789 369299 := bstep (se 1 (by rfl) ⟨276974, by rfl⟩ : syracuseStep 369299 = 553949) B553949
theorem B304019 : Blo 131789 304019 := bstep (se 1 (by rfl) ⟨228014, by rfl⟩ : syracuseStep 304019 = 456029) B456029
theorem B304073 : Blo 131789 304073 := bstep (se 2 (by rfl) ⟨114027, by rfl⟩ : syracuseStep 304073 = 228055) B228055
theorem B861131 : Blo 131789 861131 := bstep (se 1 (by rfl) ⟨645848, by rfl⟩ : syracuseStep 861131 = 1291697) B1291697
theorem B1287191 : Blo 131789 1287191 := bstep (se 1 (by rfl) ⟨965393, by rfl⟩ : syracuseStep 1287191 = 1930787) B1930787
theorem B337031 : Blo 131789 337031 := bstep (se 1 (by rfl) ⟨252773, by rfl⟩ : syracuseStep 337031 = 505547) B505547
theorem B337081 : Blo 131789 337081 := bstep (se 2 (by rfl) ⟨126405, by rfl⟩ : syracuseStep 337081 = 252811) B252811
theorem B664865 : Blo 131789 664865 := bstep (se 2 (by rfl) ⟨249324, by rfl⟩ : syracuseStep 664865 = 498649) B498649
theorem B238907 : Blo 131789 238907 := bstep (se 1 (by rfl) ⟨179180, by rfl⟩ : syracuseStep 238907 = 358361) B358361
theorem B304775 : Blo 131789 304775 := bstep (se 1 (by rfl) ⟨228581, by rfl⟩ : syracuseStep 304775 = 457163) B457163
theorem B337679 : Blo 131789 337679 := bstep (se 1 (by rfl) ⟨253259, by rfl⟩ : syracuseStep 337679 = 506519) B506519
theorem B304955 : Blo 131789 304955 := bstep (se 1 (by rfl) ⟨228716, by rfl⟩ : syracuseStep 304955 = 457433) B457433
theorem B1025945 : Blo 131789 1025945 := bstep (se 2 (by rfl) ⟨384729, by rfl⟩ : syracuseStep 1025945 = 769459) B769459
theorem B305081 : Blo 131789 305081 := bstep (se 2 (by rfl) ⟨114405, by rfl⟩ : syracuseStep 305081 = 228811) B228811
theorem B11610053 : Blo 131789 11610053 := bstep (se 4 (by rfl) ⟨1088442, by rfl⟩ : syracuseStep 11610053 = 2176885) B2176885
theorem B1747117 : Blo 131789 1747117 := bstep (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) B655169
theorem B141583 : Blo 131789 141583 := bstep (se 1 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 141583 = 212375) B212375
theorem B305423 : Blo 131789 305423 := bstep (se 1 (by rfl) ⟨229067, by rfl⟩ : syracuseStep 305423 = 458135) B458135
theorem B305441 : Blo 131789 305441 := bstep (se 2 (by rfl) ⟨114540, by rfl⟩ : syracuseStep 305441 = 229081) B229081
theorem B338377 : Blo 131789 338377 := bstep (se 2 (by rfl) ⟨126891, by rfl⟩ : syracuseStep 338377 = 253783) B253783
theorem B338519 : Blo 131789 338519 := bstep (se 1 (by rfl) ⟨253889, by rfl⟩ : syracuseStep 338519 = 507779) B507779
theorem B141959 : Blo 131789 141959 := bstep (se 1 (by rfl) ⟨106469, by rfl⟩ : syracuseStep 141959 = 212939) B212939
theorem B240263 : Blo 131789 240263 := bstep (se 1 (by rfl) ⟨180197, by rfl⟩ : syracuseStep 240263 = 360395) B360395
theorem B1288921 : Blo 131789 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B699479 : Blo 131789 699479 := bstep (se 1 (by rfl) ⟨524609, by rfl⟩ : syracuseStep 699479 = 1049219) B1049219
theorem B142651 : Blo 131789 142651 := bstep (se 1 (by rfl) ⟨106988, by rfl⟩ : syracuseStep 142651 = 213977) B213977
theorem B536017 : Blo 131789 536017 := bstep (se 2 (by rfl) ⟨201006, by rfl⟩ : syracuseStep 536017 = 402013) B402013
theorem B1224157 : Blo 131789 1224157 := bstep (se 3 (by rfl) ⟨229529, by rfl⟩ : syracuseStep 1224157 = 459059) B459059
theorem B241271 : Blo 131789 241271 := bstep (se 1 (by rfl) ⟨180953, by rfl⟩ : syracuseStep 241271 = 361907) B361907
theorem B208585 : Blo 131789 208585 := bstep (se 2 (by rfl) ⟨78219, by rfl⟩ : syracuseStep 208585 = 156439) B156439
theorem B634625 : Blo 131789 634625 := bstep (se 2 (by rfl) ⟨237984, by rfl⟩ : syracuseStep 634625 = 475969) B475969
theorem B1027889 : Blo 131789 1027889 := bstep (se 2 (by rfl) ⟨385458, by rfl⟩ : syracuseStep 1027889 = 770917) B770917
theorem B667601 : Blo 131789 667601 := bstep (se 2 (by rfl) ⟨250350, by rfl⟩ : syracuseStep 667601 = 500701) B500701
theorem B2601233 : Blo 131789 2601233 := bstep (se 2 (by rfl) ⟨975462, by rfl⟩ : syracuseStep 2601233 = 1950925) B1950925
theorem B766361 : Blo 131789 766361 := bstep (se 2 (by rfl) ⟨287385, by rfl⟩ : syracuseStep 766361 = 574771) B574771
theorem B504407 : Blo 131789 504407 := bstep (se 1 (by rfl) ⟨378305, by rfl⟩ : syracuseStep 504407 = 756611) B756611
theorem B340595 : Blo 131789 340595 := bstep (se 1 (by rfl) ⟨255446, by rfl⟩ : syracuseStep 340595 = 510893) B510893
theorem B4207285 : Blo 131789 4207285 := bstep (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) B394433
theorem B1749721 : Blo 131789 1749721 := bstep (se 2 (by rfl) ⟨656145, by rfl⟩ : syracuseStep 1749721 = 1312291) B1312291
theorem B537479 : Blo 131789 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B570397 : Blo 131789 570397 := bstep (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) B213899
theorem B504893 : Blo 131789 504893 := bstep (se 3 (by rfl) ⟨94667, by rfl⟩ : syracuseStep 504893 = 189335) B189335
theorem B341111 : Blo 131789 341111 := bstep (se 1 (by rfl) ⟨255833, by rfl⟩ : syracuseStep 341111 = 511667) B511667
theorem B242959 : Blo 131789 242959 := bstep (se 1 (by rfl) ⟨182219, by rfl⟩ : syracuseStep 242959 = 364439) B364439
theorem B570739 : Blo 131789 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B243319 : Blo 131789 243319 := bstep (se 1 (by rfl) ⟨182489, by rfl⟩ : syracuseStep 243319 = 364979) B364979
theorem B308855 : Blo 131789 308855 := bstep (se 1 (by rfl) ⟨231641, by rfl⟩ : syracuseStep 308855 = 463283) B463283
theorem B1390385 : Blo 131789 1390385 := bstep (se 2 (by rfl) ⟨521394, by rfl⟩ : syracuseStep 1390385 = 1042789) B1042789
theorem B669707 : Blo 131789 669707 := bstep (se 1 (by rfl) ⟨502280, by rfl⟩ : syracuseStep 669707 = 1004561) B1004561
theorem B342103 : Blo 131789 342103 := bstep (se 1 (by rfl) ⟨256577, by rfl⟩ : syracuseStep 342103 = 513155) B513155
theorem B1554565 : Blo 131789 1554565 := bstep (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) B291481
theorem B669869 : Blo 131789 669869 := bstep (se 3 (by rfl) ⟨125600, by rfl⟩ : syracuseStep 669869 = 251201) B251201
theorem B342407 : Blo 131789 342407 := bstep (se 1 (by rfl) ⟨256805, by rfl⟩ : syracuseStep 342407 = 513611) B513611
theorem B506321 : Blo 131789 506321 := bstep (se 2 (by rfl) ⟨189870, by rfl⟩ : syracuseStep 506321 = 379741) B379741
theorem B4143581 : Blo 131789 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B342539 : Blo 131789 342539 := bstep (se 1 (by rfl) ⟨256904, by rfl⟩ : syracuseStep 342539 = 513809) B513809
theorem B277111 : Blo 131789 277111 := bstep (se 1 (by rfl) ⟨207833, by rfl⟩ : syracuseStep 277111 = 415667) B415667
theorem B343055 : Blo 131789 343055 := bstep (se 1 (by rfl) ⟨257291, by rfl⟩ : syracuseStep 343055 = 514583) B514583
theorem B343187 : Blo 131789 343187 := bstep (se 1 (by rfl) ⟨257390, by rfl⟩ : syracuseStep 343187 = 514781) B514781
theorem B834875 : Blo 131789 834875 := bstep (se 1 (by rfl) ⟨626156, by rfl⟩ : syracuseStep 834875 = 1252313) B1252313
theorem B671489 : Blo 131789 671489 := bstep (se 2 (by rfl) ⟨251808, by rfl⟩ : syracuseStep 671489 = 503617) B503617
theorem B376609 : Blo 131789 376609 := bstep (se 2 (by rfl) ⟨141228, by rfl⟩ : syracuseStep 376609 = 282457) B282457
theorem B1523609 : Blo 131789 1523609 := bstep (se 2 (by rfl) ⟨571353, by rfl⟩ : syracuseStep 1523609 = 1142707) B1142707
theorem B507991 : Blo 131789 507991 := bstep (se 1 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 507991 = 761987) B761987
theorem B377099 : Blo 131789 377099 := bstep (se 1 (by rfl) ⟨282824, by rfl⟩ : syracuseStep 377099 = 565649) B565649
theorem B508295 : Blo 131789 508295 := bstep (se 1 (by rfl) ⟨381221, by rfl⟩ : syracuseStep 508295 = 762443) B762443
theorem B967133 : Blo 131789 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B672299 : Blo 131789 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B508477 : Blo 131789 508477 := bstep (se 3 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 508477 = 190679) B190679
theorem B574361 : Blo 131789 574361 := bstep (se 2 (by rfl) ⟨215385, by rfl⟩ : syracuseStep 574361 = 430771) B430771
theorem B148495 : Blo 131789 148495 := bstep (se 1 (by rfl) ⟨111371, by rfl⟩ : syracuseStep 148495 = 222743) B222743
theorem B377885 : Blo 131789 377885 := bstep (se 3 (by rfl) ⟨70853, by rfl⟩ : syracuseStep 377885 = 141707) B141707
theorem B771191 : Blo 131789 771191 := bstep (se 1 (by rfl) ⟨578393, by rfl⟩ : syracuseStep 771191 = 1156787) B1156787
theorem B214201 : Blo 131789 214201 := bstep (se 2 (by rfl) ⟨80325, by rfl⟩ : syracuseStep 214201 = 160651) B160651
theorem B640237 : Blo 131789 640237 := bstep (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) B240089
theorem B476417 : Blo 131789 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B771443 : Blo 131789 771443 := bstep (se 1 (by rfl) ⟨578582, by rfl⟩ : syracuseStep 771443 = 1157165) B1157165
theorem B148999 : Blo 131789 148999 := bstep (se 1 (by rfl) ⟨111749, by rfl⟩ : syracuseStep 148999 = 223499) B223499
theorem B149179 : Blo 131789 149179 := bstep (se 1 (by rfl) ⟨111884, by rfl⟩ : syracuseStep 149179 = 223769) B223769
theorem B673595 : Blo 131789 673595 := bstep (se 1 (by rfl) ⟨505196, by rfl⟩ : syracuseStep 673595 = 1010393) B1010393
theorem B673757 : Blo 131789 673757 := bstep (se 3 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 673757 = 252659) B252659
theorem B149647 : Blo 131789 149647 := bstep (se 1 (by rfl) ⟨112235, by rfl⟩ : syracuseStep 149647 = 224471) B224471
theorem B1001645 : Blo 131789 1001645 := bstep (se 3 (by rfl) ⟨187808, by rfl⟩ : syracuseStep 1001645 = 375617) B375617
theorem B510209 : Blo 131789 510209 := bstep (se 2 (by rfl) ⟨191328, by rfl⟩ : syracuseStep 510209 = 382657) B382657
theorem B674081 : Blo 131789 674081 := bstep (se 2 (by rfl) ⟨252780, by rfl⟩ : syracuseStep 674081 = 505561) B505561
theorem B150151 : Blo 131789 150151 := bstep (se 1 (by rfl) ⟨112613, by rfl⟩ : syracuseStep 150151 = 225227) B225227
theorem B19942129 : Blo 131789 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B772901 : Blo 131789 772901 := bstep (se 4 (by rfl) ⟨72459, by rfl⟩ : syracuseStep 772901 = 144919) B144919
theorem B150331 : Blo 131789 150331 := bstep (se 1 (by rfl) ⟨112748, by rfl⟩ : syracuseStep 150331 = 225497) B225497
theorem B3263381 : Blo 131789 3263381 := bstep (se 6 (by rfl) ⟨76485, by rfl⟩ : syracuseStep 3263381 = 152971) B152971
theorem B445337 : Blo 131789 445337 := bstep (se 2 (by rfl) ⟨167001, by rfl⟩ : syracuseStep 445337 = 334003) B334003
theorem B379991 : Blo 131789 379991 := bstep (se 1 (by rfl) ⟨284993, by rfl⟩ : syracuseStep 379991 = 569987) B569987
theorem B675053 : Blo 131789 675053 := bstep (se 3 (by rfl) ⟨126572, by rfl⟩ : syracuseStep 675053 = 253145) B253145
theorem B150799 : Blo 131789 150799 := bstep (se 1 (by rfl) ⟨113099, by rfl⟩ : syracuseStep 150799 = 226199) B226199
theorem B1133959 : Blo 131789 1133959 := bstep (se 1 (by rfl) ⟨850469, by rfl⟩ : syracuseStep 1133959 = 1700939) B1700939
theorem B511379 : Blo 131789 511379 := bstep (se 1 (by rfl) ⟨383534, by rfl⟩ : syracuseStep 511379 = 767069) B767069
theorem B1953233 : Blo 131789 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B446039 : Blo 131789 446039 := bstep (se 1 (by rfl) ⟨334529, by rfl⟩ : syracuseStep 446039 = 669059) B669059
theorem B151303 : Blo 131789 151303 := bstep (se 1 (by rfl) ⟨113477, by rfl⟩ : syracuseStep 151303 = 226955) B226955
theorem B216847 : Blo 131789 216847 := bstep (se 1 (by rfl) ⟨162635, by rfl⟩ : syracuseStep 216847 = 325271) B325271
theorem B511879 : Blo 131789 511879 := bstep (se 1 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 511879 = 767819) B767819
theorem B380857 : Blo 131789 380857 := bstep (se 2 (by rfl) ⟨142821, by rfl⟩ : syracuseStep 380857 = 285643) B285643
theorem B151483 : Blo 131789 151483 := bstep (se 1 (by rfl) ⟨113612, by rfl⟩ : syracuseStep 151483 = 227225) B227225
theorem B577489 : Blo 131789 577489 := bstep (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) B433117
theorem B675863 : Blo 131789 675863 := bstep (se 1 (by rfl) ⟨506897, by rfl⟩ : syracuseStep 675863 = 1013795) B1013795
theorem B446525 : Blo 131789 446525 := bstep (se 3 (by rfl) ⟨83723, by rfl⟩ : syracuseStep 446525 = 167447) B167447
theorem B381199 : Blo 131789 381199 := bstep (se 1 (by rfl) ⟨285899, by rfl⟩ : syracuseStep 381199 = 571799) B571799
theorem B151951 : Blo 131789 151951 := bstep (se 1 (by rfl) ⟨113963, by rfl⟩ : syracuseStep 151951 = 227927) B227927
theorem B381473 : Blo 131789 381473 := bstep (se 2 (by rfl) ⟨143052, by rfl⟩ : syracuseStep 381473 = 286105) B286105
theorem B1004075 : Blo 131789 1004075 := bstep (se 1 (by rfl) ⟨753056, by rfl⟩ : syracuseStep 1004075 = 1506113) B1506113
theorem B250427 : Blo 131789 250427 := bstep (se 1 (by rfl) ⟨187820, by rfl⟩ : syracuseStep 250427 = 375641) B375641
theorem B3068761 : Blo 131789 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B152455 : Blo 131789 152455 := bstep (se 1 (by rfl) ⟨114341, by rfl⟩ : syracuseStep 152455 = 228683) B228683
theorem B250913 : Blo 131789 250913 := bstep (se 2 (by rfl) ⟨94092, by rfl⟩ : syracuseStep 250913 = 188185) B188185
theorem B152635 : Blo 131789 152635 := bstep (se 1 (by rfl) ⟨114476, by rfl⟩ : syracuseStep 152635 = 228953) B228953
theorem B382087 : Blo 131789 382087 := bstep (se 1 (by rfl) ⟨286565, by rfl⟩ : syracuseStep 382087 = 573131) B573131
theorem B251255 : Blo 131789 251255 := bstep (se 1 (by rfl) ⟨188441, by rfl⟩ : syracuseStep 251255 = 376883) B376883
theorem B447929 : Blo 131789 447929 := bstep (se 2 (by rfl) ⟨167973, by rfl⟩ : syracuseStep 447929 = 335947) B335947
theorem B284105 : Blo 131789 284105 := bstep (se 2 (by rfl) ⟨106539, by rfl⟩ : syracuseStep 284105 = 213079) B213079
theorem B382475 : Blo 131789 382475 := bstep (se 1 (by rfl) ⟨286856, by rfl⟩ : syracuseStep 382475 = 573713) B573713
theorem B317081 : Blo 131789 317081 := bstep (se 2 (by rfl) ⟨118905, by rfl⟩ : syracuseStep 317081 = 237811) B237811
theorem B1464227 : Blo 131789 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B1038347 : Blo 131789 1038347 := bstep (se 1 (by rfl) ⟨778760, by rfl⟩ : syracuseStep 1038347 = 1557521) B1557521
theorem B448523 : Blo 131789 448523 := bstep (se 1 (by rfl) ⟨336392, by rfl⟩ : syracuseStep 448523 = 672785) B672785
theorem B448631 : Blo 131789 448631 := bstep (se 1 (by rfl) ⟨336473, by rfl⟩ : syracuseStep 448631 = 672947) B672947
theorem B514451 : Blo 131789 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B3103217 : Blo 131789 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B285385 : Blo 131789 285385 := bstep (se 2 (by rfl) ⟨107019, by rfl⟩ : syracuseStep 285385 = 214039) B214039
theorem B449225 : Blo 131789 449225 := bstep (se 2 (by rfl) ⟨168459, by rfl⟩ : syracuseStep 449225 = 336919) B336919
theorem B645833 : Blo 131789 645833 := bstep (se 2 (by rfl) ⟨242187, by rfl⟩ : syracuseStep 645833 = 484375) B484375
theorem B5233423 : Blo 131789 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B383773 : Blo 131789 383773 := bstep (se 3 (by rfl) ⟨71957, by rfl⟩ : syracuseStep 383773 = 143915) B143915
theorem B973619 : Blo 131789 973619 := bstep (se 1 (by rfl) ⟨730214, by rfl⟩ : syracuseStep 973619 = 1460429) B1460429
theorem B482183 : Blo 131789 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B252857 : Blo 131789 252857 := bstep (se 2 (by rfl) ⟨94821, by rfl⟩ : syracuseStep 252857 = 189643) B189643
theorem B678941 : Blo 131789 678941 := bstep (se 3 (by rfl) ⟨127301, by rfl⟩ : syracuseStep 678941 = 254603) B254603
theorem B384115 : Blo 131789 384115 := bstep (se 1 (by rfl) ⟨288086, by rfl⟩ : syracuseStep 384115 = 576173) B576173
theorem B253199 : Blo 131789 253199 := bstep (se 1 (by rfl) ⟨189899, by rfl⟩ : syracuseStep 253199 = 379799) B379799
theorem B449927 : Blo 131789 449927 := bstep (se 1 (by rfl) ⟨337445, by rfl⟩ : syracuseStep 449927 = 674891) B674891
theorem B286087 : Blo 131789 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B187849 : Blo 131789 187849 := bstep (se 2 (by rfl) ⟨70443, by rfl⟩ : syracuseStep 187849 = 140887) B140887
theorem B679427 : Blo 131789 679427 := bstep (se 1 (by rfl) ⟨509570, by rfl⟩ : syracuseStep 679427 = 1019141) B1019141
theorem B319177 : Blo 131789 319177 := bstep (se 2 (by rfl) ⟨119691, by rfl⟩ : syracuseStep 319177 = 239383) B239383
theorem B450305 : Blo 131789 450305 := bstep (se 2 (by rfl) ⟨168864, by rfl⟩ : syracuseStep 450305 = 337729) B337729
theorem B254011 : Blo 131789 254011 := bstep (se 1 (by rfl) ⟨190508, by rfl⟩ : syracuseStep 254011 = 381017) B381017
theorem B254087 : Blo 131789 254087 := bstep (se 1 (by rfl) ⟨190565, by rfl⟩ : syracuseStep 254087 = 381131) B381131
theorem B1466657 : Blo 131789 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B483869 : Blo 131789 483869 := bstep (se 3 (by rfl) ⟨90725, by rfl⟩ : syracuseStep 483869 = 181451) B181451
theorem B254497 : Blo 131789 254497 := bstep (se 2 (by rfl) ⟨95436, by rfl⟩ : syracuseStep 254497 = 190873) B190873
theorem B451115 : Blo 131789 451115 := bstep (se 1 (by rfl) ⟨338336, by rfl⟩ : syracuseStep 451115 = 676673) B676673
theorem B1368695 : Blo 131789 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B1466999 : Blo 131789 1466999 := bstep (se 1 (by rfl) ⟨1100249, by rfl⟩ : syracuseStep 1466999 = 2200499) B2200499
theorem B680737 : Blo 131789 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B254839 : Blo 131789 254839 := bstep (se 1 (by rfl) ⟨191129, by rfl⟩ : syracuseStep 254839 = 382259) B382259
theorem B1532951 : Blo 131789 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B681047 : Blo 131789 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B451855 : Blo 131789 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B550259 : Blo 131789 550259 := bstep (se 1 (by rfl) ⟨412694, by rfl⟩ : syracuseStep 550259 = 825389) B825389
theorem B222763 : Blo 131789 222763 := bstep (se 1 (by rfl) ⟨167072, by rfl⟩ : syracuseStep 222763 = 334145) B334145
theorem B681533 : Blo 131789 681533 := bstep (se 3 (by rfl) ⟨127787, by rfl⟩ : syracuseStep 681533 = 255575) B255575
theorem B812717 : Blo 131789 812717 := bstep (se 3 (by rfl) ⟨152384, by rfl⟩ : syracuseStep 812717 = 304769) B304769
theorem B222905 : Blo 131789 222905 := bstep (se 2 (by rfl) ⟨83589, by rfl⟩ : syracuseStep 222905 = 167179) B167179
theorem B452411 : Blo 131789 452411 := bstep (se 1 (by rfl) ⟨339308, by rfl⟩ : syracuseStep 452411 = 678617) B678617
theorem B14444405 : Blo 131789 14444405 := bstep (se 5 (by rfl) ⟨677081, by rfl⟩ : syracuseStep 14444405 = 1354163) B1354163
theorem B452897 : Blo 131789 452897 := bstep (se 2 (by rfl) ⟨169836, by rfl⟩ : syracuseStep 452897 = 339673) B339673
theorem B190793 : Blo 131789 190793 := bstep (se 2 (by rfl) ⟨71547, by rfl⟩ : syracuseStep 190793 = 143095) B143095
theorem B223607 : Blo 131789 223607 := bstep (se 1 (by rfl) ⟨167705, by rfl⟩ : syracuseStep 223607 = 335411) B335411
theorem B1436039 : Blo 131789 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B256441 : Blo 131789 256441 := bstep (se 2 (by rfl) ⟨96165, by rfl⟩ : syracuseStep 256441 = 192331) B192331
theorem B616889 : Blo 131789 616889 := bstep (se 2 (by rfl) ⟨231333, by rfl⟩ : syracuseStep 616889 = 462667) B462667
theorem B1501739 : Blo 131789 1501739 := bstep (se 1 (by rfl) ⟨1126304, by rfl⟩ : syracuseStep 1501739 = 2252609) B2252609
theorem B518699 : Blo 131789 518699 := bstep (se 1 (by rfl) ⟨389024, by rfl⟩ : syracuseStep 518699 = 778049) B778049
theorem B256783 : Blo 131789 256783 := bstep (se 1 (by rfl) ⟨192587, by rfl⟩ : syracuseStep 256783 = 385175) B385175
theorem B256801 : Blo 131789 256801 := bstep (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) B192601
theorem B224059 : Blo 131789 224059 := bstep (se 1 (by rfl) ⟨168044, by rfl⟩ : syracuseStep 224059 = 336089) B336089
theorem B453491 : Blo 131789 453491 := bstep (se 1 (by rfl) ⟨340118, by rfl⟩ : syracuseStep 453491 = 680237) B680237
theorem B224201 : Blo 131789 224201 := bstep (se 2 (by rfl) ⟨84075, by rfl⟩ : syracuseStep 224201 = 168151) B168151
theorem B191659 : Blo 131789 191659 := bstep (se 1 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 191659 = 287489) B287489
theorem B683315 : Blo 131789 683315 := bstep (se 1 (by rfl) ⟨512486, by rfl⟩ : syracuseStep 683315 = 1024973) B1024973
theorem B1371485 : Blo 131789 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B683639 : Blo 131789 683639 := bstep (se 1 (by rfl) ⟨512729, by rfl⟩ : syracuseStep 683639 = 1025459) B1025459
theorem B224903 : Blo 131789 224903 := bstep (se 1 (by rfl) ⟨168677, by rfl⟩ : syracuseStep 224903 = 337355) B337355
theorem B257671 : Blo 131789 257671 := bstep (se 1 (by rfl) ⟨193253, by rfl⟩ : syracuseStep 257671 = 386507) B386507
theorem B356363 : Blo 131789 356363 := bstep (se 1 (by rfl) ⟨267272, by rfl⟩ : syracuseStep 356363 = 534545) B534545
theorem B323617 : Blo 131789 323617 := bstep (se 2 (by rfl) ⟨121356, by rfl⟩ : syracuseStep 323617 = 242713) B242713
theorem B5009501 : Blo 131789 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B192775 : Blo 131789 192775 := bstep (se 1 (by rfl) ⟨144581, by rfl⟩ : syracuseStep 192775 = 289163) B289163
theorem B225551 : Blo 131789 225551 := bstep (se 1 (by rfl) ⟨169163, by rfl⟩ : syracuseStep 225551 = 338327) B338327
theorem B684611 : Blo 131789 684611 := bstep (se 1 (by rfl) ⟨513458, by rfl⟩ : syracuseStep 684611 = 1026917) B1026917
theorem B848677 : Blo 131789 848677 := bstep (se 4 (by rfl) ⟨79563, by rfl⟩ : syracuseStep 848677 = 159127) B159127
theorem B226091 : Blo 131789 226091 := bstep (se 1 (by rfl) ⟨169568, by rfl⟩ : syracuseStep 226091 = 339137) B339137
theorem B684935 : Blo 131789 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B488339 : Blo 131789 488339 := bstep (se 1 (by rfl) ⟨366254, by rfl⟩ : syracuseStep 488339 = 732509) B732509
theorem B1012823 : Blo 131789 1012823 := bstep (se 1 (by rfl) ⟨759617, by rfl⟩ : syracuseStep 1012823 = 1519235) B1519235
theorem B226489 : Blo 131789 226489 := bstep (se 2 (by rfl) ⟨84933, by rfl⟩ : syracuseStep 226489 = 169867) B169867
theorem B357691 : Blo 131789 357691 := bstep (se 1 (by rfl) ⟨268268, by rfl⟩ : syracuseStep 357691 = 536537) B536537
theorem B456083 : Blo 131789 456083 := bstep (se 1 (by rfl) ⟨342062, by rfl⟩ : syracuseStep 456083 = 684125) B684125
theorem B358187 : Blo 131789 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B1144691 : Blo 131789 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B227191 : Blo 131789 227191 := bstep (se 1 (by rfl) ⟨170393, by rfl⟩ : syracuseStep 227191 = 340787) B340787
theorem B2553869 : Blo 131789 2553869 := bstep (se 3 (by rfl) ⟨478850, by rfl⟩ : syracuseStep 2553869 = 957701) B957701
theorem B5732369 : Blo 131789 5732369 := bstep (se 2 (by rfl) ⟨2149638, by rfl⟩ : syracuseStep 5732369 = 4299277) B4299277
theorem B227387 : Blo 131789 227387 := bstep (se 1 (by rfl) ⟨170540, by rfl⟩ : syracuseStep 227387 = 341081) B341081
theorem B194761 : Blo 131789 194761 := bstep (se 2 (by rfl) ⟨73035, by rfl⟩ : syracuseStep 194761 = 146071) B146071
theorem B1440017 : Blo 131789 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B227785 : Blo 131789 227785 := bstep (se 2 (by rfl) ⟨85419, by rfl⟩ : syracuseStep 227785 = 170839) B170839
theorem B1440449 : Blo 131789 1440449 := bstep (se 2 (by rfl) ⟨540168, by rfl⟩ : syracuseStep 1440449 = 1080337) B1080337
theorem B457487 : Blo 131789 457487 := bstep (se 1 (by rfl) ⟨343115, by rfl⟩ : syracuseStep 457487 = 686231) B686231
theorem B2063141 : Blo 131789 2063141 := bstep (se 4 (by rfl) ⟨193419, by rfl⟩ : syracuseStep 2063141 = 386839) B386839
theorem B1309603 : Blo 131789 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B261065 : Blo 131789 261065 := bstep (se 2 (by rfl) ⟨97899, by rfl⟩ : syracuseStep 261065 = 195799) B195799
theorem B457757 : Blo 131789 457757 := bstep (se 3 (by rfl) ⟨85829, by rfl⟩ : syracuseStep 457757 = 171659) B171659
theorem B228487 : Blo 131789 228487 := bstep (se 1 (by rfl) ⟨171365, by rfl⟩ : syracuseStep 228487 = 342731) B342731
theorem B5078213 : Blo 131789 5078213 := bstep (se 4 (by rfl) ⟨476082, by rfl⟩ : syracuseStep 5078213 = 952165) B952165
theorem B720161 : Blo 131789 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B327179 : Blo 131789 327179 := bstep (se 1 (by rfl) ⟨245384, by rfl⟩ : syracuseStep 327179 = 490769) B490769
theorem B753239 : Blo 131789 753239 := bstep (se 1 (by rfl) ⟨564929, by rfl⟩ : syracuseStep 753239 = 1129859) B1129859
theorem B2719331 : Blo 131789 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B229135 : Blo 131789 229135 := bstep (se 1 (by rfl) ⟨171851, by rfl⟩ : syracuseStep 229135 = 343703) B343703
theorem B1180169 : Blo 131789 1180169 := bstep (se 2 (by rfl) ⟨442563, by rfl⟩ : syracuseStep 1180169 = 885127) B885127
theorem B131803 : Blo 131789 131803 := bstep (se 1 (by rfl) ⟨98852, by rfl⟩ : syracuseStep 131803 = 197705) B197705
theorem B131879 : Blo 131789 131879 := bstep (se 1 (by rfl) ⟨98909, by rfl⟩ : syracuseStep 131879 = 197819) B197819
theorem B131919 : Blo 131789 131919 := bstep (se 1 (by rfl) ⟨98939, by rfl⟩ : syracuseStep 131919 = 197879) B197879
theorem B131935 : Blo 131789 131935 := bstep (se 1 (by rfl) ⟨98951, by rfl⟩ : syracuseStep 131935 = 197903) B197903
theorem B131963 : Blo 131789 131963 := bstep (se 1 (by rfl) ⟨98972, by rfl⟩ : syracuseStep 131963 = 197945) B197945
theorem B132015 : Blo 131789 132015 := bstep (se 1 (by rfl) ⟨99011, by rfl⟩ : syracuseStep 132015 = 198023) B198023
theorem B132039 : Blo 131789 132039 := bstep (se 1 (by rfl) ⟨99029, by rfl⟩ : syracuseStep 132039 = 198059) B198059
theorem B132059 : Blo 131789 132059 := bstep (se 1 (by rfl) ⟨99044, by rfl⟩ : syracuseStep 132059 = 198089) B198089
theorem B132135 : Blo 131789 132135 := bstep (se 1 (by rfl) ⟨99101, by rfl⟩ : syracuseStep 132135 = 198203) B198203
theorem B197711 : Blo 131789 197711 := bstep (se 1 (by rfl) ⟨148283, by rfl⟩ : syracuseStep 197711 = 296567) B296567
theorem B132175 : Blo 131789 132175 := bstep (se 1 (by rfl) ⟨99131, by rfl⟩ : syracuseStep 132175 = 198263) B198263
theorem B132191 : Blo 131789 132191 := bstep (se 1 (by rfl) ⟨99143, by rfl⟩ : syracuseStep 132191 = 198287) B198287
theorem B132219 : Blo 131789 132219 := bstep (se 1 (by rfl) ⟨99164, by rfl⟩ : syracuseStep 132219 = 198329) B198329
theorem B132271 : Blo 131789 132271 := bstep (se 1 (by rfl) ⟨99203, by rfl⟩ : syracuseStep 132271 = 198407) B198407
theorem B197831 : Blo 131789 197831 := bstep (se 1 (by rfl) ⟨148373, by rfl⟩ : syracuseStep 197831 = 296747) B296747
theorem B132295 : Blo 131789 132295 := bstep (se 1 (by rfl) ⟨99221, by rfl⟩ : syracuseStep 132295 = 198443) B198443
theorem B132315 : Blo 131789 132315 := bstep (se 1 (by rfl) ⟨99236, by rfl⟩ : syracuseStep 132315 = 198473) B198473
theorem B132391 : Blo 131789 132391 := bstep (se 1 (by rfl) ⟨99293, by rfl⟩ : syracuseStep 132391 = 198587) B198587
theorem B132431 : Blo 131789 132431 := bstep (se 1 (by rfl) ⟨99323, by rfl⟩ : syracuseStep 132431 = 198647) B198647
theorem B132447 : Blo 131789 132447 := bstep (se 1 (by rfl) ⟨99335, by rfl⟩ : syracuseStep 132447 = 198671) B198671
theorem B197993 : Blo 131789 197993 := bstep (se 2 (by rfl) ⟨74247, by rfl⟩ : syracuseStep 197993 = 148495) B148495
theorem B132475 : Blo 131789 132475 := bstep (se 1 (by rfl) ⟨99356, by rfl⟩ : syracuseStep 132475 = 198713) B198713
theorem B132527 : Blo 131789 132527 := bstep (se 1 (by rfl) ⟨99395, by rfl⟩ : syracuseStep 132527 = 198791) B198791
theorem B198071 : Blo 131789 198071 := bstep (se 1 (by rfl) ⟨148553, by rfl⟩ : syracuseStep 198071 = 297107) B297107
theorem B132551 : Blo 131789 132551 := bstep (se 1 (by rfl) ⟨99413, by rfl⟩ : syracuseStep 132551 = 198827) B198827
theorem B198107 : Blo 131789 198107 := bstep (se 1 (by rfl) ⟨148580, by rfl⟩ : syracuseStep 198107 = 297161) B297161
theorem B132571 : Blo 131789 132571 := bstep (se 1 (by rfl) ⟨99428, by rfl⟩ : syracuseStep 132571 = 198857) B198857
theorem B132647 : Blo 131789 132647 := bstep (se 1 (by rfl) ⟨99485, by rfl⟩ : syracuseStep 132647 = 198971) B198971
theorem B132687 : Blo 131789 132687 := bstep (se 1 (by rfl) ⟨99515, by rfl⟩ : syracuseStep 132687 = 199031) B199031
theorem B132703 : Blo 131789 132703 := bstep (se 1 (by rfl) ⟨99527, by rfl⟩ : syracuseStep 132703 = 199055) B199055
theorem B132731 : Blo 131789 132731 := bstep (se 1 (by rfl) ⟨99548, by rfl⟩ : syracuseStep 132731 = 199097) B199097
theorem B853649 : Blo 131789 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B132783 : Blo 131789 132783 := bstep (se 1 (by rfl) ⟨99587, by rfl⟩ : syracuseStep 132783 = 199175) B199175
theorem B132807 : Blo 131789 132807 := bstep (se 1 (by rfl) ⟨99605, by rfl⟩ : syracuseStep 132807 = 199211) B199211
theorem B132827 : Blo 131789 132827 := bstep (se 1 (by rfl) ⟨99620, by rfl⟩ : syracuseStep 132827 = 199241) B199241
theorem B132903 : Blo 131789 132903 := bstep (se 1 (by rfl) ⟨99677, by rfl⟩ : syracuseStep 132903 = 199355) B199355
theorem B132943 : Blo 131789 132943 := bstep (se 1 (by rfl) ⟨99707, by rfl⟩ : syracuseStep 132943 = 199415) B199415
theorem B132959 : Blo 131789 132959 := bstep (se 1 (by rfl) ⟨99719, by rfl⟩ : syracuseStep 132959 = 199439) B199439
theorem B132987 : Blo 131789 132987 := bstep (se 1 (by rfl) ⟨99740, by rfl⟩ : syracuseStep 132987 = 199481) B199481
theorem B8259479 : Blo 131789 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B198575 : Blo 131789 198575 := bstep (se 1 (by rfl) ⟨148931, by rfl⟩ : syracuseStep 198575 = 297863) B297863
theorem B133039 : Blo 131789 133039 := bstep (se 1 (by rfl) ⟨99779, by rfl⟩ : syracuseStep 133039 = 199559) B199559
theorem B296891 : Blo 131789 296891 := bstep (se 1 (by rfl) ⟨222668, by rfl⟩ : syracuseStep 296891 = 445337) B445337
theorem B133063 : Blo 131789 133063 := bstep (se 1 (by rfl) ⟨99797, by rfl⟩ : syracuseStep 133063 = 199595) B199595
theorem B133083 : Blo 131789 133083 := bstep (se 1 (by rfl) ⟨99812, by rfl⟩ : syracuseStep 133083 = 199625) B199625
theorem B198665 : Blo 131789 198665 := bstep (se 2 (by rfl) ⟨74499, by rfl⟩ : syracuseStep 198665 = 148999) B148999
theorem B198695 : Blo 131789 198695 := bstep (se 1 (by rfl) ⟨149021, by rfl⟩ : syracuseStep 198695 = 298043) B298043
theorem B133159 : Blo 131789 133159 := bstep (se 1 (by rfl) ⟨99869, by rfl⟩ : syracuseStep 133159 = 199739) B199739
theorem B297017 : Blo 131789 297017 := bstep (se 2 (by rfl) ⟨111381, by rfl⟩ : syracuseStep 297017 = 222763) B222763
theorem B133199 : Blo 131789 133199 := bstep (se 1 (by rfl) ⟨99899, by rfl⟩ : syracuseStep 133199 = 199799) B199799
theorem B526417 : Blo 131789 526417 := bstep (se 2 (by rfl) ⟨197406, by rfl⟩ : syracuseStep 526417 = 394813) B394813
theorem B133215 : Blo 131789 133215 := bstep (se 1 (by rfl) ⟨99911, by rfl⟩ : syracuseStep 133215 = 199823) B199823
theorem B198779 : Blo 131789 198779 := bstep (se 1 (by rfl) ⟨149084, by rfl⟩ : syracuseStep 198779 = 298169) B298169
theorem B133243 : Blo 131789 133243 := bstep (se 1 (by rfl) ⟨99932, by rfl⟩ : syracuseStep 133243 = 199865) B199865
theorem B133295 : Blo 131789 133295 := bstep (se 1 (by rfl) ⟨99971, by rfl⟩ : syracuseStep 133295 = 199943) B199943
theorem B133319 : Blo 131789 133319 := bstep (se 1 (by rfl) ⟨99989, by rfl⟩ : syracuseStep 133319 = 199979) B199979
theorem B133339 : Blo 131789 133339 := bstep (se 1 (by rfl) ⟨100004, by rfl⟩ : syracuseStep 133339 = 200009) B200009
theorem B198905 : Blo 131789 198905 := bstep (se 2 (by rfl) ⟨74589, by rfl⟩ : syracuseStep 198905 = 149179) B149179
theorem B133415 : Blo 131789 133415 := bstep (se 1 (by rfl) ⟨100061, by rfl⟩ : syracuseStep 133415 = 200123) B200123
theorem B133455 : Blo 131789 133455 := bstep (se 1 (by rfl) ⟨100091, by rfl⟩ : syracuseStep 133455 = 200183) B200183
theorem B199007 : Blo 131789 199007 := bstep (se 1 (by rfl) ⟨149255, by rfl⟩ : syracuseStep 199007 = 298511) B298511
theorem B133471 : Blo 131789 133471 := bstep (se 1 (by rfl) ⟨100103, by rfl⟩ : syracuseStep 133471 = 200207) B200207
theorem B199019 : Blo 131789 199019 := bstep (se 1 (by rfl) ⟨149264, by rfl⟩ : syracuseStep 199019 = 298529) B298529
theorem B133499 : Blo 131789 133499 := bstep (se 1 (by rfl) ⟨100124, by rfl⟩ : syracuseStep 133499 = 200249) B200249
theorem B297359 : Blo 131789 297359 := bstep (se 1 (by rfl) ⟨223019, by rfl⟩ : syracuseStep 297359 = 446039) B446039
theorem B133551 : Blo 131789 133551 := bstep (se 1 (by rfl) ⟨100163, by rfl⟩ : syracuseStep 133551 = 200327) B200327
theorem B133575 : Blo 131789 133575 := bstep (se 1 (by rfl) ⟨100181, by rfl⟩ : syracuseStep 133575 = 200363) B200363
theorem B133595 : Blo 131789 133595 := bstep (se 1 (by rfl) ⟨100196, by rfl⟩ : syracuseStep 133595 = 200393) B200393
theorem B2296349 : Blo 131789 2296349 := bstep (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) B861131
theorem B133671 : Blo 131789 133671 := bstep (se 1 (by rfl) ⟨100253, by rfl⟩ : syracuseStep 133671 = 200507) B200507
theorem B199247 : Blo 131789 199247 := bstep (se 1 (by rfl) ⟨149435, by rfl⟩ : syracuseStep 199247 = 298871) B298871
theorem B133711 : Blo 131789 133711 := bstep (se 1 (by rfl) ⟨100283, by rfl⟩ : syracuseStep 133711 = 200567) B200567
theorem B133727 : Blo 131789 133727 := bstep (se 1 (by rfl) ⟨100295, by rfl⟩ : syracuseStep 133727 = 200591) B200591
theorem B133755 : Blo 131789 133755 := bstep (se 1 (by rfl) ⟨100316, by rfl⟩ : syracuseStep 133755 = 200633) B200633
theorem B133807 : Blo 131789 133807 := bstep (se 1 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 133807 = 200711) B200711
theorem B199367 : Blo 131789 199367 := bstep (se 1 (by rfl) ⟨149525, by rfl⟩ : syracuseStep 199367 = 299051) B299051
theorem B133831 : Blo 131789 133831 := bstep (se 1 (by rfl) ⟨100373, by rfl⟩ : syracuseStep 133831 = 200747) B200747
theorem B297683 : Blo 131789 297683 := bstep (se 1 (by rfl) ⟨223262, by rfl⟩ : syracuseStep 297683 = 446525) B446525
theorem B133851 : Blo 131789 133851 := bstep (se 1 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 133851 = 200777) B200777
theorem B133927 : Blo 131789 133927 := bstep (se 1 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 133927 = 200891) B200891
theorem B133967 : Blo 131789 133967 := bstep (se 1 (by rfl) ⟨100475, by rfl⟩ : syracuseStep 133967 = 200951) B200951
theorem B133983 : Blo 131789 133983 := bstep (se 1 (by rfl) ⟨100487, by rfl⟩ : syracuseStep 133983 = 200975) B200975
theorem B199529 : Blo 131789 199529 := bstep (se 2 (by rfl) ⟨74823, by rfl⟩ : syracuseStep 199529 = 149647) B149647
theorem B134011 : Blo 131789 134011 := bstep (se 1 (by rfl) ⟨100508, by rfl⟩ : syracuseStep 134011 = 201017) B201017
theorem B2329489 : Blo 131789 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B134063 : Blo 131789 134063 := bstep (se 1 (by rfl) ⟨100547, by rfl⟩ : syracuseStep 134063 = 201095) B201095
theorem B199607 : Blo 131789 199607 := bstep (se 1 (by rfl) ⟨149705, by rfl⟩ : syracuseStep 199607 = 299411) B299411
theorem B134087 : Blo 131789 134087 := bstep (se 1 (by rfl) ⟨100565, by rfl⟩ : syracuseStep 134087 = 201131) B201131
theorem B199643 : Blo 131789 199643 := bstep (se 1 (by rfl) ⟨149732, by rfl⟩ : syracuseStep 199643 = 299465) B299465
theorem B134107 : Blo 131789 134107 := bstep (se 1 (by rfl) ⟨100580, by rfl⟩ : syracuseStep 134107 = 201161) B201161
theorem B166951 : Blo 131789 166951 := bstep (se 1 (by rfl) ⟨125213, by rfl⟩ : syracuseStep 166951 = 250427) B250427
theorem B134183 : Blo 131789 134183 := bstep (se 1 (by rfl) ⟨100637, by rfl⟩ : syracuseStep 134183 = 201275) B201275
theorem B134223 : Blo 131789 134223 := bstep (se 1 (by rfl) ⟨100667, by rfl⟩ : syracuseStep 134223 = 201335) B201335
theorem B134239 : Blo 131789 134239 := bstep (se 1 (by rfl) ⟨100679, by rfl⟩ : syracuseStep 134239 = 201359) B201359
theorem B134267 : Blo 131789 134267 := bstep (se 1 (by rfl) ⟨100700, by rfl⟩ : syracuseStep 134267 = 201401) B201401
theorem B134319 : Blo 131789 134319 := bstep (se 1 (by rfl) ⟨100739, by rfl⟩ : syracuseStep 134319 = 201479) B201479
theorem B134343 : Blo 131789 134343 := bstep (se 1 (by rfl) ⟨100757, by rfl⟩ : syracuseStep 134343 = 201515) B201515
theorem B134363 : Blo 131789 134363 := bstep (se 1 (by rfl) ⟨100772, by rfl⟩ : syracuseStep 134363 = 201545) B201545
theorem B462071 : Blo 131789 462071 := bstep (se 1 (by rfl) ⟨346553, by rfl⟩ : syracuseStep 462071 = 693107) B693107
theorem B134439 : Blo 131789 134439 := bstep (se 1 (by rfl) ⟨100829, by rfl⟩ : syracuseStep 134439 = 201659) B201659
theorem B134479 : Blo 131789 134479 := bstep (se 1 (by rfl) ⟨100859, by rfl⟩ : syracuseStep 134479 = 201719) B201719
theorem B134495 : Blo 131789 134495 := bstep (se 1 (by rfl) ⟨100871, by rfl⟩ : syracuseStep 134495 = 201743) B201743
theorem B167275 : Blo 131789 167275 := bstep (se 1 (by rfl) ⟨125456, by rfl⟩ : syracuseStep 167275 = 250913) B250913
theorem B134523 : Blo 131789 134523 := bstep (se 1 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 134523 = 201785) B201785
theorem B200111 : Blo 131789 200111 := bstep (se 1 (by rfl) ⟨150083, by rfl⟩ : syracuseStep 200111 = 300167) B300167
theorem B134575 : Blo 131789 134575 := bstep (se 1 (by rfl) ⟨100931, by rfl⟩ : syracuseStep 134575 = 201863) B201863
theorem B134599 : Blo 131789 134599 := bstep (se 1 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 134599 = 201899) B201899
theorem B134619 : Blo 131789 134619 := bstep (se 1 (by rfl) ⟨100964, by rfl⟩ : syracuseStep 134619 = 201929) B201929
theorem B200201 : Blo 131789 200201 := bstep (se 2 (by rfl) ⟨75075, by rfl⟩ : syracuseStep 200201 = 150151) B150151
theorem B396809 : Blo 131789 396809 := bstep (se 2 (by rfl) ⟨148803, by rfl⟩ : syracuseStep 396809 = 297607) B297607
theorem B200231 : Blo 131789 200231 := bstep (se 1 (by rfl) ⟨150173, by rfl⟩ : syracuseStep 200231 = 300347) B300347
theorem B134695 : Blo 131789 134695 := bstep (se 1 (by rfl) ⟨101021, by rfl⟩ : syracuseStep 134695 = 202043) B202043
theorem B167503 : Blo 131789 167503 := bstep (se 1 (by rfl) ⟨125627, by rfl⟩ : syracuseStep 167503 = 251255) B251255
theorem B134735 : Blo 131789 134735 := bstep (se 1 (by rfl) ⟨101051, by rfl⟩ : syracuseStep 134735 = 202103) B202103
theorem B134751 : Blo 131789 134751 := bstep (se 1 (by rfl) ⟨101063, by rfl⟩ : syracuseStep 134751 = 202127) B202127
theorem B298619 : Blo 131789 298619 := bstep (se 1 (by rfl) ⟨223964, by rfl⟩ : syracuseStep 298619 = 447929) B447929
theorem B200315 : Blo 131789 200315 := bstep (se 1 (by rfl) ⟨150236, by rfl⟩ : syracuseStep 200315 = 300473) B300473
theorem B134779 : Blo 131789 134779 := bstep (se 1 (by rfl) ⟨101084, by rfl⟩ : syracuseStep 134779 = 202169) B202169
theorem B134831 : Blo 131789 134831 := bstep (se 1 (by rfl) ⟨101123, by rfl⟩ : syracuseStep 134831 = 202247) B202247
theorem B8261297 : Blo 131789 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B134855 : Blo 131789 134855 := bstep (se 1 (by rfl) ⟨101141, by rfl⟩ : syracuseStep 134855 = 202283) B202283
theorem B134875 : Blo 131789 134875 := bstep (se 1 (by rfl) ⟨101156, by rfl⟩ : syracuseStep 134875 = 202313) B202313
theorem B298745 : Blo 131789 298745 := bstep (se 2 (by rfl) ⟨112029, by rfl⟩ : syracuseStep 298745 = 224059) B224059
theorem B200441 : Blo 131789 200441 := bstep (se 2 (by rfl) ⟨75165, by rfl⟩ : syracuseStep 200441 = 150331) B150331
theorem B1314593 : Blo 131789 1314593 := bstep (se 2 (by rfl) ⟨492972, by rfl⟩ : syracuseStep 1314593 = 985945) B985945
theorem B134951 : Blo 131789 134951 := bstep (se 1 (by rfl) ⟨101213, by rfl⟩ : syracuseStep 134951 = 202427) B202427
theorem B134991 : Blo 131789 134991 := bstep (se 1 (by rfl) ⟨101243, by rfl⟩ : syracuseStep 134991 = 202487) B202487
theorem B200543 : Blo 131789 200543 := bstep (se 1 (by rfl) ⟨150407, by rfl⟩ : syracuseStep 200543 = 300815) B300815
theorem B135007 : Blo 131789 135007 := bstep (se 1 (by rfl) ⟨101255, by rfl⟩ : syracuseStep 135007 = 202511) B202511
theorem B200555 : Blo 131789 200555 := bstep (se 1 (by rfl) ⟨150416, by rfl⟩ : syracuseStep 200555 = 300833) B300833
theorem B757613 : Blo 131789 757613 := bstep (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) B284105
theorem B135035 : Blo 131789 135035 := bstep (se 1 (by rfl) ⟨101276, by rfl⟩ : syracuseStep 135035 = 202553) B202553
theorem B1707911 : Blo 131789 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B135087 : Blo 131789 135087 := bstep (se 1 (by rfl) ⟨101315, by rfl⟩ : syracuseStep 135087 = 202631) B202631
theorem B135111 : Blo 131789 135111 := bstep (se 1 (by rfl) ⟨101333, by rfl⟩ : syracuseStep 135111 = 202667) B202667
theorem B135131 : Blo 131789 135131 := bstep (se 1 (by rfl) ⟨101348, by rfl⟩ : syracuseStep 135131 = 202697) B202697
theorem B299015 : Blo 131789 299015 := bstep (se 1 (by rfl) ⟨224261, by rfl⟩ : syracuseStep 299015 = 448523) B448523
theorem B692231 : Blo 131789 692231 := bstep (se 1 (by rfl) ⟨519173, by rfl⟩ : syracuseStep 692231 = 1038347) B1038347
theorem B135207 : Blo 131789 135207 := bstep (se 1 (by rfl) ⟨101405, by rfl⟩ : syracuseStep 135207 = 202811) B202811
theorem B299087 : Blo 131789 299087 := bstep (se 1 (by rfl) ⟨224315, by rfl⟩ : syracuseStep 299087 = 448631) B448631
theorem B200783 : Blo 131789 200783 := bstep (se 1 (by rfl) ⟨150587, by rfl⟩ : syracuseStep 200783 = 301175) B301175
theorem B135247 : Blo 131789 135247 := bstep (se 1 (by rfl) ⟨101435, by rfl⟩ : syracuseStep 135247 = 202871) B202871
theorem B135263 : Blo 131789 135263 := bstep (se 1 (by rfl) ⟨101447, by rfl⟩ : syracuseStep 135263 = 202895) B202895
theorem B135291 : Blo 131789 135291 := bstep (se 1 (by rfl) ⟨101468, by rfl⟩ : syracuseStep 135291 = 202937) B202937
theorem B135343 : Blo 131789 135343 := bstep (se 1 (by rfl) ⟨101507, by rfl⟩ : syracuseStep 135343 = 203015) B203015
theorem B200903 : Blo 131789 200903 := bstep (se 1 (by rfl) ⟨150677, by rfl⟩ : syracuseStep 200903 = 301355) B301355
theorem B135367 : Blo 131789 135367 := bstep (se 1 (by rfl) ⟨101525, by rfl⟩ : syracuseStep 135367 = 203051) B203051
theorem B135387 : Blo 131789 135387 := bstep (se 1 (by rfl) ⟨101540, by rfl⟩ : syracuseStep 135387 = 203081) B203081
theorem B135463 : Blo 131789 135463 := bstep (se 1 (by rfl) ⟨101597, by rfl⟩ : syracuseStep 135463 = 203195) B203195
theorem B2068811 : Blo 131789 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B135503 : Blo 131789 135503 := bstep (se 1 (by rfl) ⟨101627, by rfl⟩ : syracuseStep 135503 = 203255) B203255
theorem B135519 : Blo 131789 135519 := bstep (se 1 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 135519 = 203279) B203279
theorem B201065 : Blo 131789 201065 := bstep (se 2 (by rfl) ⟨75399, by rfl⟩ : syracuseStep 201065 = 150799) B150799
theorem B135547 : Blo 131789 135547 := bstep (se 1 (by rfl) ⟨101660, by rfl⟩ : syracuseStep 135547 = 203321) B203321
theorem B364925 : Blo 131789 364925 := bstep (se 3 (by rfl) ⟨68423, by rfl⟩ : syracuseStep 364925 = 136847) B136847
theorem B135599 : Blo 131789 135599 := bstep (se 1 (by rfl) ⟨101699, by rfl⟩ : syracuseStep 135599 = 203399) B203399
theorem B201143 : Blo 131789 201143 := bstep (se 1 (by rfl) ⟨150857, by rfl⟩ : syracuseStep 201143 = 301715) B301715
theorem B135623 : Blo 131789 135623 := bstep (se 1 (by rfl) ⟨101717, by rfl⟩ : syracuseStep 135623 = 203435) B203435
theorem B299483 : Blo 131789 299483 := bstep (se 1 (by rfl) ⟨224612, by rfl⟩ : syracuseStep 299483 = 449225) B449225
theorem B201179 : Blo 131789 201179 := bstep (se 1 (by rfl) ⟨150884, by rfl⟩ : syracuseStep 201179 = 301769) B301769
theorem B430555 : Blo 131789 430555 := bstep (se 1 (by rfl) ⟨322916, by rfl⟩ : syracuseStep 430555 = 645833) B645833
theorem B135643 : Blo 131789 135643 := bstep (se 1 (by rfl) ⟨101732, by rfl⟩ : syracuseStep 135643 = 203465) B203465
theorem B1511945 : Blo 131789 1511945 := bstep (se 2 (by rfl) ⟨566979, by rfl⟩ : syracuseStep 1511945 = 1133959) B1133959
theorem B135719 : Blo 131789 135719 := bstep (se 1 (by rfl) ⟨101789, by rfl⟩ : syracuseStep 135719 = 203579) B203579
theorem B135759 : Blo 131789 135759 := bstep (se 1 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 135759 = 203639) B203639
theorem B135775 : Blo 131789 135775 := bstep (se 1 (by rfl) ⟨101831, by rfl⟩ : syracuseStep 135775 = 203663) B203663
theorem B168571 : Blo 131789 168571 := bstep (se 1 (by rfl) ⟨126428, by rfl⟩ : syracuseStep 168571 = 252857) B252857
theorem B955165 : Blo 131789 955165 := bstep (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) B358187
theorem B168799 : Blo 131789 168799 := bstep (se 1 (by rfl) ⟨126599, by rfl⟩ : syracuseStep 168799 = 253199) B253199
theorem B299951 : Blo 131789 299951 := bstep (se 1 (by rfl) ⟨224963, by rfl⟩ : syracuseStep 299951 = 449927) B449927
theorem B201647 : Blo 131789 201647 := bstep (se 1 (by rfl) ⟨151235, by rfl⟩ : syracuseStep 201647 = 302471) B302471
theorem B201737 : Blo 131789 201737 := bstep (se 2 (by rfl) ⟨75651, by rfl⟩ : syracuseStep 201737 = 151303) B151303
theorem B201767 : Blo 131789 201767 := bstep (se 1 (by rfl) ⟨151325, by rfl⟩ : syracuseStep 201767 = 302651) B302651
theorem B201851 : Blo 131789 201851 := bstep (se 1 (by rfl) ⟨151388, by rfl⟩ : syracuseStep 201851 = 302777) B302777
theorem B300203 : Blo 131789 300203 := bstep (se 1 (by rfl) ⟨225152, by rfl⟩ : syracuseStep 300203 = 450305) B450305
theorem B201977 : Blo 131789 201977 := bstep (se 2 (by rfl) ⟨75741, by rfl⟩ : syracuseStep 201977 = 151483) B151483
theorem B202079 : Blo 131789 202079 := bstep (se 1 (by rfl) ⟨151559, by rfl⟩ : syracuseStep 202079 = 303119) B303119
theorem B202091 : Blo 131789 202091 := bstep (se 1 (by rfl) ⟨151568, by rfl⟩ : syracuseStep 202091 = 303137) B303137
theorem B431489 : Blo 131789 431489 := bstep (se 2 (by rfl) ⟨161808, by rfl⟩ : syracuseStep 431489 = 323617) B323617
theorem B169391 : Blo 131789 169391 := bstep (se 1 (by rfl) ⟨127043, by rfl⟩ : syracuseStep 169391 = 254087) B254087
theorem B923081 : Blo 131789 923081 := bstep (se 2 (by rfl) ⟨346155, by rfl⟩ : syracuseStep 923081 = 692311) B692311
theorem B202319 : Blo 131789 202319 := bstep (se 1 (by rfl) ⟨151739, by rfl⟩ : syracuseStep 202319 = 303479) B303479
theorem B300743 : Blo 131789 300743 := bstep (se 1 (by rfl) ⟨225557, by rfl⟩ : syracuseStep 300743 = 451115) B451115
theorem B202439 : Blo 131789 202439 := bstep (se 1 (by rfl) ⟨151829, by rfl⟩ : syracuseStep 202439 = 303659) B303659
theorem B202601 : Blo 131789 202601 := bstep (se 2 (by rfl) ⟨75975, by rfl⟩ : syracuseStep 202601 = 151951) B151951
theorem B202679 : Blo 131789 202679 := bstep (se 1 (by rfl) ⟨152009, by rfl⟩ : syracuseStep 202679 = 304019) B304019
theorem B202715 : Blo 131789 202715 := bstep (se 1 (by rfl) ⟨152036, by rfl⟩ : syracuseStep 202715 = 304073) B304073
theorem B858127 : Blo 131789 858127 := bstep (se 1 (by rfl) ⟨643595, by rfl⟩ : syracuseStep 858127 = 1287191) B1287191
theorem B1021967 : Blo 131789 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B366839 : Blo 131789 366839 := bstep (se 1 (by rfl) ⟨275129, by rfl⟩ : syracuseStep 366839 = 550259) B550259
theorem B2332961 : Blo 131789 2332961 := bstep (se 2 (by rfl) ⟨874860, by rfl⟩ : syracuseStep 2332961 = 1749721) B1749721
theorem B203183 : Blo 131789 203183 := bstep (se 1 (by rfl) ⟨152387, by rfl⟩ : syracuseStep 203183 = 304775) B304775
theorem B203273 : Blo 131789 203273 := bstep (se 2 (by rfl) ⟨76227, by rfl⟩ : syracuseStep 203273 = 152455) B152455
theorem B301607 : Blo 131789 301607 := bstep (se 1 (by rfl) ⟨226205, by rfl⟩ : syracuseStep 301607 = 452411) B452411
theorem B203303 : Blo 131789 203303 := bstep (se 1 (by rfl) ⟨152477, by rfl⟩ : syracuseStep 203303 = 304955) B304955
theorem B203387 : Blo 131789 203387 := bstep (se 1 (by rfl) ⟨152540, by rfl⟩ : syracuseStep 203387 = 305081) B305081
theorem B7740035 : Blo 131789 7740035 := bstep (se 1 (by rfl) ⟨5805026, by rfl⟩ : syracuseStep 7740035 = 11610053) B11610053
theorem B760529 : Blo 131789 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B203513 : Blo 131789 203513 := bstep (se 2 (by rfl) ⟨76317, by rfl⟩ : syracuseStep 203513 = 152635) B152635
theorem B203615 : Blo 131789 203615 := bstep (se 1 (by rfl) ⟨152711, by rfl⟩ : syracuseStep 203615 = 305423) B305423
theorem B301931 : Blo 131789 301931 := bstep (se 1 (by rfl) ⟨226448, by rfl⟩ : syracuseStep 301931 = 452897) B452897
theorem B203627 : Blo 131789 203627 := bstep (se 1 (by rfl) ⟨152720, by rfl⟩ : syracuseStep 203627 = 305441) B305441
theorem B301985 : Blo 131789 301985 := bstep (se 2 (by rfl) ⟨113244, by rfl⟩ : syracuseStep 301985 = 226489) B226489
theorem B957359 : Blo 131789 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B760985 : Blo 131789 760985 := bstep (se 2 (by rfl) ⟨285369, by rfl⟩ : syracuseStep 760985 = 570739) B570739
theorem B302327 : Blo 131789 302327 := bstep (se 1 (by rfl) ⟨226745, by rfl⟩ : syracuseStep 302327 = 453491) B453491
theorem B466319 : Blo 131789 466319 := bstep (se 1 (by rfl) ⟨349739, by rfl⟩ : syracuseStep 466319 = 699479) B699479
theorem B302921 : Blo 131789 302921 := bstep (se 2 (by rfl) ⟨113595, by rfl⟩ : syracuseStep 302921 = 227191) B227191
theorem B237575 : Blo 131789 237575 := bstep (se 1 (by rfl) ⟨178181, by rfl⟩ : syracuseStep 237575 = 356363) B356363
theorem B2072753 : Blo 131789 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B336271 : Blo 131789 336271 := bstep (se 1 (by rfl) ⟨252203, by rfl⟩ : syracuseStep 336271 = 504407) B504407
theorem B303713 : Blo 131789 303713 := bstep (se 2 (by rfl) ⟨113892, by rfl⟩ : syracuseStep 303713 = 227785) B227785
theorem B336595 : Blo 131789 336595 := bstep (se 1 (by rfl) ⟨252446, by rfl⟩ : syracuseStep 336595 = 504893) B504893
theorem B369481 : Blo 131789 369481 := bstep (se 2 (by rfl) ⟨138555, by rfl⟩ : syracuseStep 369481 = 277111) B277111
theorem B304055 : Blo 131789 304055 := bstep (se 1 (by rfl) ⟨228041, by rfl⟩ : syracuseStep 304055 = 456083) B456083
theorem B205903 : Blo 131789 205903 := bstep (se 1 (by rfl) ⟨154427, by rfl⟩ : syracuseStep 205903 = 308855) B308855
theorem B926923 : Blo 131789 926923 := bstep (se 1 (by rfl) ⟨695192, by rfl⟩ : syracuseStep 926923 = 1390385) B1390385
theorem B1746137 : Blo 131789 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B763127 : Blo 131789 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B304649 : Blo 131789 304649 := bstep (se 2 (by rfl) ⟨114243, by rfl⟩ : syracuseStep 304649 = 228487) B228487
theorem B960011 : Blo 131789 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B337547 : Blo 131789 337547 := bstep (se 1 (by rfl) ⟨253160, by rfl⟩ : syracuseStep 337547 = 506321) B506321
theorem B2762387 : Blo 131789 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B960299 : Blo 131789 960299 := bstep (se 1 (by rfl) ⟨720224, by rfl⟩ : syracuseStep 960299 = 1440449) B1440449
theorem B304991 : Blo 131789 304991 := bstep (se 1 (by rfl) ⟨228743, by rfl⟩ : syracuseStep 304991 = 457487) B457487
theorem B174043 : Blo 131789 174043 := bstep (se 1 (by rfl) ⟨130532, by rfl⟩ : syracuseStep 174043 = 261065) B261065
theorem B305171 : Blo 131789 305171 := bstep (se 1 (by rfl) ⟨228878, by rfl⟩ : syracuseStep 305171 = 457757) B457757
theorem B3385475 : Blo 131789 3385475 := bstep (se 1 (by rfl) ⟨2539106, by rfl⟩ : syracuseStep 3385475 = 5078213) B5078213
theorem B305513 : Blo 131789 305513 := bstep (se 2 (by rfl) ⟨114567, by rfl⟩ : syracuseStep 305513 = 229135) B229135
theorem B502145 : Blo 131789 502145 := bstep (se 2 (by rfl) ⟨188304, by rfl⟩ : syracuseStep 502145 = 376609) B376609
theorem B502159 : Blo 131789 502159 := bstep (se 1 (by rfl) ⟨376619, by rfl⟩ : syracuseStep 502159 = 753239) B753239
theorem B1812887 : Blo 131789 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B338681 : Blo 131789 338681 := bstep (se 2 (by rfl) ⟨127005, by rfl⟩ : syracuseStep 338681 = 254011) B254011
theorem B1551251 : Blo 131789 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B338863 : Blo 131789 338863 := bstep (se 1 (by rfl) ⟨254147, by rfl⟩ : syracuseStep 338863 = 508295) B508295
theorem B535709 : Blo 131789 535709 := bstep (se 3 (by rfl) ⟨100445, by rfl⟩ : syracuseStep 535709 = 200891) B200891
theorem B339329 : Blo 131789 339329 := bstep (se 2 (by rfl) ⟨127248, by rfl⟩ : syracuseStep 339329 = 254497) B254497
theorem B503435 : Blo 131789 503435 := bstep (se 1 (by rfl) ⟨377576, by rfl⟩ : syracuseStep 503435 = 755153) B755153
theorem B339785 : Blo 131789 339785 := bstep (se 2 (by rfl) ⟨127419, by rfl⟩ : syracuseStep 339785 = 254839) B254839
theorem B667763 : Blo 131789 667763 := bstep (se 1 (by rfl) ⟨500822, by rfl⟩ : syracuseStep 667763 = 1001645) B1001645
theorem B340139 : Blo 131789 340139 := bstep (se 1 (by rfl) ⟨255104, by rfl⟩ : syracuseStep 340139 = 510209) B510209
theorem B438443 : Blo 131789 438443 := bstep (se 1 (by rfl) ⟨328832, by rfl⟩ : syracuseStep 438443 = 657665) B657665
theorem B3649853 : Blo 131789 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B602473 : Blo 131789 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B1290775 : Blo 131789 1290775 := bstep (se 1 (by rfl) ⟨968081, by rfl⟩ : syracuseStep 1290775 = 1936163) B1936163
theorem B2175587 : Blo 131789 2175587 := bstep (se 1 (by rfl) ⟨1631690, by rfl⟩ : syracuseStep 2175587 = 3263381) B3263381
theorem B10138385 : Blo 131789 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B340919 : Blo 131789 340919 := bstep (se 1 (by rfl) ⟨255689, by rfl⟩ : syracuseStep 340919 = 511379) B511379
theorem B439303 : Blo 131789 439303 := bstep (se 1 (by rfl) ⟨329477, by rfl⟩ : syracuseStep 439303 = 658955) B658955
theorem B538093 : Blo 131789 538093 := bstep (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) B201785
theorem B669383 : Blo 131789 669383 := bstep (se 1 (by rfl) ⟨502037, by rfl⟩ : syracuseStep 669383 = 1004075) B1004075
theorem B341921 : Blo 131789 341921 := bstep (se 2 (by rfl) ⟨128220, by rfl⟩ : syracuseStep 341921 = 256441) B256441
theorem B637085 : Blo 131789 637085 := bstep (se 3 (by rfl) ⟨119453, by rfl⟩ : syracuseStep 637085 = 238907) B238907
theorem B1718561 : Blo 131789 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B26589505 : Blo 131789 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B342377 : Blo 131789 342377 := bstep (se 2 (by rfl) ⟨128391, by rfl⟩ : syracuseStep 342377 = 256783) B256783
theorem B342401 : Blo 131789 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B342967 : Blo 131789 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B506807 : Blo 131789 506807 := bstep (se 1 (by rfl) ⟨380105, by rfl⟩ : syracuseStep 506807 = 760211) B760211
theorem B244667 : Blo 131789 244667 := bstep (se 1 (by rfl) ⟨183500, by rfl⟩ : syracuseStep 244667 = 367001) B367001
theorem B343561 : Blo 131789 343561 := bstep (se 2 (by rfl) ⟨128835, by rfl⟩ : syracuseStep 343561 = 257671) B257671
theorem B179911 : Blo 131789 179911 := bstep (se 1 (by rfl) ⟨134933, by rfl⟩ : syracuseStep 179911 = 269867) B269867
theorem B966467 : Blo 131789 966467 := bstep (se 1 (by rfl) ⟨724850, by rfl⟩ : syracuseStep 966467 = 1449701) B1449701
theorem B507809 : Blo 131789 507809 := bstep (se 2 (by rfl) ⟨190428, by rfl⟩ : syracuseStep 507809 = 380857) B380857
theorem B769985 : Blo 131789 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B180473 : Blo 131789 180473 := bstep (se 2 (by rfl) ⟨67677, by rfl⟩ : syracuseStep 180473 = 135355) B135355
theorem B508265 : Blo 131789 508265 := bstep (se 2 (by rfl) ⟨190599, by rfl⟩ : syracuseStep 508265 = 381199) B381199
theorem B246199 : Blo 131789 246199 := bstep (se 1 (by rfl) ⟨184649, by rfl⟩ : syracuseStep 246199 = 369299) B369299
theorem B443243 : Blo 131789 443243 := bstep (se 1 (by rfl) ⟨332432, by rfl⟩ : syracuseStep 443243 = 664865) B664865
theorem B508781 : Blo 131789 508781 := bstep (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) B190793
theorem B1131569 : Blo 131789 1131569 := bstep (se 2 (by rfl) ⟨424338, by rfl⟩ : syracuseStep 1131569 = 848677) B848677
theorem B541811 : Blo 131789 541811 := bstep (se 1 (by rfl) ⟨406358, by rfl⟩ : syracuseStep 541811 = 812717) B812717
theorem B148603 : Blo 131789 148603 := bstep (se 1 (by rfl) ⟨111452, by rfl⟩ : syracuseStep 148603 = 222905) B222905
theorem B509449 : Blo 131789 509449 := bstep (se 2 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 509449 = 382087) B382087
theorem B149071 : Blo 131789 149071 := bstep (se 1 (by rfl) ⟨111803, by rfl⟩ : syracuseStep 149071 = 223607) B223607
theorem B411259 : Blo 131789 411259 := bstep (se 1 (by rfl) ⟨308444, by rfl⟩ : syracuseStep 411259 = 616889) B616889
theorem B378557 : Blo 131789 378557 := bstep (se 3 (by rfl) ⟨70979, by rfl⟩ : syracuseStep 378557 = 141959) B141959
theorem B1001159 : Blo 131789 1001159 := bstep (se 1 (by rfl) ⟨750869, by rfl⟩ : syracuseStep 1001159 = 1501739) B1501739
theorem B345799 : Blo 131789 345799 := bstep (se 1 (by rfl) ⟨259349, by rfl⟩ : syracuseStep 345799 = 518699) B518699
theorem B476921 : Blo 131789 476921 := bstep (se 2 (by rfl) ⟨178845, by rfl⟩ : syracuseStep 476921 = 357691) B357691
theorem B4638617 : Blo 131789 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B149467 : Blo 131789 149467 := bstep (se 1 (by rfl) ⟨112100, by rfl⟩ : syracuseStep 149467 = 224201) B224201
theorem B1427557 : Blo 131789 1427557 := bstep (se 4 (by rfl) ⟨133833, by rfl⟩ : syracuseStep 1427557 = 267667) B267667
theorem B575849 : Blo 131789 575849 := bstep (se 2 (by rfl) ⟨215943, by rfl⟩ : syracuseStep 575849 = 431887) B431887
theorem B444797 : Blo 131789 444797 := bstep (se 3 (by rfl) ⟨83399, by rfl⟩ : syracuseStep 444797 = 166799) B166799
theorem B149935 : Blo 131789 149935 := bstep (se 1 (by rfl) ⟨112451, by rfl⟩ : syracuseStep 149935 = 224903) B224903
theorem B445067 : Blo 131789 445067 := bstep (se 1 (by rfl) ⟨333800, by rfl⟩ : syracuseStep 445067 = 667601) B667601
theorem B150367 : Blo 131789 150367 := bstep (se 1 (by rfl) ⟨112775, by rfl⟩ : syracuseStep 150367 = 225551) B225551
theorem B510907 : Blo 131789 510907 := bstep (se 1 (by rfl) ⟨383180, by rfl⟩ : syracuseStep 510907 = 766361) B766361
theorem B150727 : Blo 131789 150727 := bstep (se 1 (by rfl) ⟨113045, by rfl⟩ : syracuseStep 150727 = 226091) B226091
theorem B675215 : Blo 131789 675215 := bstep (se 1 (by rfl) ⟨506411, by rfl⟩ : syracuseStep 675215 = 1012823) B1012823
theorem B970157 : Blo 131789 970157 := bstep (se 3 (by rfl) ⟨181904, by rfl⟩ : syracuseStep 970157 = 363809) B363809
theorem B445985 : Blo 131789 445985 := bstep (se 2 (by rfl) ⟨167244, by rfl⟩ : syracuseStep 445985 = 334489) B334489
theorem B380513 : Blo 131789 380513 := bstep (se 2 (by rfl) ⟨142692, by rfl⟩ : syracuseStep 380513 = 285385) B285385
theorem B511697 : Blo 131789 511697 := bstep (se 2 (by rfl) ⟨191886, by rfl⟩ : syracuseStep 511697 = 383773) B383773
theorem B446201 : Blo 131789 446201 := bstep (se 2 (by rfl) ⟨167325, by rfl⟩ : syracuseStep 446201 = 334651) B334651
theorem B446471 : Blo 131789 446471 := bstep (se 1 (by rfl) ⟨334853, by rfl⟩ : syracuseStep 446471 = 669707) B669707
theorem B3821579 : Blo 131789 3821579 := bstep (se 1 (by rfl) ⟨2866184, by rfl⟩ : syracuseStep 3821579 = 5732369) B5732369
theorem B872477 : Blo 131789 872477 := bstep (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) B327179
theorem B151591 : Blo 131789 151591 := bstep (se 1 (by rfl) ⟨113693, by rfl⟩ : syracuseStep 151591 = 227387) B227387
theorem B446579 : Blo 131789 446579 := bstep (se 1 (by rfl) ⟨334934, by rfl⟩ : syracuseStep 446579 = 669869) B669869
theorem B512153 : Blo 131789 512153 := bstep (se 2 (by rfl) ⟨192057, by rfl⟩ : syracuseStep 512153 = 384115) B384115
theorem B446849 : Blo 131789 446849 := bstep (se 2 (by rfl) ⟨167568, by rfl⟩ : syracuseStep 446849 = 335137) B335137
theorem B381449 : Blo 131789 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B250465 : Blo 131789 250465 := bstep (se 2 (by rfl) ⟨93924, by rfl⟩ : syracuseStep 250465 = 187849) B187849
theorem B480107 : Blo 131789 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B3724289 : Blo 131789 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B447659 : Blo 131789 447659 := bstep (se 1 (by rfl) ⟨335744, by rfl⟩ : syracuseStep 447659 = 671489) B671489
theorem B972121 : Blo 131789 972121 := bstep (se 2 (by rfl) ⟨364545, by rfl⟩ : syracuseStep 972121 = 729091) B729091
theorem B677321 : Blo 131789 677321 := bstep (se 2 (by rfl) ⟨253995, by rfl⟩ : syracuseStep 677321 = 507991) B507991
theorem B284123 : Blo 131789 284123 := bstep (se 1 (by rfl) ⟨213092, by rfl⟩ : syracuseStep 284123 = 426185) B426185
theorem B251399 : Blo 131789 251399 := bstep (se 1 (by rfl) ⟨188549, by rfl⟩ : syracuseStep 251399 = 377099) B377099
theorem B1529441 : Blo 131789 1529441 := bstep (se 2 (by rfl) ⟨573540, by rfl⟩ : syracuseStep 1529441 = 1147081) B1147081
theorem B644755 : Blo 131789 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B448199 : Blo 131789 448199 := bstep (se 1 (by rfl) ⟨336149, by rfl⟩ : syracuseStep 448199 = 672299) B672299
theorem B382907 : Blo 131789 382907 := bstep (se 1 (by rfl) ⟨287180, by rfl⟩ : syracuseStep 382907 = 574361) B574361
theorem B251923 : Blo 131789 251923 := bstep (se 1 (by rfl) ⟨188942, by rfl⟩ : syracuseStep 251923 = 377885) B377885
theorem B514127 : Blo 131789 514127 := bstep (se 1 (by rfl) ⟨385595, by rfl⟩ : syracuseStep 514127 = 771191) B771191
theorem B677969 : Blo 131789 677969 := bstep (se 2 (by rfl) ⟨254238, by rfl⟩ : syracuseStep 677969 = 508477) B508477
theorem B317611 : Blo 131789 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B514295 : Blo 131789 514295 := bstep (se 1 (by rfl) ⟨385721, by rfl⟩ : syracuseStep 514295 = 771443) B771443
theorem B907649 : Blo 131789 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B449063 : Blo 131789 449063 := bstep (se 1 (by rfl) ⟨336797, by rfl⟩ : syracuseStep 449063 = 673595) B673595
theorem B449171 : Blo 131789 449171 := bstep (se 1 (by rfl) ⟨336878, by rfl⟩ : syracuseStep 449171 = 673757) B673757
theorem B449387 : Blo 131789 449387 := bstep (se 1 (by rfl) ⟨337040, by rfl⟩ : syracuseStep 449387 = 674081) B674081
theorem B449441 : Blo 131789 449441 := bstep (se 2 (by rfl) ⟨168540, by rfl⟩ : syracuseStep 449441 = 337081) B337081
theorem B285601 : Blo 131789 285601 := bstep (se 2 (by rfl) ⟨107100, by rfl⟩ : syracuseStep 285601 = 214201) B214201
theorem B482311 : Blo 131789 482311 := bstep (se 1 (by rfl) ⟨361733, by rfl⟩ : syracuseStep 482311 = 723467) B723467
theorem B515267 : Blo 131789 515267 := bstep (se 1 (by rfl) ⟨386450, by rfl⟩ : syracuseStep 515267 = 772901) B772901
theorem B285943 : Blo 131789 285943 := bstep (se 1 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 285943 = 428915) B428915
theorem B1006991 : Blo 131789 1006991 := bstep (se 1 (by rfl) ⟨755243, by rfl⟩ : syracuseStep 1006991 = 1510487) B1510487
theorem B450035 : Blo 131789 450035 := bstep (se 1 (by rfl) ⟨337526, by rfl⟩ : syracuseStep 450035 = 675053) B675053
theorem B1302155 : Blo 131789 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B810643 : Blo 131789 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B450575 : Blo 131789 450575 := bstep (se 1 (by rfl) ⟨337931, by rfl⟩ : syracuseStep 450575 = 675863) B675863
theorem B188777 : Blo 131789 188777 := bstep (se 2 (by rfl) ⟨70791, by rfl⟩ : syracuseStep 188777 = 141583) B141583
theorem B254315 : Blo 131789 254315 := bstep (se 1 (by rfl) ⟨190736, by rfl⟩ : syracuseStep 254315 = 381473) B381473
theorem B451169 : Blo 131789 451169 := bstep (se 2 (by rfl) ⟨169188, by rfl⟩ : syracuseStep 451169 = 338377) B338377
theorem B22438853 : Blo 131789 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B254983 : Blo 131789 254983 := bstep (se 1 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 254983 = 382475) B382475
theorem B976151 : Blo 131789 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B5432741 : Blo 131789 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B255545 : Blo 131789 255545 := bstep (se 2 (by rfl) ⟨95829, by rfl⟩ : syracuseStep 255545 = 191659) B191659
theorem B845549 : Blo 131789 845549 := bstep (se 3 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 845549 = 317081) B317081
theorem B190201 : Blo 131789 190201 := bstep (se 2 (by rfl) ⟨71325, by rfl⟩ : syracuseStep 190201 = 142651) B142651
theorem B649079 : Blo 131789 649079 := bstep (se 1 (by rfl) ⟨486809, by rfl⟩ : syracuseStep 649079 = 973619) B973619
theorem B321455 : Blo 131789 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B714689 : Blo 131789 714689 := bstep (se 2 (by rfl) ⟨268008, by rfl⟩ : syracuseStep 714689 = 536017) B536017
theorem B1632209 : Blo 131789 1632209 := bstep (se 2 (by rfl) ⟨612078, by rfl⟩ : syracuseStep 1632209 = 1224157) B1224157
theorem B223195 : Blo 131789 223195 := bstep (se 1 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 223195 = 334793) B334793
theorem B452627 : Blo 131789 452627 := bstep (se 1 (by rfl) ⟨339470, by rfl⟩ : syracuseStep 452627 = 678941) B678941
theorem B288787 : Blo 131789 288787 := bstep (se 1 (by rfl) ⟨216590, by rfl⟩ : syracuseStep 288787 = 433181) B433181
theorem B452951 : Blo 131789 452951 := bstep (se 1 (by rfl) ⟨339713, by rfl⟩ : syracuseStep 452951 = 679427) B679427
theorem B289129 : Blo 131789 289129 := bstep (se 2 (by rfl) ⟨108423, by rfl⟩ : syracuseStep 289129 = 216847) B216847
theorem B682505 : Blo 131789 682505 := bstep (se 2 (by rfl) ⟨255939, by rfl⟩ : syracuseStep 682505 = 511879) B511879
theorem B223823 : Blo 131789 223823 := bstep (se 1 (by rfl) ⟨167867, by rfl⟩ : syracuseStep 223823 = 335735) B335735
theorem B977771 : Blo 131789 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B257033 : Blo 131789 257033 := bstep (se 2 (by rfl) ⟨96387, by rfl⟩ : syracuseStep 257033 = 192775) B192775
theorem B322579 : Blo 131789 322579 := bstep (se 1 (by rfl) ⟨241934, by rfl⟩ : syracuseStep 322579 = 483869) B483869
theorem B977999 : Blo 131789 977999 := bstep (se 1 (by rfl) ⟨733499, by rfl⟩ : syracuseStep 977999 = 1466999) B1466999
theorem B454031 : Blo 131789 454031 := bstep (se 1 (by rfl) ⟨340523, by rfl⟩ : syracuseStep 454031 = 681047) B681047
theorem B224687 : Blo 131789 224687 := bstep (se 1 (by rfl) ⟨168515, by rfl⟩ : syracuseStep 224687 = 337031) B337031
theorem B454355 : Blo 131789 454355 := bstep (se 1 (by rfl) ⟨340766, by rfl⟩ : syracuseStep 454355 = 681533) B681533
theorem B4091681 : Blo 131789 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B225119 : Blo 131789 225119 := bstep (se 1 (by rfl) ⟨168839, by rfl⟩ : syracuseStep 225119 = 337679) B337679
theorem B9629603 : Blo 131789 9629603 := bstep (se 1 (by rfl) ⟨7222202, by rfl⟩ : syracuseStep 9629603 = 14444405) B14444405
theorem B683963 : Blo 131789 683963 := bstep (se 1 (by rfl) ⟨512972, by rfl⟩ : syracuseStep 683963 = 1025945) B1025945
theorem B880577 : Blo 131789 880577 := bstep (se 2 (by rfl) ⟨330216, by rfl⟩ : syracuseStep 880577 = 660433) B660433
theorem B618653 : Blo 131789 618653 := bstep (se 3 (by rfl) ⟨115997, by rfl⟩ : syracuseStep 618653 = 231995) B231995
theorem B323945 : Blo 131789 323945 := bstep (se 2 (by rfl) ⟨121479, by rfl⟩ : syracuseStep 323945 = 242959) B242959
theorem B225679 : Blo 131789 225679 := bstep (se 1 (by rfl) ⟨169259, by rfl⟩ : syracuseStep 225679 = 338519) B338519
theorem B160175 : Blo 131789 160175 := bstep (se 1 (by rfl) ⟨120131, by rfl⟩ : syracuseStep 160175 = 240263) B240263
theorem B324425 : Blo 131789 324425 := bstep (se 2 (by rfl) ⟨121659, by rfl⟩ : syracuseStep 324425 = 243319) B243319
theorem B455543 : Blo 131789 455543 := bstep (se 1 (by rfl) ⟨341657, by rfl⟩ : syracuseStep 455543 = 683315) B683315
theorem B914323 : Blo 131789 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B226361 : Blo 131789 226361 := bstep (se 2 (by rfl) ⟨84885, by rfl⟩ : syracuseStep 226361 = 169771) B169771
theorem B160847 : Blo 131789 160847 := bstep (se 1 (by rfl) ⟨120635, by rfl⟩ : syracuseStep 160847 = 241271) B241271
theorem B455759 : Blo 131789 455759 := bstep (se 1 (by rfl) ⟨341819, by rfl⟩ : syracuseStep 455759 = 683639) B683639
theorem B423083 : Blo 131789 423083 := bstep (se 1 (by rfl) ⟨317312, by rfl⟩ : syracuseStep 423083 = 634625) B634625
theorem B685259 : Blo 131789 685259 := bstep (se 1 (by rfl) ⟨513944, by rfl⟩ : syracuseStep 685259 = 1027889) B1027889
theorem B3339667 : Blo 131789 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B456137 : Blo 131789 456137 := bstep (se 2 (by rfl) ⟨171051, by rfl⟩ : syracuseStep 456137 = 342103) B342103
theorem B1734155 : Blo 131789 1734155 := bstep (se 1 (by rfl) ⟨1300616, by rfl⟩ : syracuseStep 1734155 = 2601233) B2601233
theorem B1013309 : Blo 131789 1013309 := bstep (se 3 (by rfl) ⟨189995, by rfl⟩ : syracuseStep 1013309 = 379991) B379991
theorem B259681 : Blo 131789 259681 := bstep (se 2 (by rfl) ⟨97380, by rfl⟩ : syracuseStep 259681 = 194761) B194761
theorem B456407 : Blo 131789 456407 := bstep (se 1 (by rfl) ⟨342305, by rfl⟩ : syracuseStep 456407 = 684611) B684611
theorem B227063 : Blo 131789 227063 := bstep (se 1 (by rfl) ⟨170297, by rfl⟩ : syracuseStep 227063 = 340595) B340595
theorem B358319 : Blo 131789 358319 := bstep (se 1 (by rfl) ⟨268739, by rfl⟩ : syracuseStep 358319 = 537479) B537479
theorem B456623 : Blo 131789 456623 := bstep (se 1 (by rfl) ⟨342467, by rfl⟩ : syracuseStep 456623 = 684935) B684935
theorem B325559 : Blo 131789 325559 := bstep (se 1 (by rfl) ⟨244169, by rfl⟩ : syracuseStep 325559 = 488339) B488339
theorem B227407 : Blo 131789 227407 := bstep (se 1 (by rfl) ⟨170555, by rfl⟩ : syracuseStep 227407 = 341111) B341111
theorem B227657 : Blo 131789 227657 := bstep (se 2 (by rfl) ⟨85371, by rfl⟩ : syracuseStep 227657 = 170743) B170743
theorem B6977897 : Blo 131789 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B1112453 : Blo 131789 1112453 := bstep (se 4 (by rfl) ⟨104292, by rfl⟩ : syracuseStep 1112453 = 208585) B208585
theorem B1014281 : Blo 131789 1014281 := bstep (se 2 (by rfl) ⟨380355, by rfl⟩ : syracuseStep 1014281 = 760711) B760711
theorem B1702579 : Blo 131789 1702579 := bstep (se 1 (by rfl) ⟨1276934, by rfl⟩ : syracuseStep 1702579 = 2553869) B2553869
theorem B228089 : Blo 131789 228089 := bstep (se 2 (by rfl) ⟨85533, by rfl⟩ : syracuseStep 228089 = 171067) B171067
theorem B228271 : Blo 131789 228271 := bstep (se 1 (by rfl) ⟨171203, by rfl⟩ : syracuseStep 228271 = 342407) B342407
theorem B228359 : Blo 131789 228359 := bstep (se 1 (by rfl) ⟨171269, by rfl⟩ : syracuseStep 228359 = 342539) B342539
theorem B1375427 : Blo 131789 1375427 := bstep (se 1 (by rfl) ⟨1031570, by rfl⟩ : syracuseStep 1375427 = 2063141) B2063141
theorem B228703 : Blo 131789 228703 := bstep (se 1 (by rfl) ⟨171527, by rfl⟩ : syracuseStep 228703 = 343055) B343055
theorem B228791 : Blo 131789 228791 := bstep (se 1 (by rfl) ⟨171593, by rfl⟩ : syracuseStep 228791 = 343187) B343187
theorem B556583 : Blo 131789 556583 := bstep (se 1 (by rfl) ⟨417437, by rfl⟩ : syracuseStep 556583 = 834875) B834875
theorem B425569 : Blo 131789 425569 := bstep (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) B319177
theorem B1015739 : Blo 131789 1015739 := bstep (se 1 (by rfl) ⟨761804, by rfl⟩ : syracuseStep 1015739 = 1523609) B1523609
theorem B786779 : Blo 131789 786779 := bstep (se 1 (by rfl) ⟨590084, by rfl⟩ : syracuseStep 786779 = 1180169) B1180169
theorem B295495 : Blo 131789 295495 := bstep (se 1 (by rfl) ⟨221621, by rfl⟩ : syracuseStep 295495 = 443243) B443243
theorem B328265 : Blo 131789 328265 := bstep (se 2 (by rfl) ⟨123099, by rfl⟩ : syracuseStep 328265 = 246199) B246199
theorem B754379 : Blo 131789 754379 := bstep (se 1 (by rfl) ⟨565784, by rfl⟩ : syracuseStep 754379 = 1131569) B1131569
theorem B131807 : Blo 131789 131807 := bstep (se 1 (by rfl) ⟨98855, by rfl⟩ : syracuseStep 131807 = 197711) B197711
theorem B361207 : Blo 131789 361207 := bstep (se 1 (by rfl) ⟨270905, by rfl⟩ : syracuseStep 361207 = 541811) B541811
theorem B131887 : Blo 131789 131887 := bstep (se 1 (by rfl) ⟨98915, by rfl⟩ : syracuseStep 131887 = 197831) B197831
theorem B131995 : Blo 131789 131995 := bstep (se 1 (by rfl) ⟨98996, by rfl⟩ : syracuseStep 131995 = 197993) B197993
theorem B132047 : Blo 131789 132047 := bstep (se 1 (by rfl) ⟨99035, by rfl⟩ : syracuseStep 132047 = 198071) B198071
theorem B132071 : Blo 131789 132071 := bstep (se 1 (by rfl) ⟨99053, by rfl⟩ : syracuseStep 132071 = 198107) B198107
theorem B492641 : Blo 131789 492641 := bstep (se 2 (by rfl) ⟨184740, by rfl⟩ : syracuseStep 492641 = 369481) B369481
theorem B427133 : Blo 131789 427133 := bstep (se 3 (by rfl) ⟨80087, by rfl⟩ : syracuseStep 427133 = 160175) B160175
theorem B5506319 : Blo 131789 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B132383 : Blo 131789 132383 := bstep (se 1 (by rfl) ⟨99287, by rfl⟩ : syracuseStep 132383 = 198575) B198575
theorem B197927 : Blo 131789 197927 := bstep (se 1 (by rfl) ⟨148445, by rfl⟩ : syracuseStep 197927 = 296891) B296891
theorem B132443 : Blo 131789 132443 := bstep (se 1 (by rfl) ⟨99332, by rfl⟩ : syracuseStep 132443 = 198665) B198665
theorem B1017197 : Blo 131789 1017197 := bstep (se 3 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 1017197 = 381449) B381449
theorem B132463 : Blo 131789 132463 := bstep (se 1 (by rfl) ⟨99347, by rfl⟩ : syracuseStep 132463 = 198695) B198695
theorem B198011 : Blo 131789 198011 := bstep (se 1 (by rfl) ⟨148508, by rfl⟩ : syracuseStep 198011 = 297017) B297017
theorem B132519 : Blo 131789 132519 := bstep (se 1 (by rfl) ⟨99389, by rfl⟩ : syracuseStep 132519 = 198779) B198779
theorem B198137 : Blo 131789 198137 := bstep (se 2 (by rfl) ⟨74301, by rfl⟩ : syracuseStep 198137 = 148603) B148603
theorem B132603 : Blo 131789 132603 := bstep (se 1 (by rfl) ⟨99452, by rfl⟩ : syracuseStep 132603 = 198905) B198905
theorem B132671 : Blo 131789 132671 := bstep (se 1 (by rfl) ⟨99503, by rfl⟩ : syracuseStep 132671 = 199007) B199007
theorem B132679 : Blo 131789 132679 := bstep (se 1 (by rfl) ⟨99509, by rfl⟩ : syracuseStep 132679 = 199019) B199019
theorem B296531 : Blo 131789 296531 := bstep (se 1 (by rfl) ⟨222398, by rfl⟩ : syracuseStep 296531 = 444797) B444797
theorem B198239 : Blo 131789 198239 := bstep (se 1 (by rfl) ⟨148679, by rfl⟩ : syracuseStep 198239 = 297359) B297359
theorem B132831 : Blo 131789 132831 := bstep (se 1 (by rfl) ⟨99623, by rfl⟩ : syracuseStep 132831 = 199247) B199247
theorem B296711 : Blo 131789 296711 := bstep (se 1 (by rfl) ⟨222533, by rfl⟩ : syracuseStep 296711 = 445067) B445067
theorem B132911 : Blo 131789 132911 := bstep (se 1 (by rfl) ⟨99683, by rfl⟩ : syracuseStep 132911 = 199367) B199367
theorem B198455 : Blo 131789 198455 := bstep (se 1 (by rfl) ⟨148841, by rfl⟩ : syracuseStep 198455 = 297683) B297683
theorem B133019 : Blo 131789 133019 := bstep (se 1 (by rfl) ⟨99764, by rfl⟩ : syracuseStep 133019 = 199529) B199529
theorem B133071 : Blo 131789 133071 := bstep (se 1 (by rfl) ⟨99803, by rfl⟩ : syracuseStep 133071 = 199607) B199607
theorem B133095 : Blo 131789 133095 := bstep (se 1 (by rfl) ⟨99821, by rfl⟩ : syracuseStep 133095 = 199643) B199643
theorem B198761 : Blo 131789 198761 := bstep (se 2 (by rfl) ⟨74535, by rfl⟩ : syracuseStep 198761 = 149071) B149071
theorem B461065 : Blo 131789 461065 := bstep (se 2 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 461065 = 345799) B345799
theorem B1280285 : Blo 131789 1280285 := bstep (se 3 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 1280285 = 480107) B480107
theorem B133407 : Blo 131789 133407 := bstep (se 1 (by rfl) ⟨100055, by rfl⟩ : syracuseStep 133407 = 200111) B200111
theorem B133467 : Blo 131789 133467 := bstep (se 1 (by rfl) ⟨100100, by rfl⟩ : syracuseStep 133467 = 200201) B200201
theorem B264539 : Blo 131789 264539 := bstep (se 1 (by rfl) ⟨198404, by rfl⟩ : syracuseStep 264539 = 396809) B396809
theorem B297323 : Blo 131789 297323 := bstep (se 1 (by rfl) ⟨222992, by rfl⟩ : syracuseStep 297323 = 445985) B445985
theorem B133487 : Blo 131789 133487 := bstep (se 1 (by rfl) ⟨100115, by rfl⟩ : syracuseStep 133487 = 200231) B200231
theorem B199079 : Blo 131789 199079 := bstep (se 1 (by rfl) ⟨149309, by rfl⟩ : syracuseStep 199079 = 298619) B298619
theorem B133543 : Blo 131789 133543 := bstep (se 1 (by rfl) ⟨100157, by rfl⟩ : syracuseStep 133543 = 200315) B200315
theorem B5507531 : Blo 131789 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B297467 : Blo 131789 297467 := bstep (se 1 (by rfl) ⟨223100, by rfl⟩ : syracuseStep 297467 = 446201) B446201
theorem B199163 : Blo 131789 199163 := bstep (se 1 (by rfl) ⟨149372, by rfl⟩ : syracuseStep 199163 = 298745) B298745
theorem B133627 : Blo 131789 133627 := bstep (se 1 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 133627 = 200441) B200441
theorem B133695 : Blo 131789 133695 := bstep (se 1 (by rfl) ⟨100271, by rfl⟩ : syracuseStep 133695 = 200543) B200543
theorem B133703 : Blo 131789 133703 := bstep (se 1 (by rfl) ⟨100277, by rfl⟩ : syracuseStep 133703 = 200555) B200555
theorem B297593 : Blo 131789 297593 := bstep (se 2 (by rfl) ⟨111597, by rfl⟩ : syracuseStep 297593 = 223195) B223195
theorem B199289 : Blo 131789 199289 := bstep (se 2 (by rfl) ⟨74733, by rfl⟩ : syracuseStep 199289 = 149467) B149467
theorem B232057 : Blo 131789 232057 := bstep (se 2 (by rfl) ⟨87021, by rfl⟩ : syracuseStep 232057 = 174043) B174043
theorem B297647 : Blo 131789 297647 := bstep (se 1 (by rfl) ⟨223235, by rfl⟩ : syracuseStep 297647 = 446471) B446471
theorem B199343 : Blo 131789 199343 := bstep (se 1 (by rfl) ⟨149507, by rfl⟩ : syracuseStep 199343 = 299015) B299015
theorem B199391 : Blo 131789 199391 := bstep (se 1 (by rfl) ⟨149543, by rfl⟩ : syracuseStep 199391 = 299087) B299087
theorem B133855 : Blo 131789 133855 := bstep (se 1 (by rfl) ⟨100391, by rfl⟩ : syracuseStep 133855 = 200783) B200783
theorem B297719 : Blo 131789 297719 := bstep (se 1 (by rfl) ⟨223289, by rfl⟩ : syracuseStep 297719 = 446579) B446579
theorem B133935 : Blo 131789 133935 := bstep (se 1 (by rfl) ⟨100451, by rfl⟩ : syracuseStep 133935 = 200903) B200903
theorem B1903409 : Blo 131789 1903409 := bstep (se 2 (by rfl) ⟨713778, by rfl⟩ : syracuseStep 1903409 = 1427557) B1427557
theorem B1379207 : Blo 131789 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B134043 : Blo 131789 134043 := bstep (se 1 (by rfl) ⟨100532, by rfl⟩ : syracuseStep 134043 = 201065) B201065
theorem B297899 : Blo 131789 297899 := bstep (se 1 (by rfl) ⟨223424, by rfl⟩ : syracuseStep 297899 = 446849) B446849
theorem B134095 : Blo 131789 134095 := bstep (se 1 (by rfl) ⟨100571, by rfl⟩ : syracuseStep 134095 = 201143) B201143
theorem B199655 : Blo 131789 199655 := bstep (se 1 (by rfl) ⟨149741, by rfl⟩ : syracuseStep 199655 = 299483) B299483
theorem B134119 : Blo 131789 134119 := bstep (se 1 (by rfl) ⟨100589, by rfl⟩ : syracuseStep 134119 = 201179) B201179
theorem B199913 : Blo 131789 199913 := bstep (se 2 (by rfl) ⟨74967, by rfl⟩ : syracuseStep 199913 = 149935) B149935
theorem B4656365 : Blo 131789 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B199967 : Blo 131789 199967 := bstep (se 1 (by rfl) ⟨149975, by rfl⟩ : syracuseStep 199967 = 299951) B299951
theorem B134431 : Blo 131789 134431 := bstep (se 1 (by rfl) ⟨100823, by rfl⟩ : syracuseStep 134431 = 201647) B201647
theorem B134491 : Blo 131789 134491 := bstep (se 1 (by rfl) ⟨100868, by rfl⟩ : syracuseStep 134491 = 201737) B201737
theorem B134511 : Blo 131789 134511 := bstep (se 1 (by rfl) ⟨100883, by rfl⟩ : syracuseStep 134511 = 201767) B201767
theorem B134567 : Blo 131789 134567 := bstep (se 1 (by rfl) ⟨100925, by rfl⟩ : syracuseStep 134567 = 201851) B201851
theorem B298439 : Blo 131789 298439 := bstep (se 1 (by rfl) ⟨223829, by rfl⟩ : syracuseStep 298439 = 447659) B447659
theorem B200135 : Blo 131789 200135 := bstep (se 1 (by rfl) ⟨150101, by rfl⟩ : syracuseStep 200135 = 300203) B300203
theorem B134651 : Blo 131789 134651 := bstep (se 1 (by rfl) ⟨100988, by rfl⟩ : syracuseStep 134651 = 201977) B201977
theorem B134719 : Blo 131789 134719 := bstep (se 1 (by rfl) ⟨101039, by rfl⟩ : syracuseStep 134719 = 202079) B202079
theorem B134727 : Blo 131789 134727 := bstep (se 1 (by rfl) ⟨101045, by rfl⟩ : syracuseStep 134727 = 202091) B202091
theorem B167599 : Blo 131789 167599 := bstep (se 1 (by rfl) ⟨125699, by rfl⟩ : syracuseStep 167599 = 251399) B251399
theorem B134879 : Blo 131789 134879 := bstep (se 1 (by rfl) ⟨101159, by rfl⟩ : syracuseStep 134879 = 202319) B202319
theorem B1019627 : Blo 131789 1019627 := bstep (se 1 (by rfl) ⟨764720, by rfl⟩ : syracuseStep 1019627 = 1529441) B1529441
theorem B200489 : Blo 131789 200489 := bstep (se 2 (by rfl) ⟨75183, by rfl⟩ : syracuseStep 200489 = 150367) B150367
theorem B298799 : Blo 131789 298799 := bstep (se 1 (by rfl) ⟨224099, by rfl⟩ : syracuseStep 298799 = 448199) B448199
theorem B200495 : Blo 131789 200495 := bstep (se 1 (by rfl) ⟨150371, by rfl⟩ : syracuseStep 200495 = 300743) B300743
theorem B134959 : Blo 131789 134959 := bstep (se 1 (by rfl) ⟨101219, by rfl⟩ : syracuseStep 134959 = 202439) B202439
theorem B2461549 : Blo 131789 2461549 := bstep (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) B923081
theorem B135067 : Blo 131789 135067 := bstep (se 1 (by rfl) ⟨101300, by rfl⟩ : syracuseStep 135067 = 202601) B202601
theorem B135119 : Blo 131789 135119 := bstep (se 1 (by rfl) ⟨101339, by rfl⟩ : syracuseStep 135119 = 202679) B202679
theorem B135143 : Blo 131789 135143 := bstep (se 1 (by rfl) ⟨101357, by rfl⟩ : syracuseStep 135143 = 202715) B202715
theorem B430105 : Blo 131789 430105 := bstep (se 2 (by rfl) ⟨161289, by rfl⟩ : syracuseStep 430105 = 322579) B322579
theorem B200969 : Blo 131789 200969 := bstep (se 2 (by rfl) ⟨75363, by rfl⟩ : syracuseStep 200969 = 150727) B150727
theorem B135455 : Blo 131789 135455 := bstep (se 1 (by rfl) ⟨101591, by rfl⟩ : syracuseStep 135455 = 203183) B203183
theorem B135515 : Blo 131789 135515 := bstep (se 1 (by rfl) ⟨101636, by rfl⟩ : syracuseStep 135515 = 203273) B203273
theorem B299375 : Blo 131789 299375 := bstep (se 1 (by rfl) ⟨224531, by rfl⟩ : syracuseStep 299375 = 449063) B449063
theorem B201071 : Blo 131789 201071 := bstep (se 1 (by rfl) ⟨150803, by rfl⟩ : syracuseStep 201071 = 301607) B301607
theorem B135535 : Blo 131789 135535 := bstep (se 1 (by rfl) ⟨101651, by rfl⟩ : syracuseStep 135535 = 203303) B203303
theorem B135591 : Blo 131789 135591 := bstep (se 1 (by rfl) ⟨101693, by rfl⟩ : syracuseStep 135591 = 203387) B203387
theorem B299447 : Blo 131789 299447 := bstep (se 1 (by rfl) ⟨224585, by rfl⟩ : syracuseStep 299447 = 449171) B449171
theorem B135675 : Blo 131789 135675 := bstep (se 1 (by rfl) ⟨101756, by rfl⟩ : syracuseStep 135675 = 203513) B203513
theorem B135743 : Blo 131789 135743 := bstep (se 1 (by rfl) ⟨101807, by rfl⟩ : syracuseStep 135743 = 203615) B203615
theorem B299591 : Blo 131789 299591 := bstep (se 1 (by rfl) ⟨224693, by rfl⟩ : syracuseStep 299591 = 449387) B449387
theorem B201287 : Blo 131789 201287 := bstep (se 1 (by rfl) ⟨150965, by rfl⟩ : syracuseStep 201287 = 301931) B301931
theorem B135751 : Blo 131789 135751 := bstep (se 1 (by rfl) ⟨101813, by rfl⟩ : syracuseStep 135751 = 203627) B203627
theorem B299627 : Blo 131789 299627 := bstep (se 1 (by rfl) ⟨224720, by rfl⟩ : syracuseStep 299627 = 449441) B449441
theorem B201323 : Blo 131789 201323 := bstep (se 1 (by rfl) ⟨150992, by rfl⟩ : syracuseStep 201323 = 301985) B301985
theorem B201551 : Blo 131789 201551 := bstep (se 1 (by rfl) ⟨151163, by rfl⟩ : syracuseStep 201551 = 302327) B302327
theorem B300023 : Blo 131789 300023 := bstep (se 1 (by rfl) ⟨225017, by rfl⟩ : syracuseStep 300023 = 450035) B450035
theorem B857213 : Blo 131789 857213 := bstep (se 3 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 857213 = 321455) B321455
theorem B1021085 : Blo 131789 1021085 := bstep (se 3 (by rfl) ⟨191453, by rfl⟩ : syracuseStep 1021085 = 382907) B382907
theorem B201947 : Blo 131789 201947 := bstep (se 1 (by rfl) ⟨151460, by rfl⟩ : syracuseStep 201947 = 302921) B302921
theorem B300383 : Blo 131789 300383 := bstep (se 1 (by rfl) ⟨225287, by rfl⟩ : syracuseStep 300383 = 450575) B450575
theorem B202121 : Blo 131789 202121 := bstep (se 2 (by rfl) ⟨75795, by rfl⟩ : syracuseStep 202121 = 151591) B151591
theorem B1381835 : Blo 131789 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B169543 : Blo 131789 169543 := bstep (se 1 (by rfl) ⟨127157, by rfl⟩ : syracuseStep 169543 = 254315) B254315
theorem B300779 : Blo 131789 300779 := bstep (se 1 (by rfl) ⟨225584, by rfl⟩ : syracuseStep 300779 = 451169) B451169
theorem B202475 : Blo 131789 202475 := bstep (se 1 (by rfl) ⟨151856, by rfl⟩ : syracuseStep 202475 = 303713) B303713
theorem B5936885 : Blo 131789 5936885 := bstep (se 5 (by rfl) ⟨278291, by rfl⟩ : syracuseStep 5936885 = 556583) B556583
theorem B300905 : Blo 131789 300905 := bstep (se 2 (by rfl) ⟨112839, by rfl⟩ : syracuseStep 300905 = 225679) B225679
theorem B202703 : Blo 131789 202703 := bstep (se 1 (by rfl) ⟨152027, by rfl⟩ : syracuseStep 202703 = 304055) B304055
theorem B333953 : Blo 131789 333953 := bstep (se 2 (by rfl) ⟨125232, by rfl⟩ : syracuseStep 333953 = 250465) B250465
theorem B203099 : Blo 131789 203099 := bstep (se 1 (by rfl) ⟨152324, by rfl⟩ : syracuseStep 203099 = 304649) B304649
theorem B170363 : Blo 131789 170363 := bstep (se 1 (by rfl) ⟨127772, by rfl⟩ : syracuseStep 170363 = 255545) B255545
theorem B1841591 : Blo 131789 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B563699 : Blo 131789 563699 := bstep (se 1 (by rfl) ⟨422774, by rfl⟩ : syracuseStep 563699 = 845549) B845549
theorem B1219097 : Blo 131789 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B203327 : Blo 131789 203327 := bstep (se 1 (by rfl) ⟨152495, by rfl⟩ : syracuseStep 203327 = 304991) B304991
theorem B432719 : Blo 131789 432719 := bstep (se 1 (by rfl) ⟨324539, by rfl⟩ : syracuseStep 432719 = 649079) B649079
theorem B301751 : Blo 131789 301751 := bstep (se 1 (by rfl) ⟨226313, by rfl⟩ : syracuseStep 301751 = 452627) B452627
theorem B203447 : Blo 131789 203447 := bstep (se 1 (by rfl) ⟨152585, by rfl⟩ : syracuseStep 203447 = 305171) B305171
theorem B301967 : Blo 131789 301967 := bstep (se 1 (by rfl) ⟨226475, by rfl⟩ : syracuseStep 301967 = 452951) B452951
theorem B203675 : Blo 131789 203675 := bstep (se 1 (by rfl) ⟨152756, by rfl⟩ : syracuseStep 203675 = 305513) B305513
theorem B334763 : Blo 131789 334763 := bstep (se 1 (by rfl) ⟨251072, by rfl⟩ : syracuseStep 334763 = 502145) B502145
theorem B859673 : Blo 131789 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B302687 : Blo 131789 302687 := bstep (se 1 (by rfl) ⟨227015, by rfl⟩ : syracuseStep 302687 = 454031) B454031
theorem B335623 : Blo 131789 335623 := bstep (se 1 (by rfl) ⟨251717, by rfl⟩ : syracuseStep 335623 = 503435) B503435
theorem B302903 : Blo 131789 302903 := bstep (se 1 (by rfl) ⟨227177, by rfl⟩ : syracuseStep 302903 = 454355) B454355
theorem B335897 : Blo 131789 335897 := bstep (se 2 (by rfl) ⟨125961, by rfl⟩ : syracuseStep 335897 = 251923) B251923
theorem B303209 : Blo 131789 303209 := bstep (se 2 (by rfl) ⟨113703, by rfl⟩ : syracuseStep 303209 = 227407) B227407
theorem B2433235 : Blo 131789 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B1450391 : Blo 131789 1450391 := bstep (se 1 (by rfl) ⟨1087793, by rfl⟩ : syracuseStep 1450391 = 2175587) B2175587
theorem B6758923 : Blo 131789 6758923 := bstep (se 1 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 6758923 = 10138385) B10138385
theorem B303695 : Blo 131789 303695 := bstep (se 1 (by rfl) ⟨227771, by rfl⟩ : syracuseStep 303695 = 455543) B455543
theorem B303839 : Blo 131789 303839 := bstep (se 1 (by rfl) ⟨227879, by rfl⟩ : syracuseStep 303839 = 455759) B455759
theorem B2270105 : Blo 131789 2270105 := bstep (se 2 (by rfl) ⟨851289, by rfl⟩ : syracuseStep 2270105 = 1702579) B1702579
theorem B304091 : Blo 131789 304091 := bstep (se 1 (by rfl) ⟨228068, by rfl⟩ : syracuseStep 304091 = 456137) B456137
theorem B1156103 : Blo 131789 1156103 := bstep (se 1 (by rfl) ⟨867077, by rfl⟩ : syracuseStep 1156103 = 1734155) B1734155
theorem B959525 : Blo 131789 959525 := bstep (se 4 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 959525 = 179911) B179911
theorem B304271 : Blo 131789 304271 := bstep (se 1 (by rfl) ⟨228203, by rfl⟩ : syracuseStep 304271 = 456407) B456407
theorem B304361 : Blo 131789 304361 := bstep (se 2 (by rfl) ⟨114135, by rfl⟩ : syracuseStep 304361 = 228271) B228271
theorem B238879 : Blo 131789 238879 := bstep (se 1 (by rfl) ⟨179159, by rfl⟩ : syracuseStep 238879 = 358319) B358319
theorem B304415 : Blo 131789 304415 := bstep (se 1 (by rfl) ⟨228311, by rfl⟩ : syracuseStep 304415 = 456623) B456623
theorem B304937 : Blo 131789 304937 := bstep (se 2 (by rfl) ⟨114351, by rfl⟩ : syracuseStep 304937 = 228703) B228703
theorem B337871 : Blo 131789 337871 := bstep (se 1 (by rfl) ⟨253403, by rfl⟩ : syracuseStep 337871 = 506807) B506807
theorem B567425 : Blo 131789 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B17410229 : Blo 131789 17410229 := bstep (se 5 (by rfl) ⟨816104, by rfl⟩ : syracuseStep 17410229 = 1632209) B1632209
theorem B338539 : Blo 131789 338539 := bstep (se 1 (by rfl) ⟨253904, by rfl⟩ : syracuseStep 338539 = 507809) B507809
theorem B1845949 : Blo 131789 1845949 := bstep (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) B692231
theorem B338843 : Blo 131789 338843 := bstep (se 1 (by rfl) ⟨254132, by rfl⟩ : syracuseStep 338843 = 508265) B508265
theorem B339187 : Blo 131789 339187 := bstep (se 1 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 339187 = 508781) B508781
theorem B1715701 : Blo 131789 1715701 := bstep (se 5 (by rfl) ⟨80423, by rfl⟩ : syracuseStep 1715701 = 160847) B160847
theorem B503405 : Blo 131789 503405 := bstep (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) B188777
theorem B569099 : Blo 131789 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B667439 : Blo 131789 667439 := bstep (se 1 (by rfl) ⟨500579, by rfl⟩ : syracuseStep 667439 = 1001159) B1001159
theorem B3092411 : Blo 131789 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B339977 : Blo 131789 339977 := bstep (se 2 (by rfl) ⟨127491, by rfl⟩ : syracuseStep 339977 = 254983) B254983
theorem B274537 : Blo 131789 274537 := bstep (se 2 (by rfl) ⟨102951, by rfl⟩ : syracuseStep 274537 = 205903) B205903
theorem B308047 : Blo 131789 308047 := bstep (se 1 (by rfl) ⟨231035, by rfl⟩ : syracuseStep 308047 = 462071) B462071
theorem B341131 : Blo 131789 341131 := bstep (se 1 (by rfl) ⟨255848, by rfl⟩ : syracuseStep 341131 = 511697) B511697
theorem B505075 : Blo 131789 505075 := bstep (se 1 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 505075 = 757613) B757613
theorem B341435 : Blo 131789 341435 := bstep (se 1 (by rfl) ⟨256076, by rfl⟩ : syracuseStep 341435 = 512153) B512153
theorem B669545 : Blo 131789 669545 := bstep (se 2 (by rfl) ⟨251079, by rfl⟩ : syracuseStep 669545 = 502159) B502159
theorem B342751 : Blo 131789 342751 := bstep (se 1 (by rfl) ⟨257063, by rfl⟩ : syracuseStep 342751 = 514127) B514127
theorem B342863 : Blo 131789 342863 := bstep (se 1 (by rfl) ⟨257147, by rfl⟩ : syracuseStep 342863 = 514295) B514295
theorem B244559 : Blo 131789 244559 := bstep (se 1 (by rfl) ⟨183419, by rfl⟩ : syracuseStep 244559 = 366839) B366839
theorem B1555307 : Blo 131789 1555307 := bstep (se 1 (by rfl) ⟨1166480, by rfl⟩ : syracuseStep 1555307 = 2332961) B2332961
theorem B605099 : Blo 131789 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B5160023 : Blo 131789 5160023 := bstep (se 1 (by rfl) ⟨3870017, by rfl⟩ : syracuseStep 5160023 = 7740035) B7740035
theorem B507019 : Blo 131789 507019 := bstep (se 1 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 507019 = 760529) B760529
theorem B638239 : Blo 131789 638239 := bstep (se 1 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 638239 = 957359) B957359
theorem B507323 : Blo 131789 507323 := bstep (se 1 (by rfl) ⟨380492, by rfl⟩ : syracuseStep 507323 = 760985) B760985
theorem B343511 : Blo 131789 343511 := bstep (se 1 (by rfl) ⟨257633, by rfl⟩ : syracuseStep 343511 = 515267) B515267
theorem B671327 : Blo 131789 671327 := bstep (se 1 (by rfl) ⟨503495, by rfl⟩ : syracuseStep 671327 = 1006991) B1006991
theorem B310879 : Blo 131789 310879 := bstep (se 1 (by rfl) ⟨233159, by rfl⟩ : syracuseStep 310879 = 466319) B466319
theorem B868103 : Blo 131789 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B868157 : Blo 131789 868157 := bstep (se 3 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 868157 = 325559) B325559
theorem B803297 : Blo 131789 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B574073 : Blo 131789 574073 := bstep (se 2 (by rfl) ⟨215277, by rfl⟩ : syracuseStep 574073 = 430555) B430555
theorem B14959235 : Blo 131789 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B1721033 : Blo 131789 1721033 := bstep (se 2 (by rfl) ⟨645387, by rfl⟩ : syracuseStep 1721033 = 1290775) B1290775
theorem B508751 : Blo 131789 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B3621827 : Blo 131789 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B640007 : Blo 131789 640007 := bstep (se 1 (by rfl) ⟨480005, by rfl⟩ : syracuseStep 640007 = 960011) B960011
theorem B640199 : Blo 131789 640199 := bstep (se 1 (by rfl) ⟨480149, by rfl⟩ : syracuseStep 640199 = 960299) B960299
theorem B476459 : Blo 131789 476459 := bstep (se 1 (by rfl) ⟨357344, by rfl⟩ : syracuseStep 476459 = 714689) B714689
theorem B149215 : Blo 131789 149215 := bstep (se 1 (by rfl) ⟨111911, by rfl⟩ : syracuseStep 149215 = 223823) B223823
theorem B1296161 : Blo 131789 1296161 := bstep (se 2 (by rfl) ⟨486060, by rfl⟩ : syracuseStep 1296161 = 972121) B972121
theorem B1034167 : Blo 131789 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B346241 : Blo 131789 346241 := bstep (se 2 (by rfl) ⟨129840, by rfl⟩ : syracuseStep 346241 = 259681) B259681
theorem B149791 : Blo 131789 149791 := bstep (se 1 (by rfl) ⟨112343, by rfl⟩ : syracuseStep 149791 = 224687) B224687
theorem B150079 : Blo 131789 150079 := bstep (se 1 (by rfl) ⟨112559, by rfl⟩ : syracuseStep 150079 = 225119) B225119
theorem B445175 : Blo 131789 445175 := bstep (se 1 (by rfl) ⟨333881, by rfl⟩ : syracuseStep 445175 = 667763) B667763
theorem B412435 : Blo 131789 412435 := bstep (se 1 (by rfl) ⟨309326, by rfl⟩ : syracuseStep 412435 = 618653) B618653
theorem B2607997 : Blo 131789 2607997 := bstep (se 3 (by rfl) ⟨488999, by rfl⟩ : syracuseStep 2607997 = 977999) B977999
theorem B215963 : Blo 131789 215963 := bstep (se 1 (by rfl) ⟨161972, by rfl⟩ : syracuseStep 215963 = 323945) B323945
theorem B216283 : Blo 131789 216283 := bstep (se 1 (by rfl) ⟨162212, by rfl⟩ : syracuseStep 216283 = 324425) B324425
theorem B150907 : Blo 131789 150907 := bstep (se 1 (by rfl) ⟨113180, by rfl⟩ : syracuseStep 150907 = 226361) B226361
theorem B282055 : Blo 131789 282055 := bstep (se 1 (by rfl) ⟨211541, by rfl⟩ : syracuseStep 282055 = 423083) B423083
theorem B675539 : Blo 131789 675539 := bstep (se 1 (by rfl) ⟨506654, by rfl⟩ : syracuseStep 675539 = 1013309) B1013309
theorem B446255 : Blo 131789 446255 := bstep (se 1 (by rfl) ⟨334691, by rfl⟩ : syracuseStep 446255 = 669383) B669383
theorem B151375 : Blo 131789 151375 := bstep (se 1 (by rfl) ⟨113531, by rfl⟩ : syracuseStep 151375 = 227063) B227063
theorem B380801 : Blo 131789 380801 := bstep (se 2 (by rfl) ⟨142800, by rfl⟩ : syracuseStep 380801 = 285601) B285601
theorem B643081 : Blo 131789 643081 := bstep (se 2 (by rfl) ⟨241155, by rfl⟩ : syracuseStep 643081 = 482311) B482311
theorem B151771 : Blo 131789 151771 := bstep (se 1 (by rfl) ⟨113828, by rfl⟩ : syracuseStep 151771 = 227657) B227657
theorem B741635 : Blo 131789 741635 := bstep (se 1 (by rfl) ⟨556226, by rfl⟩ : syracuseStep 741635 = 1112453) B1112453
theorem B381257 : Blo 131789 381257 := bstep (se 2 (by rfl) ⟨142971, by rfl⟩ : syracuseStep 381257 = 285943) B285943
theorem B676187 : Blo 131789 676187 := bstep (se 1 (by rfl) ⟨507140, by rfl⟩ : syracuseStep 676187 = 1014281) B1014281
theorem B152059 : Blo 131789 152059 := bstep (se 1 (by rfl) ⟨114044, by rfl⟩ : syracuseStep 152059 = 228089) B228089
theorem B152239 : Blo 131789 152239 := bstep (se 1 (by rfl) ⟨114179, by rfl⟩ : syracuseStep 152239 = 228359) B228359
theorem B152527 : Blo 131789 152527 := bstep (se 1 (by rfl) ⟨114395, by rfl⟩ : syracuseStep 152527 = 228791) B228791
theorem B644311 : Blo 131789 644311 := bstep (se 1 (by rfl) ⟨483233, by rfl⟩ : syracuseStep 644311 = 966467) B966467
theorem B677159 : Blo 131789 677159 := bstep (se 1 (by rfl) ⟨507869, by rfl⟩ : syracuseStep 677159 = 1015739) B1015739
theorem B513323 : Blo 131789 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B2807557 : Blo 131789 2807557 := bstep (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) B526417
theorem B448361 : Blo 131789 448361 := bstep (se 2 (by rfl) ⟨168135, by rfl⟩ : syracuseStep 448361 = 336271) B336271
theorem B481261 : Blo 131789 481261 := bstep (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) B180473
theorem B448793 : Blo 131789 448793 := bstep (se 2 (by rfl) ⟨168297, by rfl⟩ : syracuseStep 448793 = 336595) B336595
theorem B973133 : Blo 131789 973133 := bstep (se 3 (by rfl) ⟨182462, by rfl⟩ : syracuseStep 973133 = 364925) B364925
theorem B252371 : Blo 131789 252371 := bstep (se 1 (by rfl) ⟨189278, by rfl⟩ : syracuseStep 252371 = 378557) B378557
theorem B317947 : Blo 131789 317947 := bstep (se 1 (by rfl) ⟨238460, by rfl⟩ : syracuseStep 317947 = 476921) B476921
theorem B383899 : Blo 131789 383899 := bstep (se 1 (by rfl) ⟨287924, by rfl⟩ : syracuseStep 383899 = 575849) B575849
theorem B1235897 : Blo 131789 1235897 := bstep (se 2 (by rfl) ⟨463461, by rfl⟩ : syracuseStep 1235897 = 926923) B926923
theorem B1530899 : Blo 131789 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B679265 : Blo 131789 679265 := bstep (se 2 (by rfl) ⟨254724, by rfl⟩ : syracuseStep 679265 = 509449) B509449
theorem B548345 : Blo 131789 548345 := bstep (se 2 (by rfl) ⟨205629, by rfl⟩ : syracuseStep 548345 = 411259) B411259
theorem B450143 : Blo 131789 450143 := bstep (se 1 (by rfl) ⟨337607, by rfl⟩ : syracuseStep 450143 = 675215) B675215
theorem B253601 : Blo 131789 253601 := bstep (se 2 (by rfl) ⟨95100, by rfl⟩ : syracuseStep 253601 = 190201) B190201
theorem B253675 : Blo 131789 253675 := bstep (se 1 (by rfl) ⟨190256, by rfl⟩ : syracuseStep 253675 = 380513) B380513
theorem B876395 : Blo 131789 876395 := bstep (se 1 (by rfl) ⟨657296, by rfl⟩ : syracuseStep 876395 = 1314593) B1314593
theorem B1138607 : Blo 131789 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B2547719 : Blo 131789 2547719 := bstep (se 1 (by rfl) ⟨1910789, by rfl⟩ : syracuseStep 2547719 = 3821579) B3821579
theorem B581651 : Blo 131789 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B385049 : Blo 131789 385049 := bstep (se 2 (by rfl) ⟨144393, by rfl⟩ : syracuseStep 385049 = 288787) B288787
theorem B1007963 : Blo 131789 1007963 := bstep (se 1 (by rfl) ⟨755972, by rfl⟩ : syracuseStep 1007963 = 1511945) B1511945
theorem B385505 : Blo 131789 385505 := bstep (se 2 (by rfl) ⟨144564, by rfl⟩ : syracuseStep 385505 = 289129) B289129
theorem B2482859 : Blo 131789 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B287659 : Blo 131789 287659 := bstep (se 1 (by rfl) ⟨215744, by rfl⟩ : syracuseStep 287659 = 431489) B431489
theorem B451547 : Blo 131789 451547 := bstep (se 1 (by rfl) ⟨338660, by rfl⟩ : syracuseStep 451547 = 677321) B677321
theorem B189415 : Blo 131789 189415 := bstep (se 1 (by rfl) ⟨142061, by rfl⟩ : syracuseStep 189415 = 284123) B284123
theorem B451709 : Blo 131789 451709 := bstep (se 3 (by rfl) ⟨84695, by rfl⟩ : syracuseStep 451709 = 169391) B169391
theorem B3105985 : Blo 131789 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B451817 : Blo 131789 451817 := bstep (se 2 (by rfl) ⟨169431, by rfl⟩ : syracuseStep 451817 = 338863) B338863
theorem B681209 : Blo 131789 681209 := bstep (se 2 (by rfl) ⟨255453, by rfl⟩ : syracuseStep 681209 = 510907) B510907
theorem B681311 : Blo 131789 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B222601 : Blo 131789 222601 := bstep (se 2 (by rfl) ⟨83475, by rfl⟩ : syracuseStep 222601 = 166951) B166951
theorem B451979 : Blo 131789 451979 := bstep (se 1 (by rfl) ⟨338984, by rfl⟩ : syracuseStep 451979 = 677969) B677969
theorem B223033 : Blo 131789 223033 := bstep (se 2 (by rfl) ⟨83637, by rfl⟩ : syracuseStep 223033 = 167275) B167275
theorem B223337 : Blo 131789 223337 := bstep (se 2 (by rfl) ⟨83751, by rfl⟩ : syracuseStep 223337 = 167503) B167503
theorem B158383 : Blo 131789 158383 := bstep (se 1 (by rfl) ⟨118787, by rfl⟩ : syracuseStep 158383 = 237575) B237575
theorem B224761 : Blo 131789 224761 := bstep (se 2 (by rfl) ⟨84285, by rfl⟩ : syracuseStep 224761 = 168571) B168571
theorem B650767 : Blo 131789 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B913069 : Blo 131789 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B1273553 : Blo 131789 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B225031 : Blo 131789 225031 := bstep (se 1 (by rfl) ⟨168773, by rfl⟩ : syracuseStep 225031 = 337547) B337547
theorem B225065 : Blo 131789 225065 := bstep (se 2 (by rfl) ⟨84399, by rfl⟩ : syracuseStep 225065 = 168799) B168799
theorem B585737 : Blo 131789 585737 := bstep (se 2 (by rfl) ⟨219651, by rfl⟩ : syracuseStep 585737 = 439303) B439303
theorem B2256983 : Blo 131789 2256983 := bstep (se 1 (by rfl) ⟨1692737, by rfl⟩ : syracuseStep 2256983 = 3385475) B3385475
theorem B1208591 : Blo 131789 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B455003 : Blo 131789 455003 := bstep (se 1 (by rfl) ⟨341252, by rfl⟩ : syracuseStep 455003 = 682505) B682505
theorem B225787 : Blo 131789 225787 := bstep (se 1 (by rfl) ⟨169340, by rfl⟩ : syracuseStep 225787 = 338681) B338681
theorem B4452889 : Blo 131789 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B651847 : Blo 131789 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B717457 : Blo 131789 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B357139 : Blo 131789 357139 := bstep (se 1 (by rfl) ⟨267854, by rfl⟩ : syracuseStep 357139 = 535709) B535709
theorem B226219 : Blo 131789 226219 := bstep (se 1 (by rfl) ⟨169664, by rfl⟩ : syracuseStep 226219 = 339329) B339329
theorem B652445 : Blo 131789 652445 := bstep (se 3 (by rfl) ⟨122333, by rfl⟩ : syracuseStep 652445 = 244667) B244667
theorem B226523 : Blo 131789 226523 := bstep (se 1 (by rfl) ⟨169892, by rfl⟩ : syracuseStep 226523 = 339785) B339785
theorem B6419735 : Blo 131789 6419735 := bstep (se 1 (by rfl) ⟨4814801, by rfl⟩ : syracuseStep 6419735 = 9629603) B9629603
theorem B455975 : Blo 131789 455975 := bstep (se 1 (by rfl) ⟨341981, by rfl⟩ : syracuseStep 455975 = 683963) B683963
theorem B587051 : Blo 131789 587051 := bstep (se 1 (by rfl) ⟨440288, by rfl⟩ : syracuseStep 587051 = 880577) B880577
theorem B1144169 : Blo 131789 1144169 := bstep (se 2 (by rfl) ⟨429063, by rfl⟩ : syracuseStep 1144169 = 858127) B858127
theorem B685421 : Blo 131789 685421 := bstep (se 3 (by rfl) ⟨128516, by rfl⟩ : syracuseStep 685421 = 257033) B257033
theorem B292295 : Blo 131789 292295 := bstep (se 1 (by rfl) ⟨219221, by rfl⟩ : syracuseStep 292295 = 438443) B438443
theorem B226759 : Blo 131789 226759 := bstep (se 1 (by rfl) ⟨170069, by rfl⟩ : syracuseStep 226759 = 340139) B340139
theorem B423481 : Blo 131789 423481 := bstep (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) B317611
theorem B35452673 : Blo 131789 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B3667805 : Blo 131789 3667805 := bstep (se 3 (by rfl) ⟨687713, by rfl⟩ : syracuseStep 3667805 = 1375427) B1375427
theorem B227279 : Blo 131789 227279 := bstep (se 1 (by rfl) ⟨170459, by rfl⟩ : syracuseStep 227279 = 340919) B340919
theorem B456839 : Blo 131789 456839 := bstep (se 1 (by rfl) ⟨342629, by rfl⟩ : syracuseStep 456839 = 685259) B685259
theorem B2587085 : Blo 131789 2587085 := bstep (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) B970157
theorem B457289 : Blo 131789 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B227947 : Blo 131789 227947 := bstep (se 1 (by rfl) ⟨170960, by rfl⟩ : syracuseStep 227947 = 341921) B341921
theorem B424723 : Blo 131789 424723 := bstep (se 1 (by rfl) ⟨318542, by rfl⟩ : syracuseStep 424723 = 637085) B637085
theorem B1145707 : Blo 131789 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B4651931 : Blo 131789 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B228251 : Blo 131789 228251 := bstep (se 1 (by rfl) ⟨171188, by rfl⟩ : syracuseStep 228251 = 342377) B342377
theorem B458081 : Blo 131789 458081 := bstep (se 2 (by rfl) ⟨171780, by rfl⟩ : syracuseStep 458081 = 343561) B343561
theorem B10911149 : Blo 131789 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B1080857 : Blo 131789 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B524519 : Blo 131789 524519 := bstep (se 1 (by rfl) ⟨393389, by rfl⟩ : syracuseStep 524519 = 786779) B786779
theorem B3244313 : Blo 131789 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B1147355 : Blo 131789 1147355 := bstep (se 1 (by rfl) ⟨860516, by rfl⟩ : syracuseStep 1147355 = 1721033) B1721033
theorem B426671 : Blo 131789 426671 := bstep (se 1 (by rfl) ⟨320003, by rfl⟩ : syracuseStep 426671 = 640007) B640007
theorem B9011897 : Blo 131789 9011897 := bstep (se 2 (by rfl) ⟨3379461, by rfl⟩ : syracuseStep 9011897 = 6758923) B6758923
theorem B328427 : Blo 131789 328427 := bstep (se 1 (by rfl) ⟨246320, by rfl⟩ : syracuseStep 328427 = 492641) B492641
theorem B426799 : Blo 131789 426799 := bstep (se 1 (by rfl) ⟨320099, by rfl⟩ : syracuseStep 426799 = 640199) B640199
theorem B3670879 : Blo 131789 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B131951 : Blo 131789 131951 := bstep (se 1 (by rfl) ⟨98963, by rfl⟩ : syracuseStep 131951 = 197927) B197927
theorem B132007 : Blo 131789 132007 := bstep (se 1 (by rfl) ⟨99005, by rfl⟩ : syracuseStep 132007 = 198011) B198011
theorem B132091 : Blo 131789 132091 := bstep (se 1 (by rfl) ⟨99068, by rfl⟩ : syracuseStep 132091 = 198137) B198137
theorem B197687 : Blo 131789 197687 := bstep (se 1 (by rfl) ⟨148265, by rfl⟩ : syracuseStep 197687 = 296531) B296531
theorem B3867709 : Blo 131789 3867709 := bstep (se 3 (by rfl) ⟨725195, by rfl⟩ : syracuseStep 3867709 = 1450391) B1450391
theorem B132159 : Blo 131789 132159 := bstep (se 1 (by rfl) ⟨99119, by rfl⟩ : syracuseStep 132159 = 198239) B198239
theorem B197807 : Blo 131789 197807 := bstep (se 1 (by rfl) ⟨148355, by rfl⟩ : syracuseStep 197807 = 296711) B296711
theorem B132303 : Blo 131789 132303 := bstep (se 1 (by rfl) ⟨99227, by rfl⟩ : syracuseStep 132303 = 198455) B198455
theorem B132507 : Blo 131789 132507 := bstep (se 1 (by rfl) ⟨99380, by rfl⟩ : syracuseStep 132507 = 198761) B198761
theorem B853523 : Blo 131789 853523 := bstep (se 1 (by rfl) ⟨640142, by rfl⟩ : syracuseStep 853523 = 1280285) B1280285
theorem B198215 : Blo 131789 198215 := bstep (se 1 (by rfl) ⟨148661, by rfl⟩ : syracuseStep 198215 = 297323) B297323
theorem B132719 : Blo 131789 132719 := bstep (se 1 (by rfl) ⟨99539, by rfl⟩ : syracuseStep 132719 = 199079) B199079
theorem B3671687 : Blo 131789 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B198311 : Blo 131789 198311 := bstep (se 1 (by rfl) ⟨148733, by rfl⟩ : syracuseStep 198311 = 297467) B297467
theorem B132775 : Blo 131789 132775 := bstep (se 1 (by rfl) ⟨99581, by rfl⟩ : syracuseStep 132775 = 199163) B199163
theorem B198395 : Blo 131789 198395 := bstep (se 1 (by rfl) ⟨148796, by rfl⟩ : syracuseStep 198395 = 297593) B297593
theorem B132859 : Blo 131789 132859 := bstep (se 1 (by rfl) ⟨99644, by rfl⟩ : syracuseStep 132859 = 199289) B199289
theorem B6620957 : Blo 131789 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B198431 : Blo 131789 198431 := bstep (se 1 (by rfl) ⟨148823, by rfl⟩ : syracuseStep 198431 = 297647) B297647
theorem B132895 : Blo 131789 132895 := bstep (se 1 (by rfl) ⟨99671, by rfl⟩ : syracuseStep 132895 = 199343) B199343
theorem B132927 : Blo 131789 132927 := bstep (se 1 (by rfl) ⟨99695, by rfl⟩ : syracuseStep 132927 = 199391) B199391
theorem B296783 : Blo 131789 296783 := bstep (se 1 (by rfl) ⟨222587, by rfl⟩ : syracuseStep 296783 = 445175) B445175
theorem B198479 : Blo 131789 198479 := bstep (se 1 (by rfl) ⟨148859, by rfl⟩ : syracuseStep 198479 = 297719) B297719
theorem B296801 : Blo 131789 296801 := bstep (se 2 (by rfl) ⟨111300, by rfl⟩ : syracuseStep 296801 = 222601) B222601
theorem B919471 : Blo 131789 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B198599 : Blo 131789 198599 := bstep (se 1 (by rfl) ⟨148949, by rfl⟩ : syracuseStep 198599 = 297899) B297899
theorem B133103 : Blo 131789 133103 := bstep (se 1 (by rfl) ⟨99827, by rfl⟩ : syracuseStep 133103 = 199655) B199655
theorem B133275 : Blo 131789 133275 := bstep (se 1 (by rfl) ⟨99956, by rfl⟩ : syracuseStep 133275 = 199913) B199913
theorem B133311 : Blo 131789 133311 := bstep (se 1 (by rfl) ⟨99983, by rfl⟩ : syracuseStep 133311 = 199967) B199967
theorem B198953 : Blo 131789 198953 := bstep (se 2 (by rfl) ⟨74607, by rfl⟩ : syracuseStep 198953 = 149215) B149215
theorem B198959 : Blo 131789 198959 := bstep (se 1 (by rfl) ⟨149219, by rfl⟩ : syracuseStep 198959 = 298439) B298439
theorem B133423 : Blo 131789 133423 := bstep (se 1 (by rfl) ⟨100067, by rfl⟩ : syracuseStep 133423 = 200135) B200135
theorem B297377 : Blo 131789 297377 := bstep (se 2 (by rfl) ⟨111516, by rfl⟩ : syracuseStep 297377 = 223033) B223033
theorem B133659 : Blo 131789 133659 := bstep (se 1 (by rfl) ⟨100244, by rfl⟩ : syracuseStep 133659 = 200489) B200489
theorem B297503 : Blo 131789 297503 := bstep (se 1 (by rfl) ⟨223127, by rfl⟩ : syracuseStep 297503 = 446255) B446255
theorem B199199 : Blo 131789 199199 := bstep (se 1 (by rfl) ⟨149399, by rfl⟩ : syracuseStep 199199 = 298799) B298799
theorem B133663 : Blo 131789 133663 := bstep (se 1 (by rfl) ⟨100247, by rfl⟩ : syracuseStep 133663 = 200495) B200495
theorem B1378889 : Blo 131789 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B494423 : Blo 131789 494423 := bstep (se 1 (by rfl) ⟨370817, by rfl⟩ : syracuseStep 494423 = 741635) B741635
theorem B133979 : Blo 131789 133979 := bstep (se 1 (by rfl) ⟨100484, by rfl⟩ : syracuseStep 133979 = 200969) B200969
theorem B199583 : Blo 131789 199583 := bstep (se 1 (by rfl) ⟨149687, by rfl⟩ : syracuseStep 199583 = 299375) B299375
theorem B134047 : Blo 131789 134047 := bstep (se 1 (by rfl) ⟨100535, by rfl⟩ : syracuseStep 134047 = 201071) B201071
theorem B199631 : Blo 131789 199631 := bstep (se 1 (by rfl) ⟨149723, by rfl⟩ : syracuseStep 199631 = 299447) B299447
theorem B1575973 : Blo 131789 1575973 := bstep (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) B295495
theorem B199721 : Blo 131789 199721 := bstep (se 2 (by rfl) ⟨74895, by rfl⟩ : syracuseStep 199721 = 149791) B149791
theorem B199727 : Blo 131789 199727 := bstep (se 1 (by rfl) ⟨149795, by rfl⟩ : syracuseStep 199727 = 299591) B299591
theorem B134191 : Blo 131789 134191 := bstep (se 1 (by rfl) ⟨100643, by rfl⟩ : syracuseStep 134191 = 201287) B201287
theorem B199751 : Blo 131789 199751 := bstep (se 1 (by rfl) ⟨149813, by rfl⟩ : syracuseStep 199751 = 299627) B299627
theorem B134215 : Blo 131789 134215 := bstep (se 1 (by rfl) ⟨100661, by rfl⟩ : syracuseStep 134215 = 201323) B201323
theorem B134367 : Blo 131789 134367 := bstep (se 1 (by rfl) ⟨100775, by rfl⟩ : syracuseStep 134367 = 201551) B201551
theorem B200015 : Blo 131789 200015 := bstep (se 1 (by rfl) ⟨150011, by rfl⟩ : syracuseStep 200015 = 300023) B300023
theorem B200105 : Blo 131789 200105 := bstep (se 2 (by rfl) ⟨75039, by rfl⟩ : syracuseStep 200105 = 150079) B150079
theorem B134631 : Blo 131789 134631 := bstep (se 1 (by rfl) ⟨100973, by rfl⟩ : syracuseStep 134631 = 201947) B201947
theorem B200255 : Blo 131789 200255 := bstep (se 1 (by rfl) ⟨150191, by rfl⟩ : syracuseStep 200255 = 300383) B300383
theorem B2461265 : Blo 131789 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B134747 : Blo 131789 134747 := bstep (se 1 (by rfl) ⟨101060, by rfl⟩ : syracuseStep 134747 = 202121) B202121
theorem B921223 : Blo 131789 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B200519 : Blo 131789 200519 := bstep (se 1 (by rfl) ⟨150389, by rfl⟩ : syracuseStep 200519 = 300779) B300779
theorem B134983 : Blo 131789 134983 := bstep (se 1 (by rfl) ⟨101237, by rfl⟩ : syracuseStep 134983 = 202475) B202475
theorem B3477329 : Blo 131789 3477329 := bstep (se 2 (by rfl) ⟨1303998, by rfl⟩ : syracuseStep 3477329 = 2607997) B2607997
theorem B298907 : Blo 131789 298907 := bstep (se 1 (by rfl) ⟨224180, by rfl⟩ : syracuseStep 298907 = 448361) B448361
theorem B200603 : Blo 131789 200603 := bstep (se 1 (by rfl) ⟨150452, by rfl⟩ : syracuseStep 200603 = 300905) B300905
theorem B135135 : Blo 131789 135135 := bstep (se 1 (by rfl) ⟨101351, by rfl⟩ : syracuseStep 135135 = 202703) B202703
theorem B2199653 : Blo 131789 2199653 := bstep (se 4 (by rfl) ⟨206217, by rfl⟩ : syracuseStep 2199653 = 412435) B412435
theorem B1904741 : Blo 131789 1904741 := bstep (se 4 (by rfl) ⟨178569, by rfl⟩ : syracuseStep 1904741 = 357139) B357139
theorem B299195 : Blo 131789 299195 := bstep (se 1 (by rfl) ⟨224396, by rfl⟩ : syracuseStep 299195 = 448793) B448793
theorem B135399 : Blo 131789 135399 := bstep (se 1 (by rfl) ⟨101549, by rfl⟩ : syracuseStep 135399 = 203099) B203099
theorem B168247 : Blo 131789 168247 := bstep (se 1 (by rfl) ⟨126185, by rfl⟩ : syracuseStep 168247 = 252371) B252371
theorem B135551 : Blo 131789 135551 := bstep (se 1 (by rfl) ⟨101663, by rfl⟩ : syracuseStep 135551 = 203327) B203327
theorem B201167 : Blo 131789 201167 := bstep (se 1 (by rfl) ⟨150875, by rfl⟩ : syracuseStep 201167 = 301751) B301751
theorem B135631 : Blo 131789 135631 := bstep (se 1 (by rfl) ⟨101723, by rfl⟩ : syracuseStep 135631 = 203447) B203447
theorem B201209 : Blo 131789 201209 := bstep (se 2 (by rfl) ⟨75453, by rfl⟩ : syracuseStep 201209 = 150907) B150907
theorem B201311 : Blo 131789 201311 := bstep (se 1 (by rfl) ⟨150983, by rfl⟩ : syracuseStep 201311 = 301967) B301967
theorem B135783 : Blo 131789 135783 := bstep (se 1 (by rfl) ⟨101837, by rfl⟩ : syracuseStep 135783 = 203675) B203675
theorem B823931 : Blo 131789 823931 := bstep (se 1 (by rfl) ⟨617948, by rfl⟩ : syracuseStep 823931 = 1235897) B1235897
theorem B299681 : Blo 131789 299681 := bstep (se 2 (by rfl) ⟨112380, by rfl⟩ : syracuseStep 299681 = 224761) B224761
theorem B1020599 : Blo 131789 1020599 := bstep (se 1 (by rfl) ⟨765449, by rfl⟩ : syracuseStep 1020599 = 1530899) B1530899
theorem B1217425 : Blo 131789 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B365563 : Blo 131789 365563 := bstep (se 1 (by rfl) ⟨274172, by rfl⟩ : syracuseStep 365563 = 548345) B548345
theorem B300041 : Blo 131789 300041 := bstep (se 2 (by rfl) ⟨112515, by rfl⟩ : syracuseStep 300041 = 225031) B225031
theorem B300095 : Blo 131789 300095 := bstep (se 1 (by rfl) ⟨225071, by rfl⟩ : syracuseStep 300095 = 450143) B450143
theorem B201791 : Blo 131789 201791 := bstep (se 1 (by rfl) ⟨151343, by rfl⟩ : syracuseStep 201791 = 302687) B302687
theorem B201833 : Blo 131789 201833 := bstep (se 2 (by rfl) ⟨75687, by rfl⟩ : syracuseStep 201833 = 151375) B151375
theorem B169067 : Blo 131789 169067 := bstep (se 1 (by rfl) ⟨126800, by rfl⟩ : syracuseStep 169067 = 253601) B253601
theorem B3282065 : Blo 131789 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B201935 : Blo 131789 201935 := bstep (se 1 (by rfl) ⟨151451, by rfl⟩ : syracuseStep 201935 = 302903) B302903
theorem B759071 : Blo 131789 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B857441 : Blo 131789 857441 := bstep (se 2 (by rfl) ⟨321540, by rfl⟩ : syracuseStep 857441 = 643081) B643081
theorem B202139 : Blo 131789 202139 := bstep (se 1 (by rfl) ⟨151604, by rfl⟩ : syracuseStep 202139 = 303209) B303209
theorem B366049 : Blo 131789 366049 := bstep (se 2 (by rfl) ⟨137268, by rfl⟩ : syracuseStep 366049 = 274537) B274537
theorem B202361 : Blo 131789 202361 := bstep (se 2 (by rfl) ⟨75885, by rfl⟩ : syracuseStep 202361 = 151771) B151771
theorem B923309 : Blo 131789 923309 := bstep (se 3 (by rfl) ⟨173120, by rfl⟩ : syracuseStep 923309 = 346241) B346241
theorem B202463 : Blo 131789 202463 := bstep (se 1 (by rfl) ⟨151847, by rfl⟩ : syracuseStep 202463 = 303695) B303695
theorem B202559 : Blo 131789 202559 := bstep (se 1 (by rfl) ⟨151919, by rfl⟩ : syracuseStep 202559 = 303839) B303839
theorem B1513403 : Blo 131789 1513403 := bstep (se 1 (by rfl) ⟨1135052, by rfl⟩ : syracuseStep 1513403 = 2270105) B2270105
theorem B301031 : Blo 131789 301031 := bstep (se 1 (by rfl) ⟨225773, by rfl⟩ : syracuseStep 301031 = 451547) B451547
theorem B202727 : Blo 131789 202727 := bstep (se 1 (by rfl) ⟨152045, by rfl⟩ : syracuseStep 202727 = 304091) B304091
theorem B301049 : Blo 131789 301049 := bstep (se 2 (by rfl) ⟨112893, by rfl⟩ : syracuseStep 301049 = 225787) B225787
theorem B202745 : Blo 131789 202745 := bstep (se 2 (by rfl) ⟨76029, by rfl⟩ : syracuseStep 202745 = 152059) B152059
theorem B5937185 : Blo 131789 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B301139 : Blo 131789 301139 := bstep (se 1 (by rfl) ⟨225854, by rfl⟩ : syracuseStep 301139 = 451709) B451709
theorem B202847 : Blo 131789 202847 := bstep (se 1 (by rfl) ⟨152135, by rfl⟩ : syracuseStep 202847 = 304271) B304271
theorem B301211 : Blo 131789 301211 := bstep (se 1 (by rfl) ⟨225908, by rfl⟩ : syracuseStep 301211 = 451817) B451817
theorem B202907 : Blo 131789 202907 := bstep (se 1 (by rfl) ⟨152180, by rfl⟩ : syracuseStep 202907 = 304361) B304361
theorem B202943 : Blo 131789 202943 := bstep (se 1 (by rfl) ⟨152207, by rfl⟩ : syracuseStep 202943 = 304415) B304415
theorem B956609 : Blo 131789 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B202985 : Blo 131789 202985 := bstep (se 2 (by rfl) ⟨76119, by rfl⟩ : syracuseStep 202985 = 152239) B152239
theorem B301319 : Blo 131789 301319 := bstep (se 1 (by rfl) ⟨225989, by rfl⟩ : syracuseStep 301319 = 451979) B451979
theorem B203291 : Blo 131789 203291 := bstep (se 1 (by rfl) ⟨152468, by rfl⟩ : syracuseStep 203291 = 304937) B304937
theorem B301625 : Blo 131789 301625 := bstep (se 2 (by rfl) ⟨113109, by rfl⟩ : syracuseStep 301625 = 226219) B226219
theorem B203369 : Blo 131789 203369 := bstep (se 2 (by rfl) ⟨76263, by rfl⟩ : syracuseStep 203369 = 152527) B152527
theorem B3250925 : Blo 131789 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B11606819 : Blo 131789 11606819 := bstep (se 1 (by rfl) ⟨8705114, by rfl⟩ : syracuseStep 11606819 = 17410229) B17410229
theorem B859081 : Blo 131789 859081 := bstep (se 2 (by rfl) ⟨322155, by rfl⟩ : syracuseStep 859081 = 644311) B644311
theorem B302345 : Blo 131789 302345 := bstep (se 2 (by rfl) ⟨113379, by rfl⟩ : syracuseStep 302345 = 226759) B226759
theorem B564641 : Blo 131789 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B335603 : Blo 131789 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B303335 : Blo 131789 303335 := bstep (se 1 (by rfl) ⟨227501, by rfl⟩ : syracuseStep 303335 = 455003) B455003
theorem B434963 : Blo 131789 434963 := bstep (se 1 (by rfl) ⟨326222, by rfl⟩ : syracuseStep 434963 = 652445) B652445
theorem B303929 : Blo 131789 303929 := bstep (se 2 (by rfl) ⟨113973, by rfl⟩ : syracuseStep 303929 = 227947) B227947
theorem B303983 : Blo 131789 303983 := bstep (se 1 (by rfl) ⟨227987, by rfl⟩ : syracuseStep 303983 = 455975) B455975
theorem B762779 : Blo 131789 762779 := bstep (se 1 (by rfl) ⟨572084, by rfl⟩ : syracuseStep 762779 = 1144169) B1144169
theorem B566297 : Blo 131789 566297 := bstep (se 2 (by rfl) ⟨212361, by rfl⟩ : syracuseStep 566297 = 424723) B424723
theorem B23635115 : Blo 131789 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B1352933 : Blo 131789 1352933 := bstep (se 4 (by rfl) ⟨126837, by rfl⟩ : syracuseStep 1352933 = 253675) B253675
theorem B304559 : Blo 131789 304559 := bstep (se 1 (by rfl) ⟨228419, by rfl⟩ : syracuseStep 304559 = 456839) B456839
theorem B304859 : Blo 131789 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B403399 : Blo 131789 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B305387 : Blo 131789 305387 := bstep (se 1 (by rfl) ⟨229040, by rfl⟩ : syracuseStep 305387 = 458081) B458081
theorem B338215 : Blo 131789 338215 := bstep (se 1 (by rfl) ⟨253661, by rfl⟩ : syracuseStep 338215 = 507323) B507323
theorem B535531 : Blo 131789 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B9972823 : Blo 131789 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B502919 : Blo 131789 502919 := bstep (se 1 (by rfl) ⟨377189, by rfl⟩ : syracuseStep 502919 = 754379) B754379
theorem B339167 : Blo 131789 339167 := bstep (se 1 (by rfl) ⟨254375, by rfl⟩ : syracuseStep 339167 = 508751) B508751
theorem B864107 : Blo 131789 864107 := bstep (se 1 (by rfl) ⟨648080, by rfl⟩ : syracuseStep 864107 = 1296161) B1296161
theorem B176359 : Blo 131789 176359 := bstep (se 1 (by rfl) ⟨132269, by rfl⟩ : syracuseStep 176359 = 264539) B264539
theorem B4141313 : Blo 131789 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B143975 : Blo 131789 143975 := bstep (se 1 (by rfl) ⟨107981, by rfl⟩ : syracuseStep 143975 = 215963) B215963
theorem B571475 : Blo 131789 571475 := bstep (se 1 (by rfl) ⟨428606, by rfl⟩ : syracuseStep 571475 = 857213) B857213
theorem B342215 : Blo 131789 342215 := bstep (se 1 (by rfl) ⟨256661, by rfl⟩ : syracuseStep 342215 = 513323) B513323
theorem B211177 : Blo 131789 211177 := bstep (se 2 (by rfl) ⟨79191, by rfl⟩ : syracuseStep 211177 = 158383) B158383
theorem B1816829 : Blo 131789 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B1227727 : Blo 131789 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B6110437 : Blo 131789 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B376073 : Blo 131789 376073 := bstep (se 2 (by rfl) ⟨141027, by rfl⟩ : syracuseStep 376073 = 282055) B282055
theorem B867689 : Blo 131789 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B573115 : Blo 131789 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B573473 : Blo 131789 573473 := bstep (se 2 (by rfl) ⟨215052, by rfl⟩ : syracuseStep 573473 = 430105) B430105
theorem B671975 : Blo 131789 671975 := bstep (se 1 (by rfl) ⟨503981, by rfl⟩ : syracuseStep 671975 = 1007963) B1007963
theorem B770735 : Blo 131789 770735 := bstep (se 1 (by rfl) ⟨578051, by rfl⟩ : syracuseStep 770735 = 1156103) B1156103
theorem B639683 : Blo 131789 639683 := bstep (se 1 (by rfl) ⟨479762, by rfl⟩ : syracuseStep 639683 = 959525) B959525
theorem B869129 : Blo 131789 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B410729 : Blo 131789 410729 := bstep (se 2 (by rfl) ⟨154023, by rfl⟩ : syracuseStep 410729 = 308047) B308047
theorem B148891 : Blo 131789 148891 := bstep (se 1 (by rfl) ⟨111668, by rfl⟩ : syracuseStep 148891 = 223337) B223337
theorem B378283 : Blo 131789 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B673433 : Blo 131789 673433 := bstep (se 2 (by rfl) ⟨252537, by rfl⟩ : syracuseStep 673433 = 505075) B505075
theorem B379399 : Blo 131789 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B150043 : Blo 131789 150043 := bstep (se 1 (by rfl) ⟨112532, by rfl⟩ : syracuseStep 150043 = 225065) B225065
theorem B444959 : Blo 131789 444959 := bstep (se 1 (by rfl) ⟨333719, by rfl⟩ : syracuseStep 444959 = 667439) B667439
theorem B641681 : Blo 131789 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B805727 : Blo 131789 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B151015 : Blo 131789 151015 := bstep (se 1 (by rfl) ⟨113261, by rfl⟩ : syracuseStep 151015 = 226523) B226523
theorem B4279823 : Blo 131789 4279823 := bstep (se 1 (by rfl) ⟨3209867, by rfl⟩ : syracuseStep 4279823 = 6419735) B6419735
theorem B511865 : Blo 131789 511865 := bstep (se 2 (by rfl) ⟨191949, by rfl⟩ : syracuseStep 511865 = 383899) B383899
theorem B2445203 : Blo 131789 2445203 := bstep (se 1 (by rfl) ⟨1833902, by rfl⟩ : syracuseStep 2445203 = 3667805) B3667805
theorem B446363 : Blo 131789 446363 := bstep (se 1 (by rfl) ⟨334772, by rfl⟩ : syracuseStep 446363 = 669545) B669545
theorem B151519 : Blo 131789 151519 := bstep (se 1 (by rfl) ⟨113639, by rfl⟩ : syracuseStep 151519 = 227279) B227279
theorem B676025 : Blo 131789 676025 := bstep (se 2 (by rfl) ⟨253509, by rfl⟩ : syracuseStep 676025 = 507019) B507019
theorem B1724723 : Blo 131789 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B1036871 : Blo 131789 1036871 := bstep (se 1 (by rfl) ⟨777653, by rfl⟩ : syracuseStep 1036871 = 1555307) B1555307
theorem B3101287 : Blo 131789 3101287 := bstep (se 1 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 3101287 = 4651931) B4651931
theorem B152167 : Blo 131789 152167 := bstep (se 1 (by rfl) ⟨114125, by rfl⟩ : syracuseStep 152167 = 228251) B228251
theorem B414505 : Blo 131789 414505 := bstep (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) B310879
theorem B447497 : Blo 131789 447497 := bstep (se 2 (by rfl) ⟨167811, by rfl⟩ : syracuseStep 447497 = 335623) B335623
theorem B447551 : Blo 131789 447551 := bstep (se 1 (by rfl) ⟨335663, by rfl⟩ : syracuseStep 447551 = 671327) B671327
theorem B578735 : Blo 131789 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B578771 : Blo 131789 578771 := bstep (se 1 (by rfl) ⟨434078, by rfl⟩ : syracuseStep 578771 = 868157) B868157
theorem B218843 : Blo 131789 218843 := bstep (se 1 (by rfl) ⟨164132, by rfl⟩ : syracuseStep 218843 = 328265) B328265
theorem B382715 : Blo 131789 382715 := bstep (se 1 (by rfl) ⟨287036, by rfl⟩ : syracuseStep 382715 = 574073) B574073
theorem B2414551 : Blo 131789 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B284755 : Blo 131789 284755 := bstep (se 1 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 284755 = 427133) B427133
theorem B317639 : Blo 131789 317639 := bstep (se 1 (by rfl) ⟨238229, by rfl⟩ : syracuseStep 317639 = 476459) B476459
theorem B678131 : Blo 131789 678131 := bstep (se 1 (by rfl) ⟨508598, by rfl⟩ : syracuseStep 678131 = 1017197) B1017197
theorem B481609 : Blo 131789 481609 := bstep (se 2 (by rfl) ⟨180603, by rfl⟩ : syracuseStep 481609 = 361207) B361207
theorem B383545 : Blo 131789 383545 := bstep (se 2 (by rfl) ⟨143829, by rfl⟩ : syracuseStep 383545 = 287659) B287659
theorem B252553 : Blo 131789 252553 := bstep (se 2 (by rfl) ⟨94707, by rfl⟩ : syracuseStep 252553 = 189415) B189415
theorem B318505 : Blo 131789 318505 := bstep (se 2 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 318505 = 238879) B238879
theorem B1268939 : Blo 131789 1268939 := bstep (se 1 (by rfl) ⟨951704, by rfl⟩ : syracuseStep 1268939 = 1903409) B1903409
theorem B3104243 : Blo 131789 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B450359 : Blo 131789 450359 := bstep (se 1 (by rfl) ⟨337769, by rfl⟩ : syracuseStep 450359 = 675539) B675539
theorem B679751 : Blo 131789 679751 := bstep (se 1 (by rfl) ⟨509813, by rfl⟩ : syracuseStep 679751 = 1019627) B1019627
theorem B253867 : Blo 131789 253867 := bstep (se 1 (by rfl) ⟨190400, by rfl⟩ : syracuseStep 253867 = 380801) B380801
theorem B254171 : Blo 131789 254171 := bstep (se 1 (by rfl) ⟨190628, by rfl⟩ : syracuseStep 254171 = 381257) B381257
theorem B450791 : Blo 131789 450791 := bstep (se 1 (by rfl) ⟨338093, by rfl⟩ : syracuseStep 450791 = 676187) B676187
theorem B614753 : Blo 131789 614753 := bstep (se 2 (by rfl) ⟨230532, by rfl⟩ : syracuseStep 614753 = 461065) B461065
theorem B1237637 : Blo 131789 1237637 := bstep (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) B232057
theorem B680723 : Blo 131789 680723 := bstep (se 1 (by rfl) ⟨510542, by rfl⟩ : syracuseStep 680723 = 1021085) B1021085
theorem B451385 : Blo 131789 451385 := bstep (se 2 (by rfl) ⟨169269, by rfl⟩ : syracuseStep 451385 = 338539) B338539
theorem B451439 : Blo 131789 451439 := bstep (se 1 (by rfl) ⟨338579, by rfl⟩ : syracuseStep 451439 = 677159) B677159
theorem B3957923 : Blo 131789 3957923 := bstep (se 1 (by rfl) ⟨2968442, by rfl⟩ : syracuseStep 3957923 = 5936885) B5936885
theorem B779453 : Blo 131789 779453 := bstep (se 3 (by rfl) ⟨146147, by rfl⟩ : syracuseStep 779453 = 292295) B292295
theorem B222635 : Blo 131789 222635 := bstep (se 1 (by rfl) ⟨166976, by rfl⟩ : syracuseStep 222635 = 333953) B333953
theorem B648755 : Blo 131789 648755 := bstep (se 1 (by rfl) ⟨486566, by rfl⟩ : syracuseStep 648755 = 973133) B973133
theorem B288377 : Blo 131789 288377 := bstep (se 2 (by rfl) ⟨108141, by rfl⟩ : syracuseStep 288377 = 216283) B216283
theorem B452249 : Blo 131789 452249 := bstep (se 2 (by rfl) ⟨169593, by rfl⟩ : syracuseStep 452249 = 339187) B339187
theorem B288479 : Blo 131789 288479 := bstep (se 1 (by rfl) ⟨216359, by rfl⟩ : syracuseStep 288479 = 432719) B432719
theorem B223175 : Blo 131789 223175 := bstep (se 1 (by rfl) ⟨167381, by rfl⟩ : syracuseStep 223175 = 334763) B334763
theorem B2287601 : Blo 131789 2287601 := bstep (se 2 (by rfl) ⟨857850, by rfl⟩ : syracuseStep 2287601 = 1715701) B1715701
theorem B223465 : Blo 131789 223465 := bstep (se 2 (by rfl) ⟨83799, by rfl⟩ : syracuseStep 223465 = 167599) B167599
theorem B452843 : Blo 131789 452843 := bstep (se 1 (by rfl) ⟨339632, by rfl⟩ : syracuseStep 452843 = 679265) B679265
theorem B584263 : Blo 131789 584263 := bstep (se 1 (by rfl) ⟨438197, by rfl⟩ : syracuseStep 584263 = 876395) B876395
theorem B1698479 : Blo 131789 1698479 := bstep (se 1 (by rfl) ⟨1273859, by rfl⟩ : syracuseStep 1698479 = 2547719) B2547719
theorem B387767 : Blo 131789 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B223931 : Blo 131789 223931 := bstep (se 1 (by rfl) ⟨167948, by rfl⟩ : syracuseStep 223931 = 335897) B335897
theorem B256699 : Blo 131789 256699 := bstep (se 1 (by rfl) ⟨192524, by rfl⟩ : syracuseStep 256699 = 385049) B385049
theorem B59894549 : Blo 131789 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B257003 : Blo 131789 257003 := bstep (se 1 (by rfl) ⟨192752, by rfl⟩ : syracuseStep 257003 = 385505) B385505
theorem B454139 : Blo 131789 454139 := bstep (se 1 (by rfl) ⟨340604, by rfl⟩ : syracuseStep 454139 = 681209) B681209
theorem B454301 : Blo 131789 454301 := bstep (se 3 (by rfl) ⟨85181, by rfl⟩ : syracuseStep 454301 = 170363) B170363
theorem B1503197 : Blo 131789 1503197 := bstep (se 3 (by rfl) ⟨281849, by rfl⟩ : syracuseStep 1503197 = 563699) B563699
theorem B225247 : Blo 131789 225247 := bstep (se 1 (by rfl) ⟨168935, by rfl⟩ : syracuseStep 225247 = 337871) B337871
theorem B454841 : Blo 131789 454841 := bstep (se 2 (by rfl) ⟨170565, by rfl⟩ : syracuseStep 454841 = 341131) B341131
theorem B225895 : Blo 131789 225895 := bstep (se 1 (by rfl) ⟨169421, by rfl⟩ : syracuseStep 225895 = 338843) B338843
theorem B226057 : Blo 131789 226057 := bstep (se 2 (by rfl) ⟨84771, by rfl⟩ : syracuseStep 226057 = 169543) B169543
theorem B849035 : Blo 131789 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B2061607 : Blo 131789 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B226651 : Blo 131789 226651 := bstep (se 1 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 226651 = 339977) B339977
theorem B390491 : Blo 131789 390491 := bstep (se 1 (by rfl) ⟨292868, by rfl⟩ : syracuseStep 390491 = 585737) B585737
theorem B1504655 : Blo 131789 1504655 := bstep (se 1 (by rfl) ⟨1128491, by rfl⟩ : syracuseStep 1504655 = 2256983) B2256983
theorem B423929 : Blo 131789 423929 := bstep (se 2 (by rfl) ⟨158973, by rfl⟩ : syracuseStep 423929 = 317947) B317947
theorem B391367 : Blo 131789 391367 := bstep (se 1 (by rfl) ⟨293525, by rfl⟩ : syracuseStep 391367 = 587051) B587051
theorem B456947 : Blo 131789 456947 := bstep (se 1 (by rfl) ⟨342710, by rfl⟩ : syracuseStep 456947 = 685421) B685421
theorem B227623 : Blo 131789 227623 := bstep (se 1 (by rfl) ⟨170717, by rfl⟩ : syracuseStep 227623 = 341435) B341435
theorem B457001 : Blo 131789 457001 := bstep (se 2 (by rfl) ⟨171375, by rfl⟩ : syracuseStep 457001 = 342751) B342751
theorem B850985 : Blo 131789 850985 := bstep (se 2 (by rfl) ⟨319119, by rfl⟩ : syracuseStep 850985 = 638239) B638239
theorem B228575 : Blo 131789 228575 := bstep (se 1 (by rfl) ⟨171431, by rfl⟩ : syracuseStep 228575 = 342863) B342863
theorem B163039 : Blo 131789 163039 := bstep (se 1 (by rfl) ⟨122279, by rfl⟩ : syracuseStep 163039 = 244559) B244559
theorem B3440015 : Blo 131789 3440015 := bstep (se 1 (by rfl) ⟨2580011, by rfl⟩ : syracuseStep 3440015 = 5160023) B5160023
theorem B7274099 : Blo 131789 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B229007 : Blo 131789 229007 := bstep (se 1 (by rfl) ⟨171755, by rfl⟩ : syracuseStep 229007 = 343511) B343511
theorem B720571 : Blo 131789 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B2162875 : Blo 131789 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B426455 : Blo 131789 426455 := bstep (se 1 (by rfl) ⟨319841, by rfl⟩ : syracuseStep 426455 = 639683) B639683
theorem B131791 : Blo 131789 131791 := bstep (se 1 (by rfl) ⟨98843, by rfl⟩ : syracuseStep 131791 = 197687) B197687
theorem B131871 : Blo 131789 131871 := bstep (se 1 (by rfl) ⟨98903, by rfl⟩ : syracuseStep 131871 = 197807) B197807
theorem B132143 : Blo 131789 132143 := bstep (se 1 (by rfl) ⟨99107, by rfl⟩ : syracuseStep 132143 = 198215) B198215
theorem B132207 : Blo 131789 132207 := bstep (se 1 (by rfl) ⟨99155, by rfl⟩ : syracuseStep 132207 = 198311) B198311
theorem B132263 : Blo 131789 132263 := bstep (se 1 (by rfl) ⟨99197, by rfl⟩ : syracuseStep 132263 = 198395) B198395
theorem B132287 : Blo 131789 132287 := bstep (se 1 (by rfl) ⟨99215, by rfl⟩ : syracuseStep 132287 = 198431) B198431
theorem B197855 : Blo 131789 197855 := bstep (se 1 (by rfl) ⟨148391, by rfl⟩ : syracuseStep 197855 = 296783) B296783
theorem B132319 : Blo 131789 132319 := bstep (se 1 (by rfl) ⟨99239, by rfl⟩ : syracuseStep 132319 = 198479) B198479
theorem B197867 : Blo 131789 197867 := bstep (se 1 (by rfl) ⟨148400, by rfl⟩ : syracuseStep 197867 = 296801) B296801
theorem B132399 : Blo 131789 132399 := bstep (se 1 (by rfl) ⟨99299, by rfl⟩ : syracuseStep 132399 = 198599) B198599
theorem B132635 : Blo 131789 132635 := bstep (se 1 (by rfl) ⟨99476, by rfl⟩ : syracuseStep 132635 = 198953) B198953
theorem B132639 : Blo 131789 132639 := bstep (se 1 (by rfl) ⟨99479, by rfl⟩ : syracuseStep 132639 = 198959) B198959
theorem B198251 : Blo 131789 198251 := bstep (se 1 (by rfl) ⟨148688, by rfl⟩ : syracuseStep 198251 = 297377) B297377
theorem B296639 : Blo 131789 296639 := bstep (se 1 (by rfl) ⟨222479, by rfl⟩ : syracuseStep 296639 = 444959) B444959
theorem B198335 : Blo 131789 198335 := bstep (se 1 (by rfl) ⟨148751, by rfl⟩ : syracuseStep 198335 = 297503) B297503
theorem B132799 : Blo 131789 132799 := bstep (se 1 (by rfl) ⟨99599, by rfl⟩ : syracuseStep 132799 = 199199) B199199
theorem B919259 : Blo 131789 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B427787 : Blo 131789 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B198521 : Blo 131789 198521 := bstep (se 2 (by rfl) ⟨74445, by rfl⟩ : syracuseStep 198521 = 148891) B148891
theorem B329615 : Blo 131789 329615 := bstep (se 1 (by rfl) ⟨247211, by rfl⟩ : syracuseStep 329615 = 494423) B494423
theorem B133055 : Blo 131789 133055 := bstep (se 1 (by rfl) ⟨99791, by rfl⟩ : syracuseStep 133055 = 199583) B199583
theorem B133087 : Blo 131789 133087 := bstep (se 1 (by rfl) ⟨99815, by rfl⟩ : syracuseStep 133087 = 199631) B199631
theorem B133147 : Blo 131789 133147 := bstep (se 1 (by rfl) ⟨99860, by rfl⟩ : syracuseStep 133147 = 199721) B199721
theorem B133151 : Blo 131789 133151 := bstep (se 1 (by rfl) ⟨99863, by rfl⟩ : syracuseStep 133151 = 199727) B199727
theorem B133167 : Blo 131789 133167 := bstep (se 1 (by rfl) ⟨99875, by rfl⟩ : syracuseStep 133167 = 199751) B199751
theorem B133343 : Blo 131789 133343 := bstep (se 1 (by rfl) ⟨100007, by rfl⟩ : syracuseStep 133343 = 200015) B200015
theorem B133403 : Blo 131789 133403 := bstep (se 1 (by rfl) ⟨100052, by rfl⟩ : syracuseStep 133403 = 200105) B200105
theorem B2853215 : Blo 131789 2853215 := bstep (se 1 (by rfl) ⟨2139911, by rfl⟩ : syracuseStep 2853215 = 4279823) B4279823
theorem B133503 : Blo 131789 133503 := bstep (se 1 (by rfl) ⟨100127, by rfl⟩ : syracuseStep 133503 = 200255) B200255
theorem B1640843 : Blo 131789 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B2034077 : Blo 131789 2034077 := bstep (se 3 (by rfl) ⟨381389, by rfl⟩ : syracuseStep 2034077 = 762779) B762779
theorem B133679 : Blo 131789 133679 := bstep (se 1 (by rfl) ⟨100259, by rfl⟩ : syracuseStep 133679 = 200519) B200519
theorem B297575 : Blo 131789 297575 := bstep (se 1 (by rfl) ⟨223181, by rfl⟩ : syracuseStep 297575 = 446363) B446363
theorem B199271 : Blo 131789 199271 := bstep (se 1 (by rfl) ⟨149453, by rfl⟩ : syracuseStep 199271 = 298907) B298907
theorem B133735 : Blo 131789 133735 := bstep (se 1 (by rfl) ⟨100301, by rfl⟩ : syracuseStep 133735 = 200603) B200603
theorem B199463 : Blo 131789 199463 := bstep (se 1 (by rfl) ⟨149597, by rfl⟩ : syracuseStep 199463 = 299195) B299195
theorem B1149815 : Blo 131789 1149815 := bstep (se 1 (by rfl) ⟨862361, by rfl⟩ : syracuseStep 1149815 = 1724723) B1724723
theorem B134111 : Blo 131789 134111 := bstep (se 1 (by rfl) ⟨100583, by rfl⟩ : syracuseStep 134111 = 201167) B201167
theorem B297953 : Blo 131789 297953 := bstep (se 2 (by rfl) ⟨111732, by rfl⟩ : syracuseStep 297953 = 223465) B223465
theorem B134139 : Blo 131789 134139 := bstep (se 1 (by rfl) ⟨100604, by rfl⟩ : syracuseStep 134139 = 201209) B201209
theorem B691247 : Blo 131789 691247 := bstep (se 1 (by rfl) ⟨518435, by rfl⟩ : syracuseStep 691247 = 1036871) B1036871
theorem B134207 : Blo 131789 134207 := bstep (se 1 (by rfl) ⟨100655, by rfl⟩ : syracuseStep 134207 = 201311) B201311
theorem B199787 : Blo 131789 199787 := bstep (se 1 (by rfl) ⟨149840, by rfl⟩ : syracuseStep 199787 = 299681) B299681
theorem B298331 : Blo 131789 298331 := bstep (se 1 (by rfl) ⟨223748, by rfl⟩ : syracuseStep 298331 = 447497) B447497
theorem B200027 : Blo 131789 200027 := bstep (se 1 (by rfl) ⟨150020, by rfl⟩ : syracuseStep 200027 = 300041) B300041
theorem B200057 : Blo 131789 200057 := bstep (se 2 (by rfl) ⟨75021, by rfl⟩ : syracuseStep 200057 = 150043) B150043
theorem B298367 : Blo 131789 298367 := bstep (se 1 (by rfl) ⟨223775, by rfl⟩ : syracuseStep 298367 = 447551) B447551
theorem B200063 : Blo 131789 200063 := bstep (se 1 (by rfl) ⟨150047, by rfl⟩ : syracuseStep 200063 = 300095) B300095
theorem B134527 : Blo 131789 134527 := bstep (se 1 (by rfl) ⟨100895, by rfl⟩ : syracuseStep 134527 = 201791) B201791
theorem B134555 : Blo 131789 134555 := bstep (se 1 (by rfl) ⟨100916, by rfl⟩ : syracuseStep 134555 = 201833) B201833
theorem B134623 : Blo 131789 134623 := bstep (se 1 (by rfl) ⟨100967, by rfl⟩ : syracuseStep 134623 = 201935) B201935
theorem B134759 : Blo 131789 134759 := bstep (se 1 (by rfl) ⟨101069, by rfl⟩ : syracuseStep 134759 = 202139) B202139
theorem B134907 : Blo 131789 134907 := bstep (se 1 (by rfl) ⟨101180, by rfl⟩ : syracuseStep 134907 = 202361) B202361
theorem B134975 : Blo 131789 134975 := bstep (se 1 (by rfl) ⟨101231, by rfl⟩ : syracuseStep 134975 = 202463) B202463
theorem B135039 : Blo 131789 135039 := bstep (se 1 (by rfl) ⟨101279, by rfl⟩ : syracuseStep 135039 = 202559) B202559
theorem B200687 : Blo 131789 200687 := bstep (se 1 (by rfl) ⟨150515, by rfl⟩ : syracuseStep 200687 = 301031) B301031
theorem B135151 : Blo 131789 135151 := bstep (se 1 (by rfl) ⟨101363, by rfl⟩ : syracuseStep 135151 = 202727) B202727
theorem B200699 : Blo 131789 200699 := bstep (se 1 (by rfl) ⟨150524, by rfl⟩ : syracuseStep 200699 = 301049) B301049
theorem B135163 : Blo 131789 135163 := bstep (se 1 (by rfl) ⟨101372, by rfl⟩ : syracuseStep 135163 = 202745) B202745
theorem B2101297 : Blo 131789 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B200759 : Blo 131789 200759 := bstep (se 1 (by rfl) ⟨150569, by rfl⟩ : syracuseStep 200759 = 301139) B301139
theorem B135231 : Blo 131789 135231 := bstep (se 1 (by rfl) ⟨101423, by rfl⟩ : syracuseStep 135231 = 202847) B202847
theorem B200807 : Blo 131789 200807 := bstep (se 1 (by rfl) ⟨150605, by rfl⟩ : syracuseStep 200807 = 301211) B301211
theorem B135271 : Blo 131789 135271 := bstep (se 1 (by rfl) ⟨101453, by rfl⟩ : syracuseStep 135271 = 202907) B202907
theorem B135295 : Blo 131789 135295 := bstep (se 1 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 135295 = 202943) B202943
theorem B135323 : Blo 131789 135323 := bstep (se 1 (by rfl) ⟨101492, by rfl⟩ : syracuseStep 135323 = 202985) B202985
theorem B200879 : Blo 131789 200879 := bstep (se 1 (by rfl) ⟨150659, by rfl⟩ : syracuseStep 200879 = 301319) B301319
theorem B135527 : Blo 131789 135527 := bstep (se 1 (by rfl) ⟨101645, by rfl⟩ : syracuseStep 135527 = 203291) B203291
theorem B201083 : Blo 131789 201083 := bstep (se 1 (by rfl) ⟨150812, by rfl⟩ : syracuseStep 201083 = 301625) B301625
theorem B135579 : Blo 131789 135579 := bstep (se 1 (by rfl) ⟨101684, by rfl⟩ : syracuseStep 135579 = 203369) B203369
theorem B2167283 : Blo 131789 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B201353 : Blo 131789 201353 := bstep (se 2 (by rfl) ⟨75507, by rfl⟩ : syracuseStep 201353 = 151015) B151015
theorem B201563 : Blo 131789 201563 := bstep (se 1 (by rfl) ⟨151172, by rfl⟩ : syracuseStep 201563 = 302345) B302345
theorem B2069495 : Blo 131789 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B300239 : Blo 131789 300239 := bstep (se 1 (by rfl) ⟨225179, by rfl⟩ : syracuseStep 300239 = 450359) B450359
theorem B300329 : Blo 131789 300329 := bstep (se 2 (by rfl) ⟨112623, by rfl⟩ : syracuseStep 300329 = 225247) B225247
theorem B202025 : Blo 131789 202025 := bstep (se 2 (by rfl) ⟨75759, by rfl⟩ : syracuseStep 202025 = 151519) B151519
theorem B15832493 : Blo 131789 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B169447 : Blo 131789 169447 := bstep (se 1 (by rfl) ⟨127085, by rfl⟩ : syracuseStep 169447 = 254171) B254171
theorem B300527 : Blo 131789 300527 := bstep (se 1 (by rfl) ⟨225395, by rfl⟩ : syracuseStep 300527 = 450791) B450791
theorem B202223 : Blo 131789 202223 := bstep (se 1 (by rfl) ⟨151667, by rfl⟩ : syracuseStep 202223 = 303335) B303335
theorem B235145 : Blo 131789 235145 := bstep (se 2 (by rfl) ⟨88179, by rfl⟩ : syracuseStep 235145 = 176359) B176359
theorem B300923 : Blo 131789 300923 := bstep (se 1 (by rfl) ⟨225692, by rfl⟩ : syracuseStep 300923 = 451385) B451385
theorem B202619 : Blo 131789 202619 := bstep (se 1 (by rfl) ⟨151964, by rfl⟩ : syracuseStep 202619 = 303929) B303929
theorem B300959 : Blo 131789 300959 := bstep (se 1 (by rfl) ⟨225719, by rfl⟩ : syracuseStep 300959 = 451439) B451439
theorem B202655 : Blo 131789 202655 := bstep (se 1 (by rfl) ⟨151991, by rfl⟩ : syracuseStep 202655 = 303983) B303983
theorem B301193 : Blo 131789 301193 := bstep (se 2 (by rfl) ⟨112947, by rfl⟩ : syracuseStep 301193 = 225895) B225895
theorem B4135049 : Blo 131789 4135049 := bstep (se 2 (by rfl) ⟨1550643, by rfl⟩ : syracuseStep 4135049 = 3101287) B3101287
theorem B202889 : Blo 131789 202889 := bstep (se 2 (by rfl) ⟨76083, by rfl⟩ : syracuseStep 202889 = 152167) B152167
theorem B203039 : Blo 131789 203039 := bstep (se 1 (by rfl) ⟨152279, by rfl⟩ : syracuseStep 203039 = 304559) B304559
theorem B301409 : Blo 131789 301409 := bstep (se 2 (by rfl) ⟨113028, by rfl⟩ : syracuseStep 301409 = 226057) B226057
theorem B432503 : Blo 131789 432503 := bstep (se 1 (by rfl) ⟨324377, by rfl⟩ : syracuseStep 432503 = 648755) B648755
theorem B301499 : Blo 131789 301499 := bstep (se 1 (by rfl) ⟨226124, by rfl⟩ : syracuseStep 301499 = 452249) B452249
theorem B203239 : Blo 131789 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B301895 : Blo 131789 301895 := bstep (se 1 (by rfl) ⟨226421, by rfl⟩ : syracuseStep 301895 = 452843) B452843
theorem B203591 : Blo 131789 203591 := bstep (se 1 (by rfl) ⟨152693, by rfl⟩ : syracuseStep 203591 = 305387) B305387
theorem B302201 : Blo 131789 302201 := bstep (se 2 (by rfl) ⟨113325, by rfl⟩ : syracuseStep 302201 = 226651) B226651
theorem B171335 : Blo 131789 171335 := bstep (se 1 (by rfl) ⟨128501, by rfl⟩ : syracuseStep 171335 = 257003) B257003
theorem B335279 : Blo 131789 335279 := bstep (se 1 (by rfl) ⟨251459, by rfl⟩ : syracuseStep 335279 = 502919) B502919
theorem B302759 : Blo 131789 302759 := bstep (se 1 (by rfl) ⟨227069, by rfl⟩ : syracuseStep 302759 = 454139) B454139
theorem B302867 : Blo 131789 302867 := bstep (se 1 (by rfl) ⟨227150, by rfl⟩ : syracuseStep 302867 = 454301) B454301
theorem B3219401 : Blo 131789 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B303227 : Blo 131789 303227 := bstep (se 1 (by rfl) ⟨227420, by rfl⟩ : syracuseStep 303227 = 454841) B454841
theorem B2760875 : Blo 131789 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B303497 : Blo 131789 303497 := bstep (se 2 (by rfl) ⟨113811, by rfl⟩ : syracuseStep 303497 = 227623) B227623
theorem B566023 : Blo 131789 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B336737 : Blo 131789 336737 := bstep (se 2 (by rfl) ⟨126276, by rfl⟩ : syracuseStep 336737 = 252553) B252553
theorem B304631 : Blo 131789 304631 := bstep (se 1 (by rfl) ⟨228473, by rfl⟩ : syracuseStep 304631 = 456947) B456947
theorem B304667 : Blo 131789 304667 := bstep (se 1 (by rfl) ⟨228500, by rfl⟩ : syracuseStep 304667 = 457001) B457001
theorem B567323 : Blo 131789 567323 := bstep (se 1 (by rfl) ⟨425492, by rfl⟩ : syracuseStep 567323 = 850985) B850985
theorem B960761 : Blo 131789 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B764153 : Blo 131789 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B338489 : Blo 131789 338489 := bstep (se 2 (by rfl) ⟨126933, by rfl⟩ : syracuseStep 338489 = 253867) B253867
theorem B764903 : Blo 131789 764903 := bstep (se 1 (by rfl) ⟨573677, by rfl⟩ : syracuseStep 764903 = 1147355) B1147355
theorem B6007931 : Blo 131789 6007931 := bstep (se 1 (by rfl) ⟨4505948, by rfl⟩ : syracuseStep 6007931 = 9011897) B9011897
theorem B569015 : Blo 131789 569015 := bstep (se 1 (by rfl) ⟨426761, by rfl⟩ : syracuseStep 569015 = 853523) B853523
theorem B569065 : Blo 131789 569065 := bstep (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) B426799
theorem B4894505 : Blo 131789 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B5156945 : Blo 131789 5156945 := bstep (se 2 (by rfl) ⟨1933854, by rfl⟩ : syracuseStep 5156945 = 3867709) B3867709
theorem B2568581 : Blo 131789 2568581 := bstep (se 4 (by rfl) ⟨240804, by rfl⟩ : syracuseStep 2568581 = 481609) B481609
theorem B504377 : Blo 131789 504377 := bstep (se 2 (by rfl) ⟨189141, by rfl⟩ : syracuseStep 504377 = 378283) B378283
theorem B1225961 : Blo 131789 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B341243 : Blo 131789 341243 := bstep (se 1 (by rfl) ⟨255932, by rfl⟩ : syracuseStep 341243 = 511865) B511865
theorem B1095277 : Blo 131789 1095277 := bstep (se 3 (by rfl) ⟨205364, by rfl⟩ : syracuseStep 1095277 = 410729) B410729
theorem B505865 : Blo 131789 505865 := bstep (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) B379399
theorem B506047 : Blo 131789 506047 := bstep (se 1 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 506047 = 759071) B759071
theorem B571627 : Blo 131789 571627 := bstep (se 1 (by rfl) ⟨428720, by rfl⟩ : syracuseStep 571627 = 857441) B857441
theorem B342265 : Blo 131789 342265 := bstep (se 2 (by rfl) ⟨128349, by rfl⟩ : syracuseStep 342265 = 256699) B256699
theorem B145895 : Blo 131789 145895 := bstep (se 1 (by rfl) ⟨109421, by rfl⟩ : syracuseStep 145895 = 218843) B218843
theorem B637739 : Blo 131789 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B769277 : Blo 131789 769277 := bstep (se 3 (by rfl) ⟨144239, by rfl⟩ : syracuseStep 769277 = 288479) B288479
theorem B1228297 : Blo 131789 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B376427 : Blo 131789 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B409835 : Blo 131789 409835 := bstep (se 1 (by rfl) ⟨307376, by rfl⟩ : syracuseStep 409835 = 614753) B614753
theorem B377531 : Blo 131789 377531 := bstep (se 1 (by rfl) ⟨283148, by rfl⟩ : syracuseStep 377531 = 566297) B566297
theorem B2638615 : Blo 131789 2638615 := bstep (se 1 (by rfl) ⟨1978961, by rfl⟩ : syracuseStep 2638615 = 3957923) B3957923
theorem B901955 : Blo 131789 901955 := bstep (se 1 (by rfl) ⟨676466, by rfl⟩ : syracuseStep 901955 = 1352933) B1352933
theorem B148423 : Blo 131789 148423 := bstep (se 1 (by rfl) ⟨111317, by rfl⟩ : syracuseStep 148423 = 222635) B222635
theorem B1623233 : Blo 131789 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B148783 : Blo 131789 148783 := bstep (se 1 (by rfl) ⟨111587, by rfl⟩ : syracuseStep 148783 = 223175) B223175
theorem B1525067 : Blo 131789 1525067 := bstep (se 1 (by rfl) ⟨1143800, by rfl⟩ : syracuseStep 1525067 = 2287601) B2287601
theorem B1132319 : Blo 131789 1132319 := bstep (se 1 (by rfl) ⟨849239, by rfl⟩ : syracuseStep 1132319 = 1698479) B1698479
theorem B149287 : Blo 131789 149287 := bstep (se 1 (by rfl) ⟨111965, by rfl⟩ : syracuseStep 149287 = 223931) B223931
theorem B39929699 : Blo 131789 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B30951517 : Blo 131789 30951517 := bstep (se 3 (by rfl) ⟨5803409, by rfl⟩ : syracuseStep 30951517 = 11606819) B11606819
theorem B2148605 : Blo 131789 2148605 := bstep (se 3 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 2148605 = 805727) B805727
theorem B1952261 : Blo 131789 1952261 := bstep (se 4 (by rfl) ⟨183024, by rfl⟩ : syracuseStep 1952261 = 366049) B366049
theorem B576071 : Blo 131789 576071 := bstep (se 1 (by rfl) ⟨432053, by rfl⟩ : syracuseStep 576071 = 864107) B864107
theorem B1002131 : Blo 131789 1002131 := bstep (se 1 (by rfl) ⟨751598, by rfl⟩ : syracuseStep 1002131 = 1503197) B1503197
theorem B379673 : Blo 131789 379673 := bstep (se 2 (by rfl) ⟨142377, by rfl⟩ : syracuseStep 379673 = 284755) B284755
theorem B281569 : Blo 131789 281569 := bstep (se 2 (by rfl) ⟨105588, by rfl⟩ : syracuseStep 281569 = 211177) B211177
theorem B511393 : Blo 131789 511393 := bstep (se 2 (by rfl) ⟨191772, by rfl⟩ : syracuseStep 511393 = 383545) B383545
theorem B1003103 : Blo 131789 1003103 := bstep (se 1 (by rfl) ⟨752327, by rfl⟩ : syracuseStep 1003103 = 1504655) B1504655
theorem B282619 : Blo 131789 282619 := bstep (se 1 (by rfl) ⟨211964, by rfl⟩ : syracuseStep 282619 = 423929) B423929
theorem B380983 : Blo 131789 380983 := bstep (se 1 (by rfl) ⟨285737, by rfl⟩ : syracuseStep 380983 = 571475) B571475
theorem B217385 : Blo 131789 217385 := bstep (se 2 (by rfl) ⟨81519, by rfl⟩ : syracuseStep 217385 = 163039) B163039
theorem B8147249 : Blo 131789 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B152383 : Blo 131789 152383 := bstep (se 1 (by rfl) ⟨114287, by rfl⟩ : syracuseStep 152383 = 228575) B228575
theorem B250715 : Blo 131789 250715 := bstep (se 1 (by rfl) ⟨188036, by rfl⟩ : syracuseStep 250715 = 376073) B376073
theorem B578459 : Blo 131789 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B2151461 : Blo 131789 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B152671 : Blo 131789 152671 := bstep (se 1 (by rfl) ⟨114503, by rfl⟩ : syracuseStep 152671 = 229007) B229007
theorem B382315 : Blo 131789 382315 := bstep (se 1 (by rfl) ⟨286736, by rfl⟩ : syracuseStep 382315 = 573473) B573473
theorem B447983 : Blo 131789 447983 := bstep (se 1 (by rfl) ⟨335987, by rfl⟩ : syracuseStep 447983 = 671975) B671975
theorem B349679 : Blo 131789 349679 := bstep (se 1 (by rfl) ⟨262259, by rfl⟩ : syracuseStep 349679 = 524519) B524519
theorem B284447 : Blo 131789 284447 := bstep (se 1 (by rfl) ⟨213335, by rfl⟩ : syracuseStep 284447 = 426671) B426671
theorem B513823 : Blo 131789 513823 := bstep (se 1 (by rfl) ⟨385367, by rfl⟩ : syracuseStep 513823 = 770735) B770735
theorem B218951 : Blo 131789 218951 := bstep (se 1 (by rfl) ⟨164213, by rfl⟩ : syracuseStep 218951 = 328427) B328427
theorem B579419 : Blo 131789 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B448955 : Blo 131789 448955 := bstep (se 1 (by rfl) ⟨336716, by rfl⟩ : syracuseStep 448955 = 673433) B673433
theorem B4413971 : Blo 131789 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B383933 : Blo 131789 383933 := bstep (se 3 (by rfl) ⟨71987, by rfl⟩ : syracuseStep 383933 = 143975) B143975
theorem B3300365 : Blo 131789 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B2318219 : Blo 131789 2318219 := bstep (se 1 (by rfl) ⟨1738664, by rfl⟩ : syracuseStep 2318219 = 3477329) B3477329
theorem B1630135 : Blo 131789 1630135 := bstep (se 1 (by rfl) ⟨1222601, by rfl⟩ : syracuseStep 1630135 = 2445203) B2445203
theorem B1466435 : Blo 131789 1466435 := bstep (se 1 (by rfl) ⟨1099826, by rfl⟩ : syracuseStep 1466435 = 2199653) B2199653
theorem B1269827 : Blo 131789 1269827 := bstep (se 1 (by rfl) ⟨952370, by rfl⟩ : syracuseStep 1269827 = 1904741) B1904741
theorem B450683 : Blo 131789 450683 := bstep (se 1 (by rfl) ⟨338012, by rfl⟩ : syracuseStep 450683 = 676025) B676025
theorem B450845 : Blo 131789 450845 := bstep (se 3 (by rfl) ⟨84533, by rfl⟩ : syracuseStep 450845 = 169067) B169067
theorem B450953 : Blo 131789 450953 := bstep (se 2 (by rfl) ⟨169107, by rfl⟩ : syracuseStep 450953 = 338215) B338215
theorem B549287 : Blo 131789 549287 := bstep (se 1 (by rfl) ⟨411965, by rfl⟩ : syracuseStep 549287 = 823931) B823931
theorem B680399 : Blo 131789 680399 := bstep (se 1 (by rfl) ⟨510299, by rfl⟩ : syracuseStep 680399 = 1020599) B1020599
theorem B779017 : Blo 131789 779017 := bstep (se 2 (by rfl) ⟨292131, by rfl⟩ : syracuseStep 779017 = 584263) B584263
theorem B2188043 : Blo 131789 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B385823 : Blo 131789 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B385847 : Blo 131789 385847 := bstep (se 1 (by rfl) ⟨289385, by rfl⟩ : syracuseStep 385847 = 578771) B578771
theorem B615539 : Blo 131789 615539 := bstep (se 1 (by rfl) ⟨461654, by rfl⟩ : syracuseStep 615539 = 923309) B923309
theorem B255143 : Blo 131789 255143 := bstep (se 1 (by rfl) ⟨191357, by rfl⟩ : syracuseStep 255143 = 382715) B382715
theorem B1008935 : Blo 131789 1008935 := bstep (se 1 (by rfl) ⟨756701, by rfl⟩ : syracuseStep 1008935 = 1513403) B1513403
theorem B714041 : Blo 131789 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B13297097 : Blo 131789 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B452087 : Blo 131789 452087 := bstep (se 1 (by rfl) ⟨339065, by rfl⟩ : syracuseStep 452087 = 678131) B678131
theorem B9791165 : Blo 131789 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B845959 : Blo 131789 845959 := bstep (se 1 (by rfl) ⟨634469, by rfl⟩ : syracuseStep 845959 = 1268939) B1268939
theorem B6547877 : Blo 131789 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B223735 : Blo 131789 223735 := bstep (se 1 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 223735 = 335603) B335603
theorem B453167 : Blo 131789 453167 := bstep (se 1 (by rfl) ⟨339875, by rfl⟩ : syracuseStep 453167 = 679751) B679751
theorem B224329 : Blo 131789 224329 := bstep (se 2 (by rfl) ⟨84123, by rfl⟩ : syracuseStep 224329 = 168247) B168247
theorem B453815 : Blo 131789 453815 := bstep (se 1 (by rfl) ⟨340361, by rfl⟩ : syracuseStep 453815 = 680723) B680723
theorem B289975 : Blo 131789 289975 := bstep (se 1 (by rfl) ⟨217481, by rfl⟩ : syracuseStep 289975 = 434963) B434963
theorem B847037 : Blo 131789 847037 := bstep (se 3 (by rfl) ⟨158819, by rfl⟩ : syracuseStep 847037 = 317639) B317639
theorem B15756743 : Blo 131789 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B519635 : Blo 131789 519635 := bstep (se 1 (by rfl) ⟨389726, by rfl⟩ : syracuseStep 519635 = 779453) B779453
theorem B552673 : Blo 131789 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B192251 : Blo 131789 192251 := bstep (se 1 (by rfl) ⟨144188, by rfl⟩ : syracuseStep 192251 = 288377) B288377
theorem B487417 : Blo 131789 487417 := bstep (se 2 (by rfl) ⟨182781, by rfl⟩ : syracuseStep 487417 = 365563) B365563
theorem B2748809 : Blo 131789 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B258511 : Blo 131789 258511 := bstep (se 1 (by rfl) ⟨193883, by rfl⟩ : syracuseStep 258511 = 387767) B387767
theorem B226111 : Blo 131789 226111 := bstep (se 1 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 226111 = 339167) B339167
theorem B260327 : Blo 131789 260327 := bstep (se 1 (by rfl) ⟨195245, by rfl⟩ : syracuseStep 260327 = 390491) B390491
theorem B1145441 : Blo 131789 1145441 := bstep (se 2 (by rfl) ⟨429540, by rfl⟩ : syracuseStep 1145441 = 859081) B859081
theorem B424673 : Blo 131789 424673 := bstep (se 2 (by rfl) ⟨159252, by rfl⟩ : syracuseStep 424673 = 318505) B318505
theorem B228143 : Blo 131789 228143 := bstep (se 1 (by rfl) ⟨171107, by rfl⟩ : syracuseStep 228143 = 342215) B342215
theorem B260911 : Blo 131789 260911 := bstep (se 1 (by rfl) ⟨195683, by rfl⟩ : syracuseStep 260911 = 391367) B391367
theorem B1211219 : Blo 131789 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B2293343 : Blo 131789 2293343 := bstep (se 1 (by rfl) ⟨1720007, by rfl⟩ : syracuseStep 2293343 = 3440015) B3440015
theorem B4849399 : Blo 131789 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B2883833 : Blo 131789 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1082155 : Blo 131789 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B131903 : Blo 131789 131903 := bstep (se 1 (by rfl) ⟨98927, by rfl⟩ : syracuseStep 131903 = 197855) B197855
theorem B131911 : Blo 131789 131911 := bstep (se 1 (by rfl) ⟨98933, by rfl⟩ : syracuseStep 131911 = 197867) B197867
theorem B1016711 : Blo 131789 1016711 := bstep (se 1 (by rfl) ⟨762533, by rfl⟩ : syracuseStep 1016711 = 1525067) B1525067
theorem B754697 : Blo 131789 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B132167 : Blo 131789 132167 := bstep (se 1 (by rfl) ⟨99125, by rfl⟩ : syracuseStep 132167 = 198251) B198251
theorem B197759 : Blo 131789 197759 := bstep (se 1 (by rfl) ⟨148319, by rfl⟩ : syracuseStep 197759 = 296639) B296639
theorem B132223 : Blo 131789 132223 := bstep (se 1 (by rfl) ⟨99167, by rfl⟩ : syracuseStep 132223 = 198335) B198335
theorem B754879 : Blo 131789 754879 := bstep (se 1 (by rfl) ⟨566159, by rfl⟩ : syracuseStep 754879 = 1132319) B1132319
theorem B132347 : Blo 131789 132347 := bstep (se 1 (by rfl) ⟨99260, by rfl⟩ : syracuseStep 132347 = 198521) B198521
theorem B197897 : Blo 131789 197897 := bstep (se 2 (by rfl) ⟨74211, by rfl⟩ : syracuseStep 197897 = 148423) B148423
theorem B1902143 : Blo 131789 1902143 := bstep (se 1 (by rfl) ⟨1426607, by rfl⟩ : syracuseStep 1902143 = 2853215) B2853215
theorem B198377 : Blo 131789 198377 := bstep (se 2 (by rfl) ⟨74391, by rfl⟩ : syracuseStep 198377 = 148783) B148783
theorem B198383 : Blo 131789 198383 := bstep (se 1 (by rfl) ⟨148787, by rfl⟩ : syracuseStep 198383 = 297575) B297575
theorem B132847 : Blo 131789 132847 := bstep (se 1 (by rfl) ⟨99635, by rfl⟩ : syracuseStep 132847 = 199271) B199271
theorem B132975 : Blo 131789 132975 := bstep (se 1 (by rfl) ⟨99731, by rfl⟩ : syracuseStep 132975 = 199463) B199463
theorem B198635 : Blo 131789 198635 := bstep (se 1 (by rfl) ⟨148976, by rfl⟩ : syracuseStep 198635 = 297953) B297953
theorem B460831 : Blo 131789 460831 := bstep (se 1 (by rfl) ⟨345623, by rfl⟩ : syracuseStep 460831 = 691247) B691247
theorem B133191 : Blo 131789 133191 := bstep (se 1 (by rfl) ⟨99893, by rfl⟩ : syracuseStep 133191 = 199787) B199787
theorem B198887 : Blo 131789 198887 := bstep (se 1 (by rfl) ⟨149165, by rfl⟩ : syracuseStep 198887 = 298331) B298331
theorem B133351 : Blo 131789 133351 := bstep (se 1 (by rfl) ⟨100013, by rfl⟩ : syracuseStep 133351 = 200027) B200027
theorem B133371 : Blo 131789 133371 := bstep (se 1 (by rfl) ⟨100028, by rfl⟩ : syracuseStep 133371 = 200057) B200057
theorem B198911 : Blo 131789 198911 := bstep (se 1 (by rfl) ⟨149183, by rfl⟩ : syracuseStep 198911 = 298367) B298367
theorem B133375 : Blo 131789 133375 := bstep (se 1 (by rfl) ⟨100031, by rfl⟩ : syracuseStep 133375 = 200063) B200063
theorem B199049 : Blo 131789 199049 := bstep (se 2 (by rfl) ⟨74643, by rfl⟩ : syracuseStep 199049 = 149287) B149287
theorem B1542557 : Blo 131789 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B1083941 : Blo 131789 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B133791 : Blo 131789 133791 := bstep (se 1 (by rfl) ⟨100343, by rfl⟩ : syracuseStep 133791 = 200687) B200687
theorem B133799 : Blo 131789 133799 := bstep (se 1 (by rfl) ⟨100349, by rfl⟩ : syracuseStep 133799 = 200699) B200699
theorem B133839 : Blo 131789 133839 := bstep (se 1 (by rfl) ⟨100379, by rfl⟩ : syracuseStep 133839 = 200759) B200759
theorem B133871 : Blo 131789 133871 := bstep (se 1 (by rfl) ⟨100403, by rfl⟩ : syracuseStep 133871 = 200807) B200807
theorem B133919 : Blo 131789 133919 := bstep (se 1 (by rfl) ⟨100439, by rfl⟩ : syracuseStep 133919 = 200879) B200879
theorem B134055 : Blo 131789 134055 := bstep (se 1 (by rfl) ⟨100541, by rfl⟩ : syracuseStep 134055 = 201083) B201083
theorem B134235 : Blo 131789 134235 := bstep (se 1 (by rfl) ⟨100676, by rfl⟩ : syracuseStep 134235 = 201353) B201353
theorem B134375 : Blo 131789 134375 := bstep (se 1 (by rfl) ⟨100781, by rfl⟩ : syracuseStep 134375 = 201563) B201563
theorem B298313 : Blo 131789 298313 := bstep (se 2 (by rfl) ⟨111867, by rfl⟩ : syracuseStep 298313 = 223735) B223735
theorem B1379663 : Blo 131789 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B200159 : Blo 131789 200159 := bstep (se 1 (by rfl) ⟨150119, by rfl⟩ : syracuseStep 200159 = 300239) B300239
theorem B200219 : Blo 131789 200219 := bstep (se 1 (by rfl) ⟨150164, by rfl⟩ : syracuseStep 200219 = 300329) B300329
theorem B134683 : Blo 131789 134683 := bstep (se 1 (by rfl) ⟨101012, by rfl⟩ : syracuseStep 134683 = 202025) B202025
theorem B10554995 : Blo 131789 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B298655 : Blo 131789 298655 := bstep (se 1 (by rfl) ⟨223991, by rfl⟩ : syracuseStep 298655 = 447983) B447983
theorem B200351 : Blo 131789 200351 := bstep (se 1 (by rfl) ⟨150263, by rfl⟩ : syracuseStep 200351 = 300527) B300527
theorem B233119 : Blo 131789 233119 := bstep (se 1 (by rfl) ⟨174839, by rfl⟩ : syracuseStep 233119 = 349679) B349679
theorem B134815 : Blo 131789 134815 := bstep (se 1 (by rfl) ⟨101111, by rfl⟩ : syracuseStep 134815 = 202223) B202223
theorem B200615 : Blo 131789 200615 := bstep (se 1 (by rfl) ⟨150461, by rfl⟩ : syracuseStep 200615 = 300923) B300923
theorem B135079 : Blo 131789 135079 := bstep (se 1 (by rfl) ⟨101309, by rfl⟩ : syracuseStep 135079 = 202619) B202619
theorem B200639 : Blo 131789 200639 := bstep (se 1 (by rfl) ⟨150479, by rfl⟩ : syracuseStep 200639 = 300959) B300959
theorem B135103 : Blo 131789 135103 := bstep (se 1 (by rfl) ⟨101327, by rfl⟩ : syracuseStep 135103 = 202655) B202655
theorem B200795 : Blo 131789 200795 := bstep (se 1 (by rfl) ⟨150596, by rfl⟩ : syracuseStep 200795 = 301193) B301193
theorem B2756699 : Blo 131789 2756699 := bstep (se 1 (by rfl) ⟨2067524, by rfl⟩ : syracuseStep 2756699 = 4135049) B4135049
theorem B135259 : Blo 131789 135259 := bstep (se 1 (by rfl) ⟨101444, by rfl⟩ : syracuseStep 135259 = 202889) B202889
theorem B299105 : Blo 131789 299105 := bstep (se 2 (by rfl) ⟨112164, by rfl⟩ : syracuseStep 299105 = 224329) B224329
theorem B135359 : Blo 131789 135359 := bstep (se 1 (by rfl) ⟨101519, by rfl⟩ : syracuseStep 135359 = 203039) B203039
theorem B200939 : Blo 131789 200939 := bstep (se 1 (by rfl) ⟨150704, by rfl⟩ : syracuseStep 200939 = 301409) B301409
theorem B299303 : Blo 131789 299303 := bstep (se 1 (by rfl) ⟨224477, by rfl⟩ : syracuseStep 299303 = 448955) B448955
theorem B200999 : Blo 131789 200999 := bstep (se 1 (by rfl) ⟨150749, by rfl⟩ : syracuseStep 200999 = 301499) B301499
theorem B201263 : Blo 131789 201263 := bstep (se 1 (by rfl) ⟨150947, by rfl⟩ : syracuseStep 201263 = 301895) B301895
theorem B135727 : Blo 131789 135727 := bstep (se 1 (by rfl) ⟨101795, by rfl⟩ : syracuseStep 135727 = 203591) B203591
theorem B2200243 : Blo 131789 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B201467 : Blo 131789 201467 := bstep (se 1 (by rfl) ⟨151100, by rfl⟩ : syracuseStep 201467 = 302201) B302201
theorem B758753 : Blo 131789 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B201839 : Blo 131789 201839 := bstep (se 1 (by rfl) ⟨151379, by rfl⟩ : syracuseStep 201839 = 302759) B302759
theorem B201911 : Blo 131789 201911 := bstep (se 1 (by rfl) ⟨151433, by rfl⟩ : syracuseStep 201911 = 302867) B302867
theorem B1545479 : Blo 131789 1545479 := bstep (se 1 (by rfl) ⟨1159109, by rfl⟩ : syracuseStep 1545479 = 2318219) B2318219
theorem B300455 : Blo 131789 300455 := bstep (se 1 (by rfl) ⟨225341, by rfl⟩ : syracuseStep 300455 = 450683) B450683
theorem B202151 : Blo 131789 202151 := bstep (se 1 (by rfl) ⟨151613, by rfl⟩ : syracuseStep 202151 = 303227) B303227
theorem B1840583 : Blo 131789 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B300563 : Blo 131789 300563 := bstep (se 1 (by rfl) ⟨225422, by rfl⟩ : syracuseStep 300563 = 450845) B450845
theorem B300635 : Blo 131789 300635 := bstep (se 1 (by rfl) ⟨225476, by rfl⟩ : syracuseStep 300635 = 450953) B450953
theorem B202331 : Blo 131789 202331 := bstep (se 1 (by rfl) ⟨151748, by rfl⟩ : syracuseStep 202331 = 303497) B303497
theorem B366191 : Blo 131789 366191 := bstep (se 1 (by rfl) ⟨274643, by rfl⟩ : syracuseStep 366191 = 549287) B549287
theorem B170095 : Blo 131789 170095 := bstep (se 1 (by rfl) ⟨127571, by rfl⟩ : syracuseStep 170095 = 255143) B255143
theorem B301391 : Blo 131789 301391 := bstep (se 1 (by rfl) ⟨226043, by rfl⟩ : syracuseStep 301391 = 452087) B452087
theorem B203087 : Blo 131789 203087 := bstep (se 1 (by rfl) ⟨152315, by rfl⟩ : syracuseStep 203087 = 304631) B304631
theorem B203111 : Blo 131789 203111 := bstep (se 1 (by rfl) ⟨152333, by rfl⟩ : syracuseStep 203111 = 304667) B304667
theorem B301481 : Blo 131789 301481 := bstep (se 2 (by rfl) ⟨113055, by rfl⟩ : syracuseStep 301481 = 226111) B226111
theorem B203177 : Blo 131789 203177 := bstep (se 2 (by rfl) ⟨76191, by rfl⟩ : syracuseStep 203177 = 152383) B152383
theorem B203561 : Blo 131789 203561 := bstep (se 2 (by rfl) ⟨76335, by rfl⟩ : syracuseStep 203561 = 152671) B152671
theorem B4365251 : Blo 131789 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B302111 : Blo 131789 302111 := bstep (se 1 (by rfl) ⟨226583, by rfl⟩ : syracuseStep 302111 = 453167) B453167
theorem B4005287 : Blo 131789 4005287 := bstep (se 1 (by rfl) ⟨3003965, by rfl⟩ : syracuseStep 4005287 = 6007931) B6007931
theorem B302543 : Blo 131789 302543 := bstep (se 1 (by rfl) ⟨226907, by rfl⟩ : syracuseStep 302543 = 453815) B453815
theorem B564691 : Blo 131789 564691 := bstep (se 1 (by rfl) ⟨423518, by rfl⟩ : syracuseStep 564691 = 847037) B847037
theorem B1712387 : Blo 131789 1712387 := bstep (se 1 (by rfl) ⟨1284290, by rfl⟩ : syracuseStep 1712387 = 2568581) B2568581
theorem B762169 : Blo 131789 762169 := bstep (se 2 (by rfl) ⟨285813, by rfl⟩ : syracuseStep 762169 = 571627) B571627
theorem B336251 : Blo 131789 336251 := bstep (se 1 (by rfl) ⟨252188, by rfl⟩ : syracuseStep 336251 = 504377) B504377
theorem B337243 : Blo 131789 337243 := bstep (se 1 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 337243 = 505865) B505865
theorem B173551 : Blo 131789 173551 := bstep (se 1 (by rfl) ⟨130163, by rfl⟩ : syracuseStep 173551 = 260327) B260327
theorem B763627 : Blo 131789 763627 := bstep (se 1 (by rfl) ⟨572720, by rfl⟩ : syracuseStep 763627 = 1145441) B1145441
theorem B6465865 : Blo 131789 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B2173513 : Blo 131789 2173513 := bstep (se 2 (by rfl) ⟨815067, by rfl⟩ : syracuseStep 2173513 = 1630135) B1630135
theorem B273223 : Blo 131789 273223 := bstep (se 1 (by rfl) ⟨204917, by rfl⟩ : syracuseStep 273223 = 409835) B409835
theorem B3910493 : Blo 131789 3910493 := bstep (se 3 (by rfl) ⟨733217, by rfl⟩ : syracuseStep 3910493 = 1466435) B1466435
theorem B3518153 : Blo 131789 3518153 := bstep (se 2 (by rfl) ⟨1319307, by rfl⟩ : syracuseStep 3518153 = 2638615) B2638615
theorem B26619799 : Blo 131789 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B5779421 : Blo 131789 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B1093895 : Blo 131789 1093895 := bstep (se 1 (by rfl) ⟨820421, by rfl⟩ : syracuseStep 1093895 = 1640843) B1640843
theorem B668087 : Blo 131789 668087 := bstep (se 1 (by rfl) ⟨501065, by rfl⟩ : syracuseStep 668087 = 1002131) B1002131
theorem B766543 : Blo 131789 766543 := bstep (se 1 (by rfl) ⟨574907, by rfl⟩ : syracuseStep 766543 = 1149815) B1149815
theorem B1028861 : Blo 131789 1028861 := bstep (se 3 (by rfl) ⟨192911, by rfl⟩ : syracuseStep 1028861 = 385823) B385823
theorem B2405213 : Blo 131789 2405213 := bstep (se 3 (by rfl) ⟨450977, by rfl⟩ : syracuseStep 2405213 = 901955) B901955
theorem B668573 : Blo 131789 668573 := bstep (se 3 (by rfl) ⟨125357, by rfl⟩ : syracuseStep 668573 = 250715) B250715
theorem B668735 : Blo 131789 668735 := bstep (se 1 (by rfl) ⟨501551, by rfl⟩ : syracuseStep 668735 = 1003103) B1003103
theorem B41268689 : Blo 131789 41268689 := bstep (se 2 (by rfl) ⟨15475758, by rfl⟩ : syracuseStep 41268689 = 30951517) B30951517
theorem B1127945 : Blo 131789 1127945 := bstep (se 2 (by rfl) ⟨422979, by rfl⟩ : syracuseStep 1127945 = 845959) B845959
theorem B144923 : Blo 131789 144923 := bstep (se 1 (by rfl) ⟨108692, by rfl⟩ : syracuseStep 144923 = 217385) B217385
theorem B145967 : Blo 131789 145967 := bstep (se 1 (by rfl) ⟨109475, by rfl⟩ : syracuseStep 145967 = 218951) B218951
theorem B375425 : Blo 131789 375425 := bstep (se 2 (by rfl) ⟨140784, by rfl⟩ : syracuseStep 375425 = 281569) B281569
theorem B1391525 : Blo 131789 1391525 := bstep (se 4 (by rfl) ⟨130455, by rfl⟩ : syracuseStep 1391525 = 260911) B260911
theorem B736897 : Blo 131789 736897 := bstep (se 2 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 736897 = 552673) B552673
theorem B2146267 : Blo 131789 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B376825 : Blo 131789 376825 := bstep (se 2 (by rfl) ⟨141309, by rfl⟩ : syracuseStep 376825 = 282619) B282619
theorem B2801729 : Blo 131789 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B507977 : Blo 131789 507977 := bstep (se 2 (by rfl) ⟨190491, by rfl⟩ : syracuseStep 507977 = 380983) B380983
theorem B1458695 : Blo 131789 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B344681 : Blo 131789 344681 := bstep (se 2 (by rfl) ⟨129255, by rfl⟩ : syracuseStep 344681 = 258511) B258511
theorem B410359 : Blo 131789 410359 := bstep (se 1 (by rfl) ⟨307769, by rfl⟩ : syracuseStep 410359 = 615539) B615539
theorem B672623 : Blo 131789 672623 := bstep (se 1 (by rfl) ⟨504467, by rfl⟩ : syracuseStep 672623 = 1008935) B1008935
theorem B476027 : Blo 131789 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B8864731 : Blo 131789 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B5424205 : Blo 131789 5424205 := bstep (se 3 (by rfl) ⟨1017038, by rfl⟩ : syracuseStep 5424205 = 2034077) B2034077
theorem B378215 : Blo 131789 378215 := bstep (se 1 (by rfl) ⟨283661, by rfl⟩ : syracuseStep 378215 = 567323) B567323
theorem B640507 : Blo 131789 640507 := bstep (se 1 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 640507 = 960761) B960761
theorem B509435 : Blo 131789 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B509753 : Blo 131789 509753 := bstep (se 2 (by rfl) ⟨191157, by rfl⟩ : syracuseStep 509753 = 382315) B382315
theorem B509935 : Blo 131789 509935 := bstep (se 1 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 509935 = 764903) B764903
theorem B1460369 : Blo 131789 1460369 := bstep (se 2 (by rfl) ⟨547638, by rfl⟩ : syracuseStep 1460369 = 1095277) B1095277
theorem B10504495 : Blo 131789 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B346423 : Blo 131789 346423 := bstep (se 1 (by rfl) ⟨259817, by rfl⟩ : syracuseStep 346423 = 519635) B519635
theorem B379343 : Blo 131789 379343 := bstep (se 1 (by rfl) ⟨284507, by rfl⟩ : syracuseStep 379343 = 569015) B569015
theorem B3263003 : Blo 131789 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B674729 : Blo 131789 674729 := bstep (se 2 (by rfl) ⟨253023, by rfl⟩ : syracuseStep 674729 = 506047) B506047
theorem B283115 : Blo 131789 283115 := bstep (se 1 (by rfl) ⟨212336, by rfl⟩ : syracuseStep 283115 = 424673) B424673
theorem B152095 : Blo 131789 152095 := bstep (se 1 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 152095 = 228143) B228143
theorem B807479 : Blo 131789 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B512669 : Blo 131789 512669 := bstep (se 3 (by rfl) ⟨96125, by rfl⟩ : syracuseStep 512669 = 192251) B192251
theorem B512851 : Blo 131789 512851 := bstep (se 1 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 512851 = 769277) B769277
theorem B1528895 : Blo 131789 1528895 := bstep (se 1 (by rfl) ⟨1146671, by rfl⟩ : syracuseStep 1528895 = 2293343) B2293343
theorem B250951 : Blo 131789 250951 := bstep (se 1 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 250951 = 376427) B376427
theorem B284303 : Blo 131789 284303 := bstep (se 1 (by rfl) ⟨213227, by rfl⟩ : syracuseStep 284303 = 426455) B426455
theorem B251687 : Blo 131789 251687 := bstep (se 1 (by rfl) ⟨188765, by rfl⟩ : syracuseStep 251687 = 377531) B377531
theorem B1038689 : Blo 131789 1038689 := bstep (se 2 (by rfl) ⟨389508, by rfl⟩ : syracuseStep 1038689 = 779017) B779017
theorem B612839 : Blo 131789 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B285191 : Blo 131789 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B219743 : Blo 131789 219743 := bstep (se 1 (by rfl) ⟨164807, by rfl⟩ : syracuseStep 219743 = 329615) B329615
theorem B1432403 : Blo 131789 1432403 := bstep (se 1 (by rfl) ⟨1074302, by rfl⟩ : syracuseStep 1432403 = 2148605) B2148605
theorem B1301507 : Blo 131789 1301507 := bstep (se 1 (by rfl) ⟨976130, by rfl⟩ : syracuseStep 1301507 = 1952261) B1952261
theorem B384047 : Blo 131789 384047 := bstep (se 1 (by rfl) ⟨288035, by rfl⟩ : syracuseStep 384047 = 576071) B576071
theorem B253115 : Blo 131789 253115 := bstep (se 1 (by rfl) ⟨189836, by rfl⟩ : syracuseStep 253115 = 379673) B379673
theorem B5431499 : Blo 131789 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B1434307 : Blo 131789 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B156763 : Blo 131789 156763 := bstep (se 1 (by rfl) ⟨117572, by rfl⟩ : syracuseStep 156763 = 235145) B235145
theorem B189631 : Blo 131789 189631 := bstep (se 1 (by rfl) ⟨142223, by rfl⟩ : syracuseStep 189631 = 284447) B284447
theorem B386279 : Blo 131789 386279 := bstep (se 1 (by rfl) ⟨289709, by rfl⟩ : syracuseStep 386279 = 579419) B579419
theorem B386633 : Blo 131789 386633 := bstep (se 2 (by rfl) ⟨144987, by rfl⟩ : syracuseStep 386633 = 289975) B289975
theorem B288335 : Blo 131789 288335 := bstep (se 1 (by rfl) ⟨216251, by rfl⟩ : syracuseStep 288335 = 432503) B432503
theorem B2942647 : Blo 131789 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B26109773 : Blo 131789 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B681857 : Blo 131789 681857 := bstep (se 2 (by rfl) ⟨255696, by rfl⟩ : syracuseStep 681857 = 511393) B511393
theorem B255955 : Blo 131789 255955 := bstep (se 1 (by rfl) ⟨191966, by rfl⟩ : syracuseStep 255955 = 383933) B383933
theorem B223519 : Blo 131789 223519 := bstep (se 1 (by rfl) ⟨167639, by rfl⟩ : syracuseStep 223519 = 335279) B335279
theorem B649889 : Blo 131789 649889 := bstep (se 2 (by rfl) ⟨243708, by rfl⟩ : syracuseStep 649889 = 487417) B487417
theorem B846551 : Blo 131789 846551 := bstep (se 1 (by rfl) ⟨634913, by rfl⟩ : syracuseStep 846551 = 1269827) B1269827
theorem B453599 : Blo 131789 453599 := bstep (se 1 (by rfl) ⟨340199, by rfl⟩ : syracuseStep 453599 = 680399) B680399
theorem B257231 : Blo 131789 257231 := bstep (se 1 (by rfl) ⟨192923, by rfl⟩ : syracuseStep 257231 = 385847) B385847
theorem B224491 : Blo 131789 224491 := bstep (se 1 (by rfl) ⟨168368, by rfl⟩ : syracuseStep 224491 = 336737) B336737
theorem B389053 : Blo 131789 389053 := bstep (se 3 (by rfl) ⟨72947, by rfl⟩ : syracuseStep 389053 = 145895) B145895
theorem B225659 : Blo 131789 225659 := bstep (se 1 (by rfl) ⟨169244, by rfl⟩ : syracuseStep 225659 = 338489) B338489
theorem B225929 : Blo 131789 225929 := bstep (se 2 (by rfl) ⟨84723, by rfl⟩ : syracuseStep 225929 = 169447) B169447
theorem B685097 : Blo 131789 685097 := bstep (se 2 (by rfl) ⟨256911, by rfl⟩ : syracuseStep 685097 = 513823) B513823
theorem B3437963 : Blo 131789 3437963 := bstep (se 1 (by rfl) ⟨2578472, by rfl⟩ : syracuseStep 3437963 = 5156945) B5156945
theorem B1832539 : Blo 131789 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B456353 : Blo 131789 456353 := bstep (se 2 (by rfl) ⟨171132, by rfl⟩ : syracuseStep 456353 = 342265) B342265
theorem B817307 : Blo 131789 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B227495 : Blo 131789 227495 := bstep (se 1 (by rfl) ⟨170621, by rfl⟩ : syracuseStep 227495 = 341243) B341243
theorem B456893 : Blo 131789 456893 := bstep (se 3 (by rfl) ⟨85667, by rfl⟩ : syracuseStep 456893 = 171335) B171335
theorem B425159 : Blo 131789 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B1637729 : Blo 131789 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B1867819 : Blo 131789 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B229787 : Blo 131789 229787 := bstep (se 1 (by rfl) ⟨172340, by rfl⟩ : syracuseStep 229787 = 344681) B344681
theorem B1016225 : Blo 131789 1016225 := bstep (se 2 (by rfl) ⟨381084, by rfl⟩ : syracuseStep 1016225 = 762169) B762169
theorem B131839 : Blo 131789 131839 := bstep (se 1 (by rfl) ⟨98879, by rfl⟩ : syracuseStep 131839 = 197759) B197759
theorem B131931 : Blo 131789 131931 := bstep (se 1 (by rfl) ⟨98948, by rfl⟩ : syracuseStep 131931 = 197897) B197897
theorem B1442873 : Blo 131789 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B132251 : Blo 131789 132251 := bstep (se 1 (by rfl) ⟨99188, by rfl⟩ : syracuseStep 132251 = 198377) B198377
theorem B132255 : Blo 131789 132255 := bstep (se 1 (by rfl) ⟨99191, by rfl⟩ : syracuseStep 132255 = 198383) B198383
theorem B132423 : Blo 131789 132423 := bstep (se 1 (by rfl) ⟨99317, by rfl⟩ : syracuseStep 132423 = 198635) B198635
theorem B132591 : Blo 131789 132591 := bstep (se 1 (by rfl) ⟨99443, by rfl⟩ : syracuseStep 132591 = 198887) B198887
theorem B132607 : Blo 131789 132607 := bstep (se 1 (by rfl) ⟨99455, by rfl⟩ : syracuseStep 132607 = 198911) B198911
theorem B132699 : Blo 131789 132699 := bstep (se 1 (by rfl) ⟨99524, by rfl⟩ : syracuseStep 132699 = 199049) B199049
theorem B722627 : Blo 131789 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B231401 : Blo 131789 231401 := bstep (se 2 (by rfl) ⟨86775, by rfl⟩ : syracuseStep 231401 = 173551) B173551
theorem B854009 : Blo 131789 854009 := bstep (se 2 (by rfl) ⟨320253, by rfl⟩ : syracuseStep 854009 = 640507) B640507
theorem B198875 : Blo 131789 198875 := bstep (se 1 (by rfl) ⟨149156, by rfl⟩ : syracuseStep 198875 = 298313) B298313
theorem B919775 : Blo 131789 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B1018169 : Blo 131789 1018169 := bstep (se 2 (by rfl) ⟨381813, by rfl⟩ : syracuseStep 1018169 = 763627) B763627
theorem B133439 : Blo 131789 133439 := bstep (se 1 (by rfl) ⟨100079, by rfl⟩ : syracuseStep 133439 = 200159) B200159
theorem B133479 : Blo 131789 133479 := bstep (se 1 (by rfl) ⟨100109, by rfl⟩ : syracuseStep 133479 = 200219) B200219
theorem B199103 : Blo 131789 199103 := bstep (se 1 (by rfl) ⟨149327, by rfl⟩ : syracuseStep 199103 = 298655) B298655
theorem B133567 : Blo 131789 133567 := bstep (se 1 (by rfl) ⟨100175, by rfl⟩ : syracuseStep 133567 = 200351) B200351
theorem B133743 : Blo 131789 133743 := bstep (se 1 (by rfl) ⟨100307, by rfl⟩ : syracuseStep 133743 = 200615) B200615
theorem B133759 : Blo 131789 133759 := bstep (se 1 (by rfl) ⟨100319, by rfl⟩ : syracuseStep 133759 = 200639) B200639
theorem B133863 : Blo 131789 133863 := bstep (se 1 (by rfl) ⟨100397, by rfl⟩ : syracuseStep 133863 = 200795) B200795
theorem B1837799 : Blo 131789 1837799 := bstep (se 1 (by rfl) ⟨1378349, by rfl⟩ : syracuseStep 1837799 = 2756699) B2756699
theorem B199403 : Blo 131789 199403 := bstep (se 1 (by rfl) ⟨149552, by rfl⟩ : syracuseStep 199403 = 299105) B299105
theorem B133959 : Blo 131789 133959 := bstep (se 1 (by rfl) ⟨100469, by rfl⟩ : syracuseStep 133959 = 200939) B200939
theorem B199535 : Blo 131789 199535 := bstep (se 1 (by rfl) ⟨149651, by rfl⟩ : syracuseStep 199535 = 299303) B299303
theorem B133999 : Blo 131789 133999 := bstep (se 1 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 133999 = 200999) B200999
theorem B134175 : Blo 131789 134175 := bstep (se 1 (by rfl) ⟨100631, by rfl⟩ : syracuseStep 134175 = 201263) B201263
theorem B298025 : Blo 131789 298025 := bstep (se 2 (by rfl) ⟨111759, by rfl⟩ : syracuseStep 298025 = 223519) B223519
theorem B461897 : Blo 131789 461897 := bstep (se 2 (by rfl) ⟨173211, by rfl⟩ : syracuseStep 461897 = 346423) B346423
theorem B8621153 : Blo 131789 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B134311 : Blo 131789 134311 := bstep (se 1 (by rfl) ⟨100733, by rfl⟩ : syracuseStep 134311 = 201467) B201467
theorem B1019263 : Blo 131789 1019263 := bstep (se 1 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 1019263 = 1528895) B1528895
theorem B134559 : Blo 131789 134559 := bstep (se 1 (by rfl) ⟨100919, by rfl⟩ : syracuseStep 134559 = 201839) B201839
theorem B134607 : Blo 131789 134607 := bstep (se 1 (by rfl) ⟨100955, by rfl⟩ : syracuseStep 134607 = 201911) B201911
theorem B200303 : Blo 131789 200303 := bstep (se 1 (by rfl) ⟨150227, by rfl⟩ : syracuseStep 200303 = 300455) B300455
theorem B134767 : Blo 131789 134767 := bstep (se 1 (by rfl) ⟨101075, by rfl⟩ : syracuseStep 134767 = 202151) B202151
theorem B200375 : Blo 131789 200375 := bstep (se 1 (by rfl) ⟨150281, by rfl⟩ : syracuseStep 200375 = 300563) B300563
theorem B200423 : Blo 131789 200423 := bstep (se 1 (by rfl) ⟨150317, by rfl⟩ : syracuseStep 200423 = 300635) B300635
theorem B134887 : Blo 131789 134887 := bstep (se 1 (by rfl) ⟨101165, by rfl⟩ : syracuseStep 134887 = 202331) B202331
theorem B364297 : Blo 131789 364297 := bstep (se 2 (by rfl) ⟨136611, by rfl⟩ : syracuseStep 364297 = 273223) B273223
theorem B200927 : Blo 131789 200927 := bstep (se 1 (by rfl) ⟨150695, by rfl⟩ : syracuseStep 200927 = 301391) B301391
theorem B135391 : Blo 131789 135391 := bstep (se 1 (by rfl) ⟨101543, by rfl⟩ : syracuseStep 135391 = 203087) B203087
theorem B692459 : Blo 131789 692459 := bstep (se 1 (by rfl) ⟨519344, by rfl⟩ : syracuseStep 692459 = 1038689) B1038689
theorem B135407 : Blo 131789 135407 := bstep (se 1 (by rfl) ⟨101555, by rfl⟩ : syracuseStep 135407 = 203111) B203111
theorem B200987 : Blo 131789 200987 := bstep (se 1 (by rfl) ⟨150740, by rfl⟩ : syracuseStep 200987 = 301481) B301481
theorem B135451 : Blo 131789 135451 := bstep (se 1 (by rfl) ⟨101588, by rfl⟩ : syracuseStep 135451 = 203177) B203177
theorem B299321 : Blo 131789 299321 := bstep (se 2 (by rfl) ⟨112245, by rfl⟩ : syracuseStep 299321 = 224491) B224491
theorem B135707 : Blo 131789 135707 := bstep (se 1 (by rfl) ⟨101780, by rfl⟩ : syracuseStep 135707 = 203561) B203561
theorem B954935 : Blo 131789 954935 := bstep (se 1 (by rfl) ⟨716201, by rfl⟩ : syracuseStep 954935 = 1432403) B1432403
theorem B201407 : Blo 131789 201407 := bstep (se 1 (by rfl) ⟨151055, by rfl⟩ : syracuseStep 201407 = 302111) B302111
theorem B168743 : Blo 131789 168743 := bstep (se 1 (by rfl) ⟨126557, by rfl⟩ : syracuseStep 168743 = 253115) B253115
theorem B201695 : Blo 131789 201695 := bstep (se 1 (by rfl) ⟨151271, by rfl⟩ : syracuseStep 201695 = 302543) B302543
theorem B35493065 : Blo 131789 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B202793 : Blo 131789 202793 := bstep (se 2 (by rfl) ⟨76047, by rfl⟩ : syracuseStep 202793 = 152095) B152095
theorem B1022057 : Blo 131789 1022057 := bstep (se 2 (by rfl) ⟨383271, by rfl⟩ : syracuseStep 1022057 = 766543) B766543
theorem B17406515 : Blo 131789 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B334601 : Blo 131789 334601 := bstep (se 2 (by rfl) ⟨125475, by rfl⟩ : syracuseStep 334601 = 250951) B250951
theorem B433259 : Blo 131789 433259 := bstep (se 1 (by rfl) ⟨324944, by rfl⟩ : syracuseStep 433259 = 649889) B649889
theorem B564367 : Blo 131789 564367 := bstep (se 1 (by rfl) ⟨423275, by rfl⟩ : syracuseStep 564367 = 846551) B846551
theorem B302399 : Blo 131789 302399 := bstep (se 1 (by rfl) ⟨226799, by rfl⟩ : syracuseStep 302399 = 453599) B453599
theorem B171487 : Blo 131789 171487 := bstep (se 1 (by rfl) ⟨128615, by rfl⟩ : syracuseStep 171487 = 257231) B257231
theorem B729263 : Blo 131789 729263 := bstep (se 1 (by rfl) ⟨546947, by rfl⟩ : syracuseStep 729263 = 1093895) B1093895
theorem B304235 : Blo 131789 304235 := bstep (se 1 (by rfl) ⟨228176, by rfl⟩ : syracuseStep 304235 = 456353) B456353
theorem B304595 : Blo 131789 304595 := bstep (se 1 (by rfl) ⟨228446, by rfl⟩ : syracuseStep 304595 = 456893) B456893
theorem B927683 : Blo 131789 927683 := bstep (se 1 (by rfl) ⟨695762, by rfl⟩ : syracuseStep 927683 = 1391525) B1391525
theorem B1091819 : Blo 131789 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B2861689 : Blo 131789 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B502433 : Blo 131789 502433 := bstep (se 2 (by rfl) ⟨188412, by rfl⟩ : syracuseStep 502433 = 376825) B376825
theorem B338651 : Blo 131789 338651 := bstep (se 1 (by rfl) ⟨253988, by rfl⟩ : syracuseStep 338651 = 507977) B507977
theorem B503131 : Blo 131789 503131 := bstep (se 1 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 503131 = 754697) B754697
theorem B4566365 : Blo 131789 4566365 := bstep (se 3 (by rfl) ⟨856193, by rfl⟩ : syracuseStep 4566365 = 1712387) B1712387
theorem B1912409 : Blo 131789 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B339623 : Blo 131789 339623 := bstep (se 1 (by rfl) ⟨254717, by rfl⟩ : syracuseStep 339623 = 509435) B509435
theorem B339835 : Blo 131789 339835 := bstep (se 1 (by rfl) ⟨254876, by rfl⟩ : syracuseStep 339835 = 509753) B509753
theorem B209017 : Blo 131789 209017 := bstep (se 2 (by rfl) ⟨78381, by rfl⟩ : syracuseStep 209017 = 156763) B156763
theorem B1028371 : Blo 131789 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B2175335 : Blo 131789 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B341273 : Blo 131789 341273 := bstep (se 2 (by rfl) ⟨127977, by rfl⟩ : syracuseStep 341273 = 255955) B255955
theorem B538319 : Blo 131789 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B14005993 : Blo 131789 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B341779 : Blo 131789 341779 := bstep (se 1 (by rfl) ⟨256334, by rfl⟩ : syracuseStep 341779 = 512669) B512669
theorem B505835 : Blo 131789 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B2898017 : Blo 131789 2898017 := bstep (se 2 (by rfl) ⟨1086756, by rfl⟩ : syracuseStep 2898017 = 2173513) B2173513
theorem B1030319 : Blo 131789 1030319 := bstep (se 1 (by rfl) ⟨772739, by rfl⟩ : syracuseStep 1030319 = 1545479) B1545479
theorem B244127 : Blo 131789 244127 := bstep (se 1 (by rfl) ⟨183095, by rfl⟩ : syracuseStep 244127 = 366191) B366191
theorem B408559 : Blo 131789 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B146495 : Blo 131789 146495 := bstep (se 1 (by rfl) ⟨109871, by rfl⟩ : syracuseStep 146495 = 219743) B219743
theorem B867671 : Blo 131789 867671 := bstep (se 1 (by rfl) ⟨650753, by rfl⟩ : syracuseStep 867671 = 1301507) B1301507
theorem B671165 : Blo 131789 671165 := bstep (se 3 (by rfl) ⟨125843, by rfl⟩ : syracuseStep 671165 = 251687) B251687
theorem B310825 : Blo 131789 310825 := bstep (se 2 (by rfl) ⟨116559, by rfl⟩ : syracuseStep 310825 = 233119) B233119
theorem B2670191 : Blo 131789 2670191 := bstep (se 1 (by rfl) ⟨2002643, by rfl⟩ : syracuseStep 2670191 = 4005287) B4005287
theorem B3620999 : Blo 131789 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B2933657 : Blo 131789 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B2606995 : Blo 131789 2606995 := bstep (se 1 (by rfl) ⟨1955246, by rfl⟩ : syracuseStep 2606995 = 3910493) B3910493
theorem B2443385 : Blo 131789 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B2345435 : Blo 131789 2345435 := bstep (se 1 (by rfl) ⟨1759076, by rfl⟩ : syracuseStep 2345435 = 3518153) B3518153
theorem B3852947 : Blo 131789 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B150439 : Blo 131789 150439 := bstep (se 1 (by rfl) ⟨112829, by rfl⟩ : syracuseStep 150439 = 225659) B225659
theorem B445391 : Blo 131789 445391 := bstep (se 1 (by rfl) ⟨334043, by rfl⟩ : syracuseStep 445391 = 668087) B668087
theorem B150619 : Blo 131789 150619 := bstep (se 1 (by rfl) ⟨112964, by rfl⟩ : syracuseStep 150619 = 225929) B225929
theorem B445715 : Blo 131789 445715 := bstep (se 1 (by rfl) ⟨334286, by rfl⟩ : syracuseStep 445715 = 668573) B668573
theorem B445823 : Blo 131789 445823 := bstep (se 1 (by rfl) ⟨334367, by rfl⟩ : syracuseStep 445823 = 668735) B668735
theorem B27512459 : Blo 131789 27512459 := bstep (se 1 (by rfl) ⟨20634344, by rfl⟩ : syracuseStep 27512459 = 41268689) B41268689
theorem B544871 : Blo 131789 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B151663 : Blo 131789 151663 := bstep (se 1 (by rfl) ⟨113747, by rfl⟩ : syracuseStep 151663 = 227495) B227495
theorem B250283 : Blo 131789 250283 := bstep (se 1 (by rfl) ⟨187712, by rfl⟩ : syracuseStep 250283 = 375425) B375425
theorem B283439 : Blo 131789 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B1922555 : Blo 131789 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B448415 : Blo 131789 448415 := bstep (se 1 (by rfl) ⟨336311, by rfl⟩ : syracuseStep 448415 = 672623) B672623
theorem B317351 : Blo 131789 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B677807 : Blo 131789 677807 := bstep (se 1 (by rfl) ⟨508355, by rfl⟩ : syracuseStep 677807 = 1016711) B1016711
theorem B252143 : Blo 131789 252143 := bstep (se 1 (by rfl) ⟨189107, by rfl⟩ : syracuseStep 252143 = 378215) B378215
theorem B547145 : Blo 131789 547145 := bstep (se 2 (by rfl) ⟨205179, by rfl⟩ : syracuseStep 547145 = 410359) B410359
theorem B1268095 : Blo 131789 1268095 := bstep (se 1 (by rfl) ⟨951071, by rfl⟩ : syracuseStep 1268095 = 1902143) B1902143
theorem B11819641 : Blo 131789 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B3889853 : Blo 131789 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B7232273 : Blo 131789 7232273 := bstep (se 2 (by rfl) ⟨2712102, by rfl⟩ : syracuseStep 7232273 = 5424205) B5424205
theorem B1006505 : Blo 131789 1006505 := bstep (se 2 (by rfl) ⟨377439, by rfl⟩ : syracuseStep 1006505 = 754879) B754879
theorem B252895 : Blo 131789 252895 := bstep (se 1 (by rfl) ⟨189671, by rfl⟩ : syracuseStep 252895 = 379343) B379343
theorem B449657 : Blo 131789 449657 := bstep (se 2 (by rfl) ⟨168621, by rfl⟩ : syracuseStep 449657 = 337243) B337243
theorem B449819 : Blo 131789 449819 := bstep (se 1 (by rfl) ⟨337364, by rfl⟩ : syracuseStep 449819 = 674729) B674729
theorem B679913 : Blo 131789 679913 := bstep (se 2 (by rfl) ⟨254967, by rfl⟩ : syracuseStep 679913 = 509935) B509935
theorem B614441 : Blo 131789 614441 := bstep (se 2 (by rfl) ⟨230415, by rfl⟩ : syracuseStep 614441 = 460831) B460831
theorem B188743 : Blo 131789 188743 := bstep (se 1 (by rfl) ⟨141557, by rfl⟩ : syracuseStep 188743 = 283115) B283115
theorem B189535 : Blo 131789 189535 := bstep (se 1 (by rfl) ⟨142151, by rfl⟩ : syracuseStep 189535 = 284303) B284303
theorem B4908221 : Blo 131789 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B386461 : Blo 131789 386461 := bstep (se 3 (by rfl) ⟨72461, by rfl⟩ : syracuseStep 386461 = 144923) B144923
theorem B190127 : Blo 131789 190127 := bstep (se 1 (by rfl) ⟨142595, by rfl⟩ : syracuseStep 190127 = 285191) B285191
theorem B2910167 : Blo 131789 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B256031 : Blo 131789 256031 := bstep (se 1 (by rfl) ⟨192023, by rfl⟩ : syracuseStep 256031 = 384047) B384047
theorem B518737 : Blo 131789 518737 := bstep (se 2 (by rfl) ⟨194526, by rfl⟩ : syracuseStep 518737 = 389053) B389053
theorem B224167 : Blo 131789 224167 := bstep (se 1 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 224167 = 336251) B336251
theorem B3894317 : Blo 131789 3894317 := bstep (se 3 (by rfl) ⟨730184, by rfl⟩ : syracuseStep 3894317 = 1460369) B1460369
theorem B257519 : Blo 131789 257519 := bstep (se 1 (by rfl) ⟨193139, by rfl⟩ : syracuseStep 257519 = 386279) B386279
theorem B1011365 : Blo 131789 1011365 := bstep (se 4 (by rfl) ⟨94815, by rfl⟩ : syracuseStep 1011365 = 189631) B189631
theorem B257755 : Blo 131789 257755 := bstep (se 1 (by rfl) ⟨193316, by rfl⟩ : syracuseStep 257755 = 386633) B386633
theorem B192223 : Blo 131789 192223 := bstep (se 1 (by rfl) ⟨144167, by rfl⟩ : syracuseStep 192223 = 288335) B288335
theorem B683801 : Blo 131789 683801 := bstep (se 2 (by rfl) ⟨256425, by rfl⟩ : syracuseStep 683801 = 512851) B512851
theorem B454571 : Blo 131789 454571 := bstep (se 1 (by rfl) ⟨340928, by rfl⟩ : syracuseStep 454571 = 681857) B681857
theorem B389245 : Blo 131789 389245 := bstep (se 3 (by rfl) ⟨72983, by rfl⟩ : syracuseStep 389245 = 145967) B145967
theorem B226793 : Blo 131789 226793 := bstep (se 2 (by rfl) ⟨85047, by rfl⟩ : syracuseStep 226793 = 170095) B170095
theorem B685907 : Blo 131789 685907 := bstep (se 1 (by rfl) ⟨514430, by rfl⟩ : syracuseStep 685907 = 1028861) B1028861
theorem B1603475 : Blo 131789 1603475 := bstep (se 1 (by rfl) ⟨1202606, by rfl⟩ : syracuseStep 1603475 = 2405213) B2405213
theorem B456731 : Blo 131789 456731 := bstep (se 1 (by rfl) ⟨342548, by rfl⟩ : syracuseStep 456731 = 685097) B685097
theorem B2291975 : Blo 131789 2291975 := bstep (se 1 (by rfl) ⟨1718981, by rfl⟩ : syracuseStep 2291975 = 3437963) B3437963
theorem B15694117 : Blo 131789 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B751963 : Blo 131789 751963 := bstep (se 1 (by rfl) ⟨563972, by rfl⟩ : syracuseStep 751963 = 1127945) B1127945
theorem B28146653 : Blo 131789 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B752921 : Blo 131789 752921 := bstep (se 2 (by rfl) ⟨282345, by rfl⟩ : syracuseStep 752921 = 564691) B564691
theorem B982529 : Blo 131789 982529 := bstep (se 2 (by rfl) ⟨368448, by rfl⟩ : syracuseStep 982529 = 736897) B736897
theorem B2490425 : Blo 131789 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B132583 : Blo 131789 132583 := bstep (se 1 (by rfl) ⟨99437, by rfl⟩ : syracuseStep 132583 = 198875) B198875
theorem B132735 : Blo 131789 132735 := bstep (se 1 (by rfl) ⟨99551, by rfl⟩ : syracuseStep 132735 = 199103) B199103
theorem B132935 : Blo 131789 132935 := bstep (se 1 (by rfl) ⟨99701, by rfl⟩ : syracuseStep 132935 = 199403) B199403
theorem B133023 : Blo 131789 133023 := bstep (se 1 (by rfl) ⟨99767, by rfl⟩ : syracuseStep 133023 = 199535) B199535
theorem B296927 : Blo 131789 296927 := bstep (se 1 (by rfl) ⟨222695, by rfl⟩ : syracuseStep 296927 = 445391) B445391
theorem B198683 : Blo 131789 198683 := bstep (se 1 (by rfl) ⟨149012, by rfl⟩ : syracuseStep 198683 = 298025) B298025
theorem B755837 : Blo 131789 755837 := bstep (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) B283439
theorem B297143 : Blo 131789 297143 := bstep (se 1 (by rfl) ⟨222857, by rfl⟩ : syracuseStep 297143 = 445715) B445715
theorem B297215 : Blo 131789 297215 := bstep (se 1 (by rfl) ⟨222911, by rfl⟩ : syracuseStep 297215 = 445823) B445823
theorem B133535 : Blo 131789 133535 := bstep (se 1 (by rfl) ⟨100151, by rfl⟩ : syracuseStep 133535 = 200303) B200303
theorem B133583 : Blo 131789 133583 := bstep (se 1 (by rfl) ⟨100187, by rfl⟩ : syracuseStep 133583 = 200375) B200375
theorem B133615 : Blo 131789 133615 := bstep (se 1 (by rfl) ⟨100211, by rfl⟩ : syracuseStep 133615 = 200423) B200423
theorem B3475993 : Blo 131789 3475993 := bstep (se 2 (by rfl) ⟨1303497, by rfl⟩ : syracuseStep 3475993 = 2606995) B2606995
theorem B363247 : Blo 131789 363247 := bstep (se 1 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 363247 = 544871) B544871
theorem B133951 : Blo 131789 133951 := bstep (se 1 (by rfl) ⟨100463, by rfl⟩ : syracuseStep 133951 = 200927) B200927
theorem B461639 : Blo 131789 461639 := bstep (se 1 (by rfl) ⟨346229, by rfl⟩ : syracuseStep 461639 = 692459) B692459
theorem B133991 : Blo 131789 133991 := bstep (se 1 (by rfl) ⟨100493, by rfl⟩ : syracuseStep 133991 = 200987) B200987
theorem B199547 : Blo 131789 199547 := bstep (se 1 (by rfl) ⟨149660, by rfl⟩ : syracuseStep 199547 = 299321) B299321
theorem B166855 : Blo 131789 166855 := bstep (se 1 (by rfl) ⟨125141, by rfl⟩ : syracuseStep 166855 = 250283) B250283
theorem B134271 : Blo 131789 134271 := bstep (se 1 (by rfl) ⟨100703, by rfl⟩ : syracuseStep 134271 = 201407) B201407
theorem B134463 : Blo 131789 134463 := bstep (se 1 (by rfl) ⟨100847, by rfl⟩ : syracuseStep 134463 = 201695) B201695
theorem B691649 : Blo 131789 691649 := bstep (se 2 (by rfl) ⟨259368, by rfl⟩ : syracuseStep 691649 = 518737) B518737
theorem B23662043 : Blo 131789 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1281703 : Blo 131789 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B298889 : Blo 131789 298889 := bstep (se 2 (by rfl) ⟨112083, by rfl⟩ : syracuseStep 298889 = 224167) B224167
theorem B200585 : Blo 131789 200585 := bstep (se 2 (by rfl) ⟨75219, by rfl⟩ : syracuseStep 200585 = 150439) B150439
theorem B298943 : Blo 131789 298943 := bstep (se 1 (by rfl) ⟨224207, by rfl⟩ : syracuseStep 298943 = 448415) B448415
theorem B135195 : Blo 131789 135195 := bstep (se 1 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 135195 = 202793) B202793
theorem B200825 : Blo 131789 200825 := bstep (se 2 (by rfl) ⟨75309, by rfl⟩ : syracuseStep 200825 = 150619) B150619
theorem B168095 : Blo 131789 168095 := bstep (se 1 (by rfl) ⟨126071, by rfl⟩ : syracuseStep 168095 = 252143) B252143
theorem B364763 : Blo 131789 364763 := bstep (se 1 (by rfl) ⟨273572, by rfl⟩ : syracuseStep 364763 = 547145) B547145
theorem B11604343 : Blo 131789 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B2593235 : Blo 131789 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B4821515 : Blo 131789 4821515 := bstep (se 1 (by rfl) ⟨3616136, by rfl⟩ : syracuseStep 4821515 = 7232273) B7232273
theorem B299771 : Blo 131789 299771 := bstep (se 1 (by rfl) ⟨224828, by rfl⟩ : syracuseStep 299771 = 449657) B449657
theorem B299879 : Blo 131789 299879 := bstep (se 1 (by rfl) ⟨224909, by rfl⟩ : syracuseStep 299879 = 449819) B449819
theorem B201599 : Blo 131789 201599 := bstep (se 1 (by rfl) ⟨151199, by rfl⟩ : syracuseStep 201599 = 302399) B302399
theorem B202217 : Blo 131789 202217 := bstep (se 2 (by rfl) ⟨75831, by rfl⟩ : syracuseStep 202217 = 151663) B151663
theorem B202823 : Blo 131789 202823 := bstep (se 1 (by rfl) ⟨152117, by rfl⟩ : syracuseStep 202823 = 304235) B304235
theorem B203063 : Blo 131789 203063 := bstep (se 1 (by rfl) ⟨152297, by rfl⟩ : syracuseStep 203063 = 304595) B304595
theorem B1940111 : Blo 131789 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B170687 : Blo 131789 170687 := bstep (se 1 (by rfl) ⟨128015, by rfl⟩ : syracuseStep 170687 = 256031) B256031
theorem B727879 : Blo 131789 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B334955 : Blo 131789 334955 := bstep (se 1 (by rfl) ⟨251216, by rfl⟩ : syracuseStep 334955 = 502433) B502433
theorem B2596211 : Blo 131789 2596211 := bstep (se 1 (by rfl) ⟨1947158, by rfl⟩ : syracuseStep 2596211 = 3894317) B3894317
theorem B303047 : Blo 131789 303047 := bstep (se 1 (by rfl) ⟨227285, by rfl⟩ : syracuseStep 303047 = 454571) B454571
theorem B1450223 : Blo 131789 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B337193 : Blo 131789 337193 := bstep (se 2 (by rfl) ⟨126447, by rfl⟩ : syracuseStep 337193 = 252895) B252895
theorem B337223 : Blo 131789 337223 := bstep (se 1 (by rfl) ⟨252917, by rfl⟩ : syracuseStep 337223 = 505835) B505835
theorem B304487 : Blo 131789 304487 := bstep (se 1 (by rfl) ⟨228365, by rfl⟩ : syracuseStep 304487 = 456731) B456731
theorem B501947 : Blo 131789 501947 := bstep (se 1 (by rfl) ⟨376460, by rfl⟩ : syracuseStep 501947 = 752921) B752921
theorem B1780127 : Blo 131789 1780127 := bstep (se 1 (by rfl) ⟨1335095, by rfl⟩ : syracuseStep 1780127 = 2670191) B2670191
theorem B961915 : Blo 131789 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B4926901 : Blo 131789 4926901 := bstep (se 5 (by rfl) ⟨230948, by rfl⟩ : syracuseStep 4926901 = 461897) B461897
theorem B569339 : Blo 131789 569339 := bstep (se 1 (by rfl) ⟨427004, by rfl⟩ : syracuseStep 569339 = 854009) B854009
theorem B83701957 : Blo 131789 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B2568631 : Blo 131789 2568631 := bstep (se 1 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 2568631 = 3852947) B3852947
theorem B1225199 : Blo 131789 1225199 := bstep (se 1 (by rfl) ⟨918899, by rfl⟩ : syracuseStep 1225199 = 1837799) B1837799
theorem B5747435 : Blo 131789 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B636623 : Blo 131789 636623 := bstep (se 1 (by rfl) ⟨477467, by rfl⟩ : syracuseStep 636623 = 954935) B954935
theorem B3815585 : Blo 131789 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B211567 : Blo 131789 211567 := bstep (se 1 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 211567 = 317351) B317351
theorem B670841 : Blo 131789 670841 := bstep (se 2 (by rfl) ⟨251565, by rfl⟩ : syracuseStep 670841 = 503131) B503131
theorem B507005 : Blo 131789 507005 := bstep (se 3 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 507005 = 190127) B190127
theorem B1359017 : Blo 131789 1359017 := bstep (se 2 (by rfl) ⟨509631, by rfl⟩ : syracuseStep 1359017 = 1019263) B1019263
theorem B671003 : Blo 131789 671003 := bstep (se 1 (by rfl) ⟨503252, by rfl⟩ : syracuseStep 671003 = 1006505) B1006505
theorem B343673 : Blo 131789 343673 := bstep (se 2 (by rfl) ⟨128877, by rfl⟩ : syracuseStep 343673 = 257755) B257755
theorem B409627 : Blo 131789 409627 := bstep (se 1 (by rfl) ⟨307220, by rfl⟩ : syracuseStep 409627 = 614441) B614441
theorem B278689 : Blo 131789 278689 := bstep (se 2 (by rfl) ⟨104508, by rfl⟩ : syracuseStep 278689 = 209017) B209017
theorem B674243 : Blo 131789 674243 := bstep (se 1 (by rfl) ⟨505682, by rfl⟩ : syracuseStep 674243 = 1011365) B1011365
theorem B1002617 : Blo 131789 1002617 := bstep (se 2 (by rfl) ⟨375981, by rfl⟩ : syracuseStep 1002617 = 751963) B751963
theorem B1690793 : Blo 131789 1690793 := bstep (se 2 (by rfl) ⟨634047, by rfl⟩ : syracuseStep 1690793 = 1268095) B1268095
theorem B151195 : Blo 131789 151195 := bstep (se 1 (by rfl) ⟨113396, by rfl⟩ : syracuseStep 151195 = 226793) B226793
theorem B1068983 : Blo 131789 1068983 := bstep (se 1 (by rfl) ⟨801737, by rfl⟩ : syracuseStep 1068983 = 1603475) B1603475
theorem B544745 : Blo 131789 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B1527983 : Blo 131789 1527983 := bstep (se 1 (by rfl) ⟨1145987, by rfl⟩ : syracuseStep 1527983 = 2291975) B2291975
theorem B18764435 : Blo 131789 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B414433 : Blo 131789 414433 := bstep (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) B310825
theorem B578447 : Blo 131789 578447 := bstep (se 1 (by rfl) ⟨433835, by rfl⟩ : syracuseStep 578447 = 867671) B867671
theorem B447443 : Blo 131789 447443 := bstep (se 1 (by rfl) ⟨335582, by rfl⟩ : syracuseStep 447443 = 671165) B671165
theorem B2413999 : Blo 131789 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B153191 : Blo 131789 153191 := bstep (se 1 (by rfl) ⟨114893, by rfl⟩ : syracuseStep 153191 = 229787) B229787
theorem B677483 : Blo 131789 677483 := bstep (se 1 (by rfl) ⟨508112, by rfl⟩ : syracuseStep 677483 = 1016225) B1016225
theorem B251657 : Blo 131789 251657 := bstep (se 2 (by rfl) ⟨94371, by rfl⟩ : syracuseStep 251657 = 188743) B188743
theorem B1955771 : Blo 131789 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B481751 : Blo 131789 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B154267 : Blo 131789 154267 := bstep (se 1 (by rfl) ⟨115700, by rfl⟩ : syracuseStep 154267 = 231401) B231401
theorem B1628923 : Blo 131789 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B252713 : Blo 131789 252713 := bstep (se 2 (by rfl) ⟨94767, by rfl⟩ : syracuseStep 252713 = 189535) B189535
theorem B613183 : Blo 131789 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B678779 : Blo 131789 678779 := bstep (se 1 (by rfl) ⟨509084, by rfl⟩ : syracuseStep 678779 = 1018169) B1018169
theorem B1563623 : Blo 131789 1563623 := bstep (se 1 (by rfl) ⟨1172717, by rfl⟩ : syracuseStep 1563623 = 2345435) B2345435
theorem B515281 : Blo 131789 515281 := bstep (se 2 (by rfl) ⟨193230, by rfl⟩ : syracuseStep 515281 = 386461) B386461
theorem B449981 : Blo 131789 449981 := bstep (se 3 (by rfl) ⟨84371, by rfl⟩ : syracuseStep 449981 = 168743) B168743
theorem B18341639 : Blo 131789 18341639 := bstep (se 1 (by rfl) ⟨13756229, by rfl⟩ : syracuseStep 18341639 = 27512459) B27512459
theorem B451871 : Blo 131789 451871 := bstep (se 1 (by rfl) ⟨338903, by rfl⟩ : syracuseStep 451871 = 677807) B677807
theorem B681371 : Blo 131789 681371 := bstep (se 1 (by rfl) ⟨511028, by rfl⟩ : syracuseStep 681371 = 1022057) B1022057
theorem B223067 : Blo 131789 223067 := bstep (se 1 (by rfl) ⟨167300, by rfl⟩ : syracuseStep 223067 = 334601) B334601
theorem B288839 : Blo 131789 288839 := bstep (se 1 (by rfl) ⟨216629, by rfl⟩ : syracuseStep 288839 = 433259) B433259
theorem B256297 : Blo 131789 256297 := bstep (se 2 (by rfl) ⟨96111, by rfl⟩ : syracuseStep 256297 = 192223) B192223
theorem B485729 : Blo 131789 485729 := bstep (se 2 (by rfl) ⟨182148, by rfl⟩ : syracuseStep 485729 = 364297) B364297
theorem B453113 : Blo 131789 453113 := bstep (se 2 (by rfl) ⟨169917, by rfl⟩ : syracuseStep 453113 = 339835) B339835
theorem B453275 : Blo 131789 453275 := bstep (se 1 (by rfl) ⟨339956, by rfl⟩ : syracuseStep 453275 = 679913) B679913
theorem B486175 : Blo 131789 486175 := bstep (se 1 (by rfl) ⟨364631, by rfl⟩ : syracuseStep 486175 = 729263) B729263
theorem B518993 : Blo 131789 518993 := bstep (se 2 (by rfl) ⟨194622, by rfl⟩ : syracuseStep 518993 = 389245) B389245
theorem B1371161 : Blo 131789 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B3272147 : Blo 131789 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B618455 : Blo 131789 618455 := bstep (se 1 (by rfl) ⟨463841, by rfl⟩ : syracuseStep 618455 = 927683) B927683
theorem B225767 : Blo 131789 225767 := bstep (se 1 (by rfl) ⟨169325, by rfl⟩ : syracuseStep 225767 = 338651) B338651
theorem B3044243 : Blo 131789 3044243 := bstep (se 1 (by rfl) ⟨2283182, by rfl⟩ : syracuseStep 3044243 = 4566365) B4566365
theorem B18674657 : Blo 131789 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B455705 : Blo 131789 455705 := bstep (se 2 (by rfl) ⟨170889, by rfl⟩ : syracuseStep 455705 = 341779) B341779
theorem B1274939 : Blo 131789 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B226415 : Blo 131789 226415 := bstep (se 1 (by rfl) ⟨169811, by rfl⟩ : syracuseStep 226415 = 339623) B339623
theorem B455867 : Blo 131789 455867 := bstep (se 1 (by rfl) ⟨341900, by rfl⟩ : syracuseStep 455867 = 683801) B683801
theorem B390653 : Blo 131789 390653 := bstep (se 3 (by rfl) ⟨73247, by rfl⟩ : syracuseStep 390653 = 146495) B146495
theorem B15759521 : Blo 131789 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B227515 : Blo 131789 227515 := bstep (se 1 (by rfl) ⟨170636, by rfl⟩ : syracuseStep 227515 = 341273) B341273
theorem B358879 : Blo 131789 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B457271 : Blo 131789 457271 := bstep (se 1 (by rfl) ⟨342953, by rfl⟩ : syracuseStep 457271 = 685907) B685907
theorem B686717 : Blo 131789 686717 := bstep (se 3 (by rfl) ⟨128759, by rfl⟩ : syracuseStep 686717 = 257519) B257519
theorem B1932011 : Blo 131789 1932011 := bstep (se 1 (by rfl) ⟨1449008, by rfl⟩ : syracuseStep 1932011 = 2898017) B2898017
theorem B686879 : Blo 131789 686879 := bstep (se 1 (by rfl) ⟨515159, by rfl⟩ : syracuseStep 686879 = 1030319) B1030319
theorem B752489 : Blo 131789 752489 := bstep (se 2 (by rfl) ⟨282183, by rfl⟩ : syracuseStep 752489 = 564367) B564367
theorem B162751 : Blo 131789 162751 := bstep (se 1 (by rfl) ⟨122063, by rfl⟩ : syracuseStep 162751 = 244127) B244127
theorem B228649 : Blo 131789 228649 := bstep (se 2 (by rfl) ⟨85743, by rfl⟩ : syracuseStep 228649 = 171487) B171487
theorem B655019 : Blo 131789 655019 := bstep (se 1 (by rfl) ⟨491264, by rfl⟩ : syracuseStep 655019 = 982529) B982529
theorem B197951 : Blo 131789 197951 := bstep (se 1 (by rfl) ⟨148463, by rfl⟩ : syracuseStep 197951 = 296927) B296927
theorem B132455 : Blo 131789 132455 := bstep (se 1 (by rfl) ⟨99341, by rfl⟩ : syracuseStep 132455 = 198683) B198683
theorem B198095 : Blo 131789 198095 := bstep (se 1 (by rfl) ⟨148571, by rfl⟩ : syracuseStep 198095 = 297143) B297143
theorem B198143 : Blo 131789 198143 := bstep (se 1 (by rfl) ⟨148607, by rfl⟩ : syracuseStep 198143 = 297215) B297215
theorem B133031 : Blo 131789 133031 := bstep (se 1 (by rfl) ⟨99773, by rfl⟩ : syracuseStep 133031 = 199547) B199547
theorem B461099 : Blo 131789 461099 := bstep (se 1 (by rfl) ⟨345824, by rfl⟩ : syracuseStep 461099 = 691649) B691649
theorem B199259 : Blo 131789 199259 := bstep (se 1 (by rfl) ⟨149444, by rfl⟩ : syracuseStep 199259 = 298889) B298889
theorem B133723 : Blo 131789 133723 := bstep (se 1 (by rfl) ⟨100292, by rfl⟩ : syracuseStep 133723 = 200585) B200585
theorem B199295 : Blo 131789 199295 := bstep (se 1 (by rfl) ⟨149471, by rfl⟩ : syracuseStep 199295 = 298943) B298943
theorem B363163 : Blo 131789 363163 := bstep (se 1 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 363163 = 544745) B544745
theorem B133883 : Blo 131789 133883 := bstep (se 1 (by rfl) ⟨100412, by rfl⟩ : syracuseStep 133883 = 200825) B200825
theorem B1018655 : Blo 131789 1018655 := bstep (se 1 (by rfl) ⟨763991, by rfl⟩ : syracuseStep 1018655 = 1527983) B1527983
theorem B3214343 : Blo 131789 3214343 := bstep (se 1 (by rfl) ⟨2410757, by rfl⟩ : syracuseStep 3214343 = 4821515) B4821515
theorem B199847 : Blo 131789 199847 := bstep (se 1 (by rfl) ⟨149885, by rfl⟩ : syracuseStep 199847 = 299771) B299771
theorem B199919 : Blo 131789 199919 := bstep (se 1 (by rfl) ⟨149939, by rfl⟩ : syracuseStep 199919 = 299879) B299879
theorem B134399 : Blo 131789 134399 := bstep (se 1 (by rfl) ⟨100799, by rfl⟩ : syracuseStep 134399 = 201599) B201599
theorem B298295 : Blo 131789 298295 := bstep (se 1 (by rfl) ⟨223721, by rfl⟩ : syracuseStep 298295 = 447443) B447443
theorem B822757 : Blo 131789 822757 := bstep (se 4 (by rfl) ⟨77133, by rfl⟩ : syracuseStep 822757 = 154267) B154267
theorem B134811 : Blo 131789 134811 := bstep (se 1 (by rfl) ⟨101108, by rfl⟩ : syracuseStep 134811 = 202217) B202217
theorem B167771 : Blo 131789 167771 := bstep (se 1 (by rfl) ⟨125828, by rfl⟩ : syracuseStep 167771 = 251657) B251657
theorem B1937317 : Blo 131789 1937317 := bstep (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) B363247
theorem B135215 : Blo 131789 135215 := bstep (se 1 (by rfl) ⟨101411, by rfl⟩ : syracuseStep 135215 = 202823) B202823
theorem B135375 : Blo 131789 135375 := bstep (se 1 (by rfl) ⟨101531, by rfl⟩ : syracuseStep 135375 = 203063) B203063
theorem B1282553 : Blo 131789 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B168475 : Blo 131789 168475 := bstep (se 1 (by rfl) ⟨126356, by rfl⟩ : syracuseStep 168475 = 252713) B252713
theorem B201593 : Blo 131789 201593 := bstep (se 2 (by rfl) ⟨75597, by rfl⟩ : syracuseStep 201593 = 151195) B151195
theorem B1708937 : Blo 131789 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B299987 : Blo 131789 299987 := bstep (se 1 (by rfl) ⟨224990, by rfl⟩ : syracuseStep 299987 = 449981) B449981
theorem B12227759 : Blo 131789 12227759 := bstep (se 1 (by rfl) ⟨9170819, by rfl⟩ : syracuseStep 12227759 = 18341639) B18341639
theorem B202031 : Blo 131789 202031 := bstep (se 1 (by rfl) ⟨151523, by rfl⟩ : syracuseStep 202031 = 303047) B303047
theorem B15472457 : Blo 131789 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B301247 : Blo 131789 301247 := bstep (se 1 (by rfl) ⟨225935, by rfl⟩ : syracuseStep 301247 = 451871) B451871
theorem B202991 : Blo 131789 202991 := bstep (se 1 (by rfl) ⟨152243, by rfl⟩ : syracuseStep 202991 = 304487) B304487
theorem B334631 : Blo 131789 334631 := bstep (se 1 (by rfl) ⟨250973, by rfl⟩ : syracuseStep 334631 = 501947) B501947
theorem B1186751 : Blo 131789 1186751 := bstep (se 1 (by rfl) ⟨890063, by rfl⟩ : syracuseStep 1186751 = 1780127) B1780127
theorem B302075 : Blo 131789 302075 := bstep (se 1 (by rfl) ⟨226556, by rfl⟩ : syracuseStep 302075 = 453113) B453113
theorem B302183 : Blo 131789 302183 := bstep (se 1 (by rfl) ⟨226637, by rfl⟩ : syracuseStep 302183 = 453275) B453275
theorem B3218665 : Blo 131789 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B303353 : Blo 131789 303353 := bstep (se 2 (by rfl) ⟨113757, by rfl⟩ : syracuseStep 303353 = 227515) B227515
theorem B303803 : Blo 131789 303803 := bstep (se 1 (by rfl) ⟨227852, by rfl⟩ : syracuseStep 303803 = 455705) B455705
theorem B303911 : Blo 131789 303911 := bstep (se 1 (by rfl) ⟨227933, by rfl⟩ : syracuseStep 303911 = 455867) B455867
theorem B2171897 : Blo 131789 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B304847 : Blo 131789 304847 := bstep (se 1 (by rfl) ⟨228635, by rfl⟩ : syracuseStep 304847 = 457271) B457271
theorem B304865 : Blo 131789 304865 := bstep (se 2 (by rfl) ⟨114324, by rfl⟩ : syracuseStep 304865 = 228649) B228649
theorem B1288007 : Blo 131789 1288007 := bstep (se 1 (by rfl) ⟨966005, by rfl⟩ : syracuseStep 1288007 = 1932011) B1932011
theorem B501659 : Blo 131789 501659 := bstep (se 1 (by rfl) ⟨376244, by rfl⟩ : syracuseStep 501659 = 752489) B752489
theorem B338003 : Blo 131789 338003 := bstep (se 1 (by rfl) ⟨253502, by rfl⟩ : syracuseStep 338003 = 507005) B507005
theorem B436679 : Blo 131789 436679 := bstep (se 1 (by rfl) ⟨327509, by rfl⟩ : syracuseStep 436679 = 655019) B655019
theorem B371585 : Blo 131789 371585 := bstep (se 2 (by rfl) ⟨139344, by rfl⟩ : syracuseStep 371585 = 278689) B278689
theorem B503891 : Blo 131789 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B668411 : Blo 131789 668411 := bstep (se 1 (by rfl) ⟨501308, by rfl⟩ : syracuseStep 668411 = 1002617) B1002617
theorem B1127195 : Blo 131789 1127195 := bstep (se 1 (by rfl) ⟨845396, by rfl⟩ : syracuseStep 1127195 = 1690793) B1690793
theorem B15774695 : Blo 131789 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B243175 : Blo 131789 243175 := bstep (se 1 (by rfl) ⟨182381, by rfl⟩ : syracuseStep 243175 = 364763) B364763
theorem B341729 : Blo 131789 341729 := bstep (se 2 (by rfl) ⟨128148, by rfl⟩ : syracuseStep 341729 = 256297) B256297
theorem B4634657 : Blo 131789 4634657 := bstep (se 2 (by rfl) ⟨1737996, by rfl⟩ : syracuseStep 4634657 = 3475993) B3475993
theorem B408509 : Blo 131789 408509 := bstep (se 3 (by rfl) ⟨76595, by rfl⟩ : syracuseStep 408509 = 153191) B153191
theorem B1293407 : Blo 131789 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B6569201 : Blo 131789 6569201 := bstep (se 2 (by rfl) ⟨2463450, by rfl⟩ : syracuseStep 6569201 = 4926901) B4926901
theorem B966815 : Blo 131789 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B3424841 : Blo 131789 3424841 := bstep (se 2 (by rfl) ⟨1284315, by rfl⟩ : syracuseStep 3424841 = 2568631) B2568631
theorem B148711 : Blo 131789 148711 := bstep (se 1 (by rfl) ⟨111533, by rfl⟩ : syracuseStep 148711 = 223067) B223067
theorem B345995 : Blo 131789 345995 := bstep (se 1 (by rfl) ⟨259496, by rfl⟩ : syracuseStep 345995 = 518993) B518993
theorem B1231037 : Blo 131789 1231037 := bstep (se 3 (by rfl) ⟨230819, by rfl⟩ : syracuseStep 1231037 = 461639) B461639
theorem B2181431 : Blo 131789 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B412303 : Blo 131789 412303 := bstep (se 1 (by rfl) ⟨309227, by rfl⟩ : syracuseStep 412303 = 618455) B618455
theorem B379559 : Blo 131789 379559 := bstep (se 1 (by rfl) ⟨284669, by rfl⟩ : syracuseStep 379559 = 569339) B569339
theorem B150511 : Blo 131789 150511 := bstep (se 1 (by rfl) ⟨112883, by rfl⟩ : syracuseStep 150511 = 225767) B225767
theorem B478505 : Blo 131789 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B150943 : Blo 131789 150943 := bstep (se 1 (by rfl) ⟨113207, by rfl⟩ : syracuseStep 150943 = 226415) B226415
theorem B282089 : Blo 131789 282089 := bstep (se 2 (by rfl) ⟨105783, by rfl⟩ : syracuseStep 282089 = 211567) B211567
theorem B970505 : Blo 131789 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B217001 : Blo 131789 217001 := bstep (se 2 (by rfl) ⟨81375, by rfl⟩ : syracuseStep 217001 = 162751) B162751
theorem B2543723 : Blo 131789 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B10506347 : Blo 131789 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B447227 : Blo 131789 447227 := bstep (se 1 (by rfl) ⟨335420, by rfl⟩ : syracuseStep 447227 = 670841) B670841
theorem B906011 : Blo 131789 906011 := bstep (se 1 (by rfl) ⟨679508, by rfl⟩ : syracuseStep 906011 = 1359017) B1359017
theorem B447335 : Blo 131789 447335 := bstep (se 1 (by rfl) ⟨335501, by rfl⟩ : syracuseStep 447335 = 671003) B671003
theorem B1660283 : Blo 131789 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B2184677 : Blo 131789 2184677 := bstep (se 4 (by rfl) ⟨204813, by rfl⟩ : syracuseStep 2184677 = 409627) B409627
theorem B448253 : Blo 131789 448253 := bstep (se 3 (by rfl) ⟨84047, by rfl⟩ : syracuseStep 448253 = 168095) B168095
theorem B449495 : Blo 131789 449495 := bstep (se 1 (by rfl) ⟨337121, by rfl⟩ : syracuseStep 449495 = 674243) B674243
theorem B712613 : Blo 131789 712613 := bstep (se 4 (by rfl) ⟨66807, by rfl⟩ : syracuseStep 712613 = 133615) B133615
theorem B712655 : Blo 131789 712655 := bstep (se 1 (by rfl) ⟨534491, by rfl⟩ : syracuseStep 712655 = 1068983) B1068983
theorem B1728823 : Blo 131789 1728823 := bstep (se 1 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 1728823 = 2593235) B2593235
theorem B12509623 : Blo 131789 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B385631 : Blo 131789 385631 := bstep (se 1 (by rfl) ⟨289223, by rfl⟩ : syracuseStep 385631 = 578447) B578447
theorem B648233 : Blo 131789 648233 := bstep (se 2 (by rfl) ⟨243087, by rfl⟩ : syracuseStep 648233 = 486175) B486175
theorem B451655 : Blo 131789 451655 := bstep (se 1 (by rfl) ⟨338741, by rfl⟩ : syracuseStep 451655 = 677483) B677483
theorem B222473 : Blo 131789 222473 := bstep (se 2 (by rfl) ⟨83427, by rfl⟩ : syracuseStep 222473 = 166855) B166855
theorem B1303847 : Blo 131789 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B321167 : Blo 131789 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B452519 : Blo 131789 452519 := bstep (se 1 (by rfl) ⟨339389, by rfl⟩ : syracuseStep 452519 = 678779) B678779
theorem B1042415 : Blo 131789 1042415 := bstep (se 1 (by rfl) ⟨781811, by rfl⟩ : syracuseStep 1042415 = 1563623) B1563623
theorem B223303 : Blo 131789 223303 := bstep (se 1 (by rfl) ⟨167477, by rfl⟩ : syracuseStep 223303 = 334955) B334955
theorem B1730807 : Blo 131789 1730807 := bstep (se 1 (by rfl) ⟨1298105, by rfl⟩ : syracuseStep 1730807 = 2596211) B2596211
theorem B111602609 : Blo 131789 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B224795 : Blo 131789 224795 := bstep (se 1 (by rfl) ⟨168596, by rfl⟩ : syracuseStep 224795 = 337193) B337193
theorem B224815 : Blo 131789 224815 := bstep (se 1 (by rfl) ⟨168611, by rfl⟩ : syracuseStep 224815 = 337223) B337223
theorem B454247 : Blo 131789 454247 := bstep (se 1 (by rfl) ⟨340685, by rfl⟩ : syracuseStep 454247 = 681371) B681371
theorem B552577 : Blo 131789 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B192559 : Blo 131789 192559 := bstep (se 1 (by rfl) ⟨144419, by rfl⟩ : syracuseStep 192559 = 288839) B288839
theorem B323819 : Blo 131789 323819 := bstep (se 1 (by rfl) ⟨242864, by rfl⟩ : syracuseStep 323819 = 485729) B485729
theorem B455165 : Blo 131789 455165 := bstep (se 3 (by rfl) ⟨85343, by rfl⟩ : syracuseStep 455165 = 170687) B170687
theorem B914107 : Blo 131789 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B816799 : Blo 131789 816799 := bstep (se 1 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 816799 = 1225199) B1225199
theorem B3831623 : Blo 131789 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B2029495 : Blo 131789 2029495 := bstep (se 1 (by rfl) ⟨1522121, by rfl⟩ : syracuseStep 2029495 = 3044243) B3044243
theorem B12449771 : Blo 131789 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B849959 : Blo 131789 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B260435 : Blo 131789 260435 := bstep (se 1 (by rfl) ⟨195326, by rfl⟩ : syracuseStep 260435 = 390653) B390653
theorem B817577 : Blo 131789 817577 := bstep (se 2 (by rfl) ⟨306591, by rfl⟩ : syracuseStep 817577 = 613183) B613183
theorem B424415 : Blo 131789 424415 := bstep (se 1 (by rfl) ⟨318311, by rfl⟩ : syracuseStep 424415 = 636623) B636623
theorem B687041 : Blo 131789 687041 := bstep (se 2 (by rfl) ⟨257640, by rfl⟩ : syracuseStep 687041 = 515281) B515281
theorem B457811 : Blo 131789 457811 := bstep (se 1 (by rfl) ⟨343358, by rfl⟩ : syracuseStep 457811 = 686717) B686717
theorem B457919 : Blo 131789 457919 := bstep (se 1 (by rfl) ⟨343439, by rfl⟩ : syracuseStep 457919 = 686879) B686879
theorem B229115 : Blo 131789 229115 := bstep (se 1 (by rfl) ⟨171836, by rfl⟩ : syracuseStep 229115 = 343673) B343673
theorem B131967 : Blo 131789 131967 := bstep (se 1 (by rfl) ⟨98975, by rfl⟩ : syracuseStep 131967 = 197951) B197951
theorem B132063 : Blo 131789 132063 := bstep (se 1 (by rfl) ⟨99047, by rfl⟩ : syracuseStep 132063 = 198095) B198095
theorem B132095 : Blo 131789 132095 := bstep (se 1 (by rfl) ⟨99071, by rfl⟩ : syracuseStep 132095 = 198143) B198143
theorem B230663 : Blo 131789 230663 := bstep (se 1 (by rfl) ⟨172997, by rfl⟩ : syracuseStep 230663 = 345995) B345995
theorem B820691 : Blo 131789 820691 := bstep (se 1 (by rfl) ⟨615518, by rfl⟩ : syracuseStep 820691 = 1231037) B1231037
theorem B198281 : Blo 131789 198281 := bstep (se 2 (by rfl) ⟨74355, by rfl⟩ : syracuseStep 198281 = 148711) B148711
theorem B132839 : Blo 131789 132839 := bstep (se 1 (by rfl) ⟨99629, by rfl⟩ : syracuseStep 132839 = 199259) B199259
theorem B132863 : Blo 131789 132863 := bstep (se 1 (by rfl) ⟨99647, by rfl⟩ : syracuseStep 132863 = 199295) B199295
theorem B133231 : Blo 131789 133231 := bstep (se 1 (by rfl) ⟨99923, by rfl⟩ : syracuseStep 133231 = 199847) B199847
theorem B133279 : Blo 131789 133279 := bstep (se 1 (by rfl) ⟨99959, by rfl⟩ : syracuseStep 133279 = 199919) B199919
theorem B198863 : Blo 131789 198863 := bstep (se 1 (by rfl) ⟨149147, by rfl⟩ : syracuseStep 198863 = 298295) B298295
theorem B66717989 : Blo 131789 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B297737 : Blo 131789 297737 := bstep (se 2 (by rfl) ⟨111651, by rfl⟩ : syracuseStep 297737 = 223303) B223303
theorem B855035 : Blo 131789 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B298151 : Blo 131789 298151 := bstep (se 1 (by rfl) ⟨223613, by rfl⟩ : syracuseStep 298151 = 447227) B447227
theorem B298223 : Blo 131789 298223 := bstep (se 1 (by rfl) ⟨223667, by rfl⟩ : syracuseStep 298223 = 447335) B447335
theorem B134395 : Blo 131789 134395 := bstep (se 1 (by rfl) ⟨100796, by rfl⟩ : syracuseStep 134395 = 201593) B201593
theorem B199991 : Blo 131789 199991 := bstep (se 1 (by rfl) ⟨149993, by rfl⟩ : syracuseStep 199991 = 299987) B299987
theorem B134687 : Blo 131789 134687 := bstep (se 1 (by rfl) ⟨101015, by rfl⟩ : syracuseStep 134687 = 202031) B202031
theorem B298835 : Blo 131789 298835 := bstep (se 1 (by rfl) ⟨224126, by rfl⟩ : syracuseStep 298835 = 448253) B448253
theorem B200681 : Blo 131789 200681 := bstep (se 2 (by rfl) ⟨75255, by rfl⟩ : syracuseStep 200681 = 150511) B150511
theorem B200831 : Blo 131789 200831 := bstep (se 1 (by rfl) ⟨150623, by rfl⟩ : syracuseStep 200831 = 301247) B301247
theorem B135327 : Blo 131789 135327 := bstep (se 1 (by rfl) ⟨101495, by rfl⟩ : syracuseStep 135327 = 202991) B202991
theorem B201257 : Blo 131789 201257 := bstep (se 2 (by rfl) ⟨75471, by rfl⟩ : syracuseStep 201257 = 150943) B150943
theorem B791167 : Blo 131789 791167 := bstep (se 1 (by rfl) ⟨593375, by rfl⟩ : syracuseStep 791167 = 1186751) B1186751
theorem B299663 : Blo 131789 299663 := bstep (se 1 (by rfl) ⟨224747, by rfl⟩ : syracuseStep 299663 = 449495) B449495
theorem B201383 : Blo 131789 201383 := bstep (se 1 (by rfl) ⟨151037, by rfl⟩ : syracuseStep 201383 = 302075) B302075
theorem B299753 : Blo 131789 299753 := bstep (se 2 (by rfl) ⟨112407, by rfl⟩ : syracuseStep 299753 = 224815) B224815
theorem B201455 : Blo 131789 201455 := bstep (se 1 (by rfl) ⟨151091, by rfl⟩ : syracuseStep 201455 = 302183) B302183
theorem B202235 : Blo 131789 202235 := bstep (se 1 (by rfl) ⟨151676, by rfl⟩ : syracuseStep 202235 = 303353) B303353
theorem B202535 : Blo 131789 202535 := bstep (se 1 (by rfl) ⟨151901, by rfl⟩ : syracuseStep 202535 = 303803) B303803
theorem B202607 : Blo 131789 202607 := bstep (se 1 (by rfl) ⟨151955, by rfl⟩ : syracuseStep 202607 = 303911) B303911
theorem B1447931 : Blo 131789 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B432155 : Blo 131789 432155 := bstep (se 1 (by rfl) ⟨324116, by rfl⟩ : syracuseStep 432155 = 648233) B648233
theorem B301103 : Blo 131789 301103 := bstep (se 1 (by rfl) ⟨225827, by rfl⟩ : syracuseStep 301103 = 451655) B451655
theorem B694493 : Blo 131789 694493 := bstep (se 3 (by rfl) ⟨130217, by rfl⟩ : syracuseStep 694493 = 260435) B260435
theorem B1218809 : Blo 131789 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B203231 : Blo 131789 203231 := bstep (se 1 (by rfl) ⟨152423, by rfl⟩ : syracuseStep 203231 = 304847) B304847
theorem B203243 : Blo 131789 203243 := bstep (se 1 (by rfl) ⟨152432, by rfl⟩ : syracuseStep 203243 = 304865) B304865
theorem B858671 : Blo 131789 858671 := bstep (se 1 (by rfl) ⟨644003, by rfl⟩ : syracuseStep 858671 = 1288007) B1288007
theorem B334439 : Blo 131789 334439 := bstep (se 1 (by rfl) ⟨250829, by rfl⟩ : syracuseStep 334439 = 501659) B501659
theorem B301679 : Blo 131789 301679 := bstep (se 1 (by rfl) ⟨226259, by rfl⟩ : syracuseStep 301679 = 452519) B452519
theorem B694943 : Blo 131789 694943 := bstep (se 1 (by rfl) ⟨521207, by rfl⟩ : syracuseStep 694943 = 1042415) B1042415
theorem B1153871 : Blo 131789 1153871 := bstep (se 1 (by rfl) ⟨865403, by rfl⟩ : syracuseStep 1153871 = 1730807) B1730807
theorem B1089065 : Blo 131789 1089065 := bstep (se 2 (by rfl) ⟨408399, by rfl⟩ : syracuseStep 1089065 = 816799) B816799
theorem B990893 : Blo 131789 990893 := bstep (se 3 (by rfl) ⟨185792, by rfl⟩ : syracuseStep 990893 = 371585) B371585
theorem B302831 : Blo 131789 302831 := bstep (se 1 (by rfl) ⟨227123, by rfl⟩ : syracuseStep 302831 = 454247) B454247
theorem B335927 : Blo 131789 335927 := bstep (se 1 (by rfl) ⟨251945, by rfl⟩ : syracuseStep 335927 = 503891) B503891
theorem B303443 : Blo 131789 303443 := bstep (se 1 (by rfl) ⟨227582, by rfl⟩ : syracuseStep 303443 = 455165) B455165
theorem B8299847 : Blo 131789 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B3089771 : Blo 131789 3089771 := bstep (se 1 (by rfl) ⟨2317328, by rfl⟩ : syracuseStep 3089771 = 4634657) B4634657
theorem B566639 : Blo 131789 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B272339 : Blo 131789 272339 := bstep (se 1 (by rfl) ⟨204254, by rfl⟩ : syracuseStep 272339 = 408509) B408509
theorem B305207 : Blo 131789 305207 := bstep (se 1 (by rfl) ⟨228905, by rfl⟩ : syracuseStep 305207 = 457811) B457811
theorem B862271 : Blo 131789 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B305279 : Blo 131789 305279 := bstep (se 1 (by rfl) ⟨228959, by rfl⟩ : syracuseStep 305279 = 457919) B457919
theorem B2305097 : Blo 131789 2305097 := bstep (se 2 (by rfl) ⟨864411, by rfl⟩ : syracuseStep 2305097 = 1728823) B1728823
theorem B307399 : Blo 131789 307399 := bstep (se 1 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 307399 = 461099) B461099
theorem B1454287 : Blo 131789 1454287 := bstep (se 1 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 1454287 = 2181431) B2181431
theorem B2142895 : Blo 131789 2142895 := bstep (se 1 (by rfl) ⟨1607171, by rfl⟩ : syracuseStep 2142895 = 3214343) B3214343
theorem B144667 : Blo 131789 144667 := bstep (se 1 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 144667 = 217001) B217001
theorem B604007 : Blo 131789 604007 := bstep (se 1 (by rfl) ⟨453005, by rfl⟩ : syracuseStep 604007 = 906011) B906011
theorem B1456451 : Blo 131789 1456451 := bstep (se 1 (by rfl) ⟨1092338, by rfl⟩ : syracuseStep 1456451 = 2184677) B2184677
theorem B1097009 : Blo 131789 1097009 := bstep (se 2 (by rfl) ⟨411378, by rfl⟩ : syracuseStep 1097009 = 822757) B822757
theorem B736769 : Blo 131789 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B475075 : Blo 131789 475075 := bstep (se 1 (by rfl) ⟨356306, by rfl⟩ : syracuseStep 475075 = 712613) B712613
theorem B475103 : Blo 131789 475103 := bstep (se 1 (by rfl) ⟨356327, by rfl⟩ : syracuseStep 475103 = 712655) B712655
theorem B148315 : Blo 131789 148315 := bstep (se 1 (by rfl) ⟨111236, by rfl⟩ : syracuseStep 148315 = 222473) B222473
theorem B869231 : Blo 131789 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B214111 : Blo 131789 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B74401739 : Blo 131789 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B149863 : Blo 131789 149863 := bstep (se 1 (by rfl) ⟨112397, by rfl⟩ : syracuseStep 149863 = 224795) B224795
theorem B2705993 : Blo 131789 2705993 := bstep (se 2 (by rfl) ⟨1014747, by rfl⟩ : syracuseStep 2705993 = 2029495) B2029495
theorem B215879 : Blo 131789 215879 := bstep (se 1 (by rfl) ⟨161909, by rfl⟩ : syracuseStep 215879 = 323819) B323819
theorem B445607 : Blo 131789 445607 := bstep (se 1 (by rfl) ⟨334205, by rfl⟩ : syracuseStep 445607 = 668411) B668411
theorem B545051 : Blo 131789 545051 := bstep (se 1 (by rfl) ⟨408788, by rfl⟩ : syracuseStep 545051 = 817577) B817577
theorem B282943 : Blo 131789 282943 := bstep (se 1 (by rfl) ⟨212207, by rfl⟩ : syracuseStep 282943 = 424415) B424415
theorem B4379467 : Blo 131789 4379467 := bstep (se 1 (by rfl) ⟨3284600, by rfl⟩ : syracuseStep 4379467 = 6569201) B6569201
theorem B447389 : Blo 131789 447389 := bstep (se 3 (by rfl) ⟨83885, by rfl⟩ : syracuseStep 447389 = 167771) B167771
theorem B152743 : Blo 131789 152743 := bstep (se 1 (by rfl) ⟨114557, by rfl⟩ : syracuseStep 152743 = 229115) B229115
theorem B644543 : Blo 131789 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B2283227 : Blo 131789 2283227 := bstep (se 1 (by rfl) ⟨1712420, by rfl⟩ : syracuseStep 2283227 = 3424841) B3424841
theorem B253039 : Blo 131789 253039 := bstep (se 1 (by rfl) ⟨189779, by rfl⟩ : syracuseStep 253039 = 379559) B379559
theorem B679103 : Blo 131789 679103 := bstep (se 1 (by rfl) ⟨509327, by rfl⟩ : syracuseStep 679103 = 1018655) B1018655
theorem B647003 : Blo 131789 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B1695815 : Blo 131789 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B7004231 : Blo 131789 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B1139291 : Blo 131789 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B8151839 : Blo 131789 8151839 := bstep (se 1 (by rfl) ⟨6113879, by rfl⟩ : syracuseStep 8151839 = 12227759) B12227759
theorem B549737 : Blo 131789 549737 := bstep (se 2 (by rfl) ⟨206151, by rfl⟩ : syracuseStep 549737 = 412303) B412303
theorem B484217 : Blo 131789 484217 := bstep (se 2 (by rfl) ⟨181581, by rfl⟩ : syracuseStep 484217 = 363163) B363163
theorem B1106855 : Blo 131789 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B10314971 : Blo 131789 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B223087 : Blo 131789 223087 := bstep (se 1 (by rfl) ⟨167315, by rfl⟩ : syracuseStep 223087 = 334631) B334631
theorem B2583089 : Blo 131789 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B256745 : Blo 131789 256745 := bstep (se 2 (by rfl) ⟨96279, by rfl⟩ : syracuseStep 256745 = 192559) B192559
theorem B257087 : Blo 131789 257087 := bstep (se 1 (by rfl) ⟨192815, by rfl⟩ : syracuseStep 257087 = 385631) B385631
theorem B224633 : Blo 131789 224633 := bstep (se 2 (by rfl) ⟨84237, by rfl⟩ : syracuseStep 224633 = 168475) B168475
theorem B225335 : Blo 131789 225335 := bstep (se 1 (by rfl) ⟨169001, by rfl⟩ : syracuseStep 225335 = 338003) B338003
theorem B291119 : Blo 131789 291119 := bstep (se 1 (by rfl) ⟨218339, by rfl⟩ : syracuseStep 291119 = 436679) B436679
theorem B324233 : Blo 131789 324233 := bstep (se 2 (by rfl) ⟨121587, by rfl⟩ : syracuseStep 324233 = 243175) B243175
theorem B751463 : Blo 131789 751463 := bstep (se 1 (by rfl) ⟨563597, by rfl⟩ : syracuseStep 751463 = 1127195) B1127195
theorem B10516463 : Blo 131789 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B1276013 : Blo 131789 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B227819 : Blo 131789 227819 := bstep (se 1 (by rfl) ⟨170864, by rfl⟩ : syracuseStep 227819 = 341729) B341729
theorem B2554415 : Blo 131789 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B752237 : Blo 131789 752237 := bstep (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) B282089
theorem B4291553 : Blo 131789 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B458027 : Blo 131789 458027 := bstep (se 1 (by rfl) ⟨343520, by rfl⟩ : syracuseStep 458027 = 687041) B687041
theorem B132187 : Blo 131789 132187 := bstep (se 1 (by rfl) ⟨99140, by rfl⟩ : syracuseStep 132187 = 198281) B198281
theorem B197753 : Blo 131789 197753 := bstep (se 2 (by rfl) ⟨74157, by rfl⟩ : syracuseStep 197753 = 148315) B148315
theorem B132575 : Blo 131789 132575 := bstep (se 1 (by rfl) ⟨99431, by rfl⟩ : syracuseStep 132575 = 198863) B198863
theorem B1509029 : Blo 131789 1509029 := bstep (se 4 (by rfl) ⟨141471, by rfl⟩ : syracuseStep 1509029 = 282943) B282943
theorem B1803995 : Blo 131789 1803995 := bstep (se 1 (by rfl) ⟨1352996, by rfl⟩ : syracuseStep 1803995 = 2705993) B2705993
theorem B198491 : Blo 131789 198491 := bstep (se 1 (by rfl) ⟨148868, by rfl⟩ : syracuseStep 198491 = 297737) B297737
theorem B297071 : Blo 131789 297071 := bstep (se 1 (by rfl) ⟨222803, by rfl⟩ : syracuseStep 297071 = 445607) B445607
theorem B198767 : Blo 131789 198767 := bstep (se 1 (by rfl) ⟨149075, by rfl⟩ : syracuseStep 198767 = 298151) B298151
theorem B198815 : Blo 131789 198815 := bstep (se 1 (by rfl) ⟨149111, by rfl⟩ : syracuseStep 198815 = 298223) B298223
theorem B133327 : Blo 131789 133327 := bstep (se 1 (by rfl) ⟨99995, by rfl⟩ : syracuseStep 133327 = 199991) B199991
theorem B297449 : Blo 131789 297449 := bstep (se 2 (by rfl) ⟨111543, by rfl⟩ : syracuseStep 297449 = 223087) B223087
theorem B199223 : Blo 131789 199223 := bstep (se 1 (by rfl) ⟨149417, by rfl⟩ : syracuseStep 199223 = 298835) B298835
theorem B133787 : Blo 131789 133787 := bstep (se 1 (by rfl) ⟨100340, by rfl⟩ : syracuseStep 133787 = 200681) B200681
theorem B133887 : Blo 131789 133887 := bstep (se 1 (by rfl) ⟨100415, by rfl⟩ : syracuseStep 133887 = 200831) B200831
theorem B363367 : Blo 131789 363367 := bstep (se 1 (by rfl) ⟨272525, by rfl⟩ : syracuseStep 363367 = 545051) B545051
theorem B134171 : Blo 131789 134171 := bstep (se 1 (by rfl) ⟨100628, by rfl⟩ : syracuseStep 134171 = 201257) B201257
theorem B199775 : Blo 131789 199775 := bstep (se 1 (by rfl) ⟨149831, by rfl⟩ : syracuseStep 199775 = 299663) B299663
theorem B134255 : Blo 131789 134255 := bstep (se 1 (by rfl) ⟨100691, by rfl⟩ : syracuseStep 134255 = 201383) B201383
theorem B199817 : Blo 131789 199817 := bstep (se 2 (by rfl) ⟨74931, by rfl⟩ : syracuseStep 199817 = 149863) B149863
theorem B199835 : Blo 131789 199835 := bstep (se 1 (by rfl) ⟨149876, by rfl⟩ : syracuseStep 199835 = 299753) B299753
theorem B134303 : Blo 131789 134303 := bstep (se 1 (by rfl) ⟨100727, by rfl⟩ : syracuseStep 134303 = 201455) B201455
theorem B298259 : Blo 131789 298259 := bstep (se 1 (by rfl) ⟨223694, by rfl⟩ : syracuseStep 298259 = 447389) B447389
theorem B429695 : Blo 131789 429695 := bstep (se 1 (by rfl) ⟨322271, by rfl⟩ : syracuseStep 429695 = 644543) B644543
theorem B134823 : Blo 131789 134823 := bstep (se 1 (by rfl) ⟨101117, by rfl⟩ : syracuseStep 134823 = 202235) B202235
theorem B135023 : Blo 131789 135023 := bstep (se 1 (by rfl) ⟨101267, by rfl⟩ : syracuseStep 135023 = 202535) B202535
theorem B135071 : Blo 131789 135071 := bstep (se 1 (by rfl) ⟨101303, by rfl⟩ : syracuseStep 135071 = 202607) B202607
theorem B200735 : Blo 131789 200735 := bstep (se 1 (by rfl) ⟨150551, by rfl⟩ : syracuseStep 200735 = 301103) B301103
theorem B462995 : Blo 131789 462995 := bstep (se 1 (by rfl) ⟨347246, by rfl⟩ : syracuseStep 462995 = 694493) B694493
theorem B135487 : Blo 131789 135487 := bstep (se 1 (by rfl) ⟨101615, by rfl⟩ : syracuseStep 135487 = 203231) B203231
theorem B135495 : Blo 131789 135495 := bstep (se 1 (by rfl) ⟨101621, by rfl⟩ : syracuseStep 135495 = 203243) B203243
theorem B201119 : Blo 131789 201119 := bstep (se 1 (by rfl) ⟨150839, by rfl⟩ : syracuseStep 201119 = 301679) B301679
theorem B463295 : Blo 131789 463295 := bstep (se 1 (by rfl) ⟨347471, by rfl⟩ : syracuseStep 463295 = 694943) B694943
theorem B726043 : Blo 131789 726043 := bstep (se 1 (by rfl) ⟨544532, by rfl⟩ : syracuseStep 726043 = 1089065) B1089065
theorem B660595 : Blo 131789 660595 := bstep (se 1 (by rfl) ⟨495446, by rfl⟩ : syracuseStep 660595 = 990893) B990893
theorem B201887 : Blo 131789 201887 := bstep (se 1 (by rfl) ⟨151415, by rfl⟩ : syracuseStep 201887 = 302831) B302831
theorem B431335 : Blo 131789 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B1152413 : Blo 131789 1152413 := bstep (se 3 (by rfl) ⟨216077, by rfl⟩ : syracuseStep 1152413 = 432155) B432155
theorem B202295 : Blo 131789 202295 := bstep (se 1 (by rfl) ⟨151721, by rfl⟩ : syracuseStep 202295 = 303443) B303443
theorem B1939049 : Blo 131789 1939049 := bstep (se 2 (by rfl) ⟨727143, by rfl⟩ : syracuseStep 1939049 = 1454287) B1454287
theorem B759527 : Blo 131789 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B366491 : Blo 131789 366491 := bstep (se 1 (by rfl) ⟨274868, by rfl⟩ : syracuseStep 366491 = 549737) B549737
theorem B1054889 : Blo 131789 1054889 := bstep (se 2 (by rfl) ⟨395583, by rfl⟩ : syracuseStep 1054889 = 791167) B791167
theorem B2857193 : Blo 131789 2857193 := bstep (se 2 (by rfl) ⟨1071447, by rfl⟩ : syracuseStep 2857193 = 2142895) B2142895
theorem B5839289 : Blo 131789 5839289 := bstep (se 2 (by rfl) ⟨2189733, by rfl⟩ : syracuseStep 5839289 = 4379467) B4379467
theorem B203471 : Blo 131789 203471 := bstep (se 1 (by rfl) ⟨152603, by rfl⟩ : syracuseStep 203471 = 305207) B305207
theorem B203519 : Blo 131789 203519 := bstep (se 1 (by rfl) ⟨152639, by rfl⟩ : syracuseStep 203519 = 305279) B305279
theorem B203657 : Blo 131789 203657 := bstep (se 2 (by rfl) ⟨76371, by rfl⟩ : syracuseStep 203657 = 152743) B152743
theorem B171163 : Blo 131789 171163 := bstep (se 1 (by rfl) ⟨128372, by rfl⟩ : syracuseStep 171163 = 256745) B256745
theorem B171391 : Blo 131789 171391 := bstep (se 1 (by rfl) ⟨128543, by rfl⟩ : syracuseStep 171391 = 257087) B257087
theorem B11444141 : Blo 131789 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B500975 : Blo 131789 500975 := bstep (se 1 (by rfl) ⟨375731, by rfl⟩ : syracuseStep 500975 = 751463) B751463
theorem B402671 : Blo 131789 402671 := bstep (se 1 (by rfl) ⟨302003, by rfl⟩ : syracuseStep 402671 = 604007) B604007
theorem B337385 : Blo 131789 337385 := bstep (se 2 (by rfl) ⟨126519, by rfl⟩ : syracuseStep 337385 = 253039) B253039
theorem B501491 : Blo 131789 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B305351 : Blo 131789 305351 := bstep (se 1 (by rfl) ⟨229013, by rfl⟩ : syracuseStep 305351 = 458027) B458027
theorem B731339 : Blo 131789 731339 := bstep (se 1 (by rfl) ⟨548504, by rfl⟩ : syracuseStep 731339 = 1097009) B1097009
theorem B633433 : Blo 131789 633433 := bstep (se 2 (by rfl) ⟨237537, by rfl⟩ : syracuseStep 633433 = 475075) B475075
theorem B44478659 : Blo 131789 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B570023 : Blo 131789 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B1522151 : Blo 131789 1522151 := bstep (se 1 (by rfl) ⟨1141613, by rfl⟩ : syracuseStep 1522151 = 2283227) B2283227
theorem B965287 : Blo 131789 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B572447 : Blo 131789 572447 := bstep (se 1 (by rfl) ⟨429335, by rfl⟩ : syracuseStep 572447 = 858671) B858671
theorem B769247 : Blo 131789 769247 := bstep (se 1 (by rfl) ⟨576935, by rfl⟩ : syracuseStep 769247 = 1153871) B1153871
theorem B1130543 : Blo 131789 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B4669487 : Blo 131789 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B409865 : Blo 131789 409865 := bstep (se 2 (by rfl) ⟨153699, by rfl⟩ : syracuseStep 409865 = 307399) B307399
theorem B737903 : Blo 131789 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B377759 : Blo 131789 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B181559 : Blo 131789 181559 := bstep (se 1 (by rfl) ⟨136169, by rfl⟩ : syracuseStep 181559 = 272339) B272339
theorem B574847 : Blo 131789 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B1722059 : Blo 131789 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B575677 : Blo 131789 575677 := bstep (se 3 (by rfl) ⟨107939, by rfl⟩ : syracuseStep 575677 = 215879) B215879
theorem B149755 : Blo 131789 149755 := bstep (se 1 (by rfl) ⟨112316, by rfl⟩ : syracuseStep 149755 = 224633) B224633
theorem B150223 : Blo 131789 150223 := bstep (se 1 (by rfl) ⟨112667, by rfl⟩ : syracuseStep 150223 = 225335) B225335
theorem B216155 : Blo 131789 216155 := bstep (se 1 (by rfl) ⟨162116, by rfl⟩ : syracuseStep 216155 = 324233) B324233
theorem B970967 : Blo 131789 970967 := bstep (se 1 (by rfl) ⟨728225, by rfl⟩ : syracuseStep 970967 = 1456451) B1456451
theorem B151879 : Blo 131789 151879 := bstep (se 1 (by rfl) ⟨113909, by rfl⟩ : syracuseStep 151879 = 227819) B227819
theorem B1266941 : Blo 131789 1266941 := bstep (se 3 (by rfl) ⟨237551, by rfl⟩ : syracuseStep 1266941 = 475103) B475103
theorem B579487 : Blo 131789 579487 := bstep (se 1 (by rfl) ⟨434615, by rfl⟩ : syracuseStep 579487 = 869231) B869231
theorem B776317 : Blo 131789 776317 := bstep (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) B291119
theorem B153775 : Blo 131789 153775 := bstep (se 1 (by rfl) ⟨115331, by rfl⟩ : syracuseStep 153775 = 230663) B230663
theorem B547127 : Blo 131789 547127 := bstep (se 1 (by rfl) ⟨410345, by rfl⟩ : syracuseStep 547127 = 820691) B820691
theorem B49601159 : Blo 131789 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B285481 : Blo 131789 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B812539 : Blo 131789 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B222959 : Blo 131789 222959 := bstep (se 1 (by rfl) ⟨167219, by rfl⟩ : syracuseStep 222959 = 334439) B334439
theorem B452735 : Blo 131789 452735 := bstep (se 1 (by rfl) ⟨339551, by rfl⟩ : syracuseStep 452735 = 679103) B679103
theorem B223951 : Blo 131789 223951 := bstep (se 1 (by rfl) ⟨167963, by rfl⟩ : syracuseStep 223951 = 335927) B335927
theorem B5434559 : Blo 131789 5434559 := bstep (se 1 (by rfl) ⟨4075919, by rfl⟩ : syracuseStep 5434559 = 8151839) B8151839
theorem B322811 : Blo 131789 322811 := bstep (se 1 (by rfl) ⟨242108, by rfl⟩ : syracuseStep 322811 = 484217) B484217
theorem B6876647 : Blo 131789 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B5533231 : Blo 131789 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B2059847 : Blo 131789 2059847 := bstep (se 1 (by rfl) ⟨1544885, by rfl⟩ : syracuseStep 2059847 = 3089771) B3089771
theorem B192889 : Blo 131789 192889 := bstep (se 2 (by rfl) ⟨72333, by rfl⟩ : syracuseStep 192889 = 144667) B144667
theorem B1536731 : Blo 131789 1536731 := bstep (se 1 (by rfl) ⟨1152548, by rfl⟩ : syracuseStep 1536731 = 2305097) B2305097
theorem B7010975 : Blo 131789 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B850675 : Blo 131789 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1702943 : Blo 131789 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B491179 : Blo 131789 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B753695 : Blo 131789 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B3112991 : Blo 131789 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B491935 : Blo 131789 491935 := bstep (se 1 (by rfl) ⟨368951, by rfl⟩ : syracuseStep 491935 = 737903) B737903
theorem B131835 : Blo 131789 131835 := bstep (se 1 (by rfl) ⟨98876, by rfl⟩ : syracuseStep 131835 = 197753) B197753
theorem B1148039 : Blo 131789 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B132327 : Blo 131789 132327 := bstep (se 1 (by rfl) ⟨99245, by rfl⟩ : syracuseStep 132327 = 198491) B198491
theorem B198047 : Blo 131789 198047 := bstep (se 1 (by rfl) ⟨148535, by rfl⟩ : syracuseStep 198047 = 297071) B297071
theorem B132511 : Blo 131789 132511 := bstep (se 1 (by rfl) ⟨99383, by rfl⟩ : syracuseStep 132511 = 198767) B198767
theorem B132543 : Blo 131789 132543 := bstep (se 1 (by rfl) ⟨99407, by rfl⟩ : syracuseStep 132543 = 198815) B198815
theorem B198299 : Blo 131789 198299 := bstep (se 1 (by rfl) ⟨148724, by rfl⟩ : syracuseStep 198299 = 297449) B297449
theorem B132815 : Blo 131789 132815 := bstep (se 1 (by rfl) ⟨99611, by rfl⟩ : syracuseStep 132815 = 199223) B199223
theorem B1083385 : Blo 131789 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B133183 : Blo 131789 133183 := bstep (se 1 (by rfl) ⟨99887, by rfl⟩ : syracuseStep 133183 = 199775) B199775
theorem B133211 : Blo 131789 133211 := bstep (se 1 (by rfl) ⟨99908, by rfl⟩ : syracuseStep 133211 = 199817) B199817
theorem B133223 : Blo 131789 133223 := bstep (se 1 (by rfl) ⟨99917, by rfl⟩ : syracuseStep 133223 = 199835) B199835
theorem B198839 : Blo 131789 198839 := bstep (se 1 (by rfl) ⟨149129, by rfl⟩ : syracuseStep 198839 = 298259) B298259
theorem B133823 : Blo 131789 133823 := bstep (se 1 (by rfl) ⟨100367, by rfl⟩ : syracuseStep 133823 = 200735) B200735
theorem B134079 : Blo 131789 134079 := bstep (se 1 (by rfl) ⟨100559, by rfl⟩ : syracuseStep 134079 = 201119) B201119
theorem B199673 : Blo 131789 199673 := bstep (se 2 (by rfl) ⟨74877, by rfl⟩ : syracuseStep 199673 = 149755) B149755
theorem B134591 : Blo 131789 134591 := bstep (se 1 (by rfl) ⟨100943, by rfl⟩ : syracuseStep 134591 = 201887) B201887
theorem B298601 : Blo 131789 298601 := bstep (se 2 (by rfl) ⟨111975, by rfl⟩ : syracuseStep 298601 = 223951) B223951
theorem B200297 : Blo 131789 200297 := bstep (se 2 (by rfl) ⟨75111, by rfl⟩ : syracuseStep 200297 = 150223) B150223
theorem B134863 : Blo 131789 134863 := bstep (se 1 (by rfl) ⟨101147, by rfl⟩ : syracuseStep 134863 = 202295) B202295
theorem B1904795 : Blo 131789 1904795 := bstep (se 1 (by rfl) ⟨1428596, by rfl⟩ : syracuseStep 1904795 = 2857193) B2857193
theorem B364751 : Blo 131789 364751 := bstep (se 1 (by rfl) ⟨273563, by rfl⟩ : syracuseStep 364751 = 547127) B547127
theorem B33067439 : Blo 131789 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B135647 : Blo 131789 135647 := bstep (se 1 (by rfl) ⟨101735, by rfl⟩ : syracuseStep 135647 = 203471) B203471
theorem B135679 : Blo 131789 135679 := bstep (se 1 (by rfl) ⟨101759, by rfl⟩ : syracuseStep 135679 = 203519) B203519
theorem B135771 : Blo 131789 135771 := bstep (se 1 (by rfl) ⟨101828, by rfl⟩ : syracuseStep 135771 = 203657) B203657
theorem B7377641 : Blo 131789 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B202505 : Blo 131789 202505 := bstep (se 2 (by rfl) ⟨75939, by rfl⟩ : syracuseStep 202505 = 151879) B151879
theorem B333983 : Blo 131789 333983 := bstep (se 1 (by rfl) ⟨250487, by rfl⟩ : syracuseStep 333983 = 500975) B500975
theorem B268447 : Blo 131789 268447 := bstep (se 1 (by rfl) ⟨201335, by rfl⟩ : syracuseStep 268447 = 402671) B402671
theorem B334327 : Blo 131789 334327 := bstep (se 1 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 334327 = 501491) B501491
theorem B301823 : Blo 131789 301823 := bstep (se 1 (by rfl) ⟨226367, by rfl⟩ : syracuseStep 301823 = 452735) B452735
theorem B203567 : Blo 131789 203567 := bstep (se 1 (by rfl) ⟨152675, by rfl⟩ : syracuseStep 203567 = 305351) B305351
theorem B205033 : Blo 131789 205033 := bstep (se 2 (by rfl) ⟨76887, by rfl⟩ : syracuseStep 205033 = 153775) B153775
theorem B1024487 : Blo 131789 1024487 := bstep (se 1 (by rfl) ⟨768365, by rfl⟩ : syracuseStep 1024487 = 1536731) B1536731
theorem B1287049 : Blo 131789 1287049 := bstep (se 2 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 1287049 = 965287) B965287
theorem B1092973 : Blo 131789 1092973 := bstep (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) B409865
theorem B144103 : Blo 131789 144103 := bstep (se 1 (by rfl) ⟨108077, by rfl⟩ : syracuseStep 144103 = 216155) B216155
theorem B308663 : Blo 131789 308663 := bstep (se 1 (by rfl) ⟨231497, by rfl⟩ : syracuseStep 308663 = 462995) B462995
theorem B767569 : Blo 131789 767569 := bstep (se 2 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 767569 = 575677) B575677
theorem B308863 : Blo 131789 308863 := bstep (se 1 (by rfl) ⟨231647, by rfl⟩ : syracuseStep 308863 = 463295) B463295
theorem B768275 : Blo 131789 768275 := bstep (se 1 (by rfl) ⟨576206, by rfl⟩ : syracuseStep 768275 = 1152413) B1152413
theorem B1292699 : Blo 131789 1292699 := bstep (se 1 (by rfl) ⟨969524, by rfl⟩ : syracuseStep 1292699 = 1939049) B1939049
theorem B506351 : Blo 131789 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B703259 : Blo 131789 703259 := bstep (se 1 (by rfl) ⟨527444, by rfl⟩ : syracuseStep 703259 = 1054889) B1054889
theorem B148639 : Blo 131789 148639 := bstep (se 1 (by rfl) ⟨111479, by rfl⟩ : syracuseStep 148639 = 222959) B222959
theorem B968057 : Blo 131789 968057 := bstep (se 2 (by rfl) ⟨363021, by rfl⟩ : syracuseStep 968057 = 726043) B726043
theorem B575113 : Blo 131789 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B18695933 : Blo 131789 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B3623039 : Blo 131789 3623039 := bstep (se 1 (by rfl) ⟨2717279, by rfl⟩ : syracuseStep 3623039 = 5434559) B5434559
theorem B215207 : Blo 131789 215207 := bstep (se 1 (by rfl) ⟨161405, by rfl⟩ : syracuseStep 215207 = 322811) B322811
theorem B772649 : Blo 131789 772649 := bstep (se 2 (by rfl) ⟨289743, by rfl⟩ : syracuseStep 772649 = 579487) B579487
theorem B1526525 : Blo 131789 1526525 := bstep (se 3 (by rfl) ⟨286223, by rfl⟩ : syracuseStep 1526525 = 572447) B572447
theorem B1035089 : Blo 131789 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B380015 : Blo 131789 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B1134233 : Blo 131789 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B380641 : Blo 131789 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B1135295 : Blo 131789 1135295 := bstep (se 1 (by rfl) ⟨851471, by rfl⟩ : syracuseStep 1135295 = 1702943) B1702943
theorem B512831 : Blo 131789 512831 := bstep (se 1 (by rfl) ⟨384623, by rfl⟩ : syracuseStep 512831 = 769247) B769247
theorem B251839 : Blo 131789 251839 := bstep (se 1 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 251839 = 377759) B377759
theorem B383231 : Blo 131789 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B1006019 : Blo 131789 1006019 := bstep (se 1 (by rfl) ⟨754514, by rfl⟩ : syracuseStep 1006019 = 1509029) B1509029
theorem B1202663 : Blo 131789 1202663 := bstep (se 1 (by rfl) ⟨901997, by rfl⟩ : syracuseStep 1202663 = 1803995) B1803995
theorem B286463 : Blo 131789 286463 := bstep (se 1 (by rfl) ⟨214847, by rfl⟩ : syracuseStep 286463 = 429695) B429695
theorem B647311 : Blo 131789 647311 := bstep (se 1 (by rfl) ⟨485483, by rfl⟩ : syracuseStep 647311 = 970967) B970967
theorem B844577 : Blo 131789 844577 := bstep (se 2 (by rfl) ⟨316716, by rfl⟩ : syracuseStep 844577 = 633433) B633433
theorem B484157 : Blo 131789 484157 := bstep (se 3 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 484157 = 181559) B181559
theorem B844627 : Blo 131789 844627 := bstep (se 1 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 844627 = 1266941) B1266941
theorem B484489 : Blo 131789 484489 := bstep (se 2 (by rfl) ⟨181683, by rfl⟩ : syracuseStep 484489 = 363367) B363367
theorem B3892859 : Blo 131789 3892859 := bstep (se 1 (by rfl) ⟨2919644, by rfl⟩ : syracuseStep 3892859 = 5839289) B5839289
theorem B977309 : Blo 131789 977309 := bstep (se 3 (by rfl) ⟨183245, by rfl⟩ : syracuseStep 977309 = 366491) B366491
theorem B7629427 : Blo 131789 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B257185 : Blo 131789 257185 := bstep (se 2 (by rfl) ⟨96444, by rfl⟩ : syracuseStep 257185 = 192889) B192889
theorem B224923 : Blo 131789 224923 := bstep (se 1 (by rfl) ⟨168692, by rfl⟩ : syracuseStep 224923 = 337385) B337385
theorem B487559 : Blo 131789 487559 := bstep (se 1 (by rfl) ⟨365669, by rfl⟩ : syracuseStep 487559 = 731339) B731339
theorem B880793 : Blo 131789 880793 := bstep (se 2 (by rfl) ⟨330297, by rfl⟩ : syracuseStep 880793 = 660595) B660595
theorem B4584431 : Blo 131789 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B1373231 : Blo 131789 1373231 := bstep (se 1 (by rfl) ⟨1029923, by rfl⟩ : syracuseStep 1373231 = 2059847) B2059847
theorem B29652439 : Blo 131789 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B228217 : Blo 131789 228217 := bstep (se 2 (by rfl) ⟨85581, by rfl⟩ : syracuseStep 228217 = 171163) B171163
theorem B1014767 : Blo 131789 1014767 := bstep (se 1 (by rfl) ⟨761075, by rfl⟩ : syracuseStep 1014767 = 1522151) B1522151
theorem B228521 : Blo 131789 228521 := bstep (se 2 (by rfl) ⟨85695, by rfl⟩ : syracuseStep 228521 = 171391) B171391
theorem B654905 : Blo 131789 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B655913 : Blo 131789 655913 := bstep (se 2 (by rfl) ⟨245967, by rfl⟩ : syracuseStep 655913 = 491935) B491935
theorem B132031 : Blo 131789 132031 := bstep (se 1 (by rfl) ⟨99023, by rfl⟩ : syracuseStep 132031 = 198047) B198047
theorem B132199 : Blo 131789 132199 := bstep (se 1 (by rfl) ⟨99149, by rfl⟩ : syracuseStep 132199 = 198299) B198299
theorem B132559 : Blo 131789 132559 := bstep (se 1 (by rfl) ⟨99419, by rfl⟩ : syracuseStep 132559 = 198839) B198839
theorem B198185 : Blo 131789 198185 := bstep (se 2 (by rfl) ⟨74319, by rfl⟩ : syracuseStep 198185 = 148639) B148639
theorem B1017683 : Blo 131789 1017683 := bstep (se 1 (by rfl) ⟨763262, by rfl⟩ : syracuseStep 1017683 = 1526525) B1526525
theorem B690059 : Blo 131789 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B133115 : Blo 131789 133115 := bstep (se 1 (by rfl) ⟨99836, by rfl⟩ : syracuseStep 133115 = 199673) B199673
theorem B199067 : Blo 131789 199067 := bstep (se 1 (by rfl) ⟨149300, by rfl⟩ : syracuseStep 199067 = 298601) B298601
theorem B133531 : Blo 131789 133531 := bstep (se 1 (by rfl) ⟨100148, by rfl⟩ : syracuseStep 133531 = 200297) B200297
theorem B756155 : Blo 131789 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B1444513 : Blo 131789 1444513 := bstep (se 2 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 1444513 = 1083385) B1083385
theorem B756863 : Blo 131789 756863 := bstep (se 1 (by rfl) ⟨567647, by rfl⟩ : syracuseStep 756863 = 1135295) B1135295
theorem B4918427 : Blo 131789 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B135003 : Blo 131789 135003 := bstep (se 1 (by rfl) ⟨101252, by rfl⟩ : syracuseStep 135003 = 202505) B202505
theorem B201215 : Blo 131789 201215 := bstep (se 1 (by rfl) ⟨150911, by rfl⟩ : syracuseStep 201215 = 301823) B301823
theorem B135711 : Blo 131789 135711 := bstep (se 1 (by rfl) ⟨101783, by rfl⟩ : syracuseStep 135711 = 203567) B203567
theorem B299897 : Blo 131789 299897 := bstep (se 2 (by rfl) ⟨112461, by rfl⟩ : syracuseStep 299897 = 224923) B224923
theorem B563051 : Blo 131789 563051 := bstep (se 1 (by rfl) ⟨422288, by rfl⟩ : syracuseStep 563051 = 844577) B844577
theorem B2595239 : Blo 131789 2595239 := bstep (se 1 (by rfl) ⟨1946429, by rfl⟩ : syracuseStep 2595239 = 3892859) B3892859
theorem B1023425 : Blo 131789 1023425 := bstep (se 2 (by rfl) ⟨383784, by rfl⟩ : syracuseStep 1023425 = 767569) B767569
theorem B335785 : Blo 131789 335785 := bstep (se 2 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 335785 = 251839) B251839
theorem B3056287 : Blo 131789 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B205775 : Blo 131789 205775 := bstep (se 1 (by rfl) ⟨154331, by rfl⟩ : syracuseStep 205775 = 308663) B308663
theorem B304289 : Blo 131789 304289 := bstep (se 2 (by rfl) ⟨114108, by rfl⟩ : syracuseStep 304289 = 228217) B228217
theorem B861799 : Blo 131789 861799 := bstep (se 1 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 861799 = 1292699) B1292699
theorem B337567 : Blo 131789 337567 := bstep (se 1 (by rfl) ⟨253175, by rfl⟩ : syracuseStep 337567 = 506351) B506351
theorem B468839 : Blo 131789 468839 := bstep (se 1 (by rfl) ⟨351629, by rfl⟩ : syracuseStep 468839 = 703259) B703259
theorem B763901 : Blo 131789 763901 := bstep (se 3 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 763901 = 286463) B286463
theorem B436603 : Blo 131789 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B502463 : Blo 131789 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B2075327 : Blo 131789 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B863081 : Blo 131789 863081 := bstep (se 2 (by rfl) ⟨323655, by rfl⟩ : syracuseStep 863081 = 647311) B647311
theorem B273377 : Blo 131789 273377 := bstep (se 2 (by rfl) ⟨102516, by rfl⟩ : syracuseStep 273377 = 205033) B205033
theorem B765359 : Blo 131789 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B1126169 : Blo 131789 1126169 := bstep (se 2 (by rfl) ⟨422313, by rfl⟩ : syracuseStep 1126169 = 844627) B844627
theorem B12463955 : Blo 131789 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B1716065 : Blo 131789 1716065 := bstep (se 2 (by rfl) ⟨643524, by rfl⟩ : syracuseStep 1716065 = 1287049) B1287049
theorem B143471 : Blo 131789 143471 := bstep (se 1 (by rfl) ⟨107603, by rfl⟩ : syracuseStep 143471 = 215207) B215207
theorem B766817 : Blo 131789 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B243167 : Blo 131789 243167 := bstep (se 1 (by rfl) ⟨182375, by rfl⟩ : syracuseStep 243167 = 364751) B364751
theorem B10172569 : Blo 131789 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B342913 : Blo 131789 342913 := bstep (se 2 (by rfl) ⟨128592, by rfl⟩ : syracuseStep 342913 = 257185) B257185
theorem B670679 : Blo 131789 670679 := bstep (se 1 (by rfl) ⟨503009, by rfl⟩ : syracuseStep 670679 = 1006019) B1006019
theorem B801775 : Blo 131789 801775 := bstep (se 1 (by rfl) ⟨601331, by rfl⟩ : syracuseStep 801775 = 1202663) B1202663
theorem B1457297 : Blo 131789 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B507521 : Blo 131789 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B39536585 : Blo 131789 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B411817 : Blo 131789 411817 := bstep (se 2 (by rfl) ⟨154431, by rfl⟩ : syracuseStep 411817 = 308863) B308863
theorem B445769 : Blo 131789 445769 := bstep (se 2 (by rfl) ⟨167163, by rfl⟩ : syracuseStep 445769 = 334327) B334327
theorem B512183 : Blo 131789 512183 := bstep (se 1 (by rfl) ⟨384137, by rfl⟩ : syracuseStep 512183 = 768275) B768275
theorem B676511 : Blo 131789 676511 := bstep (se 1 (by rfl) ⟨507383, by rfl⟩ : syracuseStep 676511 = 1014767) B1014767
theorem B152347 : Blo 131789 152347 := bstep (se 1 (by rfl) ⟨114260, by rfl⟩ : syracuseStep 152347 = 228521) B228521
theorem B1300157 : Blo 131789 1300157 := bstep (se 3 (by rfl) ⟨243779, by rfl⟩ : syracuseStep 1300157 = 487559) B487559
theorem B645371 : Blo 131789 645371 := bstep (se 1 (by rfl) ⟨484028, by rfl⟩ : syracuseStep 645371 = 968057) B968057
theorem B2415359 : Blo 131789 2415359 := bstep (se 1 (by rfl) ⟨1811519, by rfl⟩ : syracuseStep 2415359 = 3623039) B3623039
theorem B645985 : Blo 131789 645985 := bstep (se 2 (by rfl) ⟨242244, by rfl⟩ : syracuseStep 645985 = 484489) B484489
theorem B515099 : Blo 131789 515099 := bstep (se 1 (by rfl) ⟨386324, by rfl⟩ : syracuseStep 515099 = 772649) B772649
theorem B253343 : Blo 131789 253343 := bstep (se 1 (by rfl) ⟨190007, by rfl⟩ : syracuseStep 253343 = 380015) B380015
theorem B1367549 : Blo 131789 1367549 := bstep (se 3 (by rfl) ⟨256415, by rfl⟩ : syracuseStep 1367549 = 512831) B512831
theorem B1269863 : Blo 131789 1269863 := bstep (se 1 (by rfl) ⟨952397, by rfl⟩ : syracuseStep 1269863 = 1904795) B1904795
theorem B3661949 : Blo 131789 3661949 := bstep (se 3 (by rfl) ⟨686615, by rfl⟩ : syracuseStep 3661949 = 1373231) B1373231
theorem B22044959 : Blo 131789 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B222655 : Blo 131789 222655 := bstep (se 1 (by rfl) ⟨166991, by rfl⟩ : syracuseStep 222655 = 333983) B333983
theorem B255487 : Blo 131789 255487 := bstep (se 1 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 255487 = 383231) B383231
theorem B682991 : Blo 131789 682991 := bstep (se 1 (by rfl) ⟨512243, by rfl⟩ : syracuseStep 682991 = 1024487) B1024487
theorem B322771 : Blo 131789 322771 := bstep (se 1 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 322771 = 484157) B484157
theorem B192137 : Blo 131789 192137 := bstep (se 2 (by rfl) ⟨72051, by rfl⟩ : syracuseStep 192137 = 144103) B144103
theorem B651539 : Blo 131789 651539 := bstep (se 1 (by rfl) ⟨488654, by rfl⟩ : syracuseStep 651539 = 977309) B977309
theorem B587195 : Blo 131789 587195 := bstep (se 1 (by rfl) ⟨440396, by rfl⟩ : syracuseStep 587195 = 880793) B880793
theorem B357929 : Blo 131789 357929 := bstep (se 2 (by rfl) ⟨134223, by rfl⟩ : syracuseStep 357929 = 268447) B268447
theorem B9765197 : Blo 131789 9765197 := bstep (se 3 (by rfl) ⟨1830974, by rfl⟩ : syracuseStep 9765197 = 3661949) B3661949
theorem B132123 : Blo 131789 132123 := bstep (se 1 (by rfl) ⟨99092, by rfl⟩ : syracuseStep 132123 = 198185) B198185
theorem B132711 : Blo 131789 132711 := bstep (se 1 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 132711 = 199067) B199067
theorem B296873 : Blo 131789 296873 := bstep (se 2 (by rfl) ⟨111327, by rfl⟩ : syracuseStep 296873 = 222655) B222655
theorem B3278951 : Blo 131789 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B1149065 : Blo 131789 1149065 := bstep (se 2 (by rfl) ⟨430899, by rfl⟩ : syracuseStep 1149065 = 861799) B861799
theorem B297179 : Blo 131789 297179 := bstep (se 1 (by rfl) ⟨222884, by rfl⟩ : syracuseStep 297179 = 445769) B445769
theorem B134143 : Blo 131789 134143 := bstep (se 1 (by rfl) ⟨100607, by rfl⟩ : syracuseStep 134143 = 201215) B201215
theorem B199931 : Blo 131789 199931 := bstep (se 1 (by rfl) ⟨149948, by rfl⟩ : syracuseStep 199931 = 299897) B299897
theorem B430247 : Blo 131789 430247 := bstep (se 1 (by rfl) ⟨322685, by rfl⟩ : syracuseStep 430247 = 645371) B645371
theorem B430361 : Blo 131789 430361 := bstep (se 2 (by rfl) ⟨161385, by rfl⟩ : syracuseStep 430361 = 322771) B322771
theorem B168895 : Blo 131789 168895 := bstep (se 1 (by rfl) ⟨126671, by rfl⟩ : syracuseStep 168895 = 253343) B253343
theorem B2593781 : Blo 131789 2593781 := bstep (se 5 (by rfl) ⟨121583, by rfl⟩ : syracuseStep 2593781 = 243167) B243167
theorem B1840157 : Blo 131789 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B137183 : Blo 131789 137183 := bstep (se 1 (by rfl) ⟨102887, by rfl⟩ : syracuseStep 137183 = 205775) B205775
theorem B202859 : Blo 131789 202859 := bstep (se 1 (by rfl) ⟨152144, by rfl⟩ : syracuseStep 202859 = 304289) B304289
theorem B203129 : Blo 131789 203129 := bstep (se 2 (by rfl) ⟨76173, by rfl⟩ : syracuseStep 203129 = 152347) B152347
theorem B334975 : Blo 131789 334975 := bstep (se 1 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 334975 = 502463) B502463
theorem B1383551 : Blo 131789 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B434359 : Blo 131789 434359 := bstep (se 1 (by rfl) ⟨325769, by rfl⟩ : syracuseStep 434359 = 651539) B651539
theorem B238619 : Blo 131789 238619 := bstep (se 1 (by rfl) ⟨178964, by rfl⟩ : syracuseStep 238619 = 357929) B357929
theorem B861313 : Blo 131789 861313 := bstep (se 2 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 861313 = 645985) B645985
theorem B338347 : Blo 131789 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B437275 : Blo 131789 437275 := bstep (se 1 (by rfl) ⟨327956, by rfl⟩ : syracuseStep 437275 = 655913) B655913
theorem B4075049 : Blo 131789 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B26357723 : Blo 131789 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B504103 : Blo 131789 504103 := bstep (se 1 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 504103 = 756155) B756155
theorem B340649 : Blo 131789 340649 := bstep (se 2 (by rfl) ⟨127743, by rfl⟩ : syracuseStep 340649 = 255487) B255487
theorem B504575 : Blo 131789 504575 := bstep (se 1 (by rfl) ⟨378431, by rfl⟩ : syracuseStep 504575 = 756863) B756863
theorem B341455 : Blo 131789 341455 := bstep (se 1 (by rfl) ⟨256091, by rfl⟩ : syracuseStep 341455 = 512183) B512183
theorem B866771 : Blo 131789 866771 := bstep (se 1 (by rfl) ⟨650078, by rfl⟩ : syracuseStep 866771 = 1300157) B1300157
theorem B375367 : Blo 131789 375367 := bstep (se 1 (by rfl) ⟨281525, by rfl⟩ : syracuseStep 375367 = 563051) B563051
theorem B343399 : Blo 131789 343399 := bstep (se 1 (by rfl) ⟨257549, by rfl⟩ : syracuseStep 343399 = 515099) B515099
theorem B14696639 : Blo 131789 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B312559 : Blo 131789 312559 := bstep (se 1 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 312559 = 468839) B468839
theorem B509267 : Blo 131789 509267 := bstep (se 1 (by rfl) ⟨381950, by rfl⟩ : syracuseStep 509267 = 763901) B763901
theorem B575387 : Blo 131789 575387 := bstep (se 1 (by rfl) ⟨431540, by rfl⟩ : syracuseStep 575387 = 863081) B863081
theorem B182251 : Blo 131789 182251 := bstep (se 1 (by rfl) ⟨136688, by rfl⟩ : syracuseStep 182251 = 273377) B273377
theorem B6440957 : Blo 131789 6440957 := bstep (se 3 (by rfl) ⟨1207679, by rfl⟩ : syracuseStep 6440957 = 2415359) B2415359
theorem B510239 : Blo 131789 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B8309303 : Blo 131789 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B511211 : Blo 131789 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B1069033 : Blo 131789 1069033 := bstep (se 2 (by rfl) ⟨400887, by rfl⟩ : syracuseStep 1069033 = 801775) B801775
theorem B512365 : Blo 131789 512365 := bstep (se 3 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 512365 = 192137) B192137
theorem B447119 : Blo 131789 447119 := bstep (se 1 (by rfl) ⟨335339, by rfl⟩ : syracuseStep 447119 = 670679) B670679
theorem B971531 : Blo 131789 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B447713 : Blo 131789 447713 := bstep (se 2 (by rfl) ⟨167892, by rfl⟩ : syracuseStep 447713 = 335785) B335785
theorem B382589 : Blo 131789 382589 := bstep (se 3 (by rfl) ⟨71735, by rfl⟩ : syracuseStep 382589 = 143471) B143471
theorem B678455 : Blo 131789 678455 := bstep (se 1 (by rfl) ⟨508841, by rfl⟩ : syracuseStep 678455 = 1017683) B1017683
theorem B450089 : Blo 131789 450089 := bstep (se 2 (by rfl) ⟨168783, by rfl⟩ : syracuseStep 450089 = 337567) B337567
theorem B549089 : Blo 131789 549089 := bstep (se 2 (by rfl) ⟨205908, by rfl⟩ : syracuseStep 549089 = 411817) B411817
theorem B451007 : Blo 131789 451007 := bstep (se 1 (by rfl) ⟨338255, by rfl⟩ : syracuseStep 451007 = 676511) B676511
theorem B582137 : Blo 131789 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B1926017 : Blo 131789 1926017 := bstep (se 2 (by rfl) ⟨722256, by rfl⟩ : syracuseStep 1926017 = 1444513) B1444513
theorem B1730159 : Blo 131789 1730159 := bstep (se 1 (by rfl) ⟨1297619, by rfl⟩ : syracuseStep 1730159 = 2595239) B2595239
theorem B682283 : Blo 131789 682283 := bstep (se 1 (by rfl) ⟨511712, by rfl⟩ : syracuseStep 682283 = 1023425) B1023425
theorem B911699 : Blo 131789 911699 := bstep (se 1 (by rfl) ⟨683774, by rfl⟩ : syracuseStep 911699 = 1367549) B1367549
theorem B846575 : Blo 131789 846575 := bstep (se 1 (by rfl) ⟨634931, by rfl⟩ : syracuseStep 846575 = 1269863) B1269863
theorem B455327 : Blo 131789 455327 := bstep (se 1 (by rfl) ⟨341495, by rfl⟩ : syracuseStep 455327 = 682991) B682991
theorem B750779 : Blo 131789 750779 := bstep (se 1 (by rfl) ⟨563084, by rfl⟩ : syracuseStep 750779 = 1126169) B1126169
theorem B1144043 : Blo 131789 1144043 := bstep (se 1 (by rfl) ⟨858032, by rfl⟩ : syracuseStep 1144043 = 1716065) B1716065
theorem B13563425 : Blo 131789 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B391463 : Blo 131789 391463 := bstep (se 1 (by rfl) ⟨293597, by rfl⟩ : syracuseStep 391463 = 587195) B587195
theorem B457217 : Blo 131789 457217 := bstep (se 2 (by rfl) ⟨171456, by rfl⟩ : syracuseStep 457217 = 342913) B342913
theorem B9797759 : Blo 131789 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B197915 : Blo 131789 197915 := bstep (se 1 (by rfl) ⟨148436, by rfl⟩ : syracuseStep 197915 = 296873) B296873
theorem B4293971 : Blo 131789 4293971 := bstep (se 1 (by rfl) ⟨3220478, by rfl⟩ : syracuseStep 4293971 = 6440957) B6440957
theorem B198119 : Blo 131789 198119 := bstep (se 1 (by rfl) ⟨148589, by rfl⟩ : syracuseStep 198119 = 297179) B297179
theorem B1148417 : Blo 131789 1148417 := bstep (se 2 (by rfl) ⟨430656, by rfl⟩ : syracuseStep 1148417 = 861313) B861313
theorem B5539535 : Blo 131789 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B133287 : Blo 131789 133287 := bstep (se 1 (by rfl) ⟨99965, by rfl⟩ : syracuseStep 133287 = 199931) B199931
theorem B1804517 : Blo 131789 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B298079 : Blo 131789 298079 := bstep (se 1 (by rfl) ⟨223559, by rfl⟩ : syracuseStep 298079 = 447119) B447119
theorem B298475 : Blo 131789 298475 := bstep (se 1 (by rfl) ⟨223856, by rfl⟩ : syracuseStep 298475 = 447713) B447713
theorem B135239 : Blo 131789 135239 := bstep (se 1 (by rfl) ⟨101429, by rfl⟩ : syracuseStep 135239 = 202859) B202859
theorem B135419 : Blo 131789 135419 := bstep (se 1 (by rfl) ⟨101564, by rfl⟩ : syracuseStep 135419 = 203129) B203129
theorem B922367 : Blo 131789 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B300059 : Blo 131789 300059 := bstep (se 1 (by rfl) ⟨225044, by rfl⟩ : syracuseStep 300059 = 450089) B450089
theorem B366059 : Blo 131789 366059 := bstep (se 1 (by rfl) ⟨274544, by rfl⟩ : syracuseStep 366059 = 549089) B549089
theorem B300671 : Blo 131789 300671 := bstep (se 1 (by rfl) ⟨225503, by rfl⟩ : syracuseStep 300671 = 451007) B451007
theorem B1284011 : Blo 131789 1284011 := bstep (se 1 (by rfl) ⟨963008, by rfl⟩ : syracuseStep 1284011 = 1926017) B1926017
theorem B1153439 : Blo 131789 1153439 := bstep (se 1 (by rfl) ⟨865079, by rfl⟩ : syracuseStep 1153439 = 1730159) B1730159
theorem B564383 : Blo 131789 564383 := bstep (se 1 (by rfl) ⟨423287, by rfl⟩ : syracuseStep 564383 = 846575) B846575
theorem B17571815 : Blo 131789 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B303551 : Blo 131789 303551 := bstep (se 1 (by rfl) ⟨227663, by rfl⟩ : syracuseStep 303551 = 455327) B455327
theorem B336383 : Blo 131789 336383 := bstep (se 1 (by rfl) ⟨252287, by rfl⟩ : syracuseStep 336383 = 504575) B504575
theorem B500489 : Blo 131789 500489 := bstep (se 2 (by rfl) ⟨187683, by rfl⟩ : syracuseStep 500489 = 375367) B375367
theorem B500519 : Blo 131789 500519 := bstep (se 1 (by rfl) ⟨375389, by rfl⟩ : syracuseStep 500519 = 750779) B750779
theorem B762695 : Blo 131789 762695 := bstep (se 1 (by rfl) ⟨572021, by rfl⟩ : syracuseStep 762695 = 1144043) B1144043
theorem B304811 : Blo 131789 304811 := bstep (se 1 (by rfl) ⟨228608, by rfl⟩ : syracuseStep 304811 = 457217) B457217
theorem B339511 : Blo 131789 339511 := bstep (se 1 (by rfl) ⟨254633, by rfl⟩ : syracuseStep 339511 = 509267) B509267
theorem B766043 : Blo 131789 766043 := bstep (se 1 (by rfl) ⟨574532, by rfl⟩ : syracuseStep 766043 = 1149065) B1149065
theorem B340159 : Blo 131789 340159 := bstep (se 1 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 340159 = 510239) B510239
theorem B340807 : Blo 131789 340807 := bstep (se 1 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 340807 = 511211) B511211
theorem B243001 : Blo 131789 243001 := bstep (se 2 (by rfl) ⟨91125, by rfl⟩ : syracuseStep 243001 = 182251) B182251
theorem B1226771 : Blo 131789 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B1425377 : Blo 131789 1425377 := bstep (se 2 (by rfl) ⟨534516, by rfl⟩ : syracuseStep 1425377 = 1069033) B1069033
theorem B672137 : Blo 131789 672137 := bstep (se 2 (by rfl) ⟨252051, by rfl⟩ : syracuseStep 672137 = 504103) B504103
theorem B607799 : Blo 131789 607799 := bstep (se 1 (by rfl) ⟨455849, by rfl⟩ : syracuseStep 607799 = 911699) B911699
theorem B446633 : Blo 131789 446633 := bstep (se 2 (by rfl) ⟨167487, by rfl⟩ : syracuseStep 446633 = 334975) B334975
theorem B577847 : Blo 131789 577847 := bstep (se 1 (by rfl) ⟨433385, by rfl⟩ : syracuseStep 577847 = 866771) B866771
theorem B1463285 : Blo 131789 1463285 := bstep (se 5 (by rfl) ⟨68591, by rfl⟩ : syracuseStep 1463285 = 137183) B137183
theorem B6510131 : Blo 131789 6510131 := bstep (se 1 (by rfl) ⟨4882598, by rfl⟩ : syracuseStep 6510131 = 9765197) B9765197
theorem B579145 : Blo 131789 579145 := bstep (se 2 (by rfl) ⟨217179, by rfl⟩ : syracuseStep 579145 = 434359) B434359
theorem B383591 : Blo 131789 383591 := bstep (se 1 (by rfl) ⟨287693, by rfl⟩ : syracuseStep 383591 = 575387) B575387
theorem B2185967 : Blo 131789 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B286831 : Blo 131789 286831 := bstep (se 1 (by rfl) ⟨215123, by rfl⟩ : syracuseStep 286831 = 430247) B430247
theorem B286907 : Blo 131789 286907 := bstep (se 1 (by rfl) ⟨215180, by rfl⟩ : syracuseStep 286907 = 430361) B430361
theorem B647687 : Blo 131789 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B1729187 : Blo 131789 1729187 := bstep (se 1 (by rfl) ⟨1296890, by rfl⟩ : syracuseStep 1729187 = 2593781) B2593781
theorem B255059 : Blo 131789 255059 := bstep (se 1 (by rfl) ⟨191294, by rfl⟩ : syracuseStep 255059 = 382589) B382589
theorem B583033 : Blo 131789 583033 := bstep (se 2 (by rfl) ⟨218637, by rfl⟩ : syracuseStep 583033 = 437275) B437275
theorem B452303 : Blo 131789 452303 := bstep (se 1 (by rfl) ⟨339227, by rfl⟩ : syracuseStep 452303 = 678455) B678455
theorem B388091 : Blo 131789 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B683153 : Blo 131789 683153 := bstep (se 2 (by rfl) ⟨256182, by rfl⟩ : syracuseStep 683153 = 512365) B512365
theorem B159079 : Blo 131789 159079 := bstep (se 1 (by rfl) ⟨119309, by rfl⟩ : syracuseStep 159079 = 238619) B238619
theorem B1666981 : Blo 131789 1666981 := bstep (se 4 (by rfl) ⟨156279, by rfl⟩ : syracuseStep 1666981 = 312559) B312559
theorem B225193 : Blo 131789 225193 := bstep (se 2 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 225193 = 168895) B168895
theorem B454855 : Blo 131789 454855 := bstep (se 1 (by rfl) ⟨341141, by rfl⟩ : syracuseStep 454855 = 682283) B682283
theorem B455273 : Blo 131789 455273 := bstep (se 2 (by rfl) ⟨170727, by rfl⟩ : syracuseStep 455273 = 341455) B341455
theorem B2716699 : Blo 131789 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B227099 : Blo 131789 227099 := bstep (se 1 (by rfl) ⟨170324, by rfl⟩ : syracuseStep 227099 = 340649) B340649
theorem B9042283 : Blo 131789 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B260975 : Blo 131789 260975 := bstep (se 1 (by rfl) ⟨195731, by rfl⟩ : syracuseStep 260975 = 391463) B391463
theorem B457865 : Blo 131789 457865 := bstep (se 2 (by rfl) ⟨171699, by rfl⟩ : syracuseStep 457865 = 343399) B343399
theorem B131943 : Blo 131789 131943 := bstep (se 1 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 131943 = 197915) B197915
theorem B132079 : Blo 131789 132079 := bstep (se 1 (by rfl) ⟨99059, by rfl⟩ : syracuseStep 132079 = 198119) B198119
theorem B2459645 : Blo 131789 2459645 := bstep (se 3 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 2459645 = 922367) B922367
theorem B198719 : Blo 131789 198719 := bstep (se 1 (by rfl) ⟨149039, by rfl⟩ : syracuseStep 198719 = 298079) B298079
theorem B198983 : Blo 131789 198983 := bstep (se 1 (by rfl) ⟨149237, by rfl⟩ : syracuseStep 198983 = 298475) B298475
theorem B297755 : Blo 131789 297755 := bstep (se 1 (by rfl) ⟨223316, by rfl⟩ : syracuseStep 297755 = 446633) B446633
theorem B200039 : Blo 131789 200039 := bstep (se 1 (by rfl) ⟨150029, by rfl⟩ : syracuseStep 200039 = 300059) B300059
theorem B200447 : Blo 131789 200447 := bstep (se 1 (by rfl) ⟨150335, by rfl⟩ : syracuseStep 200447 = 300671) B300671
theorem B856007 : Blo 131789 856007 := bstep (se 1 (by rfl) ⟨642005, by rfl⟩ : syracuseStep 856007 = 1284011) B1284011
theorem B300257 : Blo 131789 300257 := bstep (se 2 (by rfl) ⟨112596, by rfl⟩ : syracuseStep 300257 = 225193) B225193
theorem B202367 : Blo 131789 202367 := bstep (se 1 (by rfl) ⟨151775, by rfl⟩ : syracuseStep 202367 = 303551) B303551
theorem B1152791 : Blo 131789 1152791 := bstep (se 1 (by rfl) ⟨864593, by rfl⟩ : syracuseStep 1152791 = 1729187) B1729187
theorem B333659 : Blo 131789 333659 := bstep (se 1 (by rfl) ⟨250244, by rfl⟩ : syracuseStep 333659 = 500489) B500489
theorem B333679 : Blo 131789 333679 := bstep (se 1 (by rfl) ⟨250259, by rfl⟩ : syracuseStep 333679 = 500519) B500519
theorem B170039 : Blo 131789 170039 := bstep (se 1 (by rfl) ⟨127529, by rfl⟩ : syracuseStep 170039 = 255059) B255059
theorem B203207 : Blo 131789 203207 := bstep (se 1 (by rfl) ⟨152405, by rfl⟩ : syracuseStep 203207 = 304811) B304811
theorem B301535 : Blo 131789 301535 := bstep (se 1 (by rfl) ⟨226151, by rfl⟩ : syracuseStep 301535 = 452303) B452303
theorem B303515 : Blo 131789 303515 := bstep (se 1 (by rfl) ⟨227636, by rfl⟩ : syracuseStep 303515 = 455273) B455273
theorem B173983 : Blo 131789 173983 := bstep (se 1 (by rfl) ⟨130487, by rfl⟩ : syracuseStep 173983 = 260975) B260975
theorem B305243 : Blo 131789 305243 := bstep (se 1 (by rfl) ⟨228932, by rfl⟩ : syracuseStep 305243 = 457865) B457865
theorem B8890565 : Blo 131789 8890565 := bstep (se 4 (by rfl) ⟨833490, by rfl⟩ : syracuseStep 8890565 = 1666981) B1666981
theorem B6531839 : Blo 131789 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B765085 : Blo 131789 765085 := bstep (se 3 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 765085 = 286907) B286907
theorem B2862647 : Blo 131789 2862647 := bstep (se 1 (by rfl) ⟨2146985, by rfl⟩ : syracuseStep 2862647 = 4293971) B4293971
theorem B765611 : Blo 131789 765611 := bstep (se 1 (by rfl) ⟨574208, by rfl⟩ : syracuseStep 765611 = 1148417) B1148417
theorem B405199 : Blo 131789 405199 := bstep (se 1 (by rfl) ⟨303899, by rfl⟩ : syracuseStep 405199 = 607799) B607799
theorem B244039 : Blo 131789 244039 := bstep (se 1 (by rfl) ⟨183029, by rfl⟩ : syracuseStep 244039 = 366059) B366059
theorem B4340087 : Blo 131789 4340087 := bstep (se 1 (by rfl) ⟨3255065, by rfl⟩ : syracuseStep 4340087 = 6510131) B6510131
theorem B768959 : Blo 131789 768959 := bstep (se 1 (by rfl) ⟨576719, by rfl⟩ : syracuseStep 768959 = 1153439) B1153439
theorem B212105 : Blo 131789 212105 := bstep (se 2 (by rfl) ⟨79539, by rfl⟩ : syracuseStep 212105 = 159079) B159079
theorem B376255 : Blo 131789 376255 := bstep (se 1 (by rfl) ⟨282191, by rfl⟩ : syracuseStep 376255 = 564383) B564383
theorem B11714543 : Blo 131789 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B606473 : Blo 131789 606473 := bstep (se 2 (by rfl) ⟨227427, by rfl⟩ : syracuseStep 606473 = 454855) B454855
theorem B508463 : Blo 131789 508463 := bstep (se 1 (by rfl) ⟨381347, by rfl⟩ : syracuseStep 508463 = 762695) B762695
theorem B3622265 : Blo 131789 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B772193 : Blo 131789 772193 := bstep (se 2 (by rfl) ⟨289572, by rfl⟩ : syracuseStep 772193 = 579145) B579145
theorem B510695 : Blo 131789 510695 := bstep (se 1 (by rfl) ⟨383021, by rfl⟩ : syracuseStep 510695 = 766043) B766043
theorem B151399 : Blo 131789 151399 := bstep (se 1 (by rfl) ⟨113549, by rfl⟩ : syracuseStep 151399 = 227099) B227099
theorem B382441 : Blo 131789 382441 := bstep (se 2 (by rfl) ⟨143415, by rfl⟩ : syracuseStep 382441 = 286831) B286831
theorem B448091 : Blo 131789 448091 := bstep (se 1 (by rfl) ⟨336068, by rfl⟩ : syracuseStep 448091 = 672137) B672137
theorem B3693023 : Blo 131789 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B1727165 : Blo 131789 1727165 := bstep (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) B647687
theorem B1203011 : Blo 131789 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B777377 : Blo 131789 777377 := bstep (se 2 (by rfl) ⟨291516, by rfl⟩ : syracuseStep 777377 = 583033) B583033
theorem B385231 : Blo 131789 385231 := bstep (se 1 (by rfl) ⟨288923, by rfl⟩ : syracuseStep 385231 = 577847) B577847
theorem B975523 : Blo 131789 975523 := bstep (se 1 (by rfl) ⟨731642, by rfl⟩ : syracuseStep 975523 = 1463285) B1463285
theorem B255727 : Blo 131789 255727 := bstep (se 1 (by rfl) ⟨191795, by rfl⟩ : syracuseStep 255727 = 383591) B383591
theorem B452681 : Blo 131789 452681 := bstep (se 2 (by rfl) ⟨169755, by rfl⟩ : syracuseStep 452681 = 339511) B339511
theorem B453545 : Blo 131789 453545 := bstep (se 2 (by rfl) ⟨170079, by rfl⟩ : syracuseStep 453545 = 340159) B340159
theorem B224255 : Blo 131789 224255 := bstep (se 1 (by rfl) ⟨168191, by rfl⟩ : syracuseStep 224255 = 336383) B336383
theorem B454409 : Blo 131789 454409 := bstep (se 2 (by rfl) ⟨170403, by rfl⟩ : syracuseStep 454409 = 340807) B340807
theorem B324001 : Blo 131789 324001 := bstep (se 2 (by rfl) ⟨121500, by rfl⟩ : syracuseStep 324001 = 243001) B243001
theorem B5829245 : Blo 131789 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B258727 : Blo 131789 258727 := bstep (se 1 (by rfl) ⟨194045, by rfl⟩ : syracuseStep 258727 = 388091) B388091
theorem B455435 : Blo 131789 455435 := bstep (se 1 (by rfl) ⟨341576, by rfl⟩ : syracuseStep 455435 = 683153) B683153
theorem B12056377 : Blo 131789 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B817847 : Blo 131789 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B3801005 : Blo 131789 3801005 := bstep (se 3 (by rfl) ⟨712688, by rfl⟩ : syracuseStep 3801005 = 1425377) B1425377
theorem B1639763 : Blo 131789 1639763 := bstep (se 1 (by rfl) ⟨1229822, by rfl⟩ : syracuseStep 1639763 = 2459645) B2459645
theorem B132479 : Blo 131789 132479 := bstep (se 1 (by rfl) ⟨99359, by rfl⟩ : syracuseStep 132479 = 198719) B198719
theorem B132655 : Blo 131789 132655 := bstep (se 1 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 132655 = 198983) B198983
theorem B198503 : Blo 131789 198503 := bstep (se 1 (by rfl) ⟨148877, by rfl⟩ : syracuseStep 198503 = 297755) B297755
theorem B133359 : Blo 131789 133359 := bstep (se 1 (by rfl) ⟨100019, by rfl⟩ : syracuseStep 133359 = 200039) B200039
theorem B133631 : Blo 131789 133631 := bstep (se 1 (by rfl) ⟨100223, by rfl⟩ : syracuseStep 133631 = 200447) B200447
theorem B231977 : Blo 131789 231977 := bstep (se 2 (by rfl) ⟨86991, by rfl⟩ : syracuseStep 231977 = 173983) B173983
theorem B200171 : Blo 131789 200171 := bstep (se 1 (by rfl) ⟨150128, by rfl⟩ : syracuseStep 200171 = 300257) B300257
theorem B298727 : Blo 131789 298727 := bstep (se 1 (by rfl) ⟨224045, by rfl⟩ : syracuseStep 298727 = 448091) B448091
theorem B134911 : Blo 131789 134911 := bstep (se 1 (by rfl) ⟨101183, by rfl⟩ : syracuseStep 134911 = 202367) B202367
theorem B1020113 : Blo 131789 1020113 := bstep (se 2 (by rfl) ⟨382542, by rfl⟩ : syracuseStep 1020113 = 765085) B765085
theorem B135471 : Blo 131789 135471 := bstep (se 1 (by rfl) ⟨101603, by rfl⟩ : syracuseStep 135471 = 203207) B203207
theorem B2462015 : Blo 131789 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B201023 : Blo 131789 201023 := bstep (se 1 (by rfl) ⟨150767, by rfl⟩ : syracuseStep 201023 = 301535) B301535
theorem B1151443 : Blo 131789 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B201865 : Blo 131789 201865 := bstep (se 2 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 201865 = 151399) B151399
theorem B202343 : Blo 131789 202343 := bstep (se 1 (by rfl) ⟨151757, by rfl⟩ : syracuseStep 202343 = 303515) B303515
theorem B432001 : Blo 131789 432001 := bstep (se 2 (by rfl) ⟨162000, by rfl⟩ : syracuseStep 432001 = 324001) B324001
theorem B301787 : Blo 131789 301787 := bstep (se 1 (by rfl) ⟨226340, by rfl⟩ : syracuseStep 301787 = 452681) B452681
theorem B203495 : Blo 131789 203495 := bstep (se 1 (by rfl) ⟨152621, by rfl⟩ : syracuseStep 203495 = 305243) B305243
theorem B302363 : Blo 131789 302363 := bstep (se 1 (by rfl) ⟨226772, by rfl⟩ : syracuseStep 302363 = 453545) B453545
theorem B1908431 : Blo 131789 1908431 := bstep (se 1 (by rfl) ⟨1431323, by rfl⟩ : syracuseStep 1908431 = 2862647) B2862647
theorem B302939 : Blo 131789 302939 := bstep (se 1 (by rfl) ⟨227204, by rfl⟩ : syracuseStep 302939 = 454409) B454409
theorem B565613 : Blo 131789 565613 := bstep (se 3 (by rfl) ⟨106052, by rfl⟩ : syracuseStep 565613 = 212105) B212105
theorem B303623 : Blo 131789 303623 := bstep (se 1 (by rfl) ⟨227717, by rfl⟩ : syracuseStep 303623 = 455435) B455435
theorem B2893391 : Blo 131789 2893391 := bstep (se 1 (by rfl) ⟨2170043, by rfl⟩ : syracuseStep 2893391 = 4340087) B4340087
theorem B501673 : Blo 131789 501673 := bstep (se 2 (by rfl) ⟨188127, by rfl⟩ : syracuseStep 501673 = 376255) B376255
theorem B2534003 : Blo 131789 2534003 := bstep (se 1 (by rfl) ⟨1900502, by rfl⟩ : syracuseStep 2534003 = 3801005) B3801005
theorem B7809695 : Blo 131789 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B404315 : Blo 131789 404315 := bstep (se 1 (by rfl) ⟨303236, by rfl⟩ : syracuseStep 404315 = 606473) B606473
theorem B338975 : Blo 131789 338975 := bstep (se 1 (by rfl) ⟨254231, by rfl⟩ : syracuseStep 338975 = 508463) B508463
theorem B340463 : Blo 131789 340463 := bstep (se 1 (by rfl) ⟨255347, by rfl⟩ : syracuseStep 340463 = 510695) B510695
theorem B340969 : Blo 131789 340969 := bstep (se 2 (by rfl) ⟨127863, by rfl⟩ : syracuseStep 340969 = 255727) B255727
theorem B570671 : Blo 131789 570671 := bstep (se 1 (by rfl) ⟨428003, by rfl⟩ : syracuseStep 570671 = 856007) B856007
theorem B768527 : Blo 131789 768527 := bstep (se 1 (by rfl) ⟨576395, by rfl⟩ : syracuseStep 768527 = 1152791) B1152791
theorem B802007 : Blo 131789 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B540265 : Blo 131789 540265 := bstep (se 2 (by rfl) ⟨202599, by rfl⟩ : syracuseStep 540265 = 405199) B405199
theorem B23708173 : Blo 131789 23708173 := bstep (se 3 (by rfl) ⟨4445282, by rfl⟩ : syracuseStep 23708173 = 8890565) B8890565
theorem B344969 : Blo 131789 344969 := bstep (se 2 (by rfl) ⟨129363, by rfl⟩ : syracuseStep 344969 = 258727) B258727
theorem B509921 : Blo 131789 509921 := bstep (se 2 (by rfl) ⟨191220, by rfl⟩ : syracuseStep 509921 = 382441) B382441
theorem B149503 : Blo 131789 149503 := bstep (se 1 (by rfl) ⟨112127, by rfl⟩ : syracuseStep 149503 = 224255) B224255
theorem B16075169 : Blo 131789 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B510407 : Blo 131789 510407 := bstep (se 1 (by rfl) ⟨382805, by rfl⟩ : syracuseStep 510407 = 765611) B765611
theorem B444905 : Blo 131789 444905 := bstep (se 2 (by rfl) ⟨166839, by rfl⟩ : syracuseStep 444905 = 333679) B333679
theorem B3886163 : Blo 131789 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B545231 : Blo 131789 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B512639 : Blo 131789 512639 := bstep (se 1 (by rfl) ⟨384479, by rfl⟩ : syracuseStep 512639 = 768959) B768959
theorem B513641 : Blo 131789 513641 := bstep (se 2 (by rfl) ⟨192615, by rfl⟩ : syracuseStep 513641 = 385231) B385231
theorem B1300697 : Blo 131789 1300697 := bstep (se 2 (by rfl) ⟨487761, by rfl⟩ : syracuseStep 1300697 = 975523) B975523
theorem B2414843 : Blo 131789 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B514795 : Blo 131789 514795 := bstep (se 1 (by rfl) ⟨386096, by rfl⟩ : syracuseStep 514795 = 772193) B772193
theorem B222439 : Blo 131789 222439 := bstep (se 1 (by rfl) ⟨166829, by rfl⟩ : syracuseStep 222439 = 333659) B333659
theorem B518251 : Blo 131789 518251 := bstep (se 1 (by rfl) ⟨388688, by rfl⟩ : syracuseStep 518251 = 777377) B777377
theorem B453437 : Blo 131789 453437 := bstep (se 3 (by rfl) ⟨85019, by rfl⟩ : syracuseStep 453437 = 170039) B170039
theorem B4354559 : Blo 131789 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B325385 : Blo 131789 325385 := bstep (se 2 (by rfl) ⟨122019, by rfl⟩ : syracuseStep 325385 = 244039) B244039
theorem B229979 : Blo 131789 229979 := bstep (se 1 (by rfl) ⟨172484, by rfl⟩ : syracuseStep 229979 = 344969) B344969
theorem B132335 : Blo 131789 132335 := bstep (se 1 (by rfl) ⟨99251, by rfl⟩ : syracuseStep 132335 = 198503) B198503
theorem B10716779 : Blo 131789 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B296585 : Blo 131789 296585 := bstep (se 2 (by rfl) ⟨111219, by rfl⟩ : syracuseStep 296585 = 222439) B222439
theorem B296603 : Blo 131789 296603 := bstep (se 1 (by rfl) ⟨222452, by rfl⟩ : syracuseStep 296603 = 444905) B444905
theorem B2590775 : Blo 131789 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B133447 : Blo 131789 133447 := bstep (se 1 (by rfl) ⟨100085, by rfl⟩ : syracuseStep 133447 = 200171) B200171
theorem B199151 : Blo 131789 199151 := bstep (se 1 (by rfl) ⟨149363, by rfl⟩ : syracuseStep 199151 = 298727) B298727
theorem B199337 : Blo 131789 199337 := bstep (se 2 (by rfl) ⟨74751, by rfl⟩ : syracuseStep 199337 = 149503) B149503
theorem B691001 : Blo 131789 691001 := bstep (se 2 (by rfl) ⟨259125, by rfl⟩ : syracuseStep 691001 = 518251) B518251
theorem B1641343 : Blo 131789 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B134015 : Blo 131789 134015 := bstep (se 1 (by rfl) ⟨100511, by rfl⟩ : syracuseStep 134015 = 201023) B201023
theorem B363487 : Blo 131789 363487 := bstep (se 1 (by rfl) ⟨272615, by rfl⟩ : syracuseStep 363487 = 545231) B545231
theorem B134895 : Blo 131789 134895 := bstep (se 1 (by rfl) ⟨101171, by rfl⟩ : syracuseStep 134895 = 202343) B202343
theorem B1609895 : Blo 131789 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B201191 : Blo 131789 201191 := bstep (se 1 (by rfl) ⟨150893, by rfl⟩ : syracuseStep 201191 = 301787) B301787
theorem B135663 : Blo 131789 135663 := bstep (se 1 (by rfl) ⟨101747, by rfl⟩ : syracuseStep 135663 = 203495) B203495
theorem B201575 : Blo 131789 201575 := bstep (se 1 (by rfl) ⟨151181, by rfl⟩ : syracuseStep 201575 = 302363) B302363
theorem B201959 : Blo 131789 201959 := bstep (se 1 (by rfl) ⟨151469, by rfl⟩ : syracuseStep 201959 = 302939) B302939
theorem B202415 : Blo 131789 202415 := bstep (se 1 (by rfl) ⟨151811, by rfl⟩ : syracuseStep 202415 = 303623) B303623
theorem B269153 : Blo 131789 269153 := bstep (se 2 (by rfl) ⟨100932, by rfl⟩ : syracuseStep 269153 = 201865) B201865
theorem B302291 : Blo 131789 302291 := bstep (se 1 (by rfl) ⟨226718, by rfl⟩ : syracuseStep 302291 = 453437) B453437
theorem B269543 : Blo 131789 269543 := bstep (se 1 (by rfl) ⟨202157, by rfl⟩ : syracuseStep 269543 = 404315) B404315
theorem B534671 : Blo 131789 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B1093175 : Blo 131789 1093175 := bstep (se 1 (by rfl) ⟨819881, by rfl⟩ : syracuseStep 1093175 = 1639763) B1639763
theorem B339947 : Blo 131789 339947 := bstep (se 1 (by rfl) ⟨254960, by rfl⟩ : syracuseStep 339947 = 509921) B509921
theorem B340271 : Blo 131789 340271 := bstep (se 1 (by rfl) ⟨255203, by rfl⟩ : syracuseStep 340271 = 510407) B510407
theorem B668897 : Blo 131789 668897 := bstep (se 2 (by rfl) ⟨250836, by rfl⟩ : syracuseStep 668897 = 501673) B501673
theorem B341759 : Blo 131789 341759 := bstep (se 1 (by rfl) ⟨256319, by rfl⟩ : syracuseStep 341759 = 512639) B512639
theorem B342427 : Blo 131789 342427 := bstep (se 1 (by rfl) ⟨256820, by rfl⟩ : syracuseStep 342427 = 513641) B513641
theorem B867131 : Blo 131789 867131 := bstep (se 1 (by rfl) ⟨650348, by rfl⟩ : syracuseStep 867131 = 1300697) B1300697
theorem B377075 : Blo 131789 377075 := bstep (se 1 (by rfl) ⟨282806, by rfl⟩ : syracuseStep 377075 = 565613) B565613
theorem B1689335 : Blo 131789 1689335 := bstep (se 1 (by rfl) ⟨1267001, by rfl⟩ : syracuseStep 1689335 = 2534003) B2534003
theorem B576001 : Blo 131789 576001 := bstep (se 2 (by rfl) ⟨216000, by rfl⟩ : syracuseStep 576001 = 432001) B432001
theorem B2903039 : Blo 131789 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B380447 : Blo 131789 380447 := bstep (se 1 (by rfl) ⟨285335, by rfl⟩ : syracuseStep 380447 = 570671) B570671
theorem B216923 : Blo 131789 216923 := bstep (se 1 (by rfl) ⟨162692, by rfl⟩ : syracuseStep 216923 = 325385) B325385
theorem B512351 : Blo 131789 512351 := bstep (se 1 (by rfl) ⟨384263, by rfl⟩ : syracuseStep 512351 = 768527) B768527
theorem B31610897 : Blo 131789 31610897 := bstep (se 2 (by rfl) ⟨11854086, by rfl⟩ : syracuseStep 31610897 = 23708173) B23708173
theorem B154651 : Blo 131789 154651 := bstep (se 1 (by rfl) ⟨115988, by rfl⟩ : syracuseStep 154651 = 231977) B231977
theorem B680075 : Blo 131789 680075 := bstep (se 1 (by rfl) ⟨510056, by rfl⟩ : syracuseStep 680075 = 1020113) B1020113
theorem B1272287 : Blo 131789 1272287 := bstep (se 1 (by rfl) ⟨954215, by rfl⟩ : syracuseStep 1272287 = 1908431) B1908431
theorem B1535257 : Blo 131789 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B1928927 : Blo 131789 1928927 := bstep (se 1 (by rfl) ⟨1446695, by rfl⟩ : syracuseStep 1928927 = 2893391) B2893391
theorem B454625 : Blo 131789 454625 := bstep (se 2 (by rfl) ⟨170484, by rfl⟩ : syracuseStep 454625 = 340969) B340969
theorem B5206463 : Blo 131789 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B225983 : Blo 131789 225983 := bstep (se 1 (by rfl) ⟨169487, by rfl⟩ : syracuseStep 225983 = 338975) B338975
theorem B226975 : Blo 131789 226975 := bstep (se 1 (by rfl) ⟨170231, by rfl⟩ : syracuseStep 226975 = 340463) B340463
theorem B686393 : Blo 131789 686393 := bstep (se 2 (by rfl) ⟨257397, by rfl⟩ : syracuseStep 686393 = 514795) B514795
theorem B720353 : Blo 131789 720353 := bstep (se 2 (by rfl) ⟨270132, by rfl⟩ : syracuseStep 720353 = 540265) B540265
theorem B7144519 : Blo 131789 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B197723 : Blo 131789 197723 := bstep (se 1 (by rfl) ⟨148292, by rfl⟩ : syracuseStep 197723 = 296585) B296585
theorem B197735 : Blo 131789 197735 := bstep (se 1 (by rfl) ⟨148301, by rfl⟩ : syracuseStep 197735 = 296603) B296603
theorem B132767 : Blo 131789 132767 := bstep (se 1 (by rfl) ⟨99575, by rfl⟩ : syracuseStep 132767 = 199151) B199151
theorem B132891 : Blo 131789 132891 := bstep (se 1 (by rfl) ⟨99668, by rfl⟩ : syracuseStep 132891 = 199337) B199337
theorem B460667 : Blo 131789 460667 := bstep (se 1 (by rfl) ⟨345500, by rfl⟩ : syracuseStep 460667 = 691001) B691001
theorem B1935359 : Blo 131789 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B134127 : Blo 131789 134127 := bstep (se 1 (by rfl) ⟨100595, by rfl⟩ : syracuseStep 134127 = 201191) B201191
theorem B134383 : Blo 131789 134383 := bstep (se 1 (by rfl) ⟨100787, by rfl⟩ : syracuseStep 134383 = 201575) B201575
theorem B134639 : Blo 131789 134639 := bstep (se 1 (by rfl) ⟨100979, by rfl⟩ : syracuseStep 134639 = 201959) B201959
theorem B134943 : Blo 131789 134943 := bstep (se 1 (by rfl) ⟨101207, by rfl⟩ : syracuseStep 134943 = 202415) B202415
theorem B21073931 : Blo 131789 21073931 := bstep (se 1 (by rfl) ⟨15805448, by rfl⟩ : syracuseStep 21073931 = 31610897) B31610897
theorem B201527 : Blo 131789 201527 := bstep (se 1 (by rfl) ⟨151145, by rfl⟩ : syracuseStep 201527 = 302291) B302291
theorem B302633 : Blo 131789 302633 := bstep (se 2 (by rfl) ⟨113487, by rfl⟩ : syracuseStep 302633 = 226975) B226975
theorem B728783 : Blo 131789 728783 := bstep (se 1 (by rfl) ⟨546587, by rfl⟩ : syracuseStep 728783 = 1093175) B1093175
theorem B1285951 : Blo 131789 1285951 := bstep (se 1 (by rfl) ⟨964463, by rfl⟩ : syracuseStep 1285951 = 1928927) B1928927
theorem B303083 : Blo 131789 303083 := bstep (se 1 (by rfl) ⟨227312, by rfl⟩ : syracuseStep 303083 = 454625) B454625
theorem B206201 : Blo 131789 206201 := bstep (se 2 (by rfl) ⟨77325, by rfl⟩ : syracuseStep 206201 = 154651) B154651
theorem B1126223 : Blo 131789 1126223 := bstep (se 1 (by rfl) ⟨844667, by rfl⟩ : syracuseStep 1126223 = 1689335) B1689335
theorem B341567 : Blo 131789 341567 := bstep (se 1 (by rfl) ⟨256175, by rfl⟩ : syracuseStep 341567 = 512351) B512351
theorem B768001 : Blo 131789 768001 := bstep (se 2 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 768001 = 576001) B576001
theorem B179435 : Blo 131789 179435 := bstep (se 1 (by rfl) ⟨134576, by rfl⟩ : syracuseStep 179435 = 269153) B269153
theorem B179695 : Blo 131789 179695 := bstep (se 1 (by rfl) ⟨134771, by rfl⟩ : syracuseStep 179695 = 269543) B269543
theorem B150655 : Blo 131789 150655 := bstep (se 1 (by rfl) ⟨112991, by rfl⟩ : syracuseStep 150655 = 225983) B225983
theorem B445931 : Blo 131789 445931 := bstep (se 1 (by rfl) ⟨334448, by rfl⟩ : syracuseStep 445931 = 668897) B668897
theorem B2313845 : Blo 131789 2313845 := bstep (se 5 (by rfl) ⟨108461, by rfl⟩ : syracuseStep 2313845 = 216923) B216923
theorem B578087 : Blo 131789 578087 := bstep (se 1 (by rfl) ⟨433565, by rfl⟩ : syracuseStep 578087 = 867131) B867131
theorem B480235 : Blo 131789 480235 := bstep (se 1 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 480235 = 720353) B720353
theorem B1005533 : Blo 131789 1005533 := bstep (se 3 (by rfl) ⟨188537, by rfl⟩ : syracuseStep 1005533 = 377075) B377075
theorem B1727183 : Blo 131789 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B613277 : Blo 131789 613277 := bstep (se 3 (by rfl) ⟨114989, by rfl⟩ : syracuseStep 613277 = 229979) B229979
theorem B253631 : Blo 131789 253631 := bstep (se 1 (by rfl) ⟨190223, by rfl⟩ : syracuseStep 253631 = 380447) B380447
theorem B1073263 : Blo 131789 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B2188457 : Blo 131789 2188457 := bstep (se 2 (by rfl) ⟨820671, by rfl⟩ : syracuseStep 2188457 = 1641343) B1641343
theorem B484649 : Blo 131789 484649 := bstep (se 2 (by rfl) ⟨181743, by rfl⟩ : syracuseStep 484649 = 363487) B363487
theorem B453383 : Blo 131789 453383 := bstep (se 1 (by rfl) ⟨340037, by rfl⟩ : syracuseStep 453383 = 680075) B680075
theorem B356447 : Blo 131789 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B8188037 : Blo 131789 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B848191 : Blo 131789 848191 := bstep (se 1 (by rfl) ⟨636143, by rfl⟩ : syracuseStep 848191 = 1272287) B1272287
theorem B226631 : Blo 131789 226631 := bstep (se 1 (by rfl) ⟨169973, by rfl⟩ : syracuseStep 226631 = 339947) B339947
theorem B226847 : Blo 131789 226847 := bstep (se 1 (by rfl) ⟨170135, by rfl⟩ : syracuseStep 226847 = 340271) B340271
theorem B3470975 : Blo 131789 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B456569 : Blo 131789 456569 := bstep (se 2 (by rfl) ⟨171213, by rfl⟩ : syracuseStep 456569 = 342427) B342427
theorem B227839 : Blo 131789 227839 := bstep (se 1 (by rfl) ⟨170879, by rfl⟩ : syracuseStep 227839 = 341759) B341759
theorem B457595 : Blo 131789 457595 := bstep (se 1 (by rfl) ⟨343196, by rfl⟩ : syracuseStep 457595 = 686393) B686393
theorem B950525 : Blo 131789 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B131815 : Blo 131789 131815 := bstep (se 1 (by rfl) ⟨98861, by rfl⟩ : syracuseStep 131815 = 197723) B197723
theorem B131823 : Blo 131789 131823 := bstep (se 1 (by rfl) ⟨98867, by rfl⟩ : syracuseStep 131823 = 197735) B197735
theorem B297287 : Blo 131789 297287 := bstep (se 1 (by rfl) ⟨222965, by rfl⟩ : syracuseStep 297287 = 445931) B445931
theorem B1542563 : Blo 131789 1542563 := bstep (se 1 (by rfl) ⟨1156922, by rfl⟩ : syracuseStep 1542563 = 2313845) B2313845
theorem B134351 : Blo 131789 134351 := bstep (se 1 (by rfl) ⟨100763, by rfl⟩ : syracuseStep 134351 = 201527) B201527
theorem B200873 : Blo 131789 200873 := bstep (se 2 (by rfl) ⟨75327, by rfl⟩ : syracuseStep 200873 = 150655) B150655
theorem B1151455 : Blo 131789 1151455 := bstep (se 1 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 1151455 = 1727183) B1727183
theorem B201755 : Blo 131789 201755 := bstep (se 1 (by rfl) ⟨151316, by rfl⟩ : syracuseStep 201755 = 302633) B302633
theorem B202055 : Blo 131789 202055 := bstep (se 1 (by rfl) ⟨151541, by rfl⟩ : syracuseStep 202055 = 303083) B303083
theorem B137467 : Blo 131789 137467 := bstep (se 1 (by rfl) ⟨103100, by rfl⟩ : syracuseStep 137467 = 206201) B206201
theorem B302255 : Blo 131789 302255 := bstep (se 1 (by rfl) ⟨226691, by rfl⟩ : syracuseStep 302255 = 453383) B453383
theorem B1024001 : Blo 131789 1024001 := bstep (se 2 (by rfl) ⟨384000, by rfl⟩ : syracuseStep 1024001 = 768001) B768001
theorem B303785 : Blo 131789 303785 := bstep (se 2 (by rfl) ⟨113919, by rfl⟩ : syracuseStep 303785 = 227839) B227839
theorem B304379 : Blo 131789 304379 := bstep (se 1 (by rfl) ⟨228284, by rfl⟩ : syracuseStep 304379 = 456569) B456569
theorem B305063 : Blo 131789 305063 := bstep (se 1 (by rfl) ⟨228797, by rfl⟩ : syracuseStep 305063 = 457595) B457595
theorem B239593 : Blo 131789 239593 := bstep (se 2 (by rfl) ⟨89847, by rfl⟩ : syracuseStep 239593 = 179695) B179695
theorem B1714601 : Blo 131789 1714601 := bstep (se 2 (by rfl) ⟨642975, by rfl⟩ : syracuseStep 1714601 = 1285951) B1285951
theorem B307111 : Blo 131789 307111 := bstep (se 1 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 307111 = 460667) B460667
theorem B1290239 : Blo 131789 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B670355 : Blo 131789 670355 := bstep (se 1 (by rfl) ⟨502766, by rfl⟩ : syracuseStep 670355 = 1005533) B1005533
theorem B408851 : Blo 131789 408851 := bstep (se 1 (by rfl) ⟨306638, by rfl⟩ : syracuseStep 408851 = 613277) B613277
theorem B1130921 : Blo 131789 1130921 := bstep (se 2 (by rfl) ⟨424095, by rfl⟩ : syracuseStep 1130921 = 848191) B848191
theorem B1458971 : Blo 131789 1458971 := bstep (se 1 (by rfl) ⟨1094228, by rfl⟩ : syracuseStep 1458971 = 2188457) B2188457
theorem B640313 : Blo 131789 640313 := bstep (se 2 (by rfl) ⟨240117, by rfl⟩ : syracuseStep 640313 = 480235) B480235
theorem B5458691 : Blo 131789 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B478493 : Blo 131789 478493 := bstep (se 3 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 478493 = 179435) B179435
theorem B151087 : Blo 131789 151087 := bstep (se 1 (by rfl) ⟨113315, by rfl⟩ : syracuseStep 151087 = 226631) B226631
theorem B151231 : Blo 131789 151231 := bstep (se 1 (by rfl) ⟨113423, by rfl⟩ : syracuseStep 151231 = 226847) B226847
theorem B2313983 : Blo 131789 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B676349 : Blo 131789 676349 := bstep (se 3 (by rfl) ⟨126815, by rfl⟩ : syracuseStep 676349 = 253631) B253631
theorem B1431017 : Blo 131789 1431017 := bstep (se 2 (by rfl) ⟨536631, by rfl⟩ : syracuseStep 1431017 = 1073263) B1073263
theorem B9526025 : Blo 131789 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B14049287 : Blo 131789 14049287 := bstep (se 1 (by rfl) ⟨10536965, by rfl⟩ : syracuseStep 14049287 = 21073931) B21073931
theorem B385391 : Blo 131789 385391 := bstep (se 1 (by rfl) ⟨289043, by rfl⟩ : syracuseStep 385391 = 578087) B578087
theorem B485855 : Blo 131789 485855 := bstep (se 1 (by rfl) ⟨364391, by rfl⟩ : syracuseStep 485855 = 728783) B728783
theorem B323099 : Blo 131789 323099 := bstep (se 1 (by rfl) ⟨242324, by rfl⟩ : syracuseStep 323099 = 484649) B484649
theorem B750815 : Blo 131789 750815 := bstep (se 1 (by rfl) ⟨563111, by rfl⟩ : syracuseStep 750815 = 1126223) B1126223
theorem B227711 : Blo 131789 227711 := bstep (se 1 (by rfl) ⟨170783, by rfl⟩ : syracuseStep 227711 = 341567) B341567
theorem B753947 : Blo 131789 753947 := bstep (se 1 (by rfl) ⟨565460, by rfl⟩ : syracuseStep 753947 = 1130921) B1130921
theorem B426875 : Blo 131789 426875 := bstep (se 1 (by rfl) ⟨320156, by rfl⟩ : syracuseStep 426875 = 640313) B640313
theorem B198191 : Blo 131789 198191 := bstep (se 1 (by rfl) ⟨148643, by rfl⟩ : syracuseStep 198191 = 297287) B297287
theorem B3639127 : Blo 131789 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B1542655 : Blo 131789 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B133915 : Blo 131789 133915 := bstep (se 1 (by rfl) ⟨100436, by rfl⟩ : syracuseStep 133915 = 200873) B200873
theorem B134503 : Blo 131789 134503 := bstep (se 1 (by rfl) ⟨100877, by rfl⟩ : syracuseStep 134503 = 201755) B201755
theorem B134703 : Blo 131789 134703 := bstep (se 1 (by rfl) ⟨101027, by rfl⟩ : syracuseStep 134703 = 202055) B202055
theorem B954011 : Blo 131789 954011 := bstep (se 1 (by rfl) ⟨715508, by rfl⟩ : syracuseStep 954011 = 1431017) B1431017
theorem B201449 : Blo 131789 201449 := bstep (se 2 (by rfl) ⟨75543, by rfl⟩ : syracuseStep 201449 = 151087) B151087
theorem B201503 : Blo 131789 201503 := bstep (se 1 (by rfl) ⟨151127, by rfl⟩ : syracuseStep 201503 = 302255) B302255
theorem B201641 : Blo 131789 201641 := bstep (se 2 (by rfl) ⟨75615, by rfl⟩ : syracuseStep 201641 = 151231) B151231
theorem B202523 : Blo 131789 202523 := bstep (se 1 (by rfl) ⟨151892, by rfl⟩ : syracuseStep 202523 = 303785) B303785
theorem B202919 : Blo 131789 202919 := bstep (se 1 (by rfl) ⟨152189, by rfl⟩ : syracuseStep 202919 = 304379) B304379
theorem B203375 : Blo 131789 203375 := bstep (se 1 (by rfl) ⟨152531, by rfl⟩ : syracuseStep 203375 = 305063) B305063
theorem B860159 : Blo 131789 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B500543 : Blo 131789 500543 := bstep (se 1 (by rfl) ⟨375407, by rfl⟩ : syracuseStep 500543 = 750815) B750815
theorem B272567 : Blo 131789 272567 := bstep (se 1 (by rfl) ⟨204425, by rfl⟩ : syracuseStep 272567 = 408851) B408851
theorem B633683 : Blo 131789 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B1028375 : Blo 131789 1028375 := bstep (se 1 (by rfl) ⟨771281, by rfl⟩ : syracuseStep 1028375 = 1542563) B1542563
theorem B409481 : Blo 131789 409481 := bstep (se 2 (by rfl) ⟨153555, by rfl⟩ : syracuseStep 409481 = 307111) B307111
theorem B215399 : Blo 131789 215399 := bstep (se 1 (by rfl) ⟨161549, by rfl⟩ : syracuseStep 215399 = 323099) B323099
theorem B183289 : Blo 131789 183289 := bstep (se 2 (by rfl) ⟨68733, by rfl⟩ : syracuseStep 183289 = 137467) B137467
theorem B151807 : Blo 131789 151807 := bstep (se 1 (by rfl) ⟨113855, by rfl⟩ : syracuseStep 151807 = 227711) B227711
theorem B446903 : Blo 131789 446903 := bstep (se 1 (by rfl) ⟨335177, by rfl⟩ : syracuseStep 446903 = 670355) B670355
theorem B972647 : Blo 131789 972647 := bstep (se 1 (by rfl) ⟨729485, by rfl⟩ : syracuseStep 972647 = 1458971) B1458971
theorem B318995 : Blo 131789 318995 := bstep (se 1 (by rfl) ⟨239246, by rfl⟩ : syracuseStep 318995 = 478493) B478493
theorem B319457 : Blo 131789 319457 := bstep (se 2 (by rfl) ⟨119796, by rfl⟩ : syracuseStep 319457 = 239593) B239593
theorem B450899 : Blo 131789 450899 := bstep (se 1 (by rfl) ⟨338174, by rfl⟩ : syracuseStep 450899 = 676349) B676349
theorem B6350683 : Blo 131789 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B682667 : Blo 131789 682667 := bstep (se 1 (by rfl) ⟨512000, by rfl⟩ : syracuseStep 682667 = 1024001) B1024001
theorem B9366191 : Blo 131789 9366191 := bstep (se 1 (by rfl) ⟨7024643, by rfl⟩ : syracuseStep 9366191 = 14049287) B14049287
theorem B256927 : Blo 131789 256927 := bstep (se 1 (by rfl) ⟨192695, by rfl⟩ : syracuseStep 256927 = 385391) B385391
theorem B1535273 : Blo 131789 1535273 := bstep (se 2 (by rfl) ⟨575727, by rfl⟩ : syracuseStep 1535273 = 1151455) B1151455
theorem B1143067 : Blo 131789 1143067 := bstep (se 1 (by rfl) ⟨857300, by rfl⟩ : syracuseStep 1143067 = 1714601) B1714601
theorem B323903 : Blo 131789 323903 := bstep (se 1 (by rfl) ⟨242927, by rfl⟩ : syracuseStep 323903 = 485855) B485855
theorem B132127 : Blo 131789 132127 := bstep (se 1 (by rfl) ⟨99095, by rfl⟩ : syracuseStep 132127 = 198191) B198191
theorem B4852169 : Blo 131789 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B8227493 : Blo 131789 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B297935 : Blo 131789 297935 := bstep (se 1 (by rfl) ⟨223451, by rfl⟩ : syracuseStep 297935 = 446903) B446903
theorem B134299 : Blo 131789 134299 := bstep (se 1 (by rfl) ⟨100724, by rfl⟩ : syracuseStep 134299 = 201449) B201449
theorem B134335 : Blo 131789 134335 := bstep (se 1 (by rfl) ⟨100751, by rfl⟩ : syracuseStep 134335 = 201503) B201503
theorem B134427 : Blo 131789 134427 := bstep (se 1 (by rfl) ⟨100820, by rfl⟩ : syracuseStep 134427 = 201641) B201641
theorem B135015 : Blo 131789 135015 := bstep (se 1 (by rfl) ⟨101261, by rfl⟩ : syracuseStep 135015 = 202523) B202523
theorem B135279 : Blo 131789 135279 := bstep (se 1 (by rfl) ⟨101459, by rfl⟩ : syracuseStep 135279 = 202919) B202919
theorem B135583 : Blo 131789 135583 := bstep (se 1 (by rfl) ⟨101687, by rfl⟩ : syracuseStep 135583 = 203375) B203375
theorem B300599 : Blo 131789 300599 := bstep (se 1 (by rfl) ⟨225449, by rfl⟩ : syracuseStep 300599 = 450899) B450899
theorem B202409 : Blo 131789 202409 := bstep (se 2 (by rfl) ⟨75903, by rfl⟩ : syracuseStep 202409 = 151807) B151807
theorem B333695 : Blo 131789 333695 := bstep (se 1 (by rfl) ⟨250271, by rfl⟩ : syracuseStep 333695 = 500543) B500543
theorem B1023515 : Blo 131789 1023515 := bstep (se 1 (by rfl) ⟨767636, by rfl⟩ : syracuseStep 1023515 = 1535273) B1535273
theorem B272987 : Blo 131789 272987 := bstep (se 1 (by rfl) ⟨204740, by rfl⟩ : syracuseStep 272987 = 409481) B409481
theorem B502631 : Blo 131789 502631 := bstep (se 1 (by rfl) ⟨376973, by rfl⟩ : syracuseStep 502631 = 753947) B753947
theorem B636007 : Blo 131789 636007 := bstep (se 1 (by rfl) ⟨477005, by rfl⟩ : syracuseStep 636007 = 954011) B954011
theorem B8467577 : Blo 131789 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B342569 : Blo 131789 342569 := bstep (se 2 (by rfl) ⟨128463, by rfl⟩ : syracuseStep 342569 = 256927) B256927
theorem B244385 : Blo 131789 244385 := bstep (se 2 (by rfl) ⟨91644, by rfl⟩ : syracuseStep 244385 = 183289) B183289
theorem B212663 : Blo 131789 212663 := bstep (se 1 (by rfl) ⟨159497, by rfl⟩ : syracuseStep 212663 = 318995) B318995
theorem B212971 : Blo 131789 212971 := bstep (se 1 (by rfl) ⟨159728, by rfl⟩ : syracuseStep 212971 = 319457) B319457
theorem B573439 : Blo 131789 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B1524089 : Blo 131789 1524089 := bstep (se 2 (by rfl) ⟨571533, by rfl⟩ : syracuseStep 1524089 = 1143067) B1143067
theorem B574397 : Blo 131789 574397 := bstep (se 3 (by rfl) ⟨107699, by rfl⟩ : syracuseStep 574397 = 215399) B215399
theorem B181711 : Blo 131789 181711 := bstep (se 1 (by rfl) ⟨136283, by rfl⟩ : syracuseStep 181711 = 272567) B272567
theorem B6244127 : Blo 131789 6244127 := bstep (se 1 (by rfl) ⟨4683095, by rfl⟩ : syracuseStep 6244127 = 9366191) B9366191
theorem B1689821 : Blo 131789 1689821 := bstep (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) B633683
theorem B215935 : Blo 131789 215935 := bstep (se 1 (by rfl) ⟨161951, by rfl⟩ : syracuseStep 215935 = 323903) B323903
theorem B1138333 : Blo 131789 1138333 := bstep (se 3 (by rfl) ⟨213437, by rfl⟩ : syracuseStep 1138333 = 426875) B426875
theorem B648431 : Blo 131789 648431 := bstep (se 1 (by rfl) ⟨486323, by rfl⟩ : syracuseStep 648431 = 972647) B972647
theorem B455111 : Blo 131789 455111 := bstep (se 1 (by rfl) ⟨341333, by rfl⟩ : syracuseStep 455111 = 682667) B682667
theorem B685583 : Blo 131789 685583 := bstep (se 1 (by rfl) ⟨514187, by rfl⟩ : syracuseStep 685583 = 1028375) B1028375
theorem B1016059 : Blo 131789 1016059 := bstep (se 1 (by rfl) ⟨762044, by rfl⟩ : syracuseStep 1016059 = 1524089) B1524089
theorem B4162751 : Blo 131789 4162751 := bstep (se 1 (by rfl) ⟨3122063, by rfl⟩ : syracuseStep 4162751 = 6244127) B6244127
theorem B198623 : Blo 131789 198623 := bstep (se 1 (by rfl) ⟨148967, by rfl⟩ : syracuseStep 198623 = 297935) B297935
theorem B200399 : Blo 131789 200399 := bstep (se 1 (by rfl) ⟨150299, by rfl⟩ : syracuseStep 200399 = 300599) B300599
theorem B134939 : Blo 131789 134939 := bstep (se 1 (by rfl) ⟨101204, by rfl⟩ : syracuseStep 134939 = 202409) B202409
theorem B1151653 : Blo 131789 1151653 := bstep (se 4 (by rfl) ⟨107967, by rfl⟩ : syracuseStep 1151653 = 215935) B215935
theorem B432287 : Blo 131789 432287 := bstep (se 1 (by rfl) ⟨324215, by rfl⟩ : syracuseStep 432287 = 648431) B648431
theorem B335087 : Blo 131789 335087 := bstep (se 1 (by rfl) ⟨251315, by rfl⟩ : syracuseStep 335087 = 502631) B502631
theorem B303407 : Blo 131789 303407 := bstep (se 1 (by rfl) ⟨227555, by rfl⟩ : syracuseStep 303407 = 455111) B455111
theorem B5645051 : Blo 131789 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B567101 : Blo 131789 567101 := bstep (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) B212663
theorem B1517777 : Blo 131789 1517777 := bstep (se 2 (by rfl) ⟨569166, by rfl⟩ : syracuseStep 1517777 = 1138333) B1138333
theorem B764585 : Blo 131789 764585 := bstep (se 2 (by rfl) ⟨286719, by rfl⟩ : syracuseStep 764585 = 573439) B573439
theorem B1126547 : Blo 131789 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B5484995 : Blo 131789 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B242281 : Blo 131789 242281 := bstep (se 2 (by rfl) ⟨90855, by rfl⟩ : syracuseStep 242281 = 181711) B181711
theorem B181991 : Blo 131789 181991 := bstep (se 1 (by rfl) ⟨136493, by rfl⟩ : syracuseStep 181991 = 272987) B272987
theorem B283961 : Blo 131789 283961 := bstep (se 2 (by rfl) ⟨106485, by rfl⟩ : syracuseStep 283961 = 212971) B212971
theorem B382931 : Blo 131789 382931 := bstep (se 1 (by rfl) ⟨287198, by rfl⟩ : syracuseStep 382931 = 574397) B574397
theorem B3234779 : Blo 131789 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B222463 : Blo 131789 222463 := bstep (se 1 (by rfl) ⟨166847, by rfl⟩ : syracuseStep 222463 = 333695) B333695
theorem B682343 : Blo 131789 682343 := bstep (se 1 (by rfl) ⟨511757, by rfl⟩ : syracuseStep 682343 = 1023515) B1023515
theorem B848009 : Blo 131789 848009 := bstep (se 2 (by rfl) ⟨318003, by rfl⟩ : syracuseStep 848009 = 636007) B636007
theorem B457055 : Blo 131789 457055 := bstep (se 1 (by rfl) ⟨342791, by rfl⟩ : syracuseStep 457055 = 685583) B685583
theorem B228379 : Blo 131789 228379 := bstep (se 1 (by rfl) ⟨171284, by rfl⟩ : syracuseStep 228379 = 342569) B342569
theorem B162923 : Blo 131789 162923 := bstep (se 1 (by rfl) ⟨122192, by rfl⟩ : syracuseStep 162923 = 244385) B244385
theorem B2261357 : Blo 131789 2261357 := bstep (se 3 (by rfl) ⟨424004, by rfl⟩ : syracuseStep 2261357 = 848009) B848009
theorem B1737845 : Blo 131789 1737845 := bstep (se 5 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 1737845 = 162923) B162923
theorem B132415 : Blo 131789 132415 := bstep (se 1 (by rfl) ⟨99311, by rfl⟩ : syracuseStep 132415 = 198623) B198623
theorem B296617 : Blo 131789 296617 := bstep (se 2 (by rfl) ⟨111231, by rfl⟩ : syracuseStep 296617 = 222463) B222463
theorem B133599 : Blo 131789 133599 := bstep (se 1 (by rfl) ⟨100199, by rfl⟩ : syracuseStep 133599 = 200399) B200399
theorem B202271 : Blo 131789 202271 := bstep (se 1 (by rfl) ⟨151703, by rfl⟩ : syracuseStep 202271 = 303407) B303407
theorem B304505 : Blo 131789 304505 := bstep (se 2 (by rfl) ⟨114189, by rfl⟩ : syracuseStep 304505 = 228379) B228379
theorem B304703 : Blo 131789 304703 := bstep (se 1 (by rfl) ⟨228527, by rfl⟩ : syracuseStep 304703 = 457055) B457055
theorem B1354745 : Blo 131789 1354745 := bstep (se 2 (by rfl) ⟨508029, by rfl⟩ : syracuseStep 1354745 = 1016059) B1016059
theorem B378067 : Blo 131789 378067 := bstep (se 1 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 378067 = 567101) B567101
theorem B509723 : Blo 131789 509723 := bstep (se 1 (by rfl) ⟨382292, by rfl⟩ : syracuseStep 509723 = 764585) B764585
theorem B3656663 : Blo 131789 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B2775167 : Blo 131789 2775167 := bstep (se 1 (by rfl) ⟨2081375, by rfl⟩ : syracuseStep 2775167 = 4162751) B4162751
theorem B189307 : Blo 131789 189307 := bstep (se 1 (by rfl) ⟨141980, by rfl⟩ : syracuseStep 189307 = 283961) B283961
theorem B255287 : Blo 131789 255287 := bstep (se 1 (by rfl) ⟨191465, by rfl⟩ : syracuseStep 255287 = 382931) B382931
theorem B288191 : Blo 131789 288191 := bstep (se 1 (by rfl) ⟨216143, by rfl⟩ : syracuseStep 288191 = 432287) B432287
theorem B485309 : Blo 131789 485309 := bstep (se 3 (by rfl) ⟨90995, by rfl⟩ : syracuseStep 485309 = 181991) B181991
theorem B2156519 : Blo 131789 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B223391 : Blo 131789 223391 := bstep (se 1 (by rfl) ⟨167543, by rfl⟩ : syracuseStep 223391 = 335087) B335087
theorem B3763367 : Blo 131789 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B323041 : Blo 131789 323041 := bstep (se 2 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 323041 = 242281) B242281
theorem B1535537 : Blo 131789 1535537 := bstep (se 2 (by rfl) ⟨575826, by rfl⟩ : syracuseStep 1535537 = 1151653) B1151653
theorem B1011851 : Blo 131789 1011851 := bstep (se 1 (by rfl) ⟨758888, by rfl⟩ : syracuseStep 1011851 = 1517777) B1517777
theorem B454895 : Blo 131789 454895 := bstep (se 1 (by rfl) ⟨341171, by rfl⟩ : syracuseStep 454895 = 682343) B682343
theorem B751031 : Blo 131789 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B1507571 : Blo 131789 1507571 := bstep (se 1 (by rfl) ⟨1130678, by rfl⟩ : syracuseStep 1507571 = 2261357) B2261357
theorem B395489 : Blo 131789 395489 := bstep (se 2 (by rfl) ⟨148308, by rfl⟩ : syracuseStep 395489 = 296617) B296617
theorem B134847 : Blo 131789 134847 := bstep (se 1 (by rfl) ⟨101135, by rfl⟩ : syracuseStep 134847 = 202271) B202271
theorem B430721 : Blo 131789 430721 := bstep (se 2 (by rfl) ⟨161520, by rfl⟩ : syracuseStep 430721 = 323041) B323041
theorem B170191 : Blo 131789 170191 := bstep (se 1 (by rfl) ⟨127643, by rfl⟩ : syracuseStep 170191 = 255287) B255287
theorem B203003 : Blo 131789 203003 := bstep (se 1 (by rfl) ⟨152252, by rfl⟩ : syracuseStep 203003 = 304505) B304505
theorem B203135 : Blo 131789 203135 := bstep (se 1 (by rfl) ⟨152351, by rfl⟩ : syracuseStep 203135 = 304703) B304703
theorem B1023691 : Blo 131789 1023691 := bstep (se 1 (by rfl) ⟨767768, by rfl⟩ : syracuseStep 1023691 = 1535537) B1535537
theorem B303263 : Blo 131789 303263 := bstep (se 1 (by rfl) ⟨227447, by rfl⟩ : syracuseStep 303263 = 454895) B454895
theorem B500687 : Blo 131789 500687 := bstep (se 1 (by rfl) ⟨375515, by rfl⟩ : syracuseStep 500687 = 751031) B751031
theorem B1158563 : Blo 131789 1158563 := bstep (se 1 (by rfl) ⟨868922, by rfl⟩ : syracuseStep 1158563 = 1737845) B1737845
theorem B339815 : Blo 131789 339815 := bstep (se 1 (by rfl) ⟨254861, by rfl⟩ : syracuseStep 339815 = 509723) B509723
theorem B504089 : Blo 131789 504089 := bstep (se 2 (by rfl) ⟨189033, by rfl⟩ : syracuseStep 504089 = 378067) B378067
theorem B2437775 : Blo 131789 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B1850111 : Blo 131789 1850111 := bstep (se 1 (by rfl) ⟨1387583, by rfl⟩ : syracuseStep 1850111 = 2775167) B2775167
theorem B1294157 : Blo 131789 1294157 := bstep (se 3 (by rfl) ⟨242654, by rfl⟩ : syracuseStep 1294157 = 485309) B485309
theorem B148927 : Blo 131789 148927 := bstep (se 1 (by rfl) ⟨111695, by rfl⟩ : syracuseStep 148927 = 223391) B223391
theorem B903163 : Blo 131789 903163 := bstep (se 1 (by rfl) ⟨677372, by rfl⟩ : syracuseStep 903163 = 1354745) B1354745
theorem B2508911 : Blo 131789 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B674567 : Blo 131789 674567 := bstep (se 1 (by rfl) ⟨505925, by rfl⟩ : syracuseStep 674567 = 1011851) B1011851
theorem B252409 : Blo 131789 252409 := bstep (se 2 (by rfl) ⟨94653, by rfl⟩ : syracuseStep 252409 = 189307) B189307
theorem B192127 : Blo 131789 192127 := bstep (se 1 (by rfl) ⟨144095, by rfl⟩ : syracuseStep 192127 = 288191) B288191
theorem B1437679 : Blo 131789 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B1672607 : Blo 131789 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B198569 : Blo 131789 198569 := bstep (se 2 (by rfl) ⟨74463, by rfl⟩ : syracuseStep 198569 = 148927) B148927
theorem B135335 : Blo 131789 135335 := bstep (se 1 (by rfl) ⟨101501, by rfl⟩ : syracuseStep 135335 = 203003) B203003
theorem B135423 : Blo 131789 135423 := bstep (se 1 (by rfl) ⟨101567, by rfl⟩ : syracuseStep 135423 = 203135) B203135
theorem B202175 : Blo 131789 202175 := bstep (se 1 (by rfl) ⟨151631, by rfl⟩ : syracuseStep 202175 = 303263) B303263
theorem B1054637 : Blo 131789 1054637 := bstep (se 3 (by rfl) ⟨197744, by rfl⟩ : syracuseStep 1054637 = 395489) B395489
theorem B333791 : Blo 131789 333791 := bstep (se 1 (by rfl) ⟨250343, by rfl⟩ : syracuseStep 333791 = 500687) B500687
theorem B336059 : Blo 131789 336059 := bstep (se 1 (by rfl) ⟨252044, by rfl⟩ : syracuseStep 336059 = 504089) B504089
theorem B336545 : Blo 131789 336545 := bstep (se 2 (by rfl) ⟨126204, by rfl⟩ : syracuseStep 336545 = 252409) B252409
theorem B3451085 : Blo 131789 3451085 := bstep (se 3 (by rfl) ⟨647078, by rfl⟩ : syracuseStep 3451085 = 1294157) B1294157
theorem B1916905 : Blo 131789 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B772375 : Blo 131789 772375 := bstep (se 1 (by rfl) ⟨579281, by rfl⟩ : syracuseStep 772375 = 1158563) B1158563
theorem B1625183 : Blo 131789 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B1233407 : Blo 131789 1233407 := bstep (se 1 (by rfl) ⟨925055, by rfl⟩ : syracuseStep 1233407 = 1850111) B1850111
theorem B1364921 : Blo 131789 1364921 := bstep (se 2 (by rfl) ⟨511845, by rfl⟩ : syracuseStep 1364921 = 1023691) B1023691
theorem B1005047 : Blo 131789 1005047 := bstep (se 1 (by rfl) ⟨753785, by rfl⟩ : syracuseStep 1005047 = 1507571) B1507571
theorem B449711 : Blo 131789 449711 := bstep (se 1 (by rfl) ⟨337283, by rfl⟩ : syracuseStep 449711 = 674567) B674567
theorem B1204217 : Blo 131789 1204217 := bstep (se 2 (by rfl) ⟨451581, by rfl⟩ : syracuseStep 1204217 = 903163) B903163
theorem B287147 : Blo 131789 287147 := bstep (se 1 (by rfl) ⟨215360, by rfl⟩ : syracuseStep 287147 = 430721) B430721
theorem B256169 : Blo 131789 256169 := bstep (se 2 (by rfl) ⟨96063, by rfl⟩ : syracuseStep 256169 = 192127) B192127
theorem B226543 : Blo 131789 226543 := bstep (se 1 (by rfl) ⟨169907, by rfl⟩ : syracuseStep 226543 = 339815) B339815
theorem B226921 : Blo 131789 226921 := bstep (se 2 (by rfl) ⟨85095, by rfl⟩ : syracuseStep 226921 = 170191) B170191
theorem B132379 : Blo 131789 132379 := bstep (se 1 (by rfl) ⟨99284, by rfl⟩ : syracuseStep 132379 = 198569) B198569
theorem B1083455 : Blo 131789 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B822271 : Blo 131789 822271 := bstep (se 1 (by rfl) ⟨616703, by rfl⟩ : syracuseStep 822271 = 1233407) B1233407
theorem B134783 : Blo 131789 134783 := bstep (se 1 (by rfl) ⟨101087, by rfl⟩ : syracuseStep 134783 = 202175) B202175
theorem B4460285 : Blo 131789 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B299807 : Blo 131789 299807 := bstep (se 1 (by rfl) ⟨224855, by rfl⟩ : syracuseStep 299807 = 449711) B449711
theorem B170779 : Blo 131789 170779 := bstep (se 1 (by rfl) ⟨128084, by rfl⟩ : syracuseStep 170779 = 256169) B256169
theorem B2300723 : Blo 131789 2300723 := bstep (se 1 (by rfl) ⟨1725542, by rfl⟩ : syracuseStep 2300723 = 3451085) B3451085
theorem B302057 : Blo 131789 302057 := bstep (se 2 (by rfl) ⟨113271, by rfl⟩ : syracuseStep 302057 = 226543) B226543
theorem B302561 : Blo 131789 302561 := bstep (se 2 (by rfl) ⟨113460, by rfl⟩ : syracuseStep 302561 = 226921) B226921
theorem B1029833 : Blo 131789 1029833 := bstep (se 2 (by rfl) ⟨386187, by rfl⟩ : syracuseStep 1029833 = 772375) B772375
theorem B670031 : Blo 131789 670031 := bstep (se 1 (by rfl) ⟨502523, by rfl⟩ : syracuseStep 670031 = 1005047) B1005047
theorem B703091 : Blo 131789 703091 := bstep (se 1 (by rfl) ⟨527318, by rfl⟩ : syracuseStep 703091 = 1054637) B1054637
theorem B802811 : Blo 131789 802811 := bstep (se 1 (by rfl) ⟨602108, by rfl⟩ : syracuseStep 802811 = 1204217) B1204217
theorem B909947 : Blo 131789 909947 := bstep (se 1 (by rfl) ⟨682460, by rfl⟩ : syracuseStep 909947 = 1364921) B1364921
theorem B222527 : Blo 131789 222527 := bstep (se 1 (by rfl) ⟨166895, by rfl⟩ : syracuseStep 222527 = 333791) B333791
theorem B224039 : Blo 131789 224039 := bstep (se 1 (by rfl) ⟨168029, by rfl⟩ : syracuseStep 224039 = 336059) B336059
theorem B191431 : Blo 131789 191431 := bstep (se 1 (by rfl) ⟨143573, by rfl⟩ : syracuseStep 191431 = 287147) B287147
theorem B224363 : Blo 131789 224363 := bstep (se 1 (by rfl) ⟨168272, by rfl⟩ : syracuseStep 224363 = 336545) B336545
theorem B2555873 : Blo 131789 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B722303 : Blo 131789 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B199871 : Blo 131789 199871 := bstep (se 1 (by rfl) ⟨149903, by rfl⟩ : syracuseStep 199871 = 299807) B299807
theorem B201371 : Blo 131789 201371 := bstep (se 1 (by rfl) ⟨151028, by rfl⟩ : syracuseStep 201371 = 302057) B302057
theorem B201707 : Blo 131789 201707 := bstep (se 1 (by rfl) ⟨151280, by rfl⟩ : syracuseStep 201707 = 302561) B302561
theorem B1874909 : Blo 131789 1874909 := bstep (se 3 (by rfl) ⟨351545, by rfl⟩ : syracuseStep 1874909 = 703091) B703091
theorem B535207 : Blo 131789 535207 := bstep (se 1 (by rfl) ⟨401405, by rfl⟩ : syracuseStep 535207 = 802811) B802811
theorem B1096361 : Blo 131789 1096361 := bstep (se 2 (by rfl) ⟨411135, by rfl⟩ : syracuseStep 1096361 = 822271) B822271
theorem B606631 : Blo 131789 606631 := bstep (se 1 (by rfl) ⟨454973, by rfl⟩ : syracuseStep 606631 = 909947) B909947
theorem B148351 : Blo 131789 148351 := bstep (se 1 (by rfl) ⟨111263, by rfl⟩ : syracuseStep 148351 = 222527) B222527
theorem B149359 : Blo 131789 149359 := bstep (se 1 (by rfl) ⟨112019, by rfl⟩ : syracuseStep 149359 = 224039) B224039
theorem B149575 : Blo 131789 149575 := bstep (se 1 (by rfl) ⟨112181, by rfl⟩ : syracuseStep 149575 = 224363) B224363
theorem B446687 : Blo 131789 446687 := bstep (se 1 (by rfl) ⟨335015, by rfl⟩ : syracuseStep 446687 = 670031) B670031
theorem B2973523 : Blo 131789 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B255241 : Blo 131789 255241 := bstep (se 2 (by rfl) ⟨95715, by rfl⟩ : syracuseStep 255241 = 191431) B191431
theorem B1533815 : Blo 131789 1533815 := bstep (se 1 (by rfl) ⟨1150361, by rfl⟩ : syracuseStep 1533815 = 2300723) B2300723
theorem B227705 : Blo 131789 227705 := bstep (se 2 (by rfl) ⟨85389, by rfl⟩ : syracuseStep 227705 = 170779) B170779
theorem B686555 : Blo 131789 686555 := bstep (se 1 (by rfl) ⟨514916, by rfl⟩ : syracuseStep 686555 = 1029833) B1029833
theorem B1703915 : Blo 131789 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B197801 : Blo 131789 197801 := bstep (se 2 (by rfl) ⟨74175, by rfl⟩ : syracuseStep 197801 = 148351) B148351
theorem B133247 : Blo 131789 133247 := bstep (se 1 (by rfl) ⟨99935, by rfl⟩ : syracuseStep 133247 = 199871) B199871
theorem B199145 : Blo 131789 199145 := bstep (se 2 (by rfl) ⟨74679, by rfl⟩ : syracuseStep 199145 = 149359) B149359
theorem B199433 : Blo 131789 199433 := bstep (se 2 (by rfl) ⟨74787, by rfl⟩ : syracuseStep 199433 = 149575) B149575
theorem B297791 : Blo 131789 297791 := bstep (se 1 (by rfl) ⟨223343, by rfl⟩ : syracuseStep 297791 = 446687) B446687
theorem B134247 : Blo 131789 134247 := bstep (se 1 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 134247 = 201371) B201371
theorem B134471 : Blo 131789 134471 := bstep (se 1 (by rfl) ⟨100853, by rfl⟩ : syracuseStep 134471 = 201707) B201707
theorem B1249939 : Blo 131789 1249939 := bstep (se 1 (by rfl) ⟨937454, by rfl⟩ : syracuseStep 1249939 = 1874909) B1874909
theorem B1022543 : Blo 131789 1022543 := bstep (se 1 (by rfl) ⟨766907, by rfl⟩ : syracuseStep 1022543 = 1533815) B1533815
theorem B730907 : Blo 131789 730907 := bstep (se 1 (by rfl) ⟨548180, by rfl⟩ : syracuseStep 730907 = 1096361) B1096361
theorem B340321 : Blo 131789 340321 := bstep (se 2 (by rfl) ⟨127620, by rfl⟩ : syracuseStep 340321 = 255241) B255241
theorem B607213 : Blo 131789 607213 := bstep (se 3 (by rfl) ⟨113852, by rfl⟩ : syracuseStep 607213 = 227705) B227705
theorem B1135943 : Blo 131789 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B808841 : Blo 131789 808841 := bstep (se 2 (by rfl) ⟨303315, by rfl⟩ : syracuseStep 808841 = 606631) B606631
theorem B481535 : Blo 131789 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B713609 : Blo 131789 713609 := bstep (se 2 (by rfl) ⟨267603, by rfl⟩ : syracuseStep 713609 = 535207) B535207
theorem B457703 : Blo 131789 457703 := bstep (se 1 (by rfl) ⟨343277, by rfl⟩ : syracuseStep 457703 = 686555) B686555
theorem B3964697 : Blo 131789 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B131867 : Blo 131789 131867 := bstep (se 1 (by rfl) ⟨98900, by rfl⟩ : syracuseStep 131867 = 197801) B197801
theorem B132763 : Blo 131789 132763 := bstep (se 1 (by rfl) ⟨99572, by rfl⟩ : syracuseStep 132763 = 199145) B199145
theorem B132955 : Blo 131789 132955 := bstep (se 1 (by rfl) ⟨99716, by rfl⟩ : syracuseStep 132955 = 199433) B199433
theorem B198527 : Blo 131789 198527 := bstep (se 1 (by rfl) ⟨148895, by rfl⟩ : syracuseStep 198527 = 297791) B297791
theorem B757295 : Blo 131789 757295 := bstep (se 1 (by rfl) ⟨567971, by rfl⟩ : syracuseStep 757295 = 1135943) B1135943
theorem B305135 : Blo 131789 305135 := bstep (se 1 (by rfl) ⟨228851, by rfl⟩ : syracuseStep 305135 = 457703) B457703
theorem B539227 : Blo 131789 539227 := bstep (se 1 (by rfl) ⟨404420, by rfl⟩ : syracuseStep 539227 = 808841) B808841
theorem B475739 : Blo 131789 475739 := bstep (se 1 (by rfl) ⟨356804, by rfl⟩ : syracuseStep 475739 = 713609) B713609
theorem B2643131 : Blo 131789 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B321023 : Blo 131789 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B681695 : Blo 131789 681695 := bstep (se 1 (by rfl) ⟨511271, by rfl⟩ : syracuseStep 681695 = 1022543) B1022543
theorem B3238469 : Blo 131789 3238469 := bstep (se 4 (by rfl) ⟨303606, by rfl⟩ : syracuseStep 3238469 = 607213) B607213
theorem B453761 : Blo 131789 453761 := bstep (se 2 (by rfl) ⟨170160, by rfl⟩ : syracuseStep 453761 = 340321) B340321
theorem B1666585 : Blo 131789 1666585 := bstep (se 2 (by rfl) ⟨624969, by rfl⟩ : syracuseStep 1666585 = 1249939) B1249939
theorem B487271 : Blo 131789 487271 := bstep (se 1 (by rfl) ⟨365453, by rfl⟩ : syracuseStep 487271 = 730907) B730907
theorem B132351 : Blo 131789 132351 := bstep (se 1 (by rfl) ⟨99263, by rfl⟩ : syracuseStep 132351 = 198527) B198527
theorem B203423 : Blo 131789 203423 := bstep (se 1 (by rfl) ⟨152567, by rfl⟩ : syracuseStep 203423 = 305135) B305135
theorem B302507 : Blo 131789 302507 := bstep (se 1 (by rfl) ⟨226880, by rfl⟩ : syracuseStep 302507 = 453761) B453761
theorem B504863 : Blo 131789 504863 := bstep (se 1 (by rfl) ⟨378647, by rfl⟩ : syracuseStep 504863 = 757295) B757295
theorem B214015 : Blo 131789 214015 := bstep (se 1 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 214015 = 321023) B321023
theorem B317159 : Blo 131789 317159 := bstep (se 1 (by rfl) ⟨237869, by rfl⟩ : syracuseStep 317159 = 475739) B475739
theorem B1762087 : Blo 131789 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B2222113 : Blo 131789 2222113 := bstep (se 2 (by rfl) ⟨833292, by rfl⟩ : syracuseStep 2222113 = 1666585) B1666585
theorem B454463 : Blo 131789 454463 := bstep (se 1 (by rfl) ⟨340847, by rfl⟩ : syracuseStep 454463 = 681695) B681695
theorem B2158979 : Blo 131789 2158979 := bstep (se 1 (by rfl) ⟨1619234, by rfl⟩ : syracuseStep 2158979 = 3238469) B3238469
theorem B324847 : Blo 131789 324847 := bstep (se 1 (by rfl) ⟨243635, by rfl⟩ : syracuseStep 324847 = 487271) B487271
theorem B718969 : Blo 131789 718969 := bstep (se 2 (by rfl) ⟨269613, by rfl⟩ : syracuseStep 718969 = 539227) B539227
theorem B135615 : Blo 131789 135615 := bstep (se 1 (by rfl) ⟨101711, by rfl⟩ : syracuseStep 135615 = 203423) B203423
theorem B201671 : Blo 131789 201671 := bstep (se 1 (by rfl) ⟨151253, by rfl⟩ : syracuseStep 201671 = 302507) B302507
theorem B433129 : Blo 131789 433129 := bstep (se 2 (by rfl) ⟨162423, by rfl⟩ : syracuseStep 433129 = 324847) B324847
theorem B302975 : Blo 131789 302975 := bstep (se 1 (by rfl) ⟨227231, by rfl⟩ : syracuseStep 302975 = 454463) B454463
theorem B958625 : Blo 131789 958625 := bstep (se 2 (by rfl) ⟨359484, by rfl⟩ : syracuseStep 958625 = 718969) B718969
theorem B336575 : Blo 131789 336575 := bstep (se 1 (by rfl) ⟨252431, by rfl⟩ : syracuseStep 336575 = 504863) B504863
theorem B2962817 : Blo 131789 2962817 := bstep (se 2 (by rfl) ⟨1111056, by rfl⟩ : syracuseStep 2962817 = 2222113) B2222113
theorem B211439 : Blo 131789 211439 := bstep (se 1 (by rfl) ⟨158579, by rfl⟩ : syracuseStep 211439 = 317159) B317159
theorem B5757277 : Blo 131789 5757277 := bstep (se 3 (by rfl) ⟨1079489, by rfl⟩ : syracuseStep 5757277 = 2158979) B2158979
theorem B2349449 : Blo 131789 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B285353 : Blo 131789 285353 := bstep (se 2 (by rfl) ⟨107007, by rfl⟩ : syracuseStep 285353 = 214015) B214015
theorem B134447 : Blo 131789 134447 := bstep (se 1 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 134447 = 201671) B201671
theorem B201983 : Blo 131789 201983 := bstep (se 1 (by rfl) ⟨151487, by rfl⟩ : syracuseStep 201983 = 302975) B302975
theorem B7676369 : Blo 131789 7676369 := bstep (se 2 (by rfl) ⟨2878638, by rfl⟩ : syracuseStep 7676369 = 5757277) B5757277
theorem B1975211 : Blo 131789 1975211 := bstep (se 1 (by rfl) ⟨1481408, by rfl⟩ : syracuseStep 1975211 = 2962817) B2962817
theorem B140959 : Blo 131789 140959 := bstep (se 1 (by rfl) ⟨105719, by rfl⟩ : syracuseStep 140959 = 211439) B211439
theorem B639083 : Blo 131789 639083 := bstep (se 1 (by rfl) ⟨479312, by rfl⟩ : syracuseStep 639083 = 958625) B958625
theorem B577505 : Blo 131789 577505 := bstep (se 2 (by rfl) ⟨216564, by rfl⟩ : syracuseStep 577505 = 433129) B433129
theorem B1566299 : Blo 131789 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B190235 : Blo 131789 190235 := bstep (se 1 (by rfl) ⟨142676, by rfl⟩ : syracuseStep 190235 = 285353) B285353
theorem B224383 : Blo 131789 224383 := bstep (se 1 (by rfl) ⟨168287, by rfl⟩ : syracuseStep 224383 = 336575) B336575
theorem B426055 : Blo 131789 426055 := bstep (se 1 (by rfl) ⟨319541, by rfl⟩ : syracuseStep 426055 = 639083) B639083
theorem B134655 : Blo 131789 134655 := bstep (se 1 (by rfl) ⟨100991, by rfl⟩ : syracuseStep 134655 = 201983) B201983
theorem B299177 : Blo 131789 299177 := bstep (se 2 (by rfl) ⟨112191, by rfl⟩ : syracuseStep 299177 = 224383) B224383
theorem B5117579 : Blo 131789 5117579 := bstep (se 1 (by rfl) ⟨3838184, by rfl⟩ : syracuseStep 5117579 = 7676369) B7676369
theorem B1316807 : Blo 131789 1316807 := bstep (se 1 (by rfl) ⟨987605, by rfl⟩ : syracuseStep 1316807 = 1975211) B1975211
theorem B507293 : Blo 131789 507293 := bstep (se 3 (by rfl) ⟨95117, by rfl⟩ : syracuseStep 507293 = 190235) B190235
theorem B385003 : Blo 131789 385003 := bstep (se 1 (by rfl) ⟨288752, by rfl⟩ : syracuseStep 385003 = 577505) B577505
theorem B1044199 : Blo 131789 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B751781 : Blo 131789 751781 := bstep (se 4 (by rfl) ⟨70479, by rfl⟩ : syracuseStep 751781 = 140959) B140959
theorem B199451 : Blo 131789 199451 := bstep (se 1 (by rfl) ⟨149588, by rfl⟩ : syracuseStep 199451 = 299177) B299177
theorem B3411719 : Blo 131789 3411719 := bstep (se 1 (by rfl) ⟨2558789, by rfl⟩ : syracuseStep 3411719 = 5117579) B5117579
theorem B501187 : Blo 131789 501187 := bstep (se 1 (by rfl) ⟨375890, by rfl⟩ : syracuseStep 501187 = 751781) B751781
theorem B338195 : Blo 131789 338195 := bstep (se 1 (by rfl) ⟨253646, by rfl⟩ : syracuseStep 338195 = 507293) B507293
theorem B568073 : Blo 131789 568073 := bstep (se 2 (by rfl) ⟨213027, by rfl⟩ : syracuseStep 568073 = 426055) B426055
theorem B1392265 : Blo 131789 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B513337 : Blo 131789 513337 := bstep (se 2 (by rfl) ⟨192501, by rfl⟩ : syracuseStep 513337 = 385003) B385003
theorem B877871 : Blo 131789 877871 := bstep (se 1 (by rfl) ⟨658403, by rfl⟩ : syracuseStep 877871 = 1316807) B1316807
theorem B132967 : Blo 131789 132967 := bstep (se 1 (by rfl) ⟨99725, by rfl⟩ : syracuseStep 132967 = 199451) B199451
theorem B1514861 : Blo 131789 1514861 := bstep (se 3 (by rfl) ⟨284036, by rfl⟩ : syracuseStep 1514861 = 568073) B568073
theorem B668249 : Blo 131789 668249 := bstep (se 2 (by rfl) ⟨250593, by rfl⟩ : syracuseStep 668249 = 501187) B501187
theorem B2274479 : Blo 131789 2274479 := bstep (se 1 (by rfl) ⟨1705859, by rfl⟩ : syracuseStep 2274479 = 3411719) B3411719
theorem B1856353 : Blo 131789 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B585247 : Blo 131789 585247 := bstep (se 1 (by rfl) ⟨438935, by rfl⟩ : syracuseStep 585247 = 877871) B877871
theorem B225463 : Blo 131789 225463 := bstep (se 1 (by rfl) ⟨169097, by rfl⟩ : syracuseStep 225463 = 338195) B338195
theorem B684449 : Blo 131789 684449 := bstep (se 2 (by rfl) ⟨256668, by rfl⟩ : syracuseStep 684449 = 513337) B513337
theorem B300617 : Blo 131789 300617 := bstep (se 2 (by rfl) ⟨112731, by rfl⟩ : syracuseStep 300617 = 225463) B225463
theorem B1516319 : Blo 131789 1516319 := bstep (se 1 (by rfl) ⟨1137239, by rfl⟩ : syracuseStep 1516319 = 2274479) B2274479
theorem B2475137 : Blo 131789 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B445499 : Blo 131789 445499 := bstep (se 1 (by rfl) ⟨334124, by rfl⟩ : syracuseStep 445499 = 668249) B668249
theorem B780329 : Blo 131789 780329 := bstep (se 2 (by rfl) ⟨292623, by rfl⟩ : syracuseStep 780329 = 585247) B585247
theorem B1009907 : Blo 131789 1009907 := bstep (se 1 (by rfl) ⟨757430, by rfl⟩ : syracuseStep 1009907 = 1514861) B1514861
theorem B456299 : Blo 131789 456299 := bstep (se 1 (by rfl) ⟨342224, by rfl⟩ : syracuseStep 456299 = 684449) B684449
theorem B296999 : Blo 131789 296999 := bstep (se 1 (by rfl) ⟨222749, by rfl⟩ : syracuseStep 296999 = 445499) B445499
theorem B200411 : Blo 131789 200411 := bstep (se 1 (by rfl) ⟨150308, by rfl⟩ : syracuseStep 200411 = 300617) B300617
theorem B304199 : Blo 131789 304199 := bstep (se 1 (by rfl) ⟨228149, by rfl⟩ : syracuseStep 304199 = 456299) B456299
theorem B1650091 : Blo 131789 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B673271 : Blo 131789 673271 := bstep (se 1 (by rfl) ⟨504953, by rfl⟩ : syracuseStep 673271 = 1009907) B1009907
theorem B1010879 : Blo 131789 1010879 := bstep (se 1 (by rfl) ⟨758159, by rfl⟩ : syracuseStep 1010879 = 1516319) B1516319
theorem B520219 : Blo 131789 520219 := bstep (se 1 (by rfl) ⟨390164, by rfl⟩ : syracuseStep 520219 = 780329) B780329
theorem B197999 : Blo 131789 197999 := bstep (se 1 (by rfl) ⟨148499, by rfl⟩ : syracuseStep 197999 = 296999) B296999
theorem B133607 : Blo 131789 133607 := bstep (se 1 (by rfl) ⟨100205, by rfl⟩ : syracuseStep 133607 = 200411) B200411
theorem B2200121 : Blo 131789 2200121 := bstep (se 2 (by rfl) ⟨825045, by rfl⟩ : syracuseStep 2200121 = 1650091) B1650091
theorem B693625 : Blo 131789 693625 := bstep (se 2 (by rfl) ⟨260109, by rfl⟩ : syracuseStep 693625 = 520219) B520219
theorem B202799 : Blo 131789 202799 := bstep (se 1 (by rfl) ⟨152099, by rfl⟩ : syracuseStep 202799 = 304199) B304199
theorem B673919 : Blo 131789 673919 := bstep (se 1 (by rfl) ⟨505439, by rfl⟩ : syracuseStep 673919 = 1010879) B1010879
theorem B448847 : Blo 131789 448847 := bstep (se 1 (by rfl) ⟨336635, by rfl⟩ : syracuseStep 448847 = 673271) B673271
theorem B131999 : Blo 131789 131999 := bstep (se 1 (by rfl) ⟨98999, by rfl⟩ : syracuseStep 131999 = 197999) B197999
theorem B135199 : Blo 131789 135199 := bstep (se 1 (by rfl) ⟨101399, by rfl⟩ : syracuseStep 135199 = 202799) B202799
theorem B299231 : Blo 131789 299231 := bstep (se 1 (by rfl) ⟨224423, by rfl⟩ : syracuseStep 299231 = 448847) B448847
theorem B924833 : Blo 131789 924833 := bstep (se 2 (by rfl) ⟨346812, by rfl⟩ : syracuseStep 924833 = 693625) B693625
theorem B449279 : Blo 131789 449279 := bstep (se 1 (by rfl) ⟨336959, by rfl⟩ : syracuseStep 449279 = 673919) B673919
theorem B1466747 : Blo 131789 1466747 := bstep (se 1 (by rfl) ⟨1100060, by rfl⟩ : syracuseStep 1466747 = 2200121) B2200121
theorem B199487 : Blo 131789 199487 := bstep (se 1 (by rfl) ⟨149615, by rfl⟩ : syracuseStep 199487 = 299231) B299231
theorem B299519 : Blo 131789 299519 := bstep (se 1 (by rfl) ⟨224639, by rfl⟩ : syracuseStep 299519 = 449279) B449279
theorem B616555 : Blo 131789 616555 := bstep (se 1 (by rfl) ⟨462416, by rfl⟩ : syracuseStep 616555 = 924833) B924833
theorem B977831 : Blo 131789 977831 := bstep (se 1 (by rfl) ⟨733373, by rfl⟩ : syracuseStep 977831 = 1466747) B1466747
theorem B132991 : Blo 131789 132991 := bstep (se 1 (by rfl) ⟨99743, by rfl⟩ : syracuseStep 132991 = 199487) B199487
theorem B822073 : Blo 131789 822073 := bstep (se 2 (by rfl) ⟨308277, by rfl⟩ : syracuseStep 822073 = 616555) B616555
theorem B199679 : Blo 131789 199679 := bstep (se 1 (by rfl) ⟨149759, by rfl⟩ : syracuseStep 199679 = 299519) B299519
theorem B651887 : Blo 131789 651887 := bstep (se 1 (by rfl) ⟨488915, by rfl⟩ : syracuseStep 651887 = 977831) B977831
theorem B133119 : Blo 131789 133119 := bstep (se 1 (by rfl) ⟨99839, by rfl⟩ : syracuseStep 133119 = 199679) B199679
theorem B434591 : Blo 131789 434591 := bstep (se 1 (by rfl) ⟨325943, by rfl⟩ : syracuseStep 434591 = 651887) B651887
theorem B1096097 : Blo 131789 1096097 := bstep (se 2 (by rfl) ⟨411036, by rfl⟩ : syracuseStep 1096097 = 822073) B822073
theorem B11691701 : Blo 131789 11691701 := bstep (se 5 (by rfl) ⟨548048, by rfl⟩ : syracuseStep 11691701 = 1096097) B1096097
theorem B289727 : Blo 131789 289727 := bstep (se 1 (by rfl) ⟨217295, by rfl⟩ : syracuseStep 289727 = 434591) B434591
theorem B7794467 : Blo 131789 7794467 := bstep (se 1 (by rfl) ⟨5845850, by rfl⟩ : syracuseStep 7794467 = 11691701) B11691701
theorem B193151 : Blo 131789 193151 := bstep (se 1 (by rfl) ⟨144863, by rfl⟩ : syracuseStep 193151 = 289727) B289727
theorem B5196311 : Blo 131789 5196311 := bstep (se 1 (by rfl) ⟨3897233, by rfl⟩ : syracuseStep 5196311 = 7794467) B7794467
theorem B515069 : Blo 131789 515069 := bstep (se 3 (by rfl) ⟨96575, by rfl⟩ : syracuseStep 515069 = 193151) B193151
theorem B343379 : Blo 131789 343379 := bstep (se 1 (by rfl) ⟨257534, by rfl⟩ : syracuseStep 343379 = 515069) B515069
theorem B3464207 : Blo 131789 3464207 := bstep (se 1 (by rfl) ⟨2598155, by rfl⟩ : syracuseStep 3464207 = 5196311) B5196311
theorem B2309471 : Blo 131789 2309471 := bstep (se 1 (by rfl) ⟨1732103, by rfl⟩ : syracuseStep 2309471 = 3464207) B3464207
theorem B228919 : Blo 131789 228919 := bstep (se 1 (by rfl) ⟨171689, by rfl⟩ : syracuseStep 228919 = 343379) B343379
theorem B305225 : Blo 131789 305225 := bstep (se 2 (by rfl) ⟨114459, by rfl⟩ : syracuseStep 305225 = 228919) B228919
theorem B1539647 : Blo 131789 1539647 := bstep (se 1 (by rfl) ⟨1154735, by rfl⟩ : syracuseStep 1539647 = 2309471) B2309471
theorem B203483 : Blo 131789 203483 := bstep (se 1 (by rfl) ⟨152612, by rfl⟩ : syracuseStep 203483 = 305225) B305225
theorem B1026431 : Blo 131789 1026431 := bstep (se 1 (by rfl) ⟨769823, by rfl⟩ : syracuseStep 1026431 = 1539647) B1539647
theorem B135655 : Blo 131789 135655 := bstep (se 1 (by rfl) ⟨101741, by rfl⟩ : syracuseStep 135655 = 203483) B203483
theorem B684287 : Blo 131789 684287 := bstep (se 1 (by rfl) ⟨513215, by rfl⟩ : syracuseStep 684287 = 1026431) B1026431
theorem B456191 : Blo 131789 456191 := bstep (se 1 (by rfl) ⟨342143, by rfl⟩ : syracuseStep 456191 = 684287) B684287
theorem B304127 : Blo 131789 304127 := bstep (se 1 (by rfl) ⟨228095, by rfl⟩ : syracuseStep 304127 = 456191) B456191
theorem B202751 : Blo 131789 202751 := bstep (se 1 (by rfl) ⟨152063, by rfl⟩ : syracuseStep 202751 = 304127) B304127
theorem B135167 : Blo 131789 135167 := bstep (se 1 (by rfl) ⟨101375, by rfl⟩ : syracuseStep 135167 = 202751) B202751

theorem C0 (j : ℕ) (h1 : 32947 ≤ j) (h2 : j ≤ 33646) : Blo 131789 (4 * j + 3) := by
  interval_cases j
  · exact B131791
  · exact B131795
  · exact B131799
  · exact B131803
  · exact B131807
  · exact B131811
  · exact B131815
  · exact B131819
  · exact B131823
  · exact B131827
  · exact B131831
  · exact B131835
  · exact B131839
  · exact B131843
  · exact B131847
  · exact B131851
  · exact B131855
  · exact B131859
  · exact B131863
  · exact B131867
  · exact B131871
  · exact B131875
  · exact B131879
  · exact B131883
  · exact B131887
  · exact B131891
  · exact B131895
  · exact B131899
  · exact B131903
  · exact B131907
  · exact B131911
  · exact B131915
  · exact B131919
  · exact B131923
  · exact B131927
  · exact B131931
  · exact B131935
  · exact B131939
  · exact B131943
  · exact B131947
  · exact B131951
  · exact B131955
  · exact B131959
  · exact B131963
  · exact B131967
  · exact B131971
  · exact B131975
  · exact B131979
  · exact B131983
  · exact B131987
  · exact B131991
  · exact B131995
  · exact B131999
  · exact B132003
  · exact B132007
  · exact B132011
  · exact B132015
  · exact B132019
  · exact B132023
  · exact B132027
  · exact B132031
  · exact B132035
  · exact B132039
  · exact B132043
  · exact B132047
  · exact B132051
  · exact B132055
  · exact B132059
  · exact B132063
  · exact B132067
  · exact B132071
  · exact B132075
  · exact B132079
  · exact B132083
  · exact B132087
  · exact B132091
  · exact B132095
  · exact B132099
  · exact B132103
  · exact B132107
  · exact B132111
  · exact B132115
  · exact B132119
  · exact B132123
  · exact B132127
  · exact B132131
  · exact B132135
  · exact B132139
  · exact B132143
  · exact B132147
  · exact B132151
  · exact B132155
  · exact B132159
  · exact B132163
  · exact B132167
  · exact B132171
  · exact B132175
  · exact B132179
  · exact B132183
  · exact B132187
  · exact B132191
  · exact B132195
  · exact B132199
  · exact B132203
  · exact B132207
  · exact B132211
  · exact B132215
  · exact B132219
  · exact B132223
  · exact B132227
  · exact B132231
  · exact B132235
  · exact B132239
  · exact B132243
  · exact B132247
  · exact B132251
  · exact B132255
  · exact B132259
  · exact B132263
  · exact B132267
  · exact B132271
  · exact B132275
  · exact B132279
  · exact B132283
  · exact B132287
  · exact B132291
  · exact B132295
  · exact B132299
  · exact B132303
  · exact B132307
  · exact B132311
  · exact B132315
  · exact B132319
  · exact B132323
  · exact B132327
  · exact B132331
  · exact B132335
  · exact B132339
  · exact B132343
  · exact B132347
  · exact B132351
  · exact B132355
  · exact B132359
  · exact B132363
  · exact B132367
  · exact B132371
  · exact B132375
  · exact B132379
  · exact B132383
  · exact B132387
  · exact B132391
  · exact B132395
  · exact B132399
  · exact B132403
  · exact B132407
  · exact B132411
  · exact B132415
  · exact B132419
  · exact B132423
  · exact B132427
  · exact B132431
  · exact B132435
  · exact B132439
  · exact B132443
  · exact B132447
  · exact B132451
  · exact B132455
  · exact B132459
  · exact B132463
  · exact B132467
  · exact B132471
  · exact B132475
  · exact B132479
  · exact B132483
  · exact B132487
  · exact B132491
  · exact B132495
  · exact B132499
  · exact B132503
  · exact B132507
  · exact B132511
  · exact B132515
  · exact B132519
  · exact B132523
  · exact B132527
  · exact B132531
  · exact B132535
  · exact B132539
  · exact B132543
  · exact B132547
  · exact B132551
  · exact B132555
  · exact B132559
  · exact B132563
  · exact B132567
  · exact B132571
  · exact B132575
  · exact B132579
  · exact B132583
  · exact B132587
  · exact B132591
  · exact B132595
  · exact B132599
  · exact B132603
  · exact B132607
  · exact B132611
  · exact B132615
  · exact B132619
  · exact B132623
  · exact B132627
  · exact B132631
  · exact B132635
  · exact B132639
  · exact B132643
  · exact B132647
  · exact B132651
  · exact B132655
  · exact B132659
  · exact B132663
  · exact B132667
  · exact B132671
  · exact B132675
  · exact B132679
  · exact B132683
  · exact B132687
  · exact B132691
  · exact B132695
  · exact B132699
  · exact B132703
  · exact B132707
  · exact B132711
  · exact B132715
  · exact B132719
  · exact B132723
  · exact B132727
  · exact B132731
  · exact B132735
  · exact B132739
  · exact B132743
  · exact B132747
  · exact B132751
  · exact B132755
  · exact B132759
  · exact B132763
  · exact B132767
  · exact B132771
  · exact B132775
  · exact B132779
  · exact B132783
  · exact B132787
  · exact B132791
  · exact B132795
  · exact B132799
  · exact B132803
  · exact B132807
  · exact B132811
  · exact B132815
  · exact B132819
  · exact B132823
  · exact B132827
  · exact B132831
  · exact B132835
  · exact B132839
  · exact B132843
  · exact B132847
  · exact B132851
  · exact B132855
  · exact B132859
  · exact B132863
  · exact B132867
  · exact B132871
  · exact B132875
  · exact B132879
  · exact B132883
  · exact B132887
  · exact B132891
  · exact B132895
  · exact B132899
  · exact B132903
  · exact B132907
  · exact B132911
  · exact B132915
  · exact B132919
  · exact B132923
  · exact B132927
  · exact B132931
  · exact B132935
  · exact B132939
  · exact B132943
  · exact B132947
  · exact B132951
  · exact B132955
  · exact B132959
  · exact B132963
  · exact B132967
  · exact B132971
  · exact B132975
  · exact B132979
  · exact B132983
  · exact B132987
  · exact B132991
  · exact B132995
  · exact B132999
  · exact B133003
  · exact B133007
  · exact B133011
  · exact B133015
  · exact B133019
  · exact B133023
  · exact B133027
  · exact B133031
  · exact B133035
  · exact B133039
  · exact B133043
  · exact B133047
  · exact B133051
  · exact B133055
  · exact B133059
  · exact B133063
  · exact B133067
  · exact B133071
  · exact B133075
  · exact B133079
  · exact B133083
  · exact B133087
  · exact B133091
  · exact B133095
  · exact B133099
  · exact B133103
  · exact B133107
  · exact B133111
  · exact B133115
  · exact B133119
  · exact B133123
  · exact B133127
  · exact B133131
  · exact B133135
  · exact B133139
  · exact B133143
  · exact B133147
  · exact B133151
  · exact B133155
  · exact B133159
  · exact B133163
  · exact B133167
  · exact B133171
  · exact B133175
  · exact B133179
  · exact B133183
  · exact B133187
  · exact B133191
  · exact B133195
  · exact B133199
  · exact B133203
  · exact B133207
  · exact B133211
  · exact B133215
  · exact B133219
  · exact B133223
  · exact B133227
  · exact B133231
  · exact B133235
  · exact B133239
  · exact B133243
  · exact B133247
  · exact B133251
  · exact B133255
  · exact B133259
  · exact B133263
  · exact B133267
  · exact B133271
  · exact B133275
  · exact B133279
  · exact B133283
  · exact B133287
  · exact B133291
  · exact B133295
  · exact B133299
  · exact B133303
  · exact B133307
  · exact B133311
  · exact B133315
  · exact B133319
  · exact B133323
  · exact B133327
  · exact B133331
  · exact B133335
  · exact B133339
  · exact B133343
  · exact B133347
  · exact B133351
  · exact B133355
  · exact B133359
  · exact B133363
  · exact B133367
  · exact B133371
  · exact B133375
  · exact B133379
  · exact B133383
  · exact B133387
  · exact B133391
  · exact B133395
  · exact B133399
  · exact B133403
  · exact B133407
  · exact B133411
  · exact B133415
  · exact B133419
  · exact B133423
  · exact B133427
  · exact B133431
  · exact B133435
  · exact B133439
  · exact B133443
  · exact B133447
  · exact B133451
  · exact B133455
  · exact B133459
  · exact B133463
  · exact B133467
  · exact B133471
  · exact B133475
  · exact B133479
  · exact B133483
  · exact B133487
  · exact B133491
  · exact B133495
  · exact B133499
  · exact B133503
  · exact B133507
  · exact B133511
  · exact B133515
  · exact B133519
  · exact B133523
  · exact B133527
  · exact B133531
  · exact B133535
  · exact B133539
  · exact B133543
  · exact B133547
  · exact B133551
  · exact B133555
  · exact B133559
  · exact B133563
  · exact B133567
  · exact B133571
  · exact B133575
  · exact B133579
  · exact B133583
  · exact B133587
  · exact B133591
  · exact B133595
  · exact B133599
  · exact B133603
  · exact B133607
  · exact B133611
  · exact B133615
  · exact B133619
  · exact B133623
  · exact B133627
  · exact B133631
  · exact B133635
  · exact B133639
  · exact B133643
  · exact B133647
  · exact B133651
  · exact B133655
  · exact B133659
  · exact B133663
  · exact B133667
  · exact B133671
  · exact B133675
  · exact B133679
  · exact B133683
  · exact B133687
  · exact B133691
  · exact B133695
  · exact B133699
  · exact B133703
  · exact B133707
  · exact B133711
  · exact B133715
  · exact B133719
  · exact B133723
  · exact B133727
  · exact B133731
  · exact B133735
  · exact B133739
  · exact B133743
  · exact B133747
  · exact B133751
  · exact B133755
  · exact B133759
  · exact B133763
  · exact B133767
  · exact B133771
  · exact B133775
  · exact B133779
  · exact B133783
  · exact B133787
  · exact B133791
  · exact B133795
  · exact B133799
  · exact B133803
  · exact B133807
  · exact B133811
  · exact B133815
  · exact B133819
  · exact B133823
  · exact B133827
  · exact B133831
  · exact B133835
  · exact B133839
  · exact B133843
  · exact B133847
  · exact B133851
  · exact B133855
  · exact B133859
  · exact B133863
  · exact B133867
  · exact B133871
  · exact B133875
  · exact B133879
  · exact B133883
  · exact B133887
  · exact B133891
  · exact B133895
  · exact B133899
  · exact B133903
  · exact B133907
  · exact B133911
  · exact B133915
  · exact B133919
  · exact B133923
  · exact B133927
  · exact B133931
  · exact B133935
  · exact B133939
  · exact B133943
  · exact B133947
  · exact B133951
  · exact B133955
  · exact B133959
  · exact B133963
  · exact B133967
  · exact B133971
  · exact B133975
  · exact B133979
  · exact B133983
  · exact B133987
  · exact B133991
  · exact B133995
  · exact B133999
  · exact B134003
  · exact B134007
  · exact B134011
  · exact B134015
  · exact B134019
  · exact B134023
  · exact B134027
  · exact B134031
  · exact B134035
  · exact B134039
  · exact B134043
  · exact B134047
  · exact B134051
  · exact B134055
  · exact B134059
  · exact B134063
  · exact B134067
  · exact B134071
  · exact B134075
  · exact B134079
  · exact B134083
  · exact B134087
  · exact B134091
  · exact B134095
  · exact B134099
  · exact B134103
  · exact B134107
  · exact B134111
  · exact B134115
  · exact B134119
  · exact B134123
  · exact B134127
  · exact B134131
  · exact B134135
  · exact B134139
  · exact B134143
  · exact B134147
  · exact B134151
  · exact B134155
  · exact B134159
  · exact B134163
  · exact B134167
  · exact B134171
  · exact B134175
  · exact B134179
  · exact B134183
  · exact B134187
  · exact B134191
  · exact B134195
  · exact B134199
  · exact B134203
  · exact B134207
  · exact B134211
  · exact B134215
  · exact B134219
  · exact B134223
  · exact B134227
  · exact B134231
  · exact B134235
  · exact B134239
  · exact B134243
  · exact B134247
  · exact B134251
  · exact B134255
  · exact B134259
  · exact B134263
  · exact B134267
  · exact B134271
  · exact B134275
  · exact B134279
  · exact B134283
  · exact B134287
  · exact B134291
  · exact B134295
  · exact B134299
  · exact B134303
  · exact B134307
  · exact B134311
  · exact B134315
  · exact B134319
  · exact B134323
  · exact B134327
  · exact B134331
  · exact B134335
  · exact B134339
  · exact B134343
  · exact B134347
  · exact B134351
  · exact B134355
  · exact B134359
  · exact B134363
  · exact B134367
  · exact B134371
  · exact B134375
  · exact B134379
  · exact B134383
  · exact B134387
  · exact B134391
  · exact B134395
  · exact B134399
  · exact B134403
  · exact B134407
  · exact B134411
  · exact B134415
  · exact B134419
  · exact B134423
  · exact B134427
  · exact B134431
  · exact B134435
  · exact B134439
  · exact B134443
  · exact B134447
  · exact B134451
  · exact B134455
  · exact B134459
  · exact B134463
  · exact B134467
  · exact B134471
  · exact B134475
  · exact B134479
  · exact B134483
  · exact B134487
  · exact B134491
  · exact B134495
  · exact B134499
  · exact B134503
  · exact B134507
  · exact B134511
  · exact B134515
  · exact B134519
  · exact B134523
  · exact B134527
  · exact B134531
  · exact B134535
  · exact B134539
  · exact B134543
  · exact B134547
  · exact B134551
  · exact B134555
  · exact B134559
  · exact B134563
  · exact B134567
  · exact B134571
  · exact B134575
  · exact B134579
  · exact B134583
  · exact B134587

theorem C1 (j : ℕ) (h1 : 33647 ≤ j) (h2 : j ≤ 33946) : Blo 131789 (4 * j + 3) := by
  interval_cases j
  · exact B134591
  · exact B134595
  · exact B134599
  · exact B134603
  · exact B134607
  · exact B134611
  · exact B134615
  · exact B134619
  · exact B134623
  · exact B134627
  · exact B134631
  · exact B134635
  · exact B134639
  · exact B134643
  · exact B134647
  · exact B134651
  · exact B134655
  · exact B134659
  · exact B134663
  · exact B134667
  · exact B134671
  · exact B134675
  · exact B134679
  · exact B134683
  · exact B134687
  · exact B134691
  · exact B134695
  · exact B134699
  · exact B134703
  · exact B134707
  · exact B134711
  · exact B134715
  · exact B134719
  · exact B134723
  · exact B134727
  · exact B134731
  · exact B134735
  · exact B134739
  · exact B134743
  · exact B134747
  · exact B134751
  · exact B134755
  · exact B134759
  · exact B134763
  · exact B134767
  · exact B134771
  · exact B134775
  · exact B134779
  · exact B134783
  · exact B134787
  · exact B134791
  · exact B134795
  · exact B134799
  · exact B134803
  · exact B134807
  · exact B134811
  · exact B134815
  · exact B134819
  · exact B134823
  · exact B134827
  · exact B134831
  · exact B134835
  · exact B134839
  · exact B134843
  · exact B134847
  · exact B134851
  · exact B134855
  · exact B134859
  · exact B134863
  · exact B134867
  · exact B134871
  · exact B134875
  · exact B134879
  · exact B134883
  · exact B134887
  · exact B134891
  · exact B134895
  · exact B134899
  · exact B134903
  · exact B134907
  · exact B134911
  · exact B134915
  · exact B134919
  · exact B134923
  · exact B134927
  · exact B134931
  · exact B134935
  · exact B134939
  · exact B134943
  · exact B134947
  · exact B134951
  · exact B134955
  · exact B134959
  · exact B134963
  · exact B134967
  · exact B134971
  · exact B134975
  · exact B134979
  · exact B134983
  · exact B134987
  · exact B134991
  · exact B134995
  · exact B134999
  · exact B135003
  · exact B135007
  · exact B135011
  · exact B135015
  · exact B135019
  · exact B135023
  · exact B135027
  · exact B135031
  · exact B135035
  · exact B135039
  · exact B135043
  · exact B135047
  · exact B135051
  · exact B135055
  · exact B135059
  · exact B135063
  · exact B135067
  · exact B135071
  · exact B135075
  · exact B135079
  · exact B135083
  · exact B135087
  · exact B135091
  · exact B135095
  · exact B135099
  · exact B135103
  · exact B135107
  · exact B135111
  · exact B135115
  · exact B135119
  · exact B135123
  · exact B135127
  · exact B135131
  · exact B135135
  · exact B135139
  · exact B135143
  · exact B135147
  · exact B135151
  · exact B135155
  · exact B135159
  · exact B135163
  · exact B135167
  · exact B135171
  · exact B135175
  · exact B135179
  · exact B135183
  · exact B135187
  · exact B135191
  · exact B135195
  · exact B135199
  · exact B135203
  · exact B135207
  · exact B135211
  · exact B135215
  · exact B135219
  · exact B135223
  · exact B135227
  · exact B135231
  · exact B135235
  · exact B135239
  · exact B135243
  · exact B135247
  · exact B135251
  · exact B135255
  · exact B135259
  · exact B135263
  · exact B135267
  · exact B135271
  · exact B135275
  · exact B135279
  · exact B135283
  · exact B135287
  · exact B135291
  · exact B135295
  · exact B135299
  · exact B135303
  · exact B135307
  · exact B135311
  · exact B135315
  · exact B135319
  · exact B135323
  · exact B135327
  · exact B135331
  · exact B135335
  · exact B135339
  · exact B135343
  · exact B135347
  · exact B135351
  · exact B135355
  · exact B135359
  · exact B135363
  · exact B135367
  · exact B135371
  · exact B135375
  · exact B135379
  · exact B135383
  · exact B135387
  · exact B135391
  · exact B135395
  · exact B135399
  · exact B135403
  · exact B135407
  · exact B135411
  · exact B135415
  · exact B135419
  · exact B135423
  · exact B135427
  · exact B135431
  · exact B135435
  · exact B135439
  · exact B135443
  · exact B135447
  · exact B135451
  · exact B135455
  · exact B135459
  · exact B135463
  · exact B135467
  · exact B135471
  · exact B135475
  · exact B135479
  · exact B135483
  · exact B135487
  · exact B135491
  · exact B135495
  · exact B135499
  · exact B135503
  · exact B135507
  · exact B135511
  · exact B135515
  · exact B135519
  · exact B135523
  · exact B135527
  · exact B135531
  · exact B135535
  · exact B135539
  · exact B135543
  · exact B135547
  · exact B135551
  · exact B135555
  · exact B135559
  · exact B135563
  · exact B135567
  · exact B135571
  · exact B135575
  · exact B135579
  · exact B135583
  · exact B135587
  · exact B135591
  · exact B135595
  · exact B135599
  · exact B135603
  · exact B135607
  · exact B135611
  · exact B135615
  · exact B135619
  · exact B135623
  · exact B135627
  · exact B135631
  · exact B135635
  · exact B135639
  · exact B135643
  · exact B135647
  · exact B135651
  · exact B135655
  · exact B135659
  · exact B135663
  · exact B135667
  · exact B135671
  · exact B135675
  · exact B135679
  · exact B135683
  · exact B135687
  · exact B135691
  · exact B135695
  · exact B135699
  · exact B135703
  · exact B135707
  · exact B135711
  · exact B135715
  · exact B135719
  · exact B135723
  · exact B135727
  · exact B135731
  · exact B135735
  · exact B135739
  · exact B135743
  · exact B135747
  · exact B135751
  · exact B135755
  · exact B135759
  · exact B135763
  · exact B135767
  · exact B135771
  · exact B135775
  · exact B135779
  · exact B135783
  · exact B135787

theorem solution (m : ℕ) (hlo : 131789 ≤ m) (hhi : m ≤ 135789) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 32947 ≤ j := by omega
    have hj2 : j ≤ 33946 := by omega
    have hb : Blo 131789 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 33647 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
