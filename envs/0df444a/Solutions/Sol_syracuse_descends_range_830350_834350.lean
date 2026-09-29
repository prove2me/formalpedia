-- Prove2me | solution 1 for syracuse_descends_range_830350_834350
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:47.711279+00:00
-- url     : https://prove2.me/submissions/66f4f370-dd55-46ad-af3e-33892a426039

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


theorem B1441813 : Blo 830350 1441813 := bbase (se 6 (by rfl) ⟨33792, by rfl⟩ : syracuseStep 1441813 = 67585) (by norm_num)
theorem B1998901 : Blo 830350 1998901 := bbase (se 5 (by rfl) ⟨93698, by rfl⟩ : syracuseStep 1998901 = 187397) (by norm_num)
theorem B3997957 : Blo 830350 3997957 := bbase (se 4 (by rfl) ⟨374808, by rfl⟩ : syracuseStep 3997957 = 749617) (by norm_num)
theorem B1999133 : Blo 830350 1999133 := bbase (se 3 (by rfl) ⟨374837, by rfl⟩ : syracuseStep 1999133 = 749675) (by norm_num)
theorem B1245533 : Blo 830350 1245533 := bbase (se 3 (by rfl) ⟨233537, by rfl⟩ : syracuseStep 1245533 = 467075) (by norm_num)
theorem B1245557 : Blo 830350 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B1245581 : Blo 830350 1245581 := bbase (se 3 (by rfl) ⟨233546, by rfl⟩ : syracuseStep 1245581 = 467093) (by norm_num)
theorem B1245605 : Blo 830350 1245605 := bbase (se 4 (by rfl) ⟨116775, by rfl⟩ : syracuseStep 1245605 = 233551) (by norm_num)
theorem B1245629 : Blo 830350 1245629 := bbase (se 3 (by rfl) ⟨233555, by rfl⟩ : syracuseStep 1245629 = 467111) (by norm_num)
theorem B1245653 : Blo 830350 1245653 := bbase (se 7 (by rfl) ⟨14597, by rfl⟩ : syracuseStep 1245653 = 29195) (by norm_num)
theorem B1999325 : Blo 830350 1999325 := bbase (se 3 (by rfl) ⟨374873, by rfl⟩ : syracuseStep 1999325 = 749747) (by norm_num)
theorem B1245677 : Blo 830350 1245677 := bbase (se 3 (by rfl) ⟨233564, by rfl⟩ : syracuseStep 1245677 = 467129) (by norm_num)
theorem B1245701 : Blo 830350 1245701 := bbase (se 4 (by rfl) ⟨116784, by rfl⟩ : syracuseStep 1245701 = 233569) (by norm_num)
theorem B1868309 : Blo 830350 1868309 := bbase (se 6 (by rfl) ⟨43788, by rfl⟩ : syracuseStep 1868309 = 87577) (by norm_num)
theorem B1245725 : Blo 830350 1245725 := bbase (se 3 (by rfl) ⟨233573, by rfl⟩ : syracuseStep 1245725 = 467147) (by norm_num)
theorem B1245749 : Blo 830350 1245749 := bbase (se 5 (by rfl) ⟨58394, by rfl⟩ : syracuseStep 1245749 = 116789) (by norm_num)
theorem B1245773 : Blo 830350 1245773 := bbase (se 3 (by rfl) ⟨233582, by rfl⟩ : syracuseStep 1245773 = 467165) (by norm_num)
theorem B1868381 : Blo 830350 1868381 := bbase (se 3 (by rfl) ⟨350321, by rfl⟩ : syracuseStep 1868381 = 700643) (by norm_num)
theorem B1245797 : Blo 830350 1245797 := bbase (se 4 (by rfl) ⟨116793, by rfl⟩ : syracuseStep 1245797 = 233587) (by norm_num)
theorem B6095477 : Blo 830350 6095477 := bbase (se 5 (by rfl) ⟨285725, by rfl⟩ : syracuseStep 6095477 = 571451) (by norm_num)
theorem B1245821 : Blo 830350 1245821 := bbase (se 3 (by rfl) ⟨233591, by rfl⟩ : syracuseStep 1245821 = 467183) (by norm_num)
theorem B1245845 : Blo 830350 1245845 := bbase (se 6 (by rfl) ⟨29199, by rfl⟩ : syracuseStep 1245845 = 58399) (by norm_num)
theorem B1868453 : Blo 830350 1868453 := bbase (se 4 (by rfl) ⟨175167, by rfl⟩ : syracuseStep 1868453 = 350335) (by norm_num)
theorem B1245869 : Blo 830350 1245869 := bbase (se 3 (by rfl) ⟨233600, by rfl⟩ : syracuseStep 1245869 = 467201) (by norm_num)
theorem B1245893 : Blo 830350 1245893 := bbase (se 4 (by rfl) ⟨116802, by rfl⟩ : syracuseStep 1245893 = 233605) (by norm_num)
theorem B1245917 : Blo 830350 1245917 := bbase (se 3 (by rfl) ⟨233609, by rfl⟩ : syracuseStep 1245917 = 467219) (by norm_num)
theorem B1868525 : Blo 830350 1868525 := bbase (se 3 (by rfl) ⟨350348, by rfl⟩ : syracuseStep 1868525 = 700697) (by norm_num)
theorem B1245941 : Blo 830350 1245941 := bbase (se 5 (by rfl) ⟨58403, by rfl⟩ : syracuseStep 1245941 = 116807) (by norm_num)
theorem B1999613 : Blo 830350 1999613 := bbase (se 3 (by rfl) ⟨374927, by rfl⟩ : syracuseStep 1999613 = 749855) (by norm_num)
theorem B1245965 : Blo 830350 1245965 := bbase (se 3 (by rfl) ⟨233618, by rfl⟩ : syracuseStep 1245965 = 467237) (by norm_num)
theorem B1245989 : Blo 830350 1245989 := bbase (se 4 (by rfl) ⟨116811, by rfl⟩ : syracuseStep 1245989 = 233623) (by norm_num)
theorem B1868597 : Blo 830350 1868597 := bbase (se 5 (by rfl) ⟨87590, by rfl⟩ : syracuseStep 1868597 = 175181) (by norm_num)
theorem B1246013 : Blo 830350 1246013 := bbase (se 3 (by rfl) ⟨233627, by rfl⟩ : syracuseStep 1246013 = 467255) (by norm_num)
theorem B1246037 : Blo 830350 1246037 := bbase (se 9 (by rfl) ⟨3650, by rfl⟩ : syracuseStep 1246037 = 7301) (by norm_num)
theorem B1246061 : Blo 830350 1246061 := bbase (se 3 (by rfl) ⟨233636, by rfl⟩ : syracuseStep 1246061 = 467273) (by norm_num)
theorem B1868669 : Blo 830350 1868669 := bbase (se 3 (by rfl) ⟨350375, by rfl⟩ : syracuseStep 1868669 = 700751) (by norm_num)
theorem B1246085 : Blo 830350 1246085 := bbase (se 4 (by rfl) ⟨116820, by rfl⟩ : syracuseStep 1246085 = 233641) (by norm_num)
theorem B1246109 : Blo 830350 1246109 := bbase (se 3 (by rfl) ⟨233645, by rfl⟩ : syracuseStep 1246109 = 467291) (by norm_num)
theorem B1246133 : Blo 830350 1246133 := bbase (se 5 (by rfl) ⟨58412, by rfl⟩ : syracuseStep 1246133 = 116825) (by norm_num)
theorem B1868741 : Blo 830350 1868741 := bbase (se 4 (by rfl) ⟨175194, by rfl⟩ : syracuseStep 1868741 = 350389) (by norm_num)
theorem B1246157 : Blo 830350 1246157 := bbase (se 3 (by rfl) ⟨233654, by rfl⟩ : syracuseStep 1246157 = 467309) (by norm_num)
theorem B1246181 : Blo 830350 1246181 := bbase (se 4 (by rfl) ⟨116829, by rfl⟩ : syracuseStep 1246181 = 233659) (by norm_num)
theorem B1246205 : Blo 830350 1246205 := bbase (se 3 (by rfl) ⟨233663, by rfl⟩ : syracuseStep 1246205 = 467327) (by norm_num)
theorem B1868813 : Blo 830350 1868813 := bbase (se 3 (by rfl) ⟨350402, by rfl⟩ : syracuseStep 1868813 = 700805) (by norm_num)
theorem B1246229 : Blo 830350 1246229 := bbase (se 6 (by rfl) ⟨29208, by rfl⟩ : syracuseStep 1246229 = 58417) (by norm_num)
theorem B1246253 : Blo 830350 1246253 := bbase (se 3 (by rfl) ⟨233672, by rfl⟩ : syracuseStep 1246253 = 467345) (by norm_num)
theorem B1246277 : Blo 830350 1246277 := bbase (se 4 (by rfl) ⟨116838, by rfl⟩ : syracuseStep 1246277 = 233677) (by norm_num)
theorem B1868885 : Blo 830350 1868885 := bbase (se 8 (by rfl) ⟨10950, by rfl⟩ : syracuseStep 1868885 = 21901) (by norm_num)
theorem B1246301 : Blo 830350 1246301 := bbase (se 3 (by rfl) ⟨233681, by rfl⟩ : syracuseStep 1246301 = 467363) (by norm_num)
theorem B1246325 : Blo 830350 1246325 := bbase (se 5 (by rfl) ⟨58421, by rfl⟩ : syracuseStep 1246325 = 116843) (by norm_num)
theorem B1246349 : Blo 830350 1246349 := bbase (se 3 (by rfl) ⟨233690, by rfl⟩ : syracuseStep 1246349 = 467381) (by norm_num)
theorem B1868957 : Blo 830350 1868957 := bbase (se 3 (by rfl) ⟨350429, by rfl⟩ : syracuseStep 1868957 = 700859) (by norm_num)
theorem B1246373 : Blo 830350 1246373 := bbase (se 4 (by rfl) ⟨116847, by rfl⟩ : syracuseStep 1246373 = 233695) (by norm_num)
theorem B1246397 : Blo 830350 1246397 := bbase (se 3 (by rfl) ⟨233699, by rfl⟩ : syracuseStep 1246397 = 467399) (by norm_num)
theorem B1246421 : Blo 830350 1246421 := bbase (se 7 (by rfl) ⟨14606, by rfl⟩ : syracuseStep 1246421 = 29213) (by norm_num)
theorem B1869029 : Blo 830350 1869029 := bbase (se 4 (by rfl) ⟨175221, by rfl⟩ : syracuseStep 1869029 = 350443) (by norm_num)
theorem B1246445 : Blo 830350 1246445 := bbase (se 3 (by rfl) ⟨233708, by rfl⟩ : syracuseStep 1246445 = 467417) (by norm_num)
theorem B1246469 : Blo 830350 1246469 := bbase (se 4 (by rfl) ⟨116856, by rfl⟩ : syracuseStep 1246469 = 233713) (by norm_num)
theorem B1246493 : Blo 830350 1246493 := bbase (se 3 (by rfl) ⟨233717, by rfl⟩ : syracuseStep 1246493 = 467435) (by norm_num)
theorem B1869101 : Blo 830350 1869101 := bbase (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) (by norm_num)
theorem B1246517 : Blo 830350 1246517 := bbase (se 5 (by rfl) ⟨58430, by rfl⟩ : syracuseStep 1246517 = 116861) (by norm_num)
theorem B1246541 : Blo 830350 1246541 := bbase (se 3 (by rfl) ⟨233726, by rfl⟩ : syracuseStep 1246541 = 467453) (by norm_num)
theorem B1246565 : Blo 830350 1246565 := bbase (se 4 (by rfl) ⟨116865, by rfl⟩ : syracuseStep 1246565 = 233731) (by norm_num)
theorem B1869173 : Blo 830350 1869173 := bbase (se 5 (by rfl) ⟨87617, by rfl⟩ : syracuseStep 1869173 = 175235) (by norm_num)
theorem B1246589 : Blo 830350 1246589 := bbase (se 3 (by rfl) ⟨233735, by rfl⟩ : syracuseStep 1246589 = 467471) (by norm_num)
theorem B1246613 : Blo 830350 1246613 := bbase (se 6 (by rfl) ⟨29217, by rfl⟩ : syracuseStep 1246613 = 58435) (by norm_num)
theorem B1246637 : Blo 830350 1246637 := bbase (se 3 (by rfl) ⟨233744, by rfl⟩ : syracuseStep 1246637 = 467489) (by norm_num)
theorem B1869245 : Blo 830350 1869245 := bbase (se 3 (by rfl) ⟨350483, by rfl⟩ : syracuseStep 1869245 = 700967) (by norm_num)
theorem B1246661 : Blo 830350 1246661 := bbase (se 4 (by rfl) ⟨116874, by rfl⟩ : syracuseStep 1246661 = 233749) (by norm_num)
theorem B1246685 : Blo 830350 1246685 := bbase (se 3 (by rfl) ⟨233753, by rfl⟩ : syracuseStep 1246685 = 467507) (by norm_num)
theorem B1246709 : Blo 830350 1246709 := bbase (se 5 (by rfl) ⟨58439, by rfl⟩ : syracuseStep 1246709 = 116879) (by norm_num)
theorem B1869317 : Blo 830350 1869317 := bbase (se 4 (by rfl) ⟨175248, by rfl⟩ : syracuseStep 1869317 = 350497) (by norm_num)
theorem B1246733 : Blo 830350 1246733 := bbase (se 3 (by rfl) ⟨233762, by rfl⟩ : syracuseStep 1246733 = 467525) (by norm_num)
theorem B1246757 : Blo 830350 1246757 := bbase (se 4 (by rfl) ⟨116883, by rfl⟩ : syracuseStep 1246757 = 233767) (by norm_num)
theorem B1246781 : Blo 830350 1246781 := bbase (se 3 (by rfl) ⟨233771, by rfl⟩ : syracuseStep 1246781 = 467543) (by norm_num)
theorem B1869389 : Blo 830350 1869389 := bbase (se 3 (by rfl) ⟨350510, by rfl⟩ : syracuseStep 1869389 = 701021) (by norm_num)
theorem B1246805 : Blo 830350 1246805 := bbase (se 8 (by rfl) ⟨7305, by rfl⟩ : syracuseStep 1246805 = 14611) (by norm_num)
theorem B1246829 : Blo 830350 1246829 := bbase (se 3 (by rfl) ⟨233780, by rfl⟩ : syracuseStep 1246829 = 467561) (by norm_num)
theorem B1246853 : Blo 830350 1246853 := bbase (se 4 (by rfl) ⟨116892, by rfl⟩ : syracuseStep 1246853 = 233785) (by norm_num)
theorem B1869461 : Blo 830350 1869461 := bbase (se 6 (by rfl) ⟨43815, by rfl⟩ : syracuseStep 1869461 = 87631) (by norm_num)
theorem B1246877 : Blo 830350 1246877 := bbase (se 3 (by rfl) ⟨233789, by rfl⟩ : syracuseStep 1246877 = 467579) (by norm_num)
theorem B1246901 : Blo 830350 1246901 := bbase (se 5 (by rfl) ⟨58448, by rfl⟩ : syracuseStep 1246901 = 116897) (by norm_num)
theorem B1083065 : Blo 830350 1083065 := bbase (se 2 (by rfl) ⟨406149, by rfl⟩ : syracuseStep 1083065 = 812299) (by norm_num)
theorem B1246925 : Blo 830350 1246925 := bbase (se 3 (by rfl) ⟨233798, by rfl⟩ : syracuseStep 1246925 = 467597) (by norm_num)
theorem B1869533 : Blo 830350 1869533 := bbase (se 3 (by rfl) ⟨350537, by rfl⟩ : syracuseStep 1869533 = 701075) (by norm_num)
theorem B1246949 : Blo 830350 1246949 := bbase (se 4 (by rfl) ⟨116901, by rfl⟩ : syracuseStep 1246949 = 233803) (by norm_num)
theorem B1246973 : Blo 830350 1246973 := bbase (se 3 (by rfl) ⟨233807, by rfl⟩ : syracuseStep 1246973 = 467615) (by norm_num)
theorem B1083137 : Blo 830350 1083137 := bbase (se 2 (by rfl) ⟨406176, by rfl⟩ : syracuseStep 1083137 = 812353) (by norm_num)
theorem B1246997 : Blo 830350 1246997 := bbase (se 6 (by rfl) ⟨29226, by rfl⟩ : syracuseStep 1246997 = 58453) (by norm_num)
theorem B1869605 : Blo 830350 1869605 := bbase (se 4 (by rfl) ⟨175275, by rfl⟩ : syracuseStep 1869605 = 350551) (by norm_num)
theorem B1247021 : Blo 830350 1247021 := bbase (se 3 (by rfl) ⟨233816, by rfl⟩ : syracuseStep 1247021 = 467633) (by norm_num)
theorem B1247045 : Blo 830350 1247045 := bbase (se 4 (by rfl) ⟨116910, by rfl⟩ : syracuseStep 1247045 = 233821) (by norm_num)
theorem B1247069 : Blo 830350 1247069 := bbase (se 3 (by rfl) ⟨233825, by rfl⟩ : syracuseStep 1247069 = 467651) (by norm_num)
theorem B1869677 : Blo 830350 1869677 := bbase (se 3 (by rfl) ⟨350564, by rfl⟩ : syracuseStep 1869677 = 701129) (by norm_num)
theorem B1247093 : Blo 830350 1247093 := bbase (se 5 (by rfl) ⟨58457, by rfl⟩ : syracuseStep 1247093 = 116915) (by norm_num)
theorem B1247117 : Blo 830350 1247117 := bbase (se 3 (by rfl) ⟨233834, by rfl⟩ : syracuseStep 1247117 = 467669) (by norm_num)
theorem B1247141 : Blo 830350 1247141 := bbase (se 4 (by rfl) ⟨116919, by rfl⟩ : syracuseStep 1247141 = 233839) (by norm_num)
theorem B1869749 : Blo 830350 1869749 := bbase (se 5 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 1869749 = 175289) (by norm_num)
theorem B1247165 : Blo 830350 1247165 := bbase (se 3 (by rfl) ⟨233843, by rfl⟩ : syracuseStep 1247165 = 467687) (by norm_num)
theorem B1247189 : Blo 830350 1247189 := bbase (se 7 (by rfl) ⟨14615, by rfl⟩ : syracuseStep 1247189 = 29231) (by norm_num)
theorem B5998549 : Blo 830350 5998549 := bbase (se 7 (by rfl) ⟨70295, by rfl⟩ : syracuseStep 5998549 = 140591) (by norm_num)
theorem B1247213 : Blo 830350 1247213 := bbase (se 3 (by rfl) ⟨233852, by rfl⟩ : syracuseStep 1247213 = 467705) (by norm_num)
theorem B6326261 : Blo 830350 6326261 := bbase (se 5 (by rfl) ⟨296543, by rfl⟩ : syracuseStep 6326261 = 593087) (by norm_num)
theorem B1869821 : Blo 830350 1869821 := bbase (se 3 (by rfl) ⟨350591, by rfl⟩ : syracuseStep 1869821 = 701183) (by norm_num)
theorem B1247237 : Blo 830350 1247237 := bbase (se 4 (by rfl) ⟨116928, by rfl⟩ : syracuseStep 1247237 = 233857) (by norm_num)
theorem B1247261 : Blo 830350 1247261 := bbase (se 3 (by rfl) ⟨233861, by rfl⟩ : syracuseStep 1247261 = 467723) (by norm_num)
theorem B886825 : Blo 830350 886825 := bbase (se 2 (by rfl) ⟨332559, by rfl⟩ : syracuseStep 886825 = 665119) (by norm_num)
theorem B1247285 : Blo 830350 1247285 := bbase (se 5 (by rfl) ⟨58466, by rfl⟩ : syracuseStep 1247285 = 116933) (by norm_num)
theorem B1869893 : Blo 830350 1869893 := bbase (se 4 (by rfl) ⟨175302, by rfl⟩ : syracuseStep 1869893 = 350605) (by norm_num)
theorem B1247309 : Blo 830350 1247309 := bbase (se 3 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 1247309 = 467741) (by norm_num)
theorem B1247333 : Blo 830350 1247333 := bbase (se 4 (by rfl) ⟨116937, by rfl⟩ : syracuseStep 1247333 = 233875) (by norm_num)
theorem B886897 : Blo 830350 886897 := bbase (se 2 (by rfl) ⟨332586, by rfl⟩ : syracuseStep 886897 = 665173) (by norm_num)
theorem B2852981 : Blo 830350 2852981 := bbase (se 5 (by rfl) ⟨133733, by rfl⟩ : syracuseStep 2852981 = 267467) (by norm_num)
theorem B1247357 : Blo 830350 1247357 := bbase (se 3 (by rfl) ⟨233879, by rfl⟩ : syracuseStep 1247357 = 467759) (by norm_num)
theorem B1869965 : Blo 830350 1869965 := bbase (se 3 (by rfl) ⟨350618, by rfl⟩ : syracuseStep 1869965 = 701237) (by norm_num)
theorem B1247381 : Blo 830350 1247381 := bbase (se 6 (by rfl) ⟨29235, by rfl⟩ : syracuseStep 1247381 = 58471) (by norm_num)
theorem B1247405 : Blo 830350 1247405 := bbase (se 3 (by rfl) ⟨233888, by rfl⟩ : syracuseStep 1247405 = 467777) (by norm_num)
theorem B1247429 : Blo 830350 1247429 := bbase (se 4 (by rfl) ⟨116946, by rfl⟩ : syracuseStep 1247429 = 233893) (by norm_num)
theorem B1902797 : Blo 830350 1902797 := bbase (se 3 (by rfl) ⟨356774, by rfl⟩ : syracuseStep 1902797 = 713549) (by norm_num)
theorem B1870037 : Blo 830350 1870037 := bbase (se 7 (by rfl) ⟨21914, by rfl⟩ : syracuseStep 1870037 = 43829) (by norm_num)
theorem B1247453 : Blo 830350 1247453 := bbase (se 3 (by rfl) ⟨233897, by rfl⟩ : syracuseStep 1247453 = 467795) (by norm_num)
theorem B1247477 : Blo 830350 1247477 := bbase (se 5 (by rfl) ⟨58475, by rfl⟩ : syracuseStep 1247477 = 116951) (by norm_num)
theorem B1247501 : Blo 830350 1247501 := bbase (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) (by norm_num)
theorem B1870109 : Blo 830350 1870109 := bbase (se 3 (by rfl) ⟨350645, by rfl⟩ : syracuseStep 1870109 = 701291) (by norm_num)
theorem B1247525 : Blo 830350 1247525 := bbase (se 4 (by rfl) ⟨116955, by rfl⟩ : syracuseStep 1247525 = 233911) (by norm_num)
theorem B1247549 : Blo 830350 1247549 := bbase (se 3 (by rfl) ⟨233915, by rfl⟩ : syracuseStep 1247549 = 467831) (by norm_num)
theorem B1247573 : Blo 830350 1247573 := bbase (se 10 (by rfl) ⟨1827, by rfl⟩ : syracuseStep 1247573 = 3655) (by norm_num)
theorem B1870181 : Blo 830350 1870181 := bbase (se 4 (by rfl) ⟨175329, by rfl⟩ : syracuseStep 1870181 = 350659) (by norm_num)
theorem B1050985 : Blo 830350 1050985 := bbase (se 2 (by rfl) ⟨394119, by rfl⟩ : syracuseStep 1050985 = 788239) (by norm_num)
theorem B1247597 : Blo 830350 1247597 := bbase (se 3 (by rfl) ⟨233924, by rfl⟩ : syracuseStep 1247597 = 467849) (by norm_num)
theorem B1247621 : Blo 830350 1247621 := bbase (se 4 (by rfl) ⟨116964, by rfl⟩ : syracuseStep 1247621 = 233929) (by norm_num)
theorem B1247645 : Blo 830350 1247645 := bbase (se 3 (by rfl) ⟨233933, by rfl⟩ : syracuseStep 1247645 = 467867) (by norm_num)
theorem B1870253 : Blo 830350 1870253 := bbase (se 3 (by rfl) ⟨350672, by rfl⟩ : syracuseStep 1870253 = 701345) (by norm_num)
theorem B1247669 : Blo 830350 1247669 := bbase (se 5 (by rfl) ⟨58484, by rfl⟩ : syracuseStep 1247669 = 116969) (by norm_num)
theorem B2853317 : Blo 830350 2853317 := bbase (se 4 (by rfl) ⟨267498, by rfl⟩ : syracuseStep 2853317 = 534997) (by norm_num)
theorem B1247693 : Blo 830350 1247693 := bbase (se 3 (by rfl) ⟨233942, by rfl⟩ : syracuseStep 1247693 = 467885) (by norm_num)
theorem B887269 : Blo 830350 887269 := bbase (se 4 (by rfl) ⟨83181, by rfl⟩ : syracuseStep 887269 = 166363) (by norm_num)
theorem B1247717 : Blo 830350 1247717 := bbase (se 4 (by rfl) ⟨116973, by rfl⟩ : syracuseStep 1247717 = 233947) (by norm_num)
theorem B1870325 : Blo 830350 1870325 := bbase (se 5 (by rfl) ⟨87671, by rfl⟩ : syracuseStep 1870325 = 175343) (by norm_num)
theorem B8554997 : Blo 830350 8554997 := bbase (se 5 (by rfl) ⟨401015, by rfl⟩ : syracuseStep 8554997 = 802031) (by norm_num)
theorem B1247741 : Blo 830350 1247741 := bbase (se 3 (by rfl) ⟨233951, by rfl⟩ : syracuseStep 1247741 = 467903) (by norm_num)
theorem B1051157 : Blo 830350 1051157 := bbase (se 6 (by rfl) ⟨24636, by rfl⟩ : syracuseStep 1051157 = 49273) (by norm_num)
theorem B1247765 : Blo 830350 1247765 := bbase (se 6 (by rfl) ⟨29244, by rfl⟩ : syracuseStep 1247765 = 58489) (by norm_num)
theorem B1247789 : Blo 830350 1247789 := bbase (se 3 (by rfl) ⟨233960, by rfl⟩ : syracuseStep 1247789 = 467921) (by norm_num)
theorem B4262453 : Blo 830350 4262453 := bbase (se 5 (by rfl) ⟨199802, by rfl⟩ : syracuseStep 4262453 = 399605) (by norm_num)
theorem B1870397 : Blo 830350 1870397 := bbase (se 3 (by rfl) ⟨350699, by rfl⟩ : syracuseStep 1870397 = 701399) (by norm_num)
theorem B1247813 : Blo 830350 1247813 := bbase (se 4 (by rfl) ⟨116982, by rfl⟩ : syracuseStep 1247813 = 233965) (by norm_num)
theorem B1051213 : Blo 830350 1051213 := bbase (se 3 (by rfl) ⟨197102, by rfl⟩ : syracuseStep 1051213 = 394205) (by norm_num)
theorem B1247837 : Blo 830350 1247837 := bbase (se 3 (by rfl) ⟨233969, by rfl⟩ : syracuseStep 1247837 = 467939) (by norm_num)
theorem B1247861 : Blo 830350 1247861 := bbase (se 5 (by rfl) ⟨58493, by rfl⟩ : syracuseStep 1247861 = 116987) (by norm_num)
theorem B1870469 : Blo 830350 1870469 := bbase (se 4 (by rfl) ⟨175356, by rfl⟩ : syracuseStep 1870469 = 350713) (by norm_num)
theorem B1247885 : Blo 830350 1247885 := bbase (se 3 (by rfl) ⟨233978, by rfl⟩ : syracuseStep 1247885 = 467957) (by norm_num)
theorem B1247909 : Blo 830350 1247909 := bbase (se 4 (by rfl) ⟨116991, by rfl⟩ : syracuseStep 1247909 = 233983) (by norm_num)
theorem B1051309 : Blo 830350 1051309 := bbase (se 3 (by rfl) ⟨197120, by rfl⟩ : syracuseStep 1051309 = 394241) (by norm_num)
theorem B1247933 : Blo 830350 1247933 := bbase (se 3 (by rfl) ⟨233987, by rfl⟩ : syracuseStep 1247933 = 467975) (by norm_num)
theorem B1870541 : Blo 830350 1870541 := bbase (se 3 (by rfl) ⟨350726, by rfl⟩ : syracuseStep 1870541 = 701453) (by norm_num)
theorem B1247957 : Blo 830350 1247957 := bbase (se 7 (by rfl) ⟨14624, by rfl⟩ : syracuseStep 1247957 = 29249) (by norm_num)
theorem B1247981 : Blo 830350 1247981 := bbase (se 3 (by rfl) ⟨233996, by rfl⟩ : syracuseStep 1247981 = 467993) (by norm_num)
theorem B1248005 : Blo 830350 1248005 := bbase (se 4 (by rfl) ⟨117000, by rfl⟩ : syracuseStep 1248005 = 234001) (by norm_num)
theorem B1870613 : Blo 830350 1870613 := bbase (se 6 (by rfl) ⟨43842, by rfl⟩ : syracuseStep 1870613 = 87685) (by norm_num)
theorem B1248029 : Blo 830350 1248029 := bbase (se 3 (by rfl) ⟨234005, by rfl⟩ : syracuseStep 1248029 = 468011) (by norm_num)
theorem B1248053 : Blo 830350 1248053 := bbase (se 5 (by rfl) ⟨58502, by rfl⟩ : syracuseStep 1248053 = 117005) (by norm_num)
theorem B1182541 : Blo 830350 1182541 := bbase (se 3 (by rfl) ⟨221726, by rfl⟩ : syracuseStep 1182541 = 443453) (by norm_num)
theorem B1248077 : Blo 830350 1248077 := bbase (se 3 (by rfl) ⟨234014, by rfl⟩ : syracuseStep 1248077 = 468029) (by norm_num)
theorem B1051481 : Blo 830350 1051481 := bbase (se 2 (by rfl) ⟨394305, by rfl⟩ : syracuseStep 1051481 = 788611) (by norm_num)
theorem B887645 : Blo 830350 887645 := bbase (se 3 (by rfl) ⟨166433, by rfl⟩ : syracuseStep 887645 = 332867) (by norm_num)
theorem B1870685 : Blo 830350 1870685 := bbase (se 3 (by rfl) ⟨350753, by rfl⟩ : syracuseStep 1870685 = 701507) (by norm_num)
theorem B2132837 : Blo 830350 2132837 := bbase (se 4 (by rfl) ⟨199953, by rfl⟩ : syracuseStep 2132837 = 399907) (by norm_num)
theorem B1248101 : Blo 830350 1248101 := bbase (se 4 (by rfl) ⟨117009, by rfl⟩ : syracuseStep 1248101 = 234019) (by norm_num)
theorem B1248125 : Blo 830350 1248125 := bbase (se 3 (by rfl) ⟨234023, by rfl⟩ : syracuseStep 1248125 = 468047) (by norm_num)
theorem B1051537 : Blo 830350 1051537 := bbase (se 2 (by rfl) ⟨394326, by rfl⟩ : syracuseStep 1051537 = 788653) (by norm_num)
theorem B1248149 : Blo 830350 1248149 := bbase (se 6 (by rfl) ⟨29253, by rfl⟩ : syracuseStep 1248149 = 58507) (by norm_num)
theorem B887717 : Blo 830350 887717 := bbase (se 4 (by rfl) ⟨83223, by rfl⟩ : syracuseStep 887717 = 166447) (by norm_num)
theorem B1870757 : Blo 830350 1870757 := bbase (se 4 (by rfl) ⟨175383, by rfl⟩ : syracuseStep 1870757 = 350767) (by norm_num)
theorem B1248173 : Blo 830350 1248173 := bbase (se 3 (by rfl) ⟨234032, by rfl⟩ : syracuseStep 1248173 = 468065) (by norm_num)
theorem B1248197 : Blo 830350 1248197 := bbase (se 4 (by rfl) ⟨117018, by rfl⟩ : syracuseStep 1248197 = 234037) (by norm_num)
theorem B1248221 : Blo 830350 1248221 := bbase (se 3 (by rfl) ⟨234041, by rfl⟩ : syracuseStep 1248221 = 468083) (by norm_num)
theorem B1870829 : Blo 830350 1870829 := bbase (se 3 (by rfl) ⟨350780, by rfl⟩ : syracuseStep 1870829 = 701561) (by norm_num)
theorem B1051633 : Blo 830350 1051633 := bbase (se 2 (by rfl) ⟨394362, by rfl⟩ : syracuseStep 1051633 = 788725) (by norm_num)
theorem B1248245 : Blo 830350 1248245 := bbase (se 5 (by rfl) ⟨58511, by rfl⟩ : syracuseStep 1248245 = 117023) (by norm_num)
theorem B6753269 : Blo 830350 6753269 := bbase (se 5 (by rfl) ⟨316559, by rfl⟩ : syracuseStep 6753269 = 633119) (by norm_num)
theorem B1248269 : Blo 830350 1248269 := bbase (se 3 (by rfl) ⟨234050, by rfl⟩ : syracuseStep 1248269 = 468101) (by norm_num)
theorem B1182757 : Blo 830350 1182757 := bbase (se 4 (by rfl) ⟨110883, by rfl⟩ : syracuseStep 1182757 = 221767) (by norm_num)
theorem B1248293 : Blo 830350 1248293 := bbase (se 4 (by rfl) ⟨117027, by rfl⟩ : syracuseStep 1248293 = 234055) (by norm_num)
theorem B1870901 : Blo 830350 1870901 := bbase (se 5 (by rfl) ⟨87698, by rfl⟩ : syracuseStep 1870901 = 175397) (by norm_num)
theorem B1248317 : Blo 830350 1248317 := bbase (se 3 (by rfl) ⟨234059, by rfl⟩ : syracuseStep 1248317 = 468119) (by norm_num)
theorem B1248341 : Blo 830350 1248341 := bbase (se 8 (by rfl) ⟨7314, by rfl⟩ : syracuseStep 1248341 = 14629) (by norm_num)
theorem B887905 : Blo 830350 887905 := bbase (se 2 (by rfl) ⟨332964, by rfl⟩ : syracuseStep 887905 = 665929) (by norm_num)
theorem B1248365 : Blo 830350 1248365 := bbase (se 3 (by rfl) ⟨234068, by rfl⟩ : syracuseStep 1248365 = 468137) (by norm_num)
theorem B1870973 : Blo 830350 1870973 := bbase (se 3 (by rfl) ⟨350807, by rfl⟩ : syracuseStep 1870973 = 701615) (by norm_num)
theorem B1248389 : Blo 830350 1248389 := bbase (se 4 (by rfl) ⟨117036, by rfl⟩ : syracuseStep 1248389 = 234073) (by norm_num)
theorem B1051805 : Blo 830350 1051805 := bbase (se 3 (by rfl) ⟨197213, by rfl⟩ : syracuseStep 1051805 = 394427) (by norm_num)
theorem B1248413 : Blo 830350 1248413 := bbase (se 3 (by rfl) ⟨234077, by rfl⟩ : syracuseStep 1248413 = 468155) (by norm_num)
theorem B1248437 : Blo 830350 1248437 := bbase (se 5 (by rfl) ⟨58520, by rfl⟩ : syracuseStep 1248437 = 117041) (by norm_num)
theorem B1871045 : Blo 830350 1871045 := bbase (se 4 (by rfl) ⟨175410, by rfl⟩ : syracuseStep 1871045 = 350821) (by norm_num)
theorem B2133197 : Blo 830350 2133197 := bbase (se 3 (by rfl) ⟨399974, by rfl⟩ : syracuseStep 2133197 = 799949) (by norm_num)
theorem B1248461 : Blo 830350 1248461 := bbase (se 3 (by rfl) ⟨234086, by rfl⟩ : syracuseStep 1248461 = 468173) (by norm_num)
theorem B1051861 : Blo 830350 1051861 := bbase (se 7 (by rfl) ⟨12326, by rfl⟩ : syracuseStep 1051861 = 24653) (by norm_num)
theorem B1248485 : Blo 830350 1248485 := bbase (se 4 (by rfl) ⟨117045, by rfl⟩ : syracuseStep 1248485 = 234091) (by norm_num)
theorem B1248509 : Blo 830350 1248509 := bbase (se 3 (by rfl) ⟨234095, by rfl⟩ : syracuseStep 1248509 = 468191) (by norm_num)
theorem B1871117 : Blo 830350 1871117 := bbase (se 3 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 1871117 = 701669) (by norm_num)
theorem B1248533 : Blo 830350 1248533 := bbase (se 6 (by rfl) ⟨29262, by rfl⟩ : syracuseStep 1248533 = 58525) (by norm_num)
theorem B888089 : Blo 830350 888089 := bbase (se 2 (by rfl) ⟨333033, by rfl⟩ : syracuseStep 888089 = 666067) (by norm_num)
theorem B1248557 : Blo 830350 1248557 := bbase (se 3 (by rfl) ⟨234104, by rfl⟩ : syracuseStep 1248557 = 468209) (by norm_num)
theorem B1051957 : Blo 830350 1051957 := bbase (se 5 (by rfl) ⟨49310, by rfl⟩ : syracuseStep 1051957 = 98621) (by norm_num)
theorem B1248581 : Blo 830350 1248581 := bbase (se 4 (by rfl) ⟨117054, by rfl⟩ : syracuseStep 1248581 = 234109) (by norm_num)
theorem B1871189 : Blo 830350 1871189 := bbase (se 11 (by rfl) ⟨1370, by rfl⟩ : syracuseStep 1871189 = 2741) (by norm_num)
theorem B1248605 : Blo 830350 1248605 := bbase (se 3 (by rfl) ⟨234113, by rfl⟩ : syracuseStep 1248605 = 468227) (by norm_num)
theorem B1248629 : Blo 830350 1248629 := bbase (se 5 (by rfl) ⟨58529, by rfl⟩ : syracuseStep 1248629 = 117059) (by norm_num)
theorem B1248653 : Blo 830350 1248653 := bbase (se 3 (by rfl) ⟨234122, by rfl⟩ : syracuseStep 1248653 = 468245) (by norm_num)
theorem B1183133 : Blo 830350 1183133 := bbase (se 3 (by rfl) ⟨221837, by rfl⟩ : syracuseStep 1183133 = 443675) (by norm_num)
theorem B1871261 : Blo 830350 1871261 := bbase (se 3 (by rfl) ⟨350861, by rfl⟩ : syracuseStep 1871261 = 701723) (by norm_num)
theorem B1248677 : Blo 830350 1248677 := bbase (se 4 (by rfl) ⟨117063, by rfl⟩ : syracuseStep 1248677 = 234127) (by norm_num)
theorem B1248701 : Blo 830350 1248701 := bbase (se 3 (by rfl) ⟨234131, by rfl⟩ : syracuseStep 1248701 = 468263) (by norm_num)
theorem B1248725 : Blo 830350 1248725 := bbase (se 7 (by rfl) ⟨14633, by rfl⟩ : syracuseStep 1248725 = 29267) (by norm_num)
theorem B855517 : Blo 830350 855517 := bbase (se 3 (by rfl) ⟨160409, by rfl⟩ : syracuseStep 855517 = 320819) (by norm_num)
theorem B1052129 : Blo 830350 1052129 := bbase (se 2 (by rfl) ⟨394548, by rfl⟩ : syracuseStep 1052129 = 789097) (by norm_num)
theorem B1871333 : Blo 830350 1871333 := bbase (se 4 (by rfl) ⟨175437, by rfl⟩ : syracuseStep 1871333 = 350875) (by norm_num)
theorem B1248749 : Blo 830350 1248749 := bbase (se 3 (by rfl) ⟨234140, by rfl⟩ : syracuseStep 1248749 = 468281) (by norm_num)
theorem B1248773 : Blo 830350 1248773 := bbase (se 4 (by rfl) ⟨117072, by rfl⟩ : syracuseStep 1248773 = 234145) (by norm_num)
theorem B1052185 : Blo 830350 1052185 := bbase (se 2 (by rfl) ⟨394569, by rfl⟩ : syracuseStep 1052185 = 789139) (by norm_num)
theorem B1248797 : Blo 830350 1248797 := bbase (se 3 (by rfl) ⟨234149, by rfl⟩ : syracuseStep 1248797 = 468299) (by norm_num)
theorem B1576493 : Blo 830350 1576493 := bbase (se 3 (by rfl) ⟨295592, by rfl⟩ : syracuseStep 1576493 = 591185) (by norm_num)
theorem B1871405 : Blo 830350 1871405 := bbase (se 3 (by rfl) ⟨350888, by rfl⟩ : syracuseStep 1871405 = 701777) (by norm_num)
theorem B1248821 : Blo 830350 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B1248845 : Blo 830350 1248845 := bbase (se 3 (by rfl) ⟨234158, by rfl⟩ : syracuseStep 1248845 = 468317) (by norm_num)
theorem B1248869 : Blo 830350 1248869 := bbase (se 4 (by rfl) ⟨117081, by rfl⟩ : syracuseStep 1248869 = 234163) (by norm_num)
theorem B1871477 : Blo 830350 1871477 := bbase (se 5 (by rfl) ⟨87725, by rfl⟩ : syracuseStep 1871477 = 175451) (by norm_num)
theorem B1052281 : Blo 830350 1052281 := bbase (se 2 (by rfl) ⟨394605, by rfl⟩ : syracuseStep 1052281 = 789211) (by norm_num)
theorem B1248893 : Blo 830350 1248893 := bbase (se 3 (by rfl) ⟨234167, by rfl⟩ : syracuseStep 1248893 = 468335) (by norm_num)
theorem B1248917 : Blo 830350 1248917 := bbase (se 6 (by rfl) ⟨29271, by rfl⟩ : syracuseStep 1248917 = 58543) (by norm_num)
theorem B1805981 : Blo 830350 1805981 := bbase (se 3 (by rfl) ⟨338621, by rfl⟩ : syracuseStep 1805981 = 677243) (by norm_num)
theorem B1248941 : Blo 830350 1248941 := bbase (se 3 (by rfl) ⟨234176, by rfl⟩ : syracuseStep 1248941 = 468353) (by norm_num)
theorem B1871549 : Blo 830350 1871549 := bbase (se 3 (by rfl) ⟨350915, by rfl⟩ : syracuseStep 1871549 = 701831) (by norm_num)
theorem B1248965 : Blo 830350 1248965 := bbase (se 4 (by rfl) ⟨117090, by rfl⟩ : syracuseStep 1248965 = 234181) (by norm_num)
theorem B1248989 : Blo 830350 1248989 := bbase (se 3 (by rfl) ⟨234185, by rfl⟩ : syracuseStep 1248989 = 468371) (by norm_num)
theorem B1249013 : Blo 830350 1249013 := bbase (se 5 (by rfl) ⟨58547, by rfl⟩ : syracuseStep 1249013 = 117095) (by norm_num)
theorem B1871621 : Blo 830350 1871621 := bbase (se 4 (by rfl) ⟨175464, by rfl⟩ : syracuseStep 1871621 = 350929) (by norm_num)
theorem B1249037 : Blo 830350 1249037 := bbase (se 3 (by rfl) ⟨234194, by rfl⟩ : syracuseStep 1249037 = 468389) (by norm_num)
theorem B1052453 : Blo 830350 1052453 := bbase (se 4 (by rfl) ⟨98667, by rfl⟩ : syracuseStep 1052453 = 197335) (by norm_num)
theorem B1249061 : Blo 830350 1249061 := bbase (se 4 (by rfl) ⟨117099, by rfl⟩ : syracuseStep 1249061 = 234199) (by norm_num)
theorem B1249085 : Blo 830350 1249085 := bbase (se 3 (by rfl) ⟨234203, by rfl⟩ : syracuseStep 1249085 = 468407) (by norm_num)
theorem B1871693 : Blo 830350 1871693 := bbase (se 3 (by rfl) ⟨350942, by rfl⟩ : syracuseStep 1871693 = 701885) (by norm_num)
theorem B1249109 : Blo 830350 1249109 := bbase (se 9 (by rfl) ⟨3659, by rfl⟩ : syracuseStep 1249109 = 7319) (by norm_num)
theorem B1052509 : Blo 830350 1052509 := bbase (se 3 (by rfl) ⟨197345, by rfl⟩ : syracuseStep 1052509 = 394691) (by norm_num)
theorem B1249133 : Blo 830350 1249133 := bbase (se 3 (by rfl) ⟨234212, by rfl⟩ : syracuseStep 1249133 = 468425) (by norm_num)
theorem B1249157 : Blo 830350 1249157 := bbase (se 4 (by rfl) ⟨117108, by rfl⟩ : syracuseStep 1249157 = 234217) (by norm_num)
theorem B1871765 : Blo 830350 1871765 := bbase (se 6 (by rfl) ⟨43869, by rfl⟩ : syracuseStep 1871765 = 87739) (by norm_num)
theorem B1249181 : Blo 830350 1249181 := bbase (se 3 (by rfl) ⟨234221, by rfl⟩ : syracuseStep 1249181 = 468443) (by norm_num)
theorem B1249205 : Blo 830350 1249205 := bbase (se 5 (by rfl) ⟨58556, by rfl⟩ : syracuseStep 1249205 = 117113) (by norm_num)
theorem B1052605 : Blo 830350 1052605 := bbase (se 3 (by rfl) ⟨197363, by rfl⟩ : syracuseStep 1052605 = 394727) (by norm_num)
theorem B1249229 : Blo 830350 1249229 := bbase (se 3 (by rfl) ⟨234230, by rfl⟩ : syracuseStep 1249229 = 468461) (by norm_num)
theorem B1871837 : Blo 830350 1871837 := bbase (se 3 (by rfl) ⟨350969, by rfl⟩ : syracuseStep 1871837 = 701939) (by norm_num)
theorem B1249253 : Blo 830350 1249253 := bbase (se 4 (by rfl) ⟨117117, by rfl⟩ : syracuseStep 1249253 = 234235) (by norm_num)
theorem B1249277 : Blo 830350 1249277 := bbase (se 3 (by rfl) ⟨234239, by rfl⟩ : syracuseStep 1249277 = 468479) (by norm_num)
theorem B888841 : Blo 830350 888841 := bbase (se 2 (by rfl) ⟨333315, by rfl⟩ : syracuseStep 888841 = 666631) (by norm_num)
theorem B1773589 : Blo 830350 1773589 := bbase (se 6 (by rfl) ⟨41568, by rfl⟩ : syracuseStep 1773589 = 83137) (by norm_num)
theorem B1249301 : Blo 830350 1249301 := bbase (se 6 (by rfl) ⟨29280, by rfl⟩ : syracuseStep 1249301 = 58561) (by norm_num)
theorem B1871909 : Blo 830350 1871909 := bbase (se 4 (by rfl) ⟨175491, by rfl⟩ : syracuseStep 1871909 = 350983) (by norm_num)
theorem B1249325 : Blo 830350 1249325 := bbase (se 3 (by rfl) ⟨234248, by rfl⟩ : syracuseStep 1249325 = 468497) (by norm_num)
theorem B1249349 : Blo 830350 1249349 := bbase (se 4 (by rfl) ⟨117126, by rfl⟩ : syracuseStep 1249349 = 234253) (by norm_num)
theorem B888913 : Blo 830350 888913 := bbase (se 2 (by rfl) ⟨333342, by rfl⟩ : syracuseStep 888913 = 666685) (by norm_num)
theorem B1249373 : Blo 830350 1249373 := bbase (se 3 (by rfl) ⟨234257, by rfl⟩ : syracuseStep 1249373 = 468515) (by norm_num)
theorem B1052777 : Blo 830350 1052777 := bbase (se 2 (by rfl) ⟨394791, by rfl⟩ : syracuseStep 1052777 = 789583) (by norm_num)
theorem B1871981 : Blo 830350 1871981 := bbase (se 3 (by rfl) ⟨350996, by rfl⟩ : syracuseStep 1871981 = 701993) (by norm_num)
theorem B2003053 : Blo 830350 2003053 := bbase (se 3 (by rfl) ⟨375572, by rfl⟩ : syracuseStep 2003053 = 751145) (by norm_num)
theorem B1249397 : Blo 830350 1249397 := bbase (se 5 (by rfl) ⟨58565, by rfl⟩ : syracuseStep 1249397 = 117131) (by norm_num)
theorem B1249421 : Blo 830350 1249421 := bbase (se 3 (by rfl) ⟨234266, by rfl⟩ : syracuseStep 1249421 = 468533) (by norm_num)
theorem B1052833 : Blo 830350 1052833 := bbase (se 2 (by rfl) ⟨394812, by rfl⟩ : syracuseStep 1052833 = 789625) (by norm_num)
theorem B1249445 : Blo 830350 1249445 := bbase (se 4 (by rfl) ⟨117135, by rfl⟩ : syracuseStep 1249445 = 234271) (by norm_num)
theorem B1872053 : Blo 830350 1872053 := bbase (se 5 (by rfl) ⟨87752, by rfl⟩ : syracuseStep 1872053 = 175505) (by norm_num)
theorem B1249469 : Blo 830350 1249469 := bbase (se 3 (by rfl) ⟨234275, by rfl⟩ : syracuseStep 1249469 = 468551) (by norm_num)
theorem B1249493 : Blo 830350 1249493 := bbase (se 7 (by rfl) ⟨14642, by rfl⟩ : syracuseStep 1249493 = 29285) (by norm_num)
theorem B1249517 : Blo 830350 1249517 := bbase (se 3 (by rfl) ⟨234284, by rfl⟩ : syracuseStep 1249517 = 468569) (by norm_num)
theorem B1872125 : Blo 830350 1872125 := bbase (se 3 (by rfl) ⟨351023, by rfl⟩ : syracuseStep 1872125 = 702047) (by norm_num)
theorem B1052929 : Blo 830350 1052929 := bbase (se 2 (by rfl) ⟨394848, by rfl⟩ : syracuseStep 1052929 = 789697) (by norm_num)
theorem B889093 : Blo 830350 889093 := bbase (se 4 (by rfl) ⟨83352, by rfl⟩ : syracuseStep 889093 = 166705) (by norm_num)
theorem B1249541 : Blo 830350 1249541 := bbase (se 4 (by rfl) ⟨117144, by rfl⟩ : syracuseStep 1249541 = 234289) (by norm_num)
theorem B1577245 : Blo 830350 1577245 := bbase (se 3 (by rfl) ⟨295733, by rfl⟩ : syracuseStep 1577245 = 591467) (by norm_num)
theorem B1249565 : Blo 830350 1249565 := bbase (se 3 (by rfl) ⟨234293, by rfl⟩ : syracuseStep 1249565 = 468587) (by norm_num)
theorem B1249589 : Blo 830350 1249589 := bbase (se 5 (by rfl) ⟨58574, by rfl⟩ : syracuseStep 1249589 = 117149) (by norm_num)
theorem B1872197 : Blo 830350 1872197 := bbase (se 4 (by rfl) ⟨175518, by rfl⟩ : syracuseStep 1872197 = 351037) (by norm_num)
theorem B1249613 : Blo 830350 1249613 := bbase (se 3 (by rfl) ⟨234302, by rfl⟩ : syracuseStep 1249613 = 468605) (by norm_num)
theorem B2003285 : Blo 830350 2003285 := bbase (se 10 (by rfl) ⟨2934, by rfl⟩ : syracuseStep 2003285 = 5869) (by norm_num)
theorem B4002149 : Blo 830350 4002149 := bbase (se 4 (by rfl) ⟨375201, by rfl⟩ : syracuseStep 4002149 = 750403) (by norm_num)
theorem B1249637 : Blo 830350 1249637 := bbase (se 4 (by rfl) ⟨117153, by rfl⟩ : syracuseStep 1249637 = 234307) (by norm_num)
theorem B1249661 : Blo 830350 1249661 := bbase (se 3 (by rfl) ⟨234311, by rfl⟩ : syracuseStep 1249661 = 468623) (by norm_num)
theorem B1872269 : Blo 830350 1872269 := bbase (se 3 (by rfl) ⟨351050, by rfl⟩ : syracuseStep 1872269 = 702101) (by norm_num)
theorem B1249685 : Blo 830350 1249685 := bbase (se 6 (by rfl) ⟨29289, by rfl⟩ : syracuseStep 1249685 = 58579) (by norm_num)
theorem B1577389 : Blo 830350 1577389 := bbase (se 3 (by rfl) ⟨295760, by rfl⟩ : syracuseStep 1577389 = 591521) (by norm_num)
theorem B1053101 : Blo 830350 1053101 := bbase (se 3 (by rfl) ⟨197456, by rfl⟩ : syracuseStep 1053101 = 394913) (by norm_num)
theorem B1249709 : Blo 830350 1249709 := bbase (se 3 (by rfl) ⟨234320, by rfl⟩ : syracuseStep 1249709 = 468641) (by norm_num)
theorem B6951349 : Blo 830350 6951349 := bbase (se 5 (by rfl) ⟨325844, by rfl⟩ : syracuseStep 6951349 = 651689) (by norm_num)
theorem B1249733 : Blo 830350 1249733 := bbase (se 4 (by rfl) ⟨117162, by rfl⟩ : syracuseStep 1249733 = 234325) (by norm_num)
theorem B1872341 : Blo 830350 1872341 := bbase (se 7 (by rfl) ⟨21941, by rfl⟩ : syracuseStep 1872341 = 43883) (by norm_num)
theorem B5706197 : Blo 830350 5706197 := bbase (se 7 (by rfl) ⟨66869, by rfl⟩ : syracuseStep 5706197 = 133739) (by norm_num)
theorem B1249757 : Blo 830350 1249757 := bbase (se 3 (by rfl) ⟨234329, by rfl⟩ : syracuseStep 1249757 = 468659) (by norm_num)
theorem B1053157 : Blo 830350 1053157 := bbase (se 4 (by rfl) ⟨98733, by rfl⟩ : syracuseStep 1053157 = 197467) (by norm_num)
theorem B2003429 : Blo 830350 2003429 := bbase (se 4 (by rfl) ⟨187821, by rfl⟩ : syracuseStep 2003429 = 375643) (by norm_num)
theorem B1249781 : Blo 830350 1249781 := bbase (se 5 (by rfl) ⟨58583, by rfl⟩ : syracuseStep 1249781 = 117167) (by norm_num)
theorem B1249805 : Blo 830350 1249805 := bbase (se 3 (by rfl) ⟨234338, by rfl⟩ : syracuseStep 1249805 = 468677) (by norm_num)
theorem B1872413 : Blo 830350 1872413 := bbase (se 3 (by rfl) ⟨351077, by rfl⟩ : syracuseStep 1872413 = 702155) (by norm_num)
theorem B1249829 : Blo 830350 1249829 := bbase (se 4 (by rfl) ⟨117171, by rfl⟩ : syracuseStep 1249829 = 234343) (by norm_num)
theorem B3379765 : Blo 830350 3379765 := bbase (se 5 (by rfl) ⟨158426, by rfl⟩ : syracuseStep 3379765 = 316853) (by norm_num)
theorem B1249853 : Blo 830350 1249853 := bbase (se 3 (by rfl) ⟨234347, by rfl⟩ : syracuseStep 1249853 = 468695) (by norm_num)
theorem B1053253 : Blo 830350 1053253 := bbase (se 4 (by rfl) ⟨98742, by rfl⟩ : syracuseStep 1053253 = 197485) (by norm_num)
theorem B1577549 : Blo 830350 1577549 := bbase (se 3 (by rfl) ⟨295790, by rfl⟩ : syracuseStep 1577549 = 591581) (by norm_num)
theorem B1249877 : Blo 830350 1249877 := bbase (se 8 (by rfl) ⟨7323, by rfl⟩ : syracuseStep 1249877 = 14647) (by norm_num)
theorem B1872485 : Blo 830350 1872485 := bbase (se 4 (by rfl) ⟨175545, by rfl⟩ : syracuseStep 1872485 = 351091) (by norm_num)
theorem B1249901 : Blo 830350 1249901 := bbase (se 3 (by rfl) ⟨234356, by rfl⟩ : syracuseStep 1249901 = 468713) (by norm_num)
theorem B1249925 : Blo 830350 1249925 := bbase (se 4 (by rfl) ⟨117180, by rfl⟩ : syracuseStep 1249925 = 234361) (by norm_num)
theorem B2101909 : Blo 830350 2101909 := bbase (se 6 (by rfl) ⟨49263, by rfl⟩ : syracuseStep 2101909 = 98527) (by norm_num)
theorem B1217173 : Blo 830350 1217173 := bbase (se 6 (by rfl) ⟨28527, by rfl⟩ : syracuseStep 1217173 = 57055) (by norm_num)
theorem B1249949 : Blo 830350 1249949 := bbase (se 3 (by rfl) ⟨234365, by rfl⟩ : syracuseStep 1249949 = 468731) (by norm_num)
theorem B1872557 : Blo 830350 1872557 := bbase (se 3 (by rfl) ⟨351104, by rfl⟩ : syracuseStep 1872557 = 702209) (by norm_num)
theorem B1249973 : Blo 830350 1249973 := bbase (se 5 (by rfl) ⟨58592, by rfl⟩ : syracuseStep 1249973 = 117185) (by norm_num)
theorem B889537 : Blo 830350 889537 := bbase (se 2 (by rfl) ⟨333576, by rfl⟩ : syracuseStep 889537 = 667153) (by norm_num)
theorem B1249997 : Blo 830350 1249997 := bbase (se 3 (by rfl) ⟨234374, by rfl⟩ : syracuseStep 1249997 = 468749) (by norm_num)
theorem B2003669 : Blo 830350 2003669 := bbase (se 7 (by rfl) ⟨23480, by rfl⟩ : syracuseStep 2003669 = 46961) (by norm_num)
theorem B1577693 : Blo 830350 1577693 := bbase (se 3 (by rfl) ⟨295817, by rfl⟩ : syracuseStep 1577693 = 591635) (by norm_num)
theorem B1250021 : Blo 830350 1250021 := bbase (se 4 (by rfl) ⟨117189, by rfl⟩ : syracuseStep 1250021 = 234379) (by norm_num)
theorem B1053425 : Blo 830350 1053425 := bbase (se 2 (by rfl) ⟨395034, by rfl⟩ : syracuseStep 1053425 = 790069) (by norm_num)
theorem B1872629 : Blo 830350 1872629 := bbase (se 5 (by rfl) ⟨87779, by rfl⟩ : syracuseStep 1872629 = 175559) (by norm_num)
theorem B1250045 : Blo 830350 1250045 := bbase (se 3 (by rfl) ⟨234383, by rfl⟩ : syracuseStep 1250045 = 468767) (by norm_num)
theorem B2102021 : Blo 830350 2102021 := bbase (se 4 (by rfl) ⟨197064, by rfl⟩ : syracuseStep 2102021 = 394129) (by norm_num)
theorem B1250069 : Blo 830350 1250069 := bbase (se 6 (by rfl) ⟨29298, by rfl⟩ : syracuseStep 1250069 = 58597) (by norm_num)
theorem B1053481 : Blo 830350 1053481 := bbase (se 2 (by rfl) ⟨395055, by rfl⟩ : syracuseStep 1053481 = 790111) (by norm_num)
theorem B1184557 : Blo 830350 1184557 := bbase (se 3 (by rfl) ⟨222104, by rfl⟩ : syracuseStep 1184557 = 444209) (by norm_num)
theorem B1250093 : Blo 830350 1250093 := bbase (se 3 (by rfl) ⟨234392, by rfl⟩ : syracuseStep 1250093 = 468785) (by norm_num)
theorem B1872701 : Blo 830350 1872701 := bbase (se 3 (by rfl) ⟨351131, by rfl⟩ : syracuseStep 1872701 = 702263) (by norm_num)
theorem B889661 : Blo 830350 889661 := bbase (se 3 (by rfl) ⟨166811, by rfl⟩ : syracuseStep 889661 = 333623) (by norm_num)
theorem B1250117 : Blo 830350 1250117 := bbase (se 4 (by rfl) ⟨117198, by rfl⟩ : syracuseStep 1250117 = 234397) (by norm_num)
theorem B1250141 : Blo 830350 1250141 := bbase (se 3 (by rfl) ⟨234401, by rfl⟩ : syracuseStep 1250141 = 468803) (by norm_num)
theorem B1250165 : Blo 830350 1250165 := bbase (se 5 (by rfl) ⟨58601, by rfl⟩ : syracuseStep 1250165 = 117203) (by norm_num)
theorem B1872773 : Blo 830350 1872773 := bbase (se 4 (by rfl) ⟨175572, by rfl⟩ : syracuseStep 1872773 = 351145) (by norm_num)
theorem B1053577 : Blo 830350 1053577 := bbase (se 2 (by rfl) ⟨395091, by rfl⟩ : syracuseStep 1053577 = 790183) (by norm_num)
theorem B1774477 : Blo 830350 1774477 := bbase (se 3 (by rfl) ⟨332714, by rfl⟩ : syracuseStep 1774477 = 665429) (by norm_num)
theorem B1250189 : Blo 830350 1250189 := bbase (se 3 (by rfl) ⟨234410, by rfl⟩ : syracuseStep 1250189 = 468821) (by norm_num)
theorem B1250213 : Blo 830350 1250213 := bbase (se 4 (by rfl) ⟨117207, by rfl⟩ : syracuseStep 1250213 = 234415) (by norm_num)
theorem B1250237 : Blo 830350 1250237 := bbase (se 3 (by rfl) ⟨234419, by rfl⟩ : syracuseStep 1250237 = 468839) (by norm_num)
theorem B2102213 : Blo 830350 2102213 := bbase (se 4 (by rfl) ⟨197082, by rfl⟩ : syracuseStep 2102213 = 394165) (by norm_num)
theorem B1872845 : Blo 830350 1872845 := bbase (se 3 (by rfl) ⟨351158, by rfl⟩ : syracuseStep 1872845 = 702317) (by norm_num)
theorem B1250261 : Blo 830350 1250261 := bbase (se 7 (by rfl) ⟨14651, by rfl⟩ : syracuseStep 1250261 = 29303) (by norm_num)
theorem B1250285 : Blo 830350 1250285 := bbase (se 3 (by rfl) ⟨234428, by rfl⟩ : syracuseStep 1250285 = 468857) (by norm_num)
theorem B1577981 : Blo 830350 1577981 := bbase (se 3 (by rfl) ⟨295871, by rfl⟩ : syracuseStep 1577981 = 591743) (by norm_num)
theorem B1250309 : Blo 830350 1250309 := bbase (se 4 (by rfl) ⟨117216, by rfl⟩ : syracuseStep 1250309 = 234433) (by norm_num)
theorem B1872917 : Blo 830350 1872917 := bbase (se 6 (by rfl) ⟨43896, by rfl⟩ : syracuseStep 1872917 = 87793) (by norm_num)
theorem B1250333 : Blo 830350 1250333 := bbase (se 3 (by rfl) ⟨234437, by rfl⟩ : syracuseStep 1250333 = 468875) (by norm_num)
theorem B1053749 : Blo 830350 1053749 := bbase (se 5 (by rfl) ⟨49394, by rfl⟩ : syracuseStep 1053749 = 98789) (by norm_num)
theorem B1250357 : Blo 830350 1250357 := bbase (se 5 (by rfl) ⟨58610, by rfl⟩ : syracuseStep 1250357 = 117221) (by norm_num)
theorem B889913 : Blo 830350 889913 := bbase (se 2 (by rfl) ⟨333717, by rfl⟩ : syracuseStep 889913 = 667435) (by norm_num)
theorem B1250381 : Blo 830350 1250381 := bbase (se 3 (by rfl) ⟨234446, by rfl⟩ : syracuseStep 1250381 = 468893) (by norm_num)
theorem B1872989 : Blo 830350 1872989 := bbase (se 3 (by rfl) ⟨351185, by rfl⟩ : syracuseStep 1872989 = 702371) (by norm_num)
theorem B1250405 : Blo 830350 1250405 := bbase (se 4 (by rfl) ⟨117225, by rfl⟩ : syracuseStep 1250405 = 234451) (by norm_num)
theorem B1053805 : Blo 830350 1053805 := bbase (se 3 (by rfl) ⟨197588, by rfl⟩ : syracuseStep 1053805 = 395177) (by norm_num)
theorem B1250429 : Blo 830350 1250429 := bbase (se 3 (by rfl) ⟨234455, by rfl⟩ : syracuseStep 1250429 = 468911) (by norm_num)
theorem B1578133 : Blo 830350 1578133 := bbase (se 6 (by rfl) ⟨36987, by rfl⟩ : syracuseStep 1578133 = 73975) (by norm_num)
theorem B1250453 : Blo 830350 1250453 := bbase (se 6 (by rfl) ⟨29307, by rfl⟩ : syracuseStep 1250453 = 58615) (by norm_num)
theorem B1873061 : Blo 830350 1873061 := bbase (se 4 (by rfl) ⟨175599, by rfl⟩ : syracuseStep 1873061 = 351199) (by norm_num)
theorem B1283237 : Blo 830350 1283237 := bbase (se 4 (by rfl) ⟨120303, by rfl⟩ : syracuseStep 1283237 = 240607) (by norm_num)
theorem B1250477 : Blo 830350 1250477 := bbase (se 3 (by rfl) ⟨234464, by rfl⟩ : syracuseStep 1250477 = 468929) (by norm_num)
theorem B1250501 : Blo 830350 1250501 := bbase (se 4 (by rfl) ⟨117234, by rfl⟩ : syracuseStep 1250501 = 234469) (by norm_num)
theorem B1053901 : Blo 830350 1053901 := bbase (se 3 (by rfl) ⟨197606, by rfl⟩ : syracuseStep 1053901 = 395213) (by norm_num)
theorem B1250525 : Blo 830350 1250525 := bbase (se 3 (by rfl) ⟨234473, by rfl⟩ : syracuseStep 1250525 = 468947) (by norm_num)
theorem B1873133 : Blo 830350 1873133 := bbase (se 3 (by rfl) ⟨351212, by rfl⟩ : syracuseStep 1873133 = 702425) (by norm_num)
theorem B1250549 : Blo 830350 1250549 := bbase (se 5 (by rfl) ⟨58619, by rfl⟩ : syracuseStep 1250549 = 117239) (by norm_num)
theorem B1250573 : Blo 830350 1250573 := bbase (se 3 (by rfl) ⟨234482, by rfl⟩ : syracuseStep 1250573 = 468965) (by norm_num)
theorem B2102557 : Blo 830350 2102557 := bbase (se 3 (by rfl) ⟨394229, by rfl⟩ : syracuseStep 2102557 = 788459) (by norm_num)
theorem B1250597 : Blo 830350 1250597 := bbase (se 4 (by rfl) ⟨117243, by rfl⟩ : syracuseStep 1250597 = 234487) (by norm_num)
theorem B1873205 : Blo 830350 1873205 := bbase (se 5 (by rfl) ⟨87806, by rfl⟩ : syracuseStep 1873205 = 175613) (by norm_num)
theorem B1250621 : Blo 830350 1250621 := bbase (se 3 (by rfl) ⟨234491, by rfl⟩ : syracuseStep 1250621 = 468983) (by norm_num)
theorem B2528597 : Blo 830350 2528597 := bbase (se 14 (by rfl) ⟨231, by rfl⟩ : syracuseStep 2528597 = 463) (by norm_num)
theorem B1250645 : Blo 830350 1250645 := bbase (se 14 (by rfl) ⟨114, by rfl⟩ : syracuseStep 1250645 = 229) (by norm_num)
theorem B1250669 : Blo 830350 1250669 := bbase (se 3 (by rfl) ⟨234500, by rfl⟩ : syracuseStep 1250669 = 469001) (by norm_num)
theorem B1054073 : Blo 830350 1054073 := bbase (se 2 (by rfl) ⟨395277, by rfl⟩ : syracuseStep 1054073 = 790555) (by norm_num)
theorem B1774973 : Blo 830350 1774973 := bbase (se 3 (by rfl) ⟨332807, by rfl⟩ : syracuseStep 1774973 = 665615) (by norm_num)
theorem B1185149 : Blo 830350 1185149 := bbase (se 3 (by rfl) ⟨222215, by rfl⟩ : syracuseStep 1185149 = 444431) (by norm_num)
theorem B1873277 : Blo 830350 1873277 := bbase (se 3 (by rfl) ⟨351239, by rfl⟩ : syracuseStep 1873277 = 702479) (by norm_num)
theorem B1250693 : Blo 830350 1250693 := bbase (se 4 (by rfl) ⟨117252, by rfl⟩ : syracuseStep 1250693 = 234505) (by norm_num)
theorem B2102669 : Blo 830350 2102669 := bbase (se 3 (by rfl) ⟨394250, by rfl⟩ : syracuseStep 2102669 = 788501) (by norm_num)
theorem B1250717 : Blo 830350 1250717 := bbase (se 3 (by rfl) ⟨234509, by rfl⟩ : syracuseStep 1250717 = 469019) (by norm_num)
theorem B1054129 : Blo 830350 1054129 := bbase (se 2 (by rfl) ⟨395298, by rfl⟩ : syracuseStep 1054129 = 790597) (by norm_num)
theorem B1250741 : Blo 830350 1250741 := bbase (se 5 (by rfl) ⟨58628, by rfl⟩ : syracuseStep 1250741 = 117257) (by norm_num)
theorem B1578437 : Blo 830350 1578437 := bbase (se 4 (by rfl) ⟨147978, by rfl⟩ : syracuseStep 1578437 = 295957) (by norm_num)
theorem B1873349 : Blo 830350 1873349 := bbase (se 4 (by rfl) ⟨175626, by rfl⟩ : syracuseStep 1873349 = 351253) (by norm_num)
theorem B1185229 : Blo 830350 1185229 := bbase (se 3 (by rfl) ⟨222230, by rfl⟩ : syracuseStep 1185229 = 444461) (by norm_num)
theorem B1250765 : Blo 830350 1250765 := bbase (se 3 (by rfl) ⟨234518, by rfl⟩ : syracuseStep 1250765 = 469037) (by norm_num)
theorem B9475541 : Blo 830350 9475541 := bbase (se 7 (by rfl) ⟨111041, by rfl⟩ : syracuseStep 9475541 = 222083) (by norm_num)
theorem B2004437 : Blo 830350 2004437 := bbase (se 7 (by rfl) ⟨23489, by rfl⟩ : syracuseStep 2004437 = 46979) (by norm_num)
theorem B1250789 : Blo 830350 1250789 := bbase (se 4 (by rfl) ⟨117261, by rfl⟩ : syracuseStep 1250789 = 234523) (by norm_num)
theorem B890357 : Blo 830350 890357 := bbase (se 5 (by rfl) ⟨41735, by rfl⟩ : syracuseStep 890357 = 83471) (by norm_num)
theorem B1250813 : Blo 830350 1250813 := bbase (se 3 (by rfl) ⟨234527, by rfl⟩ : syracuseStep 1250813 = 469055) (by norm_num)
theorem B1873421 : Blo 830350 1873421 := bbase (se 3 (by rfl) ⟨351266, by rfl⟩ : syracuseStep 1873421 = 702533) (by norm_num)
theorem B1054225 : Blo 830350 1054225 := bbase (se 2 (by rfl) ⟨395334, by rfl⟩ : syracuseStep 1054225 = 790669) (by norm_num)
theorem B1250837 : Blo 830350 1250837 := bbase (se 6 (by rfl) ⟨29316, by rfl⟩ : syracuseStep 1250837 = 58633) (by norm_num)
theorem B1250861 : Blo 830350 1250861 := bbase (se 3 (by rfl) ⟨234536, by rfl⟩ : syracuseStep 1250861 = 469073) (by norm_num)
theorem B1185349 : Blo 830350 1185349 := bbase (se 4 (by rfl) ⟨111126, by rfl⟩ : syracuseStep 1185349 = 222253) (by norm_num)
theorem B1250885 : Blo 830350 1250885 := bbase (se 4 (by rfl) ⟨117270, by rfl⟩ : syracuseStep 1250885 = 234541) (by norm_num)
theorem B2102861 : Blo 830350 2102861 := bbase (se 3 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 2102861 = 788573) (by norm_num)
theorem B2365013 : Blo 830350 2365013 := bbase (se 8 (by rfl) ⟨13857, by rfl⟩ : syracuseStep 2365013 = 27715) (by norm_num)
theorem B1873493 : Blo 830350 1873493 := bbase (se 8 (by rfl) ⟨10977, by rfl⟩ : syracuseStep 1873493 = 21955) (by norm_num)
theorem B1250909 : Blo 830350 1250909 := bbase (se 3 (by rfl) ⟨234545, by rfl⟩ : syracuseStep 1250909 = 469091) (by norm_num)
theorem B1250933 : Blo 830350 1250933 := bbase (se 5 (by rfl) ⟨58637, by rfl⟩ : syracuseStep 1250933 = 117275) (by norm_num)
theorem B1250957 : Blo 830350 1250957 := bbase (se 3 (by rfl) ⟨234554, by rfl⟩ : syracuseStep 1250957 = 469109) (by norm_num)
theorem B1873565 : Blo 830350 1873565 := bbase (se 3 (by rfl) ⟨351293, by rfl⟩ : syracuseStep 1873565 = 702587) (by norm_num)
theorem B1185445 : Blo 830350 1185445 := bbase (se 4 (by rfl) ⟨111135, by rfl⟩ : syracuseStep 1185445 = 222271) (by norm_num)
theorem B1250981 : Blo 830350 1250981 := bbase (se 4 (by rfl) ⟨117279, by rfl⟩ : syracuseStep 1250981 = 234559) (by norm_num)
theorem B1054397 : Blo 830350 1054397 := bbase (se 3 (by rfl) ⟨197699, by rfl⟩ : syracuseStep 1054397 = 395399) (by norm_num)
theorem B1251005 : Blo 830350 1251005 := bbase (se 3 (by rfl) ⟨234563, by rfl⟩ : syracuseStep 1251005 = 469127) (by norm_num)
theorem B1251029 : Blo 830350 1251029 := bbase (se 7 (by rfl) ⟨14660, by rfl⟩ : syracuseStep 1251029 = 29321) (by norm_num)
theorem B1873637 : Blo 830350 1873637 := bbase (se 4 (by rfl) ⟨175653, by rfl⟩ : syracuseStep 1873637 = 351307) (by norm_num)
theorem B890605 : Blo 830350 890605 := bbase (se 3 (by rfl) ⟨166988, by rfl⟩ : syracuseStep 890605 = 333977) (by norm_num)
theorem B1251053 : Blo 830350 1251053 := bbase (se 3 (by rfl) ⟨234572, by rfl⟩ : syracuseStep 1251053 = 469145) (by norm_num)
theorem B1054453 : Blo 830350 1054453 := bbase (se 5 (by rfl) ⟨49427, by rfl⟩ : syracuseStep 1054453 = 98855) (by norm_num)
theorem B1251077 : Blo 830350 1251077 := bbase (se 4 (by rfl) ⟨117288, by rfl⟩ : syracuseStep 1251077 = 234577) (by norm_num)
theorem B1251101 : Blo 830350 1251101 := bbase (se 3 (by rfl) ⟨234581, by rfl⟩ : syracuseStep 1251101 = 469163) (by norm_num)
theorem B1873709 : Blo 830350 1873709 := bbase (se 3 (by rfl) ⟨351320, by rfl⟩ : syracuseStep 1873709 = 702641) (by norm_num)
theorem B1251125 : Blo 830350 1251125 := bbase (se 5 (by rfl) ⟨58646, by rfl⟩ : syracuseStep 1251125 = 117293) (by norm_num)
theorem B1251149 : Blo 830350 1251149 := bbase (se 3 (by rfl) ⟨234590, by rfl⟩ : syracuseStep 1251149 = 469181) (by norm_num)
theorem B1054549 : Blo 830350 1054549 := bbase (se 9 (by rfl) ⟨3089, by rfl⟩ : syracuseStep 1054549 = 6179) (by norm_num)
theorem B1251173 : Blo 830350 1251173 := bbase (se 4 (by rfl) ⟨117297, by rfl⟩ : syracuseStep 1251173 = 234595) (by norm_num)
theorem B1873781 : Blo 830350 1873781 := bbase (se 5 (by rfl) ⟨87833, by rfl⟩ : syracuseStep 1873781 = 175667) (by norm_num)
theorem B1251197 : Blo 830350 1251197 := bbase (se 3 (by rfl) ⟨234599, by rfl⟩ : syracuseStep 1251197 = 469199) (by norm_num)
theorem B1251221 : Blo 830350 1251221 := bbase (se 6 (by rfl) ⟨29325, by rfl⟩ : syracuseStep 1251221 = 58651) (by norm_num)
theorem B2103205 : Blo 830350 2103205 := bbase (se 4 (by rfl) ⟨197175, by rfl⟩ : syracuseStep 2103205 = 394351) (by norm_num)
theorem B1251245 : Blo 830350 1251245 := bbase (se 3 (by rfl) ⟨234608, by rfl⟩ : syracuseStep 1251245 = 469217) (by norm_num)
theorem B1873853 : Blo 830350 1873853 := bbase (se 3 (by rfl) ⟨351347, by rfl⟩ : syracuseStep 1873853 = 702695) (by norm_num)
theorem B1251269 : Blo 830350 1251269 := bbase (se 4 (by rfl) ⟨117306, by rfl⟩ : syracuseStep 1251269 = 234613) (by norm_num)
theorem B1251293 : Blo 830350 1251293 := bbase (se 3 (by rfl) ⟨234617, by rfl⟩ : syracuseStep 1251293 = 469235) (by norm_num)
theorem B1251317 : Blo 830350 1251317 := bbase (se 5 (by rfl) ⟨58655, by rfl⟩ : syracuseStep 1251317 = 117311) (by norm_num)
theorem B1054721 : Blo 830350 1054721 := bbase (se 2 (by rfl) ⟨395520, by rfl⟩ : syracuseStep 1054721 = 791041) (by norm_num)
theorem B1873925 : Blo 830350 1873925 := bbase (se 4 (by rfl) ⟨175680, by rfl⟩ : syracuseStep 1873925 = 351361) (by norm_num)
theorem B1251341 : Blo 830350 1251341 := bbase (se 3 (by rfl) ⟨234626, by rfl⟩ : syracuseStep 1251341 = 469253) (by norm_num)
theorem B2103317 : Blo 830350 2103317 := bbase (se 6 (by rfl) ⟨49296, by rfl⟩ : syracuseStep 2103317 = 98593) (by norm_num)
theorem B1251365 : Blo 830350 1251365 := bbase (se 4 (by rfl) ⟨117315, by rfl⟩ : syracuseStep 1251365 = 234631) (by norm_num)
theorem B1054777 : Blo 830350 1054777 := bbase (se 2 (by rfl) ⟨395541, by rfl⟩ : syracuseStep 1054777 = 791083) (by norm_num)
theorem B1251389 : Blo 830350 1251389 := bbase (se 3 (by rfl) ⟨234635, by rfl⟩ : syracuseStep 1251389 = 469271) (by norm_num)
theorem B1873997 : Blo 830350 1873997 := bbase (se 3 (by rfl) ⟨351374, by rfl⟩ : syracuseStep 1873997 = 702749) (by norm_num)
theorem B1251413 : Blo 830350 1251413 := bbase (se 8 (by rfl) ⟨7332, by rfl⟩ : syracuseStep 1251413 = 14665) (by norm_num)
theorem B1251437 : Blo 830350 1251437 := bbase (se 3 (by rfl) ⟨234644, by rfl⟩ : syracuseStep 1251437 = 469289) (by norm_num)
theorem B1251461 : Blo 830350 1251461 := bbase (se 4 (by rfl) ⟨117324, by rfl⟩ : syracuseStep 1251461 = 234649) (by norm_num)
theorem B1874069 : Blo 830350 1874069 := bbase (se 6 (by rfl) ⟨43923, by rfl⟩ : syracuseStep 1874069 = 87847) (by norm_num)
theorem B1185941 : Blo 830350 1185941 := bbase (se 6 (by rfl) ⟨27795, by rfl⟩ : syracuseStep 1185941 = 55591) (by norm_num)
theorem B1054873 : Blo 830350 1054873 := bbase (se 2 (by rfl) ⟨395577, by rfl⟩ : syracuseStep 1054873 = 791155) (by norm_num)
theorem B1251485 : Blo 830350 1251485 := bbase (se 3 (by rfl) ⟨234653, by rfl⟩ : syracuseStep 1251485 = 469307) (by norm_num)
theorem B1579189 : Blo 830350 1579189 := bbase (se 5 (by rfl) ⟨74024, by rfl⟩ : syracuseStep 1579189 = 148049) (by norm_num)
theorem B1251509 : Blo 830350 1251509 := bbase (se 5 (by rfl) ⟨58664, by rfl⟩ : syracuseStep 1251509 = 117329) (by norm_num)
theorem B2103509 : Blo 830350 2103509 := bbase (se 7 (by rfl) ⟨24650, by rfl⟩ : syracuseStep 2103509 = 49301) (by norm_num)
theorem B1775837 : Blo 830350 1775837 := bbase (se 3 (by rfl) ⟨332969, by rfl⟩ : syracuseStep 1775837 = 665939) (by norm_num)
theorem B1874141 : Blo 830350 1874141 := bbase (se 3 (by rfl) ⟨351401, by rfl⟩ : syracuseStep 1874141 = 702803) (by norm_num)
theorem B1874213 : Blo 830350 1874213 := bbase (se 4 (by rfl) ⟨175707, by rfl⟩ : syracuseStep 1874213 = 351415) (by norm_num)
theorem B1579333 : Blo 830350 1579333 := bbase (se 4 (by rfl) ⟨148062, by rfl⟩ : syracuseStep 1579333 = 296125) (by norm_num)
theorem B1055045 : Blo 830350 1055045 := bbase (se 4 (by rfl) ⟨98910, by rfl⟩ : syracuseStep 1055045 = 197821) (by norm_num)
theorem B1775981 : Blo 830350 1775981 := bbase (se 3 (by rfl) ⟨332996, by rfl⟩ : syracuseStep 1775981 = 665993) (by norm_num)
theorem B1874285 : Blo 830350 1874285 := bbase (se 3 (by rfl) ⟨351428, by rfl⟩ : syracuseStep 1874285 = 702857) (by norm_num)
theorem B1055101 : Blo 830350 1055101 := bbase (se 3 (by rfl) ⟨197831, by rfl⟩ : syracuseStep 1055101 = 395663) (by norm_num)
theorem B1874357 : Blo 830350 1874357 := bbase (se 5 (by rfl) ⟨87860, by rfl⟩ : syracuseStep 1874357 = 175721) (by norm_num)
theorem B1055197 : Blo 830350 1055197 := bbase (se 3 (by rfl) ⟨197849, by rfl⟩ : syracuseStep 1055197 = 395699) (by norm_num)
theorem B1579493 : Blo 830350 1579493 := bbase (se 4 (by rfl) ⟨148077, by rfl⟩ : syracuseStep 1579493 = 296155) (by norm_num)
theorem B1874429 : Blo 830350 1874429 := bbase (se 3 (by rfl) ⟨351455, by rfl⟩ : syracuseStep 1874429 = 702911) (by norm_num)
theorem B2103853 : Blo 830350 2103853 := bbase (se 3 (by rfl) ⟨394472, by rfl⟩ : syracuseStep 2103853 = 788945) (by norm_num)
theorem B1874501 : Blo 830350 1874501 := bbase (se 4 (by rfl) ⟨175734, by rfl⟩ : syracuseStep 1874501 = 351469) (by norm_num)
theorem B1579637 : Blo 830350 1579637 := bbase (se 5 (by rfl) ⟨74045, by rfl⟩ : syracuseStep 1579637 = 148091) (by norm_num)
theorem B1055369 : Blo 830350 1055369 := bbase (se 2 (by rfl) ⟨395763, by rfl⟩ : syracuseStep 1055369 = 791527) (by norm_num)
theorem B1874573 : Blo 830350 1874573 := bbase (se 3 (by rfl) ⟨351482, by rfl⟩ : syracuseStep 1874573 = 702965) (by norm_num)
theorem B2103965 : Blo 830350 2103965 := bbase (se 3 (by rfl) ⟨394493, by rfl⟩ : syracuseStep 2103965 = 788987) (by norm_num)
theorem B1186493 : Blo 830350 1186493 := bbase (se 3 (by rfl) ⟨222467, by rfl⟩ : syracuseStep 1186493 = 444935) (by norm_num)
theorem B1055425 : Blo 830350 1055425 := bbase (se 2 (by rfl) ⟨395784, by rfl⟩ : syracuseStep 1055425 = 791569) (by norm_num)
theorem B1874645 : Blo 830350 1874645 := bbase (se 7 (by rfl) ⟨21968, by rfl⟩ : syracuseStep 1874645 = 43937) (by norm_num)
theorem B1874717 : Blo 830350 1874717 := bbase (se 3 (by rfl) ⟨351509, by rfl⟩ : syracuseStep 1874717 = 703019) (by norm_num)
theorem B1055521 : Blo 830350 1055521 := bbase (se 2 (by rfl) ⟨395820, by rfl⟩ : syracuseStep 1055521 = 791641) (by norm_num)
theorem B2104157 : Blo 830350 2104157 := bbase (se 3 (by rfl) ⟨394529, by rfl⟩ : syracuseStep 2104157 = 789059) (by norm_num)
theorem B1874789 : Blo 830350 1874789 := bbase (se 4 (by rfl) ⟨175761, by rfl⟩ : syracuseStep 1874789 = 351523) (by norm_num)
theorem B3152789 : Blo 830350 3152789 := bbase (se 6 (by rfl) ⟨73893, by rfl⟩ : syracuseStep 3152789 = 147787) (by norm_num)
theorem B1579925 : Blo 830350 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B3382165 : Blo 830350 3382165 := bbase (se 6 (by rfl) ⟨79269, by rfl⟩ : syracuseStep 3382165 = 158539) (by norm_num)
theorem B1874861 : Blo 830350 1874861 := bbase (se 3 (by rfl) ⟨351536, by rfl⟩ : syracuseStep 1874861 = 703073) (by norm_num)
theorem B2562997 : Blo 830350 2562997 := bbase (se 5 (by rfl) ⟨120140, by rfl⟩ : syracuseStep 2562997 = 240281) (by norm_num)
theorem B1055693 : Blo 830350 1055693 := bbase (se 3 (by rfl) ⟨197942, by rfl⟩ : syracuseStep 1055693 = 395885) (by norm_num)
theorem B9608149 : Blo 830350 9608149 := bbase (se 7 (by rfl) ⟨112595, by rfl⟩ : syracuseStep 9608149 = 225191) (by norm_num)
theorem B3382229 : Blo 830350 3382229 := bbase (se 7 (by rfl) ⟨39635, by rfl⟩ : syracuseStep 3382229 = 79271) (by norm_num)
theorem B1874933 : Blo 830350 1874933 := bbase (se 5 (by rfl) ⟨87887, by rfl⟩ : syracuseStep 1874933 = 175775) (by norm_num)
theorem B1055749 : Blo 830350 1055749 := bbase (se 4 (by rfl) ⟨98976, by rfl⟩ : syracuseStep 1055749 = 197953) (by norm_num)
theorem B8526869 : Blo 830350 8526869 := bbase (se 6 (by rfl) ⟨199848, by rfl⟩ : syracuseStep 8526869 = 399697) (by norm_num)
theorem B1580077 : Blo 830350 1580077 := bbase (se 3 (by rfl) ⟨296264, by rfl⟩ : syracuseStep 1580077 = 592529) (by norm_num)
theorem B1875005 : Blo 830350 1875005 := bbase (se 3 (by rfl) ⟨351563, by rfl⟩ : syracuseStep 1875005 = 703127) (by norm_num)
theorem B2661461 : Blo 830350 2661461 := bbase (se 8 (by rfl) ⟨15594, by rfl⟩ : syracuseStep 2661461 = 31189) (by norm_num)
theorem B1776725 : Blo 830350 1776725 := bbase (se 8 (by rfl) ⟨10410, by rfl⟩ : syracuseStep 1776725 = 20821) (by norm_num)
theorem B1055845 : Blo 830350 1055845 := bbase (se 4 (by rfl) ⟨98985, by rfl⟩ : syracuseStep 1055845 = 197971) (by norm_num)
theorem B2366597 : Blo 830350 2366597 := bbase (se 4 (by rfl) ⟨221868, by rfl⟩ : syracuseStep 2366597 = 443737) (by norm_num)
theorem B1875077 : Blo 830350 1875077 := bbase (se 4 (by rfl) ⟨175788, by rfl⟩ : syracuseStep 1875077 = 351577) (by norm_num)
theorem B3153077 : Blo 830350 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B2104501 : Blo 830350 2104501 := bbase (se 5 (by rfl) ⟨98648, by rfl⟩ : syracuseStep 2104501 = 197297) (by norm_num)
theorem B1875149 : Blo 830350 1875149 := bbase (se 3 (by rfl) ⟨351590, by rfl⟩ : syracuseStep 1875149 = 703181) (by norm_num)
theorem B1875221 : Blo 830350 1875221 := bbase (se 6 (by rfl) ⟨43950, by rfl⟩ : syracuseStep 1875221 = 87901) (by norm_num)
theorem B2104613 : Blo 830350 2104613 := bbase (se 4 (by rfl) ⟨197307, by rfl⟩ : syracuseStep 2104613 = 394615) (by norm_num)
theorem B1580381 : Blo 830350 1580381 := bbase (se 3 (by rfl) ⟨296321, by rfl⟩ : syracuseStep 1580381 = 592643) (by norm_num)
theorem B1875293 : Blo 830350 1875293 := bbase (se 3 (by rfl) ⟨351617, by rfl⟩ : syracuseStep 1875293 = 703235) (by norm_num)
theorem B1351037 : Blo 830350 1351037 := bbase (se 3 (by rfl) ⟨253319, by rfl⟩ : syracuseStep 1351037 = 506639) (by norm_num)
theorem B1875365 : Blo 830350 1875365 := bbase (se 4 (by rfl) ⟨175815, by rfl⟩ : syracuseStep 1875365 = 351631) (by norm_num)
theorem B1187245 : Blo 830350 1187245 := bbase (se 3 (by rfl) ⟨222608, by rfl⟩ : syracuseStep 1187245 = 445217) (by norm_num)
theorem B2104805 : Blo 830350 2104805 := bbase (se 4 (by rfl) ⟨197325, by rfl⟩ : syracuseStep 2104805 = 394651) (by norm_num)
theorem B1875437 : Blo 830350 1875437 := bbase (se 3 (by rfl) ⟨351644, by rfl⟩ : syracuseStep 1875437 = 703289) (by norm_num)
theorem B1875509 : Blo 830350 1875509 := bbase (se 5 (by rfl) ⟨87914, by rfl⟩ : syracuseStep 1875509 = 175829) (by norm_num)
theorem B1875581 : Blo 830350 1875581 := bbase (se 3 (by rfl) ⟨351671, by rfl⟩ : syracuseStep 1875581 = 703343) (by norm_num)
theorem B1875653 : Blo 830350 1875653 := bbase (se 4 (by rfl) ⟨175842, by rfl⟩ : syracuseStep 1875653 = 351685) (by norm_num)
theorem B7118549 : Blo 830350 7118549 := bbase (se 7 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 7118549 = 166841) (by norm_num)
theorem B1875725 : Blo 830350 1875725 := bbase (se 3 (by rfl) ⟨351698, by rfl⟩ : syracuseStep 1875725 = 703397) (by norm_num)
theorem B2367269 : Blo 830350 2367269 := bbase (se 4 (by rfl) ⟨221931, by rfl⟩ : syracuseStep 2367269 = 443863) (by norm_num)
theorem B4267829 : Blo 830350 4267829 := bbase (se 5 (by rfl) ⟨200054, by rfl⟩ : syracuseStep 4267829 = 400109) (by norm_num)
theorem B2105149 : Blo 830350 2105149 := bbase (se 3 (by rfl) ⟨394715, by rfl⟩ : syracuseStep 2105149 = 789431) (by norm_num)
theorem B1777477 : Blo 830350 1777477 := bbase (se 4 (by rfl) ⟨166638, by rfl⟩ : syracuseStep 1777477 = 333277) (by norm_num)
theorem B2662229 : Blo 830350 2662229 := bbase (se 9 (by rfl) ⟨7799, by rfl⟩ : syracuseStep 2662229 = 15599) (by norm_num)
theorem B1875797 : Blo 830350 1875797 := bbase (se 9 (by rfl) ⟨5495, by rfl⟩ : syracuseStep 1875797 = 10991) (by norm_num)
theorem B1875869 : Blo 830350 1875869 := bbase (se 3 (by rfl) ⟨351725, by rfl⟩ : syracuseStep 1875869 = 703451) (by norm_num)
theorem B2105261 : Blo 830350 2105261 := bbase (se 3 (by rfl) ⟨394736, by rfl⟩ : syracuseStep 2105261 = 789473) (by norm_num)
theorem B1777621 : Blo 830350 1777621 := bbase (se 7 (by rfl) ⟨20831, by rfl⟩ : syracuseStep 1777621 = 41663) (by norm_num)
theorem B1875941 : Blo 830350 1875941 := bbase (se 4 (by rfl) ⟨175869, by rfl⟩ : syracuseStep 1875941 = 351739) (by norm_num)
theorem B1876013 : Blo 830350 1876013 := bbase (se 3 (by rfl) ⟨351752, by rfl⟩ : syracuseStep 1876013 = 703505) (by norm_num)
theorem B1581133 : Blo 830350 1581133 := bbase (se 3 (by rfl) ⟨296462, by rfl⟩ : syracuseStep 1581133 = 592925) (by norm_num)
theorem B2105453 : Blo 830350 2105453 := bbase (se 3 (by rfl) ⟨394772, by rfl⟩ : syracuseStep 2105453 = 789545) (by norm_num)
theorem B1876085 : Blo 830350 1876085 := bbase (se 5 (by rfl) ⟨87941, by rfl⟩ : syracuseStep 1876085 = 175883) (by norm_num)
theorem B1876157 : Blo 830350 1876157 := bbase (se 3 (by rfl) ⟨351779, by rfl⟩ : syracuseStep 1876157 = 703559) (by norm_num)
theorem B2138309 : Blo 830350 2138309 := bbase (se 4 (by rfl) ⟨200466, by rfl⟩ : syracuseStep 2138309 = 400933) (by norm_num)
theorem B2367701 : Blo 830350 2367701 := bbase (se 7 (by rfl) ⟨27746, by rfl⟩ : syracuseStep 2367701 = 55493) (by norm_num)
theorem B1581277 : Blo 830350 1581277 := bbase (se 3 (by rfl) ⟨296489, by rfl⟩ : syracuseStep 1581277 = 592979) (by norm_num)
theorem B1876229 : Blo 830350 1876229 := bbase (se 4 (by rfl) ⟨175896, by rfl⟩ : syracuseStep 1876229 = 351793) (by norm_num)
theorem B1777997 : Blo 830350 1777997 := bbase (se 3 (by rfl) ⟨333374, by rfl⟩ : syracuseStep 1777997 = 666749) (by norm_num)
theorem B1876301 : Blo 830350 1876301 := bbase (se 3 (by rfl) ⟨351806, by rfl⟩ : syracuseStep 1876301 = 703613) (by norm_num)
theorem B3154261 : Blo 830350 3154261 := bbase (se 10 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 3154261 = 9241) (by norm_num)
theorem B2662741 : Blo 830350 2662741 := bbase (se 10 (by rfl) ⟨3900, by rfl⟩ : syracuseStep 2662741 = 7801) (by norm_num)
theorem B12165461 : Blo 830350 12165461 := bbase (se 10 (by rfl) ⟨17820, by rfl⟩ : syracuseStep 12165461 = 35641) (by norm_num)
theorem B1581437 : Blo 830350 1581437 := bbase (se 3 (by rfl) ⟨296519, by rfl⟩ : syracuseStep 1581437 = 593039) (by norm_num)
theorem B1876373 : Blo 830350 1876373 := bbase (se 6 (by rfl) ⟨43977, by rfl⟩ : syracuseStep 1876373 = 87955) (by norm_num)
theorem B2105797 : Blo 830350 2105797 := bbase (se 4 (by rfl) ⟨197418, by rfl⟩ : syracuseStep 2105797 = 394837) (by norm_num)
theorem B1876445 : Blo 830350 1876445 := bbase (se 3 (by rfl) ⟨351833, by rfl⟩ : syracuseStep 1876445 = 703667) (by norm_num)
theorem B1581581 : Blo 830350 1581581 := bbase (se 3 (by rfl) ⟨296546, by rfl⟩ : syracuseStep 1581581 = 593093) (by norm_num)
theorem B1876517 : Blo 830350 1876517 := bbase (se 4 (by rfl) ⟨175923, by rfl⟩ : syracuseStep 1876517 = 351847) (by norm_num)
theorem B2105909 : Blo 830350 2105909 := bbase (se 5 (by rfl) ⟨98714, by rfl⟩ : syracuseStep 2105909 = 197429) (by norm_num)
theorem B2531893 : Blo 830350 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B1876589 : Blo 830350 1876589 := bbase (se 3 (by rfl) ⟨351860, by rfl⟩ : syracuseStep 1876589 = 703721) (by norm_num)
theorem B3154565 : Blo 830350 3154565 := bbase (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) (by norm_num)
theorem B1876661 : Blo 830350 1876661 := bbase (se 5 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 1876661 = 175937) (by norm_num)
theorem B1778365 : Blo 830350 1778365 := bbase (se 3 (by rfl) ⟨333443, by rfl⟩ : syracuseStep 1778365 = 666887) (by norm_num)
theorem B1123021 : Blo 830350 1123021 := bbase (se 3 (by rfl) ⟨210566, by rfl⟩ : syracuseStep 1123021 = 421133) (by norm_num)
theorem B2106101 : Blo 830350 2106101 := bbase (se 5 (by rfl) ⟨98723, by rfl⟩ : syracuseStep 2106101 = 197447) (by norm_num)
theorem B1876733 : Blo 830350 1876733 := bbase (se 3 (by rfl) ⟨351887, by rfl⟩ : syracuseStep 1876733 = 703775) (by norm_num)
theorem B1581869 : Blo 830350 1581869 := bbase (se 3 (by rfl) ⟨296600, by rfl⟩ : syracuseStep 1581869 = 593201) (by norm_num)
theorem B1876805 : Blo 830350 1876805 := bbase (se 4 (by rfl) ⟨175950, by rfl⟩ : syracuseStep 1876805 = 351901) (by norm_num)
theorem B2532197 : Blo 830350 2532197 := bbase (se 4 (by rfl) ⟨237393, by rfl⟩ : syracuseStep 2532197 = 474787) (by norm_num)
theorem B2597765 : Blo 830350 2597765 := bbase (se 4 (by rfl) ⟨243540, by rfl⟩ : syracuseStep 2597765 = 487081) (by norm_num)
theorem B1876877 : Blo 830350 1876877 := bbase (se 3 (by rfl) ⟨351914, by rfl⟩ : syracuseStep 1876877 = 703829) (by norm_num)
theorem B1123237 : Blo 830350 1123237 := bbase (se 4 (by rfl) ⟨105303, by rfl⟩ : syracuseStep 1123237 = 210607) (by norm_num)
theorem B2368453 : Blo 830350 2368453 := bbase (se 4 (by rfl) ⟨222042, by rfl⟩ : syracuseStep 2368453 = 444085) (by norm_num)
theorem B1582021 : Blo 830350 1582021 := bbase (se 4 (by rfl) ⟨148314, by rfl⟩ : syracuseStep 1582021 = 296629) (by norm_num)
theorem B1876949 : Blo 830350 1876949 := bbase (se 7 (by rfl) ⟨21995, by rfl⟩ : syracuseStep 1876949 = 43991) (by norm_num)
theorem B1123301 : Blo 830350 1123301 := bbase (se 4 (by rfl) ⟨105309, by rfl⟩ : syracuseStep 1123301 = 210619) (by norm_num)
theorem B1877021 : Blo 830350 1877021 := bbase (se 3 (by rfl) ⟨351941, by rfl⟩ : syracuseStep 1877021 = 703883) (by norm_num)
theorem B1713221 : Blo 830350 1713221 := bbase (se 4 (by rfl) ⟨160614, by rfl⟩ : syracuseStep 1713221 = 321229) (by norm_num)
theorem B2106445 : Blo 830350 2106445 := bbase (se 3 (by rfl) ⟨394958, by rfl⟩ : syracuseStep 2106445 = 789917) (by norm_num)
theorem B1877093 : Blo 830350 1877093 := bbase (se 4 (by rfl) ⟨175977, by rfl⟩ : syracuseStep 1877093 = 351955) (by norm_num)
theorem B4007029 : Blo 830350 4007029 := bbase (se 5 (by rfl) ⟨187829, by rfl⟩ : syracuseStep 4007029 = 375659) (by norm_num)
theorem B13477013 : Blo 830350 13477013 := bbase (se 6 (by rfl) ⟨315867, by rfl⟩ : syracuseStep 13477013 = 631735) (by norm_num)
theorem B1877165 : Blo 830350 1877165 := bbase (se 3 (by rfl) ⟨351968, by rfl⟩ : syracuseStep 1877165 = 703937) (by norm_num)
theorem B2106557 : Blo 830350 2106557 := bbase (se 3 (by rfl) ⟨394979, by rfl⟩ : syracuseStep 2106557 = 789959) (by norm_num)
theorem B1582325 : Blo 830350 1582325 := bbase (se 5 (by rfl) ⟨74171, by rfl⟩ : syracuseStep 1582325 = 148343) (by norm_num)
theorem B1877237 : Blo 830350 1877237 := bbase (se 5 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 1877237 = 175991) (by norm_num)
theorem B2106749 : Blo 830350 2106749 := bbase (se 3 (by rfl) ⟨395015, by rfl⟩ : syracuseStep 2106749 = 790031) (by norm_num)
theorem B959941 : Blo 830350 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B1713613 : Blo 830350 1713613 := bbase (se 3 (by rfl) ⟨321302, by rfl⟩ : syracuseStep 1713613 = 642605) (by norm_num)
theorem B6334037 : Blo 830350 6334037 := bbase (se 8 (by rfl) ⟨37113, by rfl⟩ : syracuseStep 6334037 = 74227) (by norm_num)
theorem B2107093 : Blo 830350 2107093 := bbase (se 7 (by rfl) ⟨24692, by rfl⟩ : syracuseStep 2107093 = 49385) (by norm_num)
theorem B960217 : Blo 830350 960217 := bbase (se 2 (by rfl) ⟨360081, by rfl⟩ : syracuseStep 960217 = 720163) (by norm_num)
theorem B1124101 : Blo 830350 1124101 := bbase (se 4 (by rfl) ⟨105384, by rfl⟩ : syracuseStep 1124101 = 210769) (by norm_num)
theorem B2139949 : Blo 830350 2139949 := bbase (se 3 (by rfl) ⟨401240, by rfl⟩ : syracuseStep 2139949 = 802481) (by norm_num)
theorem B2107205 : Blo 830350 2107205 := bbase (se 4 (by rfl) ⟨197550, by rfl⟩ : syracuseStep 2107205 = 395101) (by norm_num)
theorem B1124221 : Blo 830350 1124221 := bbase (se 3 (by rfl) ⟨210791, by rfl⟩ : syracuseStep 1124221 = 421583) (by norm_num)
theorem B1583077 : Blo 830350 1583077 := bbase (se 4 (by rfl) ⟨148413, by rfl⟩ : syracuseStep 1583077 = 296827) (by norm_num)
theorem B2107397 : Blo 830350 2107397 := bbase (se 4 (by rfl) ⟨197568, by rfl⟩ : syracuseStep 2107397 = 395137) (by norm_num)
theorem B2664485 : Blo 830350 2664485 := bbase (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) (by norm_num)
theorem B13674581 : Blo 830350 13674581 := bbase (se 8 (by rfl) ⟨80124, by rfl⟩ : syracuseStep 13674581 = 160249) (by norm_num)
theorem B1124437 : Blo 830350 1124437 := bbase (se 8 (by rfl) ⟨6588, by rfl⟩ : syracuseStep 1124437 = 13177) (by norm_num)
theorem B1583221 : Blo 830350 1583221 := bbase (se 5 (by rfl) ⟨74213, by rfl⟩ : syracuseStep 1583221 = 148427) (by norm_num)
theorem B1779869 : Blo 830350 1779869 := bbase (se 3 (by rfl) ⟨333725, by rfl⟩ : syracuseStep 1779869 = 667451) (by norm_num)
theorem B4204709 : Blo 830350 4204709 := bbase (se 4 (by rfl) ⟨394191, by rfl⟩ : syracuseStep 4204709 = 788383) (by norm_num)
theorem B3549365 : Blo 830350 3549365 := bbase (se 5 (by rfl) ⟨166376, by rfl⟩ : syracuseStep 3549365 = 332753) (by norm_num)
theorem B2664677 : Blo 830350 2664677 := bbase (se 4 (by rfl) ⟨249813, by rfl⟩ : syracuseStep 2664677 = 499627) (by norm_num)
theorem B1583381 : Blo 830350 1583381 := bbase (se 6 (by rfl) ⟨37110, by rfl⟩ : syracuseStep 1583381 = 74221) (by norm_num)
theorem B1780013 : Blo 830350 1780013 := bbase (se 3 (by rfl) ⟨333752, by rfl⟩ : syracuseStep 1780013 = 667505) (by norm_num)
theorem B2107741 : Blo 830350 2107741 := bbase (se 3 (by rfl) ⟨395201, by rfl⟩ : syracuseStep 2107741 = 790403) (by norm_num)
theorem B4729205 : Blo 830350 4729205 := bbase (se 5 (by rfl) ⟨221681, by rfl⟩ : syracuseStep 4729205 = 443363) (by norm_num)
theorem B1583525 : Blo 830350 1583525 := bbase (se 4 (by rfl) ⟨148455, by rfl⟩ : syracuseStep 1583525 = 296911) (by norm_num)
theorem B2107853 : Blo 830350 2107853 := bbase (se 3 (by rfl) ⟨395222, by rfl⟩ : syracuseStep 2107853 = 790445) (by norm_num)
theorem B2108045 : Blo 830350 2108045 := bbase (se 3 (by rfl) ⟨395258, by rfl⟩ : syracuseStep 2108045 = 790517) (by norm_num)
theorem B1780373 : Blo 830350 1780373 := bbase (se 6 (by rfl) ⟨41727, by rfl⟩ : syracuseStep 1780373 = 83455) (by norm_num)
theorem B3156677 : Blo 830350 3156677 := bbase (se 4 (by rfl) ⟨295938, by rfl⟩ : syracuseStep 3156677 = 591877) (by norm_num)
theorem B1583813 : Blo 830350 1583813 := bbase (se 4 (by rfl) ⟨148482, by rfl⟩ : syracuseStep 1583813 = 296965) (by norm_num)
theorem B3156965 : Blo 830350 3156965 := bbase (se 4 (by rfl) ⟨295965, by rfl⟩ : syracuseStep 3156965 = 591931) (by norm_num)
theorem B2108389 : Blo 830350 2108389 := bbase (se 4 (by rfl) ⟨197661, by rfl⟩ : syracuseStep 2108389 = 395323) (by norm_num)
theorem B2108501 : Blo 830350 2108501 := bbase (se 8 (by rfl) ⟨12354, by rfl⟩ : syracuseStep 2108501 = 24709) (by norm_num)
theorem B2993381 : Blo 830350 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B2108693 : Blo 830350 2108693 := bbase (se 6 (by rfl) ⟨49422, by rfl⟩ : syracuseStep 2108693 = 98845) (by norm_num)
theorem B961897 : Blo 830350 961897 := bbase (se 2 (by rfl) ⟨360711, by rfl⟩ : syracuseStep 961897 = 721423) (by norm_num)
theorem B4206005 : Blo 830350 4206005 := bbase (se 5 (by rfl) ⟨197156, by rfl⟩ : syracuseStep 4206005 = 394313) (by norm_num)
theorem B1781261 : Blo 830350 1781261 := bbase (se 3 (by rfl) ⟨333986, by rfl⟩ : syracuseStep 1781261 = 667973) (by norm_num)
theorem B2109037 : Blo 830350 2109037 := bbase (se 3 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 2109037 = 790889) (by norm_num)
theorem B2109149 : Blo 830350 2109149 := bbase (se 3 (by rfl) ⟨395465, by rfl⟩ : syracuseStep 2109149 = 790931) (by norm_num)
theorem B2371301 : Blo 830350 2371301 := bbase (se 4 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 2371301 = 444619) (by norm_num)
theorem B1781509 : Blo 830350 1781509 := bbase (se 4 (by rfl) ⟨167016, by rfl⟩ : syracuseStep 1781509 = 334033) (by norm_num)
theorem B1421077 : Blo 830350 1421077 := bbase (se 6 (by rfl) ⟨33306, by rfl⟩ : syracuseStep 1421077 = 66613) (by norm_num)
theorem B2109341 : Blo 830350 2109341 := bbase (se 3 (by rfl) ⟨395501, by rfl⟩ : syracuseStep 2109341 = 791003) (by norm_num)
theorem B3551141 : Blo 830350 3551141 := bbase (se 4 (by rfl) ⟨332919, by rfl⟩ : syracuseStep 3551141 = 665839) (by norm_num)
theorem B1683413 : Blo 830350 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B3158149 : Blo 830350 3158149 := bbase (se 4 (by rfl) ⟨296076, by rfl⟩ : syracuseStep 3158149 = 592153) (by norm_num)
theorem B2109685 : Blo 830350 2109685 := bbase (se 5 (by rfl) ⟨98891, by rfl⟩ : syracuseStep 2109685 = 197783) (by norm_num)
theorem B2109797 : Blo 830350 2109797 := bbase (se 4 (by rfl) ⟨197793, by rfl⟩ : syracuseStep 2109797 = 395587) (by norm_num)
theorem B3158453 : Blo 830350 3158453 := bbase (se 5 (by rfl) ⟨148052, by rfl⟩ : syracuseStep 3158453 = 296105) (by norm_num)
theorem B2994661 : Blo 830350 2994661 := bbase (se 4 (by rfl) ⟨280749, by rfl⟩ : syracuseStep 2994661 = 561499) (by norm_num)
theorem B2109989 : Blo 830350 2109989 := bbase (se 4 (by rfl) ⟨197811, by rfl⟩ : syracuseStep 2109989 = 395623) (by norm_num)
theorem B1684061 : Blo 830350 1684061 := bbase (se 3 (by rfl) ⟨315761, by rfl⟩ : syracuseStep 1684061 = 631523) (by norm_num)
theorem B4207301 : Blo 830350 4207301 := bbase (se 4 (by rfl) ⟨394434, by rfl⟩ : syracuseStep 4207301 = 788869) (by norm_num)
theorem B3420917 : Blo 830350 3420917 := bbase (se 5 (by rfl) ⟨160355, by rfl⟩ : syracuseStep 3420917 = 320711) (by norm_num)
theorem B2110333 : Blo 830350 2110333 := bbase (se 3 (by rfl) ⟨395687, by rfl⟩ : syracuseStep 2110333 = 791375) (by norm_num)
theorem B3552133 : Blo 830350 3552133 := bbase (se 4 (by rfl) ⟨333012, by rfl⟩ : syracuseStep 3552133 = 666025) (by norm_num)
theorem B2372485 : Blo 830350 2372485 := bbase (se 4 (by rfl) ⟨222420, by rfl⟩ : syracuseStep 2372485 = 444841) (by norm_num)
theorem B2110445 : Blo 830350 2110445 := bbase (se 3 (by rfl) ⟨395708, by rfl⟩ : syracuseStep 2110445 = 791417) (by norm_num)
theorem B2372645 : Blo 830350 2372645 := bbase (se 4 (by rfl) ⟨222435, by rfl⟩ : syracuseStep 2372645 = 444871) (by norm_num)
theorem B1520741 : Blo 830350 1520741 := bbase (se 4 (by rfl) ⟨142569, by rfl⟩ : syracuseStep 1520741 = 285139) (by norm_num)
theorem B2110637 : Blo 830350 2110637 := bbase (se 3 (by rfl) ⟨395744, by rfl⟩ : syracuseStep 2110637 = 791489) (by norm_num)
theorem B1684685 : Blo 830350 1684685 := bbase (se 3 (by rfl) ⟨315878, by rfl⟩ : syracuseStep 1684685 = 631757) (by norm_num)
theorem B2372885 : Blo 830350 2372885 := bbase (se 6 (by rfl) ⟨55614, by rfl⟩ : syracuseStep 2372885 = 111229) (by norm_num)
theorem B2373077 : Blo 830350 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B2110981 : Blo 830350 2110981 := bbase (se 4 (by rfl) ⟨197904, by rfl⟩ : syracuseStep 2110981 = 395809) (by norm_num)
theorem B2111093 : Blo 830350 2111093 := bbase (se 5 (by rfl) ⟨98957, by rfl⟩ : syracuseStep 2111093 = 197915) (by norm_num)
theorem B2668277 : Blo 830350 2668277 := bbase (se 5 (by rfl) ⟨125075, by rfl⟩ : syracuseStep 2668277 = 250151) (by norm_num)
theorem B2111285 : Blo 830350 2111285 := bbase (se 5 (by rfl) ⟨98966, by rfl⟩ : syracuseStep 2111285 = 197933) (by norm_num)
theorem B2996149 : Blo 830350 2996149 := bbase (se 5 (by rfl) ⟨140444, by rfl⟩ : syracuseStep 2996149 = 280889) (by norm_num)
theorem B4208597 : Blo 830350 4208597 := bbase (se 7 (by rfl) ⟨49319, by rfl⟩ : syracuseStep 4208597 = 98639) (by norm_num)
theorem B2111629 : Blo 830350 2111629 := bbase (se 3 (by rfl) ⟨395930, by rfl⟩ : syracuseStep 2111629 = 791861) (by norm_num)
theorem B2111741 : Blo 830350 2111741 := bbase (se 3 (by rfl) ⟨395951, by rfl⟩ : syracuseStep 2111741 = 791903) (by norm_num)
theorem B2374069 : Blo 830350 2374069 := bbase (se 5 (by rfl) ⟨111284, by rfl⟩ : syracuseStep 2374069 = 222569) (by norm_num)
theorem B997817 : Blo 830350 997817 := bbase (se 2 (by rfl) ⟨374181, by rfl⟩ : syracuseStep 997817 = 748363) (by norm_num)
theorem B2111933 : Blo 830350 2111933 := bbase (se 3 (by rfl) ⟨395987, by rfl⟩ : syracuseStep 2111933 = 791975) (by norm_num)
theorem B1423813 : Blo 830350 1423813 := bbase (se 4 (by rfl) ⟨133482, by rfl⟩ : syracuseStep 1423813 = 266965) (by norm_num)
theorem B3160565 : Blo 830350 3160565 := bbase (se 5 (by rfl) ⟨148151, by rfl⟩ : syracuseStep 3160565 = 296303) (by norm_num)
theorem B997913 : Blo 830350 997913 := bbase (se 2 (by rfl) ⟨374217, by rfl⟩ : syracuseStep 997913 = 748435) (by norm_num)
theorem B997933 : Blo 830350 997933 := bbase (se 3 (by rfl) ⟨187112, by rfl⟩ : syracuseStep 997933 = 374225) (by norm_num)
theorem B998077 : Blo 830350 998077 := bbase (se 3 (by rfl) ⟨187139, by rfl⟩ : syracuseStep 998077 = 374279) (by norm_num)
theorem B3160853 : Blo 830350 3160853 := bbase (se 6 (by rfl) ⟨74082, by rfl⟩ : syracuseStep 3160853 = 148165) (by norm_num)
theorem B5323637 : Blo 830350 5323637 := bbase (se 5 (by rfl) ⟨249545, by rfl⟩ : syracuseStep 5323637 = 499091) (by norm_num)
theorem B867305 : Blo 830350 867305 := bbase (se 2 (by rfl) ⟨325239, by rfl⟩ : syracuseStep 867305 = 650479) (by norm_num)
theorem B1686509 : Blo 830350 1686509 := bbase (se 3 (by rfl) ⟨316220, by rfl⟩ : syracuseStep 1686509 = 632441) (by norm_num)
theorem B4209893 : Blo 830350 4209893 := bbase (se 4 (by rfl) ⟨394677, by rfl⟩ : syracuseStep 4209893 = 789355) (by norm_num)
theorem B2571605 : Blo 830350 2571605 := bbase (se 11 (by rfl) ⟨1883, by rfl⟩ : syracuseStep 2571605 = 3767) (by norm_num)
theorem B2375173 : Blo 830350 2375173 := bbase (se 4 (by rfl) ⟨222672, by rfl⟩ : syracuseStep 2375173 = 445345) (by norm_num)
theorem B7126613 : Blo 830350 7126613 := bbase (se 8 (by rfl) ⟨41757, by rfl⟩ : syracuseStep 7126613 = 83515) (by norm_num)
theorem B1425181 : Blo 830350 1425181 := bbase (se 3 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 1425181 = 534443) (by norm_num)
theorem B2408309 : Blo 830350 2408309 := bbase (se 5 (by rfl) ⟨112889, by rfl⟩ : syracuseStep 2408309 = 225779) (by norm_num)
theorem B3162037 : Blo 830350 3162037 := bbase (se 5 (by rfl) ⟨148220, by rfl⟩ : syracuseStep 3162037 = 296441) (by norm_num)
theorem B2670533 : Blo 830350 2670533 := bbase (se 4 (by rfl) ⟨250362, by rfl⟩ : syracuseStep 2670533 = 500725) (by norm_num)
theorem B2670661 : Blo 830350 2670661 := bbase (se 4 (by rfl) ⟨250374, by rfl⟩ : syracuseStep 2670661 = 500749) (by norm_num)
theorem B3162341 : Blo 830350 3162341 := bbase (se 4 (by rfl) ⟨296469, by rfl⟩ : syracuseStep 3162341 = 592939) (by norm_num)
theorem B934177 : Blo 830350 934177 := bbase (se 2 (by rfl) ⟨350316, by rfl⟩ : syracuseStep 934177 = 700633) (by norm_num)
theorem B934213 : Blo 830350 934213 := bbase (se 4 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 934213 = 175165) (by norm_num)
theorem B934249 : Blo 830350 934249 := bbase (se 2 (by rfl) ⟨350343, by rfl⟩ : syracuseStep 934249 = 700687) (by norm_num)
theorem B934285 : Blo 830350 934285 := bbase (se 3 (by rfl) ⟨175178, by rfl⟩ : syracuseStep 934285 = 350357) (by norm_num)
theorem B934321 : Blo 830350 934321 := bbase (se 2 (by rfl) ⟨350370, by rfl⟩ : syracuseStep 934321 = 700741) (by norm_num)
theorem B999869 : Blo 830350 999869 := bbase (se 3 (by rfl) ⟨187475, by rfl⟩ : syracuseStep 999869 = 374951) (by norm_num)
theorem B934357 : Blo 830350 934357 := bbase (se 7 (by rfl) ⟨10949, by rfl⟩ : syracuseStep 934357 = 21899) (by norm_num)
theorem B2998757 : Blo 830350 2998757 := bbase (se 4 (by rfl) ⟨281133, by rfl⟩ : syracuseStep 2998757 = 562267) (by norm_num)
theorem B4211189 : Blo 830350 4211189 := bbase (se 5 (by rfl) ⟨197399, by rfl⟩ : syracuseStep 4211189 = 394799) (by norm_num)
theorem B934393 : Blo 830350 934393 := bbase (se 2 (by rfl) ⟨350397, by rfl⟩ : syracuseStep 934393 = 700795) (by norm_num)
theorem B901649 : Blo 830350 901649 := bbase (se 2 (by rfl) ⟨338118, by rfl⟩ : syracuseStep 901649 = 676237) (by norm_num)
theorem B934429 : Blo 830350 934429 := bbase (se 3 (by rfl) ⟨175205, by rfl⟩ : syracuseStep 934429 = 350411) (by norm_num)
theorem B934465 : Blo 830350 934465 := bbase (se 2 (by rfl) ⟨350424, by rfl⟩ : syracuseStep 934465 = 700849) (by norm_num)
theorem B934501 : Blo 830350 934501 := bbase (se 4 (by rfl) ⟨87609, by rfl⟩ : syracuseStep 934501 = 175219) (by norm_num)
theorem B1688197 : Blo 830350 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B934537 : Blo 830350 934537 := bbase (se 2 (by rfl) ⟨350451, by rfl⟩ : syracuseStep 934537 = 700903) (by norm_num)
theorem B4276901 : Blo 830350 4276901 := bbase (se 4 (by rfl) ⟨400959, by rfl⟩ : syracuseStep 4276901 = 801919) (by norm_num)
theorem B934573 : Blo 830350 934573 := bbase (se 3 (by rfl) ⟨175232, by rfl⟩ : syracuseStep 934573 = 350465) (by norm_num)
theorem B934609 : Blo 830350 934609 := bbase (se 2 (by rfl) ⟨350478, by rfl⟩ : syracuseStep 934609 = 700957) (by norm_num)
theorem B934645 : Blo 830350 934645 := bbase (se 5 (by rfl) ⟨43811, by rfl⟩ : syracuseStep 934645 = 87623) (by norm_num)
theorem B2802437 : Blo 830350 2802437 := bbase (se 4 (by rfl) ⟨262728, by rfl⟩ : syracuseStep 2802437 = 525457) (by norm_num)
theorem B1000201 : Blo 830350 1000201 := bbase (se 2 (by rfl) ⟨375075, by rfl⟩ : syracuseStep 1000201 = 750151) (by norm_num)
theorem B934681 : Blo 830350 934681 := bbase (se 2 (by rfl) ⟨350505, by rfl⟩ : syracuseStep 934681 = 701011) (by norm_num)
theorem B1065761 : Blo 830350 1065761 := bbase (se 2 (by rfl) ⟨399660, by rfl⟩ : syracuseStep 1065761 = 799321) (by norm_num)
theorem B934717 : Blo 830350 934717 := bbase (se 3 (by rfl) ⟨175259, by rfl⟩ : syracuseStep 934717 = 350519) (by norm_num)
theorem B934753 : Blo 830350 934753 := bbase (se 2 (by rfl) ⟨350532, by rfl⟩ : syracuseStep 934753 = 701065) (by norm_num)
theorem B2245477 : Blo 830350 2245477 := bbase (se 4 (by rfl) ⟨210513, by rfl⟩ : syracuseStep 2245477 = 421027) (by norm_num)
theorem B934789 : Blo 830350 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B1000345 : Blo 830350 1000345 := bbase (se 2 (by rfl) ⟨375129, by rfl⟩ : syracuseStep 1000345 = 750259) (by norm_num)
theorem B934825 : Blo 830350 934825 := bbase (se 2 (by rfl) ⟨350559, by rfl⟩ : syracuseStep 934825 = 701119) (by norm_num)
theorem B934861 : Blo 830350 934861 := bbase (se 3 (by rfl) ⟨175286, by rfl⟩ : syracuseStep 934861 = 350573) (by norm_num)
theorem B934897 : Blo 830350 934897 := bbase (se 2 (by rfl) ⟨350586, by rfl⟩ : syracuseStep 934897 = 701173) (by norm_num)
theorem B934933 : Blo 830350 934933 := bbase (se 6 (by rfl) ⟨21912, by rfl⟩ : syracuseStep 934933 = 43825) (by norm_num)
theorem B934969 : Blo 830350 934969 := bbase (se 2 (by rfl) ⟨350613, by rfl⟩ : syracuseStep 934969 = 701227) (by norm_num)
theorem B935005 : Blo 830350 935005 := bbase (se 3 (by rfl) ⟨175313, by rfl⟩ : syracuseStep 935005 = 350627) (by norm_num)
theorem B935041 : Blo 830350 935041 := bbase (se 2 (by rfl) ⟨350640, by rfl⟩ : syracuseStep 935041 = 701281) (by norm_num)
theorem B935077 : Blo 830350 935077 := bbase (se 4 (by rfl) ⟨87663, by rfl⟩ : syracuseStep 935077 = 175327) (by norm_num)
theorem B2802869 : Blo 830350 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B935113 : Blo 830350 935113 := bbase (se 2 (by rfl) ⟨350667, by rfl⟩ : syracuseStep 935113 = 701335) (by norm_num)
theorem B1066217 : Blo 830350 1066217 := bbase (se 2 (by rfl) ⟨399831, by rfl⟩ : syracuseStep 1066217 = 799663) (by norm_num)
theorem B935149 : Blo 830350 935149 := bbase (se 3 (by rfl) ⟨175340, by rfl⟩ : syracuseStep 935149 = 350681) (by norm_num)
theorem B1688845 : Blo 830350 1688845 := bbase (se 3 (by rfl) ⟨316658, by rfl⟩ : syracuseStep 1688845 = 633317) (by norm_num)
theorem B935185 : Blo 830350 935185 := bbase (se 2 (by rfl) ⟨350694, by rfl⟩ : syracuseStep 935185 = 701389) (by norm_num)
theorem B935221 : Blo 830350 935221 := bbase (se 5 (by rfl) ⟨43838, by rfl⟩ : syracuseStep 935221 = 87677) (by norm_num)
theorem B1066321 : Blo 830350 1066321 := bbase (se 2 (by rfl) ⟨399870, by rfl⟩ : syracuseStep 1066321 = 799741) (by norm_num)
theorem B935257 : Blo 830350 935257 := bbase (se 2 (by rfl) ⟨350721, by rfl⟩ : syracuseStep 935257 = 701443) (by norm_num)
theorem B935293 : Blo 830350 935293 := bbase (se 3 (by rfl) ⟨175367, by rfl⟩ : syracuseStep 935293 = 350735) (by norm_num)
theorem B935329 : Blo 830350 935329 := bbase (se 2 (by rfl) ⟨350748, by rfl⟩ : syracuseStep 935329 = 701497) (by norm_num)
theorem B935365 : Blo 830350 935365 := bbase (se 4 (by rfl) ⟨87690, by rfl⟩ : syracuseStep 935365 = 175381) (by norm_num)
theorem B935401 : Blo 830350 935401 := bbase (se 2 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 935401 = 701551) (by norm_num)
theorem B935437 : Blo 830350 935437 := bbase (se 3 (by rfl) ⟨175394, by rfl⟩ : syracuseStep 935437 = 350789) (by norm_num)
theorem B935473 : Blo 830350 935473 := bbase (se 2 (by rfl) ⟨350802, by rfl⟩ : syracuseStep 935473 = 701605) (by norm_num)
theorem B935509 : Blo 830350 935509 := bbase (se 8 (by rfl) ⟨5481, by rfl⟩ : syracuseStep 935509 = 10963) (by norm_num)
theorem B2803301 : Blo 830350 2803301 := bbase (se 4 (by rfl) ⟨262809, by rfl⟩ : syracuseStep 2803301 = 525619) (by norm_num)
theorem B2737781 : Blo 830350 2737781 := bbase (se 5 (by rfl) ⟨128333, by rfl⟩ : syracuseStep 2737781 = 256667) (by norm_num)
theorem B935545 : Blo 830350 935545 := bbase (se 2 (by rfl) ⟨350829, by rfl⟩ : syracuseStep 935545 = 701659) (by norm_num)
theorem B935581 : Blo 830350 935581 := bbase (se 3 (by rfl) ⟨175421, by rfl⟩ : syracuseStep 935581 = 350843) (by norm_num)
theorem B935617 : Blo 830350 935617 := bbase (se 2 (by rfl) ⟨350856, by rfl⟩ : syracuseStep 935617 = 701713) (by norm_num)
theorem B14436053 : Blo 830350 14436053 := bbase (se 7 (by rfl) ⟨169172, by rfl⟩ : syracuseStep 14436053 = 338345) (by norm_num)
theorem B935653 : Blo 830350 935653 := bbase (se 4 (by rfl) ⟨87717, by rfl⟩ : syracuseStep 935653 = 175435) (by norm_num)
theorem B4212485 : Blo 830350 4212485 := bbase (se 4 (by rfl) ⟨394920, by rfl⟩ : syracuseStep 4212485 = 789841) (by norm_num)
theorem B935689 : Blo 830350 935689 := bbase (se 2 (by rfl) ⟨350883, by rfl⟩ : syracuseStep 935689 = 701767) (by norm_num)
theorem B3557141 : Blo 830350 3557141 := bbase (se 6 (by rfl) ⟨83370, by rfl⟩ : syracuseStep 3557141 = 166741) (by norm_num)
theorem B935725 : Blo 830350 935725 := bbase (se 3 (by rfl) ⟨175448, by rfl⟩ : syracuseStep 935725 = 350897) (by norm_num)
theorem B1066829 : Blo 830350 1066829 := bbase (se 3 (by rfl) ⟨200030, by rfl⟩ : syracuseStep 1066829 = 400061) (by norm_num)
theorem B935761 : Blo 830350 935761 := bbase (se 2 (by rfl) ⟨350910, by rfl⟩ : syracuseStep 935761 = 701821) (by norm_num)
theorem B935797 : Blo 830350 935797 := bbase (se 5 (by rfl) ⟨43865, by rfl⟩ : syracuseStep 935797 = 87731) (by norm_num)
theorem B3000197 : Blo 830350 3000197 := bbase (se 4 (by rfl) ⟨281268, by rfl⟩ : syracuseStep 3000197 = 562537) (by norm_num)
theorem B935833 : Blo 830350 935833 := bbase (se 2 (by rfl) ⟨350937, by rfl⟩ : syracuseStep 935833 = 701875) (by norm_num)
theorem B1001369 : Blo 830350 1001369 := bbase (se 2 (by rfl) ⟨375513, by rfl⟩ : syracuseStep 1001369 = 751027) (by norm_num)
theorem B1689509 : Blo 830350 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B935869 : Blo 830350 935869 := bbase (se 3 (by rfl) ⟨175475, by rfl⟩ : syracuseStep 935869 = 350951) (by norm_num)
theorem B935905 : Blo 830350 935905 := bbase (se 2 (by rfl) ⟨350964, by rfl⟩ : syracuseStep 935905 = 701929) (by norm_num)
theorem B935941 : Blo 830350 935941 := bbase (se 4 (by rfl) ⟨87744, by rfl⟩ : syracuseStep 935941 = 175489) (by norm_num)
theorem B2803733 : Blo 830350 2803733 := bbase (se 6 (by rfl) ⟨65712, by rfl⟩ : syracuseStep 2803733 = 131425) (by norm_num)
theorem B935977 : Blo 830350 935977 := bbase (se 2 (by rfl) ⟨350991, by rfl⟩ : syracuseStep 935977 = 701983) (by norm_num)
theorem B3557429 : Blo 830350 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B936013 : Blo 830350 936013 := bbase (se 3 (by rfl) ⟨175502, by rfl⟩ : syracuseStep 936013 = 351005) (by norm_num)
theorem B936049 : Blo 830350 936049 := bbase (se 2 (by rfl) ⟨351018, by rfl⟩ : syracuseStep 936049 = 702037) (by norm_num)
theorem B936085 : Blo 830350 936085 := bbase (se 6 (by rfl) ⟨21939, by rfl⟩ : syracuseStep 936085 = 43879) (by norm_num)
theorem B936121 : Blo 830350 936121 := bbase (se 2 (by rfl) ⟨351045, by rfl⟩ : syracuseStep 936121 = 702091) (by norm_num)
theorem B936157 : Blo 830350 936157 := bbase (se 3 (by rfl) ⟨175529, by rfl⟩ : syracuseStep 936157 = 351059) (by norm_num)
theorem B936193 : Blo 830350 936193 := bbase (se 2 (by rfl) ⟨351072, by rfl⟩ : syracuseStep 936193 = 702145) (by norm_num)
theorem B936229 : Blo 830350 936229 := bbase (se 4 (by rfl) ⟨87771, by rfl⟩ : syracuseStep 936229 = 175543) (by norm_num)
theorem B3164453 : Blo 830350 3164453 := bbase (se 4 (by rfl) ⟨296667, by rfl⟩ : syracuseStep 3164453 = 593335) (by norm_num)
theorem B936265 : Blo 830350 936265 := bbase (se 2 (by rfl) ⟨351099, by rfl⟩ : syracuseStep 936265 = 702199) (by norm_num)
theorem B936301 : Blo 830350 936301 := bbase (se 3 (by rfl) ⟨175556, by rfl⟩ : syracuseStep 936301 = 351113) (by norm_num)
theorem B936337 : Blo 830350 936337 := bbase (se 2 (by rfl) ⟨351126, by rfl⟩ : syracuseStep 936337 = 702253) (by norm_num)
theorem B936373 : Blo 830350 936373 := bbase (se 5 (by rfl) ⟨43892, by rfl⟩ : syracuseStep 936373 = 87785) (by norm_num)
theorem B2804165 : Blo 830350 2804165 := bbase (se 4 (by rfl) ⟨262890, by rfl⟩ : syracuseStep 2804165 = 525781) (by norm_num)
theorem B21121493 : Blo 830350 21121493 := bbase (se 7 (by rfl) ⟨247517, by rfl⟩ : syracuseStep 21121493 = 495035) (by norm_num)
theorem B936409 : Blo 830350 936409 := bbase (se 2 (by rfl) ⟨351153, by rfl⟩ : syracuseStep 936409 = 702307) (by norm_num)
theorem B936445 : Blo 830350 936445 := bbase (se 3 (by rfl) ⟨175583, by rfl⟩ : syracuseStep 936445 = 351167) (by norm_num)
theorem B6736405 : Blo 830350 6736405 := bbase (se 6 (by rfl) ⟨157884, by rfl⟩ : syracuseStep 6736405 = 315769) (by norm_num)
theorem B936481 : Blo 830350 936481 := bbase (se 2 (by rfl) ⟨351180, by rfl⟩ : syracuseStep 936481 = 702361) (by norm_num)
theorem B936517 : Blo 830350 936517 := bbase (se 4 (by rfl) ⟨87798, by rfl⟩ : syracuseStep 936517 = 175597) (by norm_num)
theorem B3164741 : Blo 830350 3164741 := bbase (se 4 (by rfl) ⟨296694, by rfl⟩ : syracuseStep 3164741 = 593389) (by norm_num)
theorem B936553 : Blo 830350 936553 := bbase (se 2 (by rfl) ⟨351207, by rfl⟩ : syracuseStep 936553 = 702415) (by norm_num)
theorem B936589 : Blo 830350 936589 := bbase (se 3 (by rfl) ⟨175610, by rfl⟩ : syracuseStep 936589 = 351221) (by norm_num)
theorem B936625 : Blo 830350 936625 := bbase (se 2 (by rfl) ⟨351234, by rfl⟩ : syracuseStep 936625 = 702469) (by norm_num)
theorem B936661 : Blo 830350 936661 := bbase (se 7 (by rfl) ⟨10976, by rfl⟩ : syracuseStep 936661 = 21953) (by norm_num)
theorem B936697 : Blo 830350 936697 := bbase (se 2 (by rfl) ⟨351261, by rfl⟩ : syracuseStep 936697 = 702523) (by norm_num)
theorem B1067789 : Blo 830350 1067789 := bbase (se 3 (by rfl) ⟨200210, by rfl⟩ : syracuseStep 1067789 = 400421) (by norm_num)
theorem B936733 : Blo 830350 936733 := bbase (se 3 (by rfl) ⟨175637, by rfl⟩ : syracuseStep 936733 = 351275) (by norm_num)
theorem B3558181 : Blo 830350 3558181 := bbase (se 4 (by rfl) ⟨333579, by rfl⟩ : syracuseStep 3558181 = 667159) (by norm_num)
theorem B6310709 : Blo 830350 6310709 := bbase (se 5 (by rfl) ⟨295814, by rfl⟩ : syracuseStep 6310709 = 591629) (by norm_num)
theorem B936769 : Blo 830350 936769 := bbase (se 2 (by rfl) ⟨351288, by rfl⟩ : syracuseStep 936769 = 702577) (by norm_num)
theorem B936805 : Blo 830350 936805 := bbase (se 4 (by rfl) ⟨87825, by rfl⟩ : syracuseStep 936805 = 175651) (by norm_num)
theorem B2804597 : Blo 830350 2804597 := bbase (se 5 (by rfl) ⟨131465, by rfl⟩ : syracuseStep 2804597 = 262931) (by norm_num)
theorem B936841 : Blo 830350 936841 := bbase (se 2 (by rfl) ⟨351315, by rfl⟩ : syracuseStep 936841 = 702631) (by norm_num)
theorem B936877 : Blo 830350 936877 := bbase (se 3 (by rfl) ⟨175664, by rfl⟩ : syracuseStep 936877 = 351329) (by norm_num)
theorem B936913 : Blo 830350 936913 := bbase (se 2 (by rfl) ⟨351342, by rfl⟩ : syracuseStep 936913 = 702685) (by norm_num)
theorem B936949 : Blo 830350 936949 := bbase (se 5 (by rfl) ⟨43919, by rfl⟩ : syracuseStep 936949 = 87839) (by norm_num)
theorem B4213781 : Blo 830350 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B936985 : Blo 830350 936985 := bbase (se 2 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 936985 = 702739) (by norm_num)
theorem B1068061 : Blo 830350 1068061 := bbase (se 3 (by rfl) ⟨200261, by rfl⟩ : syracuseStep 1068061 = 400523) (by norm_num)
theorem B937021 : Blo 830350 937021 := bbase (se 3 (by rfl) ⟨175691, by rfl⟩ : syracuseStep 937021 = 351383) (by norm_num)
theorem B937057 : Blo 830350 937057 := bbase (se 2 (by rfl) ⟨351396, by rfl⟩ : syracuseStep 937057 = 702793) (by norm_num)
theorem B937093 : Blo 830350 937093 := bbase (se 4 (by rfl) ⟨87852, by rfl⟩ : syracuseStep 937093 = 175705) (by norm_num)
theorem B1068169 : Blo 830350 1068169 := bbase (se 2 (by rfl) ⟨400563, by rfl⟩ : syracuseStep 1068169 = 801127) (by norm_num)
theorem B937129 : Blo 830350 937129 := bbase (se 2 (by rfl) ⟨351423, by rfl⟩ : syracuseStep 937129 = 702847) (by norm_num)
theorem B937165 : Blo 830350 937165 := bbase (se 3 (by rfl) ⟨175718, by rfl⟩ : syracuseStep 937165 = 351437) (by norm_num)
theorem B3788005 : Blo 830350 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B937201 : Blo 830350 937201 := bbase (se 2 (by rfl) ⟨351450, by rfl⟩ : syracuseStep 937201 = 702901) (by norm_num)
theorem B937237 : Blo 830350 937237 := bbase (se 6 (by rfl) ⟨21966, by rfl⟩ : syracuseStep 937237 = 43933) (by norm_num)
theorem B2805029 : Blo 830350 2805029 := bbase (se 4 (by rfl) ⟨262971, by rfl⟩ : syracuseStep 2805029 = 525943) (by norm_num)
theorem B937273 : Blo 830350 937273 := bbase (se 2 (by rfl) ⟨351477, by rfl⟩ : syracuseStep 937273 = 702955) (by norm_num)
theorem B937309 : Blo 830350 937309 := bbase (se 3 (by rfl) ⟨175745, by rfl⟩ : syracuseStep 937309 = 351491) (by norm_num)
theorem B937345 : Blo 830350 937345 := bbase (se 2 (by rfl) ⟨351504, by rfl⟩ : syracuseStep 937345 = 703009) (by norm_num)
theorem B937381 : Blo 830350 937381 := bbase (se 4 (by rfl) ⟨87879, by rfl⟩ : syracuseStep 937381 = 175759) (by norm_num)
theorem B937417 : Blo 830350 937417 := bbase (se 2 (by rfl) ⟨351531, by rfl⟩ : syracuseStep 937417 = 703063) (by norm_num)
theorem B937453 : Blo 830350 937453 := bbase (se 3 (by rfl) ⟨175772, by rfl⟩ : syracuseStep 937453 = 351545) (by norm_num)
theorem B3558917 : Blo 830350 3558917 := bbase (se 4 (by rfl) ⟨333648, by rfl⟩ : syracuseStep 3558917 = 667297) (by norm_num)
theorem B937489 : Blo 830350 937489 := bbase (se 2 (by rfl) ⟨351558, by rfl⟩ : syracuseStep 937489 = 703117) (by norm_num)
theorem B937525 : Blo 830350 937525 := bbase (se 5 (by rfl) ⟨43946, by rfl⟩ : syracuseStep 937525 = 87893) (by norm_num)
theorem B937561 : Blo 830350 937561 := bbase (se 2 (by rfl) ⟨351585, by rfl⟩ : syracuseStep 937561 = 703171) (by norm_num)
theorem B937597 : Blo 830350 937597 := bbase (se 3 (by rfl) ⟨175799, by rfl⟩ : syracuseStep 937597 = 351599) (by norm_num)
theorem B937633 : Blo 830350 937633 := bbase (se 2 (by rfl) ⟨351612, by rfl⟩ : syracuseStep 937633 = 703225) (by norm_num)
theorem B1560253 : Blo 830350 1560253 := bbase (se 3 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 1560253 = 585095) (by norm_num)
theorem B937669 : Blo 830350 937669 := bbase (se 4 (by rfl) ⟨87906, by rfl⟩ : syracuseStep 937669 = 175813) (by norm_num)
theorem B2805461 : Blo 830350 2805461 := bbase (se 7 (by rfl) ⟨32876, by rfl⟩ : syracuseStep 2805461 = 65753) (by norm_num)
theorem B3165925 : Blo 830350 3165925 := bbase (se 4 (by rfl) ⟨296805, by rfl⟩ : syracuseStep 3165925 = 593611) (by norm_num)
theorem B937705 : Blo 830350 937705 := bbase (se 2 (by rfl) ⟨351639, by rfl⟩ : syracuseStep 937705 = 703279) (by norm_num)
theorem B937741 : Blo 830350 937741 := bbase (se 3 (by rfl) ⟨175826, by rfl⟩ : syracuseStep 937741 = 351653) (by norm_num)
theorem B937777 : Blo 830350 937777 := bbase (se 2 (by rfl) ⟨351666, by rfl⟩ : syracuseStep 937777 = 703333) (by norm_num)
theorem B937813 : Blo 830350 937813 := bbase (se 9 (by rfl) ⟨2747, by rfl⟩ : syracuseStep 937813 = 5495) (by norm_num)
theorem B937849 : Blo 830350 937849 := bbase (se 2 (by rfl) ⟨351693, by rfl⟩ : syracuseStep 937849 = 703387) (by norm_num)
theorem B937885 : Blo 830350 937885 := bbase (se 3 (by rfl) ⟨175853, by rfl⟩ : syracuseStep 937885 = 351707) (by norm_num)
theorem B937921 : Blo 830350 937921 := bbase (se 2 (by rfl) ⟨351720, by rfl⟩ : syracuseStep 937921 = 703441) (by norm_num)
theorem B937957 : Blo 830350 937957 := bbase (se 4 (by rfl) ⟨87933, by rfl⟩ : syracuseStep 937957 = 175867) (by norm_num)
theorem B937993 : Blo 830350 937993 := bbase (se 2 (by rfl) ⟨351747, by rfl⟩ : syracuseStep 937993 = 703495) (by norm_num)
theorem B4739093 : Blo 830350 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B3166229 : Blo 830350 3166229 := bbase (se 6 (by rfl) ⟨74208, by rfl⟩ : syracuseStep 3166229 = 148417) (by norm_num)
theorem B938029 : Blo 830350 938029 := bbase (se 3 (by rfl) ⟨175880, by rfl⟩ : syracuseStep 938029 = 351761) (by norm_num)
theorem B938065 : Blo 830350 938065 := bbase (se 2 (by rfl) ⟨351774, by rfl⟩ : syracuseStep 938065 = 703549) (by norm_num)
theorem B938101 : Blo 830350 938101 := bbase (se 5 (by rfl) ⟨43973, by rfl⟩ : syracuseStep 938101 = 87947) (by norm_num)
theorem B1331333 : Blo 830350 1331333 := bbase (se 4 (by rfl) ⟨124812, by rfl⟩ : syracuseStep 1331333 = 249625) (by norm_num)
theorem B2805893 : Blo 830350 2805893 := bbase (se 4 (by rfl) ⟨263052, by rfl⟩ : syracuseStep 2805893 = 526105) (by norm_num)
theorem B938137 : Blo 830350 938137 := bbase (se 2 (by rfl) ⟨351801, by rfl⟩ : syracuseStep 938137 = 703603) (by norm_num)
theorem B938173 : Blo 830350 938173 := bbase (se 3 (by rfl) ⟨175907, by rfl⟩ : syracuseStep 938173 = 351815) (by norm_num)
theorem B938209 : Blo 830350 938209 := bbase (se 2 (by rfl) ⟨351828, by rfl⟩ : syracuseStep 938209 = 703657) (by norm_num)
theorem B938245 : Blo 830350 938245 := bbase (se 4 (by rfl) ⟨87960, by rfl⟩ : syracuseStep 938245 = 175921) (by norm_num)
theorem B4215077 : Blo 830350 4215077 := bbase (se 4 (by rfl) ⟨395163, by rfl⟩ : syracuseStep 4215077 = 790327) (by norm_num)
theorem B938281 : Blo 830350 938281 := bbase (se 2 (by rfl) ⟨351855, by rfl⟩ : syracuseStep 938281 = 703711) (by norm_num)
theorem B1331525 : Blo 830350 1331525 := bbase (se 4 (by rfl) ⟨124830, by rfl⟩ : syracuseStep 1331525 = 249661) (by norm_num)
theorem B938317 : Blo 830350 938317 := bbase (se 3 (by rfl) ⟨175934, by rfl⟩ : syracuseStep 938317 = 351869) (by norm_num)
theorem B938353 : Blo 830350 938353 := bbase (se 2 (by rfl) ⟨351882, by rfl⟩ : syracuseStep 938353 = 703765) (by norm_num)
theorem B2281861 : Blo 830350 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B938389 : Blo 830350 938389 := bbase (se 6 (by rfl) ⟨21993, by rfl⟩ : syracuseStep 938389 = 43987) (by norm_num)
theorem B938425 : Blo 830350 938425 := bbase (se 2 (by rfl) ⟨351909, by rfl⟩ : syracuseStep 938425 = 703819) (by norm_num)
theorem B1331653 : Blo 830350 1331653 := bbase (se 4 (by rfl) ⟨124842, by rfl⟩ : syracuseStep 1331653 = 249685) (by norm_num)
theorem B938461 : Blo 830350 938461 := bbase (se 3 (by rfl) ⟨175961, by rfl⟩ : syracuseStep 938461 = 351923) (by norm_num)
theorem B938497 : Blo 830350 938497 := bbase (se 2 (by rfl) ⟨351936, by rfl⟩ : syracuseStep 938497 = 703873) (by norm_num)
theorem B938533 : Blo 830350 938533 := bbase (se 4 (by rfl) ⟨87987, by rfl⟩ : syracuseStep 938533 = 175975) (by norm_num)
theorem B2806325 : Blo 830350 2806325 := bbase (se 5 (by rfl) ⟨131546, by rfl⟩ : syracuseStep 2806325 = 263093) (by norm_num)
theorem B938569 : Blo 830350 938569 := bbase (se 2 (by rfl) ⟨351963, by rfl⟩ : syracuseStep 938569 = 703927) (by norm_num)
theorem B938605 : Blo 830350 938605 := bbase (se 3 (by rfl) ⟨175988, by rfl⟩ : syracuseStep 938605 = 351977) (by norm_num)
theorem B938641 : Blo 830350 938641 := bbase (se 2 (by rfl) ⟨351990, by rfl⟩ : syracuseStep 938641 = 703981) (by norm_num)
theorem B1200973 : Blo 830350 1200973 := bbase (se 3 (by rfl) ⟨225182, by rfl⟩ : syracuseStep 1200973 = 450365) (by norm_num)
theorem B2806757 : Blo 830350 2806757 := bbase (se 4 (by rfl) ⟨263133, by rfl⟩ : syracuseStep 2806757 = 526267) (by norm_num)
theorem B1332293 : Blo 830350 1332293 := bbase (se 4 (by rfl) ⟨124902, by rfl⟩ : syracuseStep 1332293 = 249805) (by norm_num)
theorem B5067893 : Blo 830350 5067893 := bbase (se 5 (by rfl) ⟨237557, by rfl⟩ : syracuseStep 5067893 = 475115) (by norm_num)
theorem B1266877 : Blo 830350 1266877 := bbase (se 3 (by rfl) ⟨237539, by rfl⟩ : syracuseStep 1266877 = 475079) (by norm_num)
theorem B8541397 : Blo 830350 8541397 := bbase (se 7 (by rfl) ⟨100094, by rfl⟩ : syracuseStep 8541397 = 200189) (by norm_num)
theorem B2807189 : Blo 830350 2807189 := bbase (se 6 (by rfl) ⟨65793, by rfl⟩ : syracuseStep 2807189 = 131587) (by norm_num)
theorem B1332749 : Blo 830350 1332749 := bbase (se 3 (by rfl) ⟨249890, by rfl⟩ : syracuseStep 1332749 = 499781) (by norm_num)
theorem B4216373 : Blo 830350 4216373 := bbase (se 5 (by rfl) ⟨197642, by rfl⟩ : syracuseStep 4216373 = 395285) (by norm_num)
theorem B1332973 : Blo 830350 1332973 := bbase (se 3 (by rfl) ⟨249932, by rfl⟩ : syracuseStep 1332973 = 499865) (by norm_num)
theorem B1333037 : Blo 830350 1333037 := bbase (se 3 (by rfl) ⟨249944, by rfl⟩ : syracuseStep 1333037 = 499889) (by norm_num)
theorem B2807621 : Blo 830350 2807621 := bbase (se 4 (by rfl) ⟨263214, by rfl⟩ : syracuseStep 2807621 = 526429) (by norm_num)
theorem B1333165 : Blo 830350 1333165 := bbase (se 3 (by rfl) ⟨249968, by rfl⟩ : syracuseStep 1333165 = 499937) (by norm_num)
theorem B5986325 : Blo 830350 5986325 := bbase (se 6 (by rfl) ⟨140304, by rfl⟩ : syracuseStep 5986325 = 280609) (by norm_num)
theorem B2808053 : Blo 830350 2808053 := bbase (se 5 (by rfl) ⟨131627, by rfl⟩ : syracuseStep 2808053 = 263255) (by norm_num)
theorem B1268093 : Blo 830350 1268093 := bbase (se 3 (by rfl) ⟨237767, by rfl⟩ : syracuseStep 1268093 = 475535) (by norm_num)
theorem B1497533 : Blo 830350 1497533 := bbase (se 3 (by rfl) ⟨280787, by rfl⟩ : syracuseStep 1497533 = 561575) (by norm_num)
theorem B3005029 : Blo 830350 3005029 := bbase (se 4 (by rfl) ⟨281721, by rfl⟩ : syracuseStep 3005029 = 563443) (by norm_num)
theorem B2808485 : Blo 830350 2808485 := bbase (se 4 (by rfl) ⟨263295, by rfl⟩ : syracuseStep 2808485 = 526591) (by norm_num)
theorem B3562213 : Blo 830350 3562213 := bbase (se 4 (by rfl) ⟨333957, by rfl⟩ : syracuseStep 3562213 = 667915) (by norm_num)
theorem B2841413 : Blo 830350 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B4217669 : Blo 830350 4217669 := bbase (se 4 (by rfl) ⟨395406, by rfl⟩ : syracuseStep 4217669 = 790813) (by norm_num)
theorem B1465237 : Blo 830350 1465237 := bbase (se 6 (by rfl) ⟨34341, by rfl⟩ : syracuseStep 1465237 = 68683) (by norm_num)
theorem B13523861 : Blo 830350 13523861 := bbase (se 6 (by rfl) ⟨316965, by rfl⟩ : syracuseStep 13523861 = 633931) (by norm_num)
theorem B2841605 : Blo 830350 2841605 := bbase (se 4 (by rfl) ⟨266400, by rfl⟩ : syracuseStep 2841605 = 532801) (by norm_num)
theorem B2808917 : Blo 830350 2808917 := bbase (se 8 (by rfl) ⟨16458, by rfl⟩ : syracuseStep 2808917 = 32917) (by norm_num)
theorem B1334389 : Blo 830350 1334389 := bbase (se 5 (by rfl) ⟨62549, by rfl⟩ : syracuseStep 1334389 = 125099) (by norm_num)
theorem B2809349 : Blo 830350 2809349 := bbase (se 4 (by rfl) ⟨263376, by rfl⟩ : syracuseStep 2809349 = 526753) (by norm_num)
theorem B1335061 : Blo 830350 1335061 := bbase (se 6 (by rfl) ⟨31290, by rfl⟩ : syracuseStep 1335061 = 62581) (by norm_num)
theorem B3006341 : Blo 830350 3006341 := bbase (se 4 (by rfl) ⟨281844, by rfl⟩ : syracuseStep 3006341 = 563689) (by norm_num)
theorem B2809781 : Blo 830350 2809781 := bbase (se 5 (by rfl) ⟨131708, by rfl⟩ : syracuseStep 2809781 = 263417) (by norm_num)
theorem B1368029 : Blo 830350 1368029 := bbase (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) (by norm_num)
theorem B4218965 : Blo 830350 4218965 := bbase (se 8 (by rfl) ⟨24720, by rfl⟩ : syracuseStep 4218965 = 49441) (by norm_num)
theorem B2810213 : Blo 830350 2810213 := bbase (se 4 (by rfl) ⟨263457, by rfl⟩ : syracuseStep 2810213 = 526915) (by norm_num)
theorem B2253221 : Blo 830350 2253221 := bbase (se 4 (by rfl) ⟨211239, by rfl⟩ : syracuseStep 2253221 = 422479) (by norm_num)
theorem B1401293 : Blo 830350 1401293 := bbase (se 3 (by rfl) ⟨262742, by rfl⟩ : syracuseStep 1401293 = 525485) (by norm_num)
theorem B1401421 : Blo 830350 1401421 := bbase (se 3 (by rfl) ⟨262766, by rfl⟩ : syracuseStep 1401421 = 525533) (by norm_num)
theorem B1401509 : Blo 830350 1401509 := bbase (se 4 (by rfl) ⟨131391, by rfl⟩ : syracuseStep 1401509 = 262783) (by norm_num)
theorem B6087413 : Blo 830350 6087413 := bbase (se 5 (by rfl) ⟨285347, by rfl⟩ : syracuseStep 6087413 = 570695) (by norm_num)
theorem B1336061 : Blo 830350 1336061 := bbase (se 3 (by rfl) ⟨250511, by rfl⟩ : syracuseStep 1336061 = 501023) (by norm_num)
theorem B9003797 : Blo 830350 9003797 := bbase (se 6 (by rfl) ⟨211026, by rfl⟩ : syracuseStep 9003797 = 422053) (by norm_num)
theorem B2810645 : Blo 830350 2810645 := bbase (se 6 (by rfl) ⟨65874, by rfl⟩ : syracuseStep 2810645 = 131749) (by norm_num)
theorem B1401637 : Blo 830350 1401637 := bbase (se 4 (by rfl) ⟨131403, by rfl⟩ : syracuseStep 1401637 = 262807) (by norm_num)
theorem B844625 : Blo 830350 844625 := bbase (se 2 (by rfl) ⟨316734, by rfl⟩ : syracuseStep 844625 = 633469) (by norm_num)
theorem B2253653 : Blo 830350 2253653 := bbase (se 9 (by rfl) ⟨6602, by rfl⟩ : syracuseStep 2253653 = 13205) (by norm_num)
theorem B1401725 : Blo 830350 1401725 := bbase (se 3 (by rfl) ⟨262823, by rfl⟩ : syracuseStep 1401725 = 525647) (by norm_num)
theorem B1598341 : Blo 830350 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B3367813 : Blo 830350 3367813 := bbase (se 4 (by rfl) ⟨315732, by rfl⟩ : syracuseStep 3367813 = 631465) (by norm_num)
theorem B3990421 : Blo 830350 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B2253781 : Blo 830350 2253781 := bbase (se 7 (by rfl) ⟨26411, by rfl⟩ : syracuseStep 2253781 = 52823) (by norm_num)
theorem B1401853 : Blo 830350 1401853 := bbase (se 3 (by rfl) ⟨262847, by rfl⟩ : syracuseStep 1401853 = 525695) (by norm_num)
theorem B1500157 : Blo 830350 1500157 := bbase (se 3 (by rfl) ⟨281279, by rfl⟩ : syracuseStep 1500157 = 562559) (by norm_num)
theorem B844877 : Blo 830350 844877 := bbase (se 3 (by rfl) ⟨158414, by rfl⟩ : syracuseStep 844877 = 316829) (by norm_num)
theorem B1401941 : Blo 830350 1401941 := bbase (se 8 (by rfl) ⟨8214, by rfl⟩ : syracuseStep 1401941 = 16429) (by norm_num)
theorem B2811077 : Blo 830350 2811077 := bbase (se 4 (by rfl) ⟨263538, by rfl⟩ : syracuseStep 2811077 = 527077) (by norm_num)
theorem B1402069 : Blo 830350 1402069 := bbase (se 7 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 1402069 = 32861) (by norm_num)
theorem B1402157 : Blo 830350 1402157 := bbase (se 3 (by rfl) ⟨262904, by rfl⟩ : syracuseStep 1402157 = 525809) (by norm_num)
theorem B4220261 : Blo 830350 4220261 := bbase (se 4 (by rfl) ⟨395649, by rfl⟩ : syracuseStep 4220261 = 791299) (by norm_num)
theorem B1402285 : Blo 830350 1402285 := bbase (se 3 (by rfl) ⟨262928, by rfl⟩ : syracuseStep 1402285 = 525857) (by norm_num)
theorem B1402373 : Blo 830350 1402373 := bbase (se 4 (by rfl) ⟨131472, by rfl⟩ : syracuseStep 1402373 = 262945) (by norm_num)
theorem B2745893 : Blo 830350 2745893 := bbase (se 4 (by rfl) ⟨257427, by rfl⟩ : syracuseStep 2745893 = 514855) (by norm_num)
theorem B1205869 : Blo 830350 1205869 := bbase (se 3 (by rfl) ⟨226100, by rfl⟩ : syracuseStep 1205869 = 452201) (by norm_num)
theorem B2811509 : Blo 830350 2811509 := bbase (se 5 (by rfl) ⟨131789, by rfl⟩ : syracuseStep 2811509 = 263579) (by norm_num)
theorem B1402501 : Blo 830350 1402501 := bbase (se 4 (by rfl) ⟨131484, by rfl⟩ : syracuseStep 1402501 = 262969) (by norm_num)
theorem B1402589 : Blo 830350 1402589 := bbase (se 3 (by rfl) ⟨262985, by rfl⟩ : syracuseStep 1402589 = 525971) (by norm_num)
theorem B1402717 : Blo 830350 1402717 := bbase (se 3 (by rfl) ⟨263009, by rfl⟩ : syracuseStep 1402717 = 526019) (by norm_num)
theorem B1402805 : Blo 830350 1402805 := bbase (se 5 (by rfl) ⟨65756, by rfl⟩ : syracuseStep 1402805 = 131513) (by norm_num)
theorem B7104469 : Blo 830350 7104469 := bbase (se 7 (by rfl) ⟨83255, by rfl⟩ : syracuseStep 7104469 = 166511) (by norm_num)
theorem B2811941 : Blo 830350 2811941 := bbase (se 4 (by rfl) ⟨263619, by rfl⟩ : syracuseStep 2811941 = 527239) (by norm_num)
theorem B1402933 : Blo 830350 1402933 := bbase (se 5 (by rfl) ⟨65762, by rfl⟩ : syracuseStep 1402933 = 131525) (by norm_num)
theorem B1403021 : Blo 830350 1403021 := bbase (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) (by norm_num)
theorem B1501325 : Blo 830350 1501325 := bbase (se 3 (by rfl) ⟨281498, by rfl⟩ : syracuseStep 1501325 = 562997) (by norm_num)
theorem B1403149 : Blo 830350 1403149 := bbase (se 3 (by rfl) ⟨263090, by rfl⟩ : syracuseStep 1403149 = 526181) (by norm_num)
theorem B1403237 : Blo 830350 1403237 := bbase (se 4 (by rfl) ⟨131553, by rfl⟩ : syracuseStep 1403237 = 263107) (by norm_num)
theorem B6318485 : Blo 830350 6318485 := bbase (se 6 (by rfl) ⟨148089, by rfl⟩ : syracuseStep 6318485 = 296179) (by norm_num)
theorem B2812373 : Blo 830350 2812373 := bbase (se 7 (by rfl) ⟨32957, by rfl⟩ : syracuseStep 2812373 = 65915) (by norm_num)
theorem B1403365 : Blo 830350 1403365 := bbase (se 4 (by rfl) ⟨131565, by rfl⟩ : syracuseStep 1403365 = 263131) (by norm_num)
theorem B1403453 : Blo 830350 1403453 := bbase (se 3 (by rfl) ⟨263147, by rfl⟩ : syracuseStep 1403453 = 526295) (by norm_num)
theorem B4221557 : Blo 830350 4221557 := bbase (se 5 (by rfl) ⟨197885, by rfl⟩ : syracuseStep 4221557 = 395771) (by norm_num)
theorem B1501829 : Blo 830350 1501829 := bbase (se 4 (by rfl) ⟨140796, by rfl⟩ : syracuseStep 1501829 = 281593) (by norm_num)
theorem B5335733 : Blo 830350 5335733 := bbase (se 5 (by rfl) ⟨250112, by rfl⟩ : syracuseStep 5335733 = 500225) (by norm_num)
theorem B1403581 : Blo 830350 1403581 := bbase (se 3 (by rfl) ⟨263171, by rfl⟩ : syracuseStep 1403581 = 526343) (by norm_num)
theorem B1403669 : Blo 830350 1403669 := bbase (se 6 (by rfl) ⟨32898, by rfl⟩ : syracuseStep 1403669 = 65797) (by norm_num)
theorem B2812805 : Blo 830350 2812805 := bbase (se 4 (by rfl) ⟨263700, by rfl⟩ : syracuseStep 2812805 = 527401) (by norm_num)
theorem B1403797 : Blo 830350 1403797 := bbase (se 6 (by rfl) ⟨32901, by rfl⟩ : syracuseStep 1403797 = 65803) (by norm_num)
theorem B1600469 : Blo 830350 1600469 := bbase (se 7 (by rfl) ⟨18755, by rfl⟩ : syracuseStep 1600469 = 37511) (by norm_num)
theorem B1403885 : Blo 830350 1403885 := bbase (se 3 (by rfl) ⟨263228, by rfl⟩ : syracuseStep 1403885 = 526457) (by norm_num)
theorem B912493 : Blo 830350 912493 := bbase (se 3 (by rfl) ⟨171092, by rfl⟩ : syracuseStep 912493 = 342185) (by norm_num)
theorem B1404013 : Blo 830350 1404013 := bbase (se 3 (by rfl) ⟨263252, by rfl⟩ : syracuseStep 1404013 = 526505) (by norm_num)
theorem B1404101 : Blo 830350 1404101 := bbase (se 4 (by rfl) ⟨131634, by rfl⟩ : syracuseStep 1404101 = 263269) (by norm_num)
theorem B2813237 : Blo 830350 2813237 := bbase (se 5 (by rfl) ⟨131870, by rfl⟩ : syracuseStep 2813237 = 263741) (by norm_num)
theorem B1142069 : Blo 830350 1142069 := bbase (se 5 (by rfl) ⟨53534, by rfl⟩ : syracuseStep 1142069 = 107069) (by norm_num)
theorem B1404229 : Blo 830350 1404229 := bbase (se 4 (by rfl) ⟨131646, by rfl⟩ : syracuseStep 1404229 = 263293) (by norm_num)
theorem B1895789 : Blo 830350 1895789 := bbase (se 3 (by rfl) ⟨355460, by rfl⟩ : syracuseStep 1895789 = 710921) (by norm_num)
theorem B1404317 : Blo 830350 1404317 := bbase (se 3 (by rfl) ⟨263309, by rfl⟩ : syracuseStep 1404317 = 526619) (by norm_num)
theorem B1601021 : Blo 830350 1601021 := bbase (se 3 (by rfl) ⟨300191, by rfl⟩ : syracuseStep 1601021 = 600383) (by norm_num)
theorem B1404445 : Blo 830350 1404445 := bbase (se 3 (by rfl) ⟨263333, by rfl⟩ : syracuseStep 1404445 = 526667) (by norm_num)
theorem B1404533 : Blo 830350 1404533 := bbase (se 5 (by rfl) ⟨65837, by rfl⟩ : syracuseStep 1404533 = 131675) (by norm_num)
theorem B2813669 : Blo 830350 2813669 := bbase (se 4 (by rfl) ⟨263781, by rfl⟩ : syracuseStep 2813669 = 527563) (by norm_num)
theorem B1404661 : Blo 830350 1404661 := bbase (se 5 (by rfl) ⟨65843, by rfl⟩ : syracuseStep 1404661 = 131687) (by norm_num)
theorem B1404749 : Blo 830350 1404749 := bbase (se 3 (by rfl) ⟨263390, by rfl⟩ : syracuseStep 1404749 = 526781) (by norm_num)
theorem B4222853 : Blo 830350 4222853 := bbase (se 4 (by rfl) ⟨395892, by rfl⟩ : syracuseStep 4222853 = 791785) (by norm_num)
theorem B7106453 : Blo 830350 7106453 := bbase (se 6 (by rfl) ⟨166557, by rfl⟩ : syracuseStep 7106453 = 333115) (by norm_num)
theorem B4747157 : Blo 830350 4747157 := bbase (se 6 (by rfl) ⟨111261, by rfl⟩ : syracuseStep 4747157 = 222523) (by norm_num)
theorem B2191301 : Blo 830350 2191301 := bbase (se 4 (by rfl) ⟨205434, by rfl⟩ : syracuseStep 2191301 = 410869) (by norm_num)
theorem B1404877 : Blo 830350 1404877 := bbase (se 3 (by rfl) ⟨263414, by rfl⟩ : syracuseStep 1404877 = 526829) (by norm_num)
theorem B1404965 : Blo 830350 1404965 := bbase (se 4 (by rfl) ⟨131715, by rfl⟩ : syracuseStep 1404965 = 263431) (by norm_num)
theorem B2814101 : Blo 830350 2814101 := bbase (se 6 (by rfl) ⟨65955, by rfl⟩ : syracuseStep 2814101 = 131911) (by norm_num)
theorem B15429781 : Blo 830350 15429781 := bbase (se 6 (by rfl) ⟨361635, by rfl⟩ : syracuseStep 15429781 = 723271) (by norm_num)
theorem B1405093 : Blo 830350 1405093 := bbase (se 4 (by rfl) ⟨131727, by rfl⟩ : syracuseStep 1405093 = 263455) (by norm_num)
theorem B1896629 : Blo 830350 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B1405181 : Blo 830350 1405181 := bbase (se 3 (by rfl) ⟨263471, by rfl⟩ : syracuseStep 1405181 = 526943) (by norm_num)
theorem B3993941 : Blo 830350 3993941 := bbase (se 10 (by rfl) ⟨5850, by rfl⟩ : syracuseStep 3993941 = 11701) (by norm_num)
theorem B1405309 : Blo 830350 1405309 := bbase (se 3 (by rfl) ⟨263495, by rfl⟩ : syracuseStep 1405309 = 526991) (by norm_num)
theorem B1405397 : Blo 830350 1405397 := bbase (se 7 (by rfl) ⟨16469, by rfl⟩ : syracuseStep 1405397 = 32939) (by norm_num)
theorem B2814533 : Blo 830350 2814533 := bbase (se 4 (by rfl) ⟨263862, by rfl⟩ : syracuseStep 2814533 = 527725) (by norm_num)
theorem B1405525 : Blo 830350 1405525 := bbase (se 8 (by rfl) ⟨8235, by rfl⟩ : syracuseStep 1405525 = 16471) (by norm_num)
theorem B1405613 : Blo 830350 1405613 := bbase (se 3 (by rfl) ⟨263552, by rfl⟩ : syracuseStep 1405613 = 527105) (by norm_num)
theorem B1405741 : Blo 830350 1405741 := bbase (se 3 (by rfl) ⟨263576, by rfl⟩ : syracuseStep 1405741 = 527153) (by norm_num)
theorem B1405829 : Blo 830350 1405829 := bbase (se 4 (by rfl) ⟨131796, by rfl⟩ : syracuseStep 1405829 = 263593) (by norm_num)
theorem B2814965 : Blo 830350 2814965 := bbase (se 5 (by rfl) ⟨131951, by rfl⟩ : syracuseStep 2814965 = 263903) (by norm_num)
theorem B1405957 : Blo 830350 1405957 := bbase (se 4 (by rfl) ⟨131808, by rfl⟩ : syracuseStep 1405957 = 263617) (by norm_num)
theorem B4748341 : Blo 830350 4748341 := bbase (se 5 (by rfl) ⟨222578, by rfl⟩ : syracuseStep 4748341 = 445157) (by norm_num)
theorem B1406045 : Blo 830350 1406045 := bbase (se 3 (by rfl) ⟨263633, by rfl⟩ : syracuseStep 1406045 = 527267) (by norm_num)
theorem B1406173 : Blo 830350 1406173 := bbase (se 3 (by rfl) ⟨263657, by rfl⟩ : syracuseStep 1406173 = 527315) (by norm_num)
theorem B1406261 : Blo 830350 1406261 := bbase (se 5 (by rfl) ⟨65918, by rfl⟩ : syracuseStep 1406261 = 131837) (by norm_num)
theorem B2159941 : Blo 830350 2159941 := bbase (se 4 (by rfl) ⟨202494, by rfl⟩ : syracuseStep 2159941 = 404989) (by norm_num)
theorem B947585 : Blo 830350 947585 := bbase (se 2 (by rfl) ⟨355344, by rfl⟩ : syracuseStep 947585 = 710689) (by norm_num)
theorem B2815397 : Blo 830350 2815397 := bbase (se 4 (by rfl) ⟨263943, by rfl⟩ : syracuseStep 2815397 = 527887) (by norm_num)
theorem B1406389 : Blo 830350 1406389 := bbase (se 5 (by rfl) ⟨65924, by rfl⟩ : syracuseStep 1406389 = 131849) (by norm_num)
theorem B1406477 : Blo 830350 1406477 := bbase (se 3 (by rfl) ⟨263714, by rfl⟩ : syracuseStep 1406477 = 527429) (by norm_num)
theorem B3995189 : Blo 830350 3995189 := bbase (se 5 (by rfl) ⟨187274, by rfl⟩ : syracuseStep 3995189 = 374549) (by norm_num)
theorem B7992917 : Blo 830350 7992917 := bbase (se 8 (by rfl) ⟨46833, by rfl⟩ : syracuseStep 7992917 = 93667) (by norm_num)
theorem B5338709 : Blo 830350 5338709 := bbase (se 8 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 5338709 = 62563) (by norm_num)
theorem B1406605 : Blo 830350 1406605 := bbase (se 3 (by rfl) ⟨263738, by rfl⟩ : syracuseStep 1406605 = 527477) (by norm_num)
theorem B1013477 : Blo 830350 1013477 := bbase (se 4 (by rfl) ⟨95013, by rfl⟩ : syracuseStep 1013477 = 190027) (by norm_num)
theorem B1406693 : Blo 830350 1406693 := bbase (se 4 (by rfl) ⟨131877, by rfl⟩ : syracuseStep 1406693 = 263755) (by norm_num)
theorem B5699413 : Blo 830350 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B2815829 : Blo 830350 2815829 := bbase (se 9 (by rfl) ⟨8249, by rfl⟩ : syracuseStep 2815829 = 16499) (by norm_num)
theorem B1406821 : Blo 830350 1406821 := bbase (se 4 (by rfl) ⟨131889, by rfl⟩ : syracuseStep 1406821 = 263779) (by norm_num)
theorem B1406909 : Blo 830350 1406909 := bbase (se 3 (by rfl) ⟨263795, by rfl⟩ : syracuseStep 1406909 = 527591) (by norm_num)
theorem B1407037 : Blo 830350 1407037 := bbase (se 3 (by rfl) ⟨263819, by rfl⟩ : syracuseStep 1407037 = 527639) (by norm_num)
theorem B1407125 : Blo 830350 1407125 := bbase (se 6 (by rfl) ⟨32979, by rfl⟩ : syracuseStep 1407125 = 65959) (by norm_num)
theorem B1407253 : Blo 830350 1407253 := bbase (se 6 (by rfl) ⟨32982, by rfl⟩ : syracuseStep 1407253 = 65965) (by norm_num)
theorem B1407341 : Blo 830350 1407341 := bbase (se 3 (by rfl) ⟨263876, by rfl⟩ : syracuseStep 1407341 = 527753) (by norm_num)
theorem B1407469 : Blo 830350 1407469 := bbase (se 3 (by rfl) ⟨263900, by rfl⟩ : syracuseStep 1407469 = 527801) (by norm_num)
theorem B1407557 : Blo 830350 1407557 := bbase (se 4 (by rfl) ⟨131958, by rfl⟩ : syracuseStep 1407557 = 263917) (by norm_num)
theorem B1407685 : Blo 830350 1407685 := bbase (se 4 (by rfl) ⟨131970, by rfl⟩ : syracuseStep 1407685 = 263941) (by norm_num)
theorem B1407773 : Blo 830350 1407773 := bbase (se 3 (by rfl) ⟨263957, by rfl⟩ : syracuseStep 1407773 = 527915) (by norm_num)
theorem B1407901 : Blo 830350 1407901 := bbase (se 3 (by rfl) ⟨263981, by rfl⟩ : syracuseStep 1407901 = 527963) (by norm_num)
theorem B3799973 : Blo 830350 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B4750325 : Blo 830350 4750325 := bbase (se 5 (by rfl) ⟨222671, by rfl⟩ : syracuseStep 4750325 = 445343) (by norm_num)
theorem B1997893 : Blo 830350 1997893 := bbase (se 4 (by rfl) ⟨187302, by rfl⟩ : syracuseStep 1997893 = 374605) (by norm_num)
theorem B1997941 : Blo 830350 1997941 := bbase (se 5 (by rfl) ⟨93653, by rfl⟩ : syracuseStep 1997941 = 187307) (by norm_num)
theorem B949537 : Blo 830350 949537 := bbase (se 2 (by rfl) ⟨356076, by rfl⟩ : syracuseStep 949537 = 712153) (by norm_num)
theorem B1899877 : Blo 830350 1899877 := bbase (se 4 (by rfl) ⟨178113, by rfl⟩ : syracuseStep 1899877 = 356227) (by norm_num)
theorem B949865 : Blo 830350 949865 := bbase (se 2 (by rfl) ⟨356199, by rfl⟩ : syracuseStep 949865 = 712399) (by norm_num)
theorem B1998557 : Blo 830350 1998557 := bbase (se 3 (by rfl) ⟨374729, by rfl⟩ : syracuseStep 1998557 = 749459) (by norm_num)
theorem B3211093 : Blo 830350 3211093 := bbase (se 9 (by rfl) ⟨9407, by rfl⟩ : syracuseStep 3211093 = 18815) (by norm_num)
theorem B1900525 : Blo 830350 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B1999171 : Blo 830350 1999171 := bstep (se 1 (by rfl) ⟨1499378, by rfl⟩ : syracuseStep 1999171 = 2998757) B2998757
theorem B1245539 : Blo 830350 1245539 := bstep (se 1 (by rfl) ⟨934154, by rfl⟩ : syracuseStep 1245539 = 1868309) B1868309
theorem B1245569 : Blo 830350 1245569 := bstep (se 2 (by rfl) ⟨467088, by rfl⟩ : syracuseStep 1245569 = 934177) B934177
theorem B1245587 : Blo 830350 1245587 := bstep (se 1 (by rfl) ⟨934190, by rfl⟩ : syracuseStep 1245587 = 1868381) B1868381
theorem B4063651 : Blo 830350 4063651 := bstep (se 1 (by rfl) ⟨3047738, by rfl⟩ : syracuseStep 4063651 = 6095477) B6095477
theorem B1245617 : Blo 830350 1245617 := bstep (se 2 (by rfl) ⟨467106, by rfl⟩ : syracuseStep 1245617 = 934213) B934213
theorem B1245635 : Blo 830350 1245635 := bstep (se 1 (by rfl) ⟨934226, by rfl⟩ : syracuseStep 1245635 = 1868453) B1868453
theorem B1245665 : Blo 830350 1245665 := bstep (se 2 (by rfl) ⟨467124, by rfl⟩ : syracuseStep 1245665 = 934249) B934249
theorem B1245683 : Blo 830350 1245683 := bstep (se 1 (by rfl) ⟨934262, by rfl⟩ : syracuseStep 1245683 = 1868525) B1868525
theorem B1868291 : Blo 830350 1868291 := bstep (se 1 (by rfl) ⟨1401218, by rfl⟩ : syracuseStep 1868291 = 2802437) B2802437
theorem B1245713 : Blo 830350 1245713 := bstep (se 2 (by rfl) ⟨467142, by rfl⟩ : syracuseStep 1245713 = 934285) B934285
theorem B1245731 : Blo 830350 1245731 := bstep (se 1 (by rfl) ⟨934298, by rfl⟩ : syracuseStep 1245731 = 1868597) B1868597
theorem B1245761 : Blo 830350 1245761 := bstep (se 2 (by rfl) ⟨467160, by rfl⟩ : syracuseStep 1245761 = 934321) B934321
theorem B1245779 : Blo 830350 1245779 := bstep (se 1 (by rfl) ⟨934334, by rfl⟩ : syracuseStep 1245779 = 1868669) B1868669
theorem B1245809 : Blo 830350 1245809 := bstep (se 2 (by rfl) ⟨467178, by rfl⟩ : syracuseStep 1245809 = 934357) B934357
theorem B1245827 : Blo 830350 1245827 := bstep (se 1 (by rfl) ⟨934370, by rfl⟩ : syracuseStep 1245827 = 1868741) B1868741
theorem B1245857 : Blo 830350 1245857 := bstep (se 2 (by rfl) ⟨467196, by rfl⟩ : syracuseStep 1245857 = 934393) B934393
theorem B1245875 : Blo 830350 1245875 := bstep (se 1 (by rfl) ⟨934406, by rfl⟩ : syracuseStep 1245875 = 1868813) B1868813
theorem B1245905 : Blo 830350 1245905 := bstep (se 2 (by rfl) ⟨467214, by rfl⟩ : syracuseStep 1245905 = 934429) B934429
theorem B1245923 : Blo 830350 1245923 := bstep (se 1 (by rfl) ⟨934442, by rfl⟩ : syracuseStep 1245923 = 1868885) B1868885
theorem B3375857 : Blo 830350 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B1245953 : Blo 830350 1245953 := bstep (se 2 (by rfl) ⟨467232, by rfl⟩ : syracuseStep 1245953 = 934465) B934465
theorem B1868561 : Blo 830350 1868561 := bstep (se 2 (by rfl) ⟨700710, by rfl⟩ : syracuseStep 1868561 = 1401421) B1401421
theorem B1245971 : Blo 830350 1245971 := bstep (se 1 (by rfl) ⟨934478, by rfl⟩ : syracuseStep 1245971 = 1868957) B1868957
theorem B1868579 : Blo 830350 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1246001 : Blo 830350 1246001 := bstep (se 2 (by rfl) ⟨467250, by rfl⟩ : syracuseStep 1246001 = 934501) B934501
theorem B1246019 : Blo 830350 1246019 := bstep (se 1 (by rfl) ⟨934514, by rfl⟩ : syracuseStep 1246019 = 1869029) B1869029
theorem B1246049 : Blo 830350 1246049 := bstep (se 2 (by rfl) ⟨467268, by rfl⟩ : syracuseStep 1246049 = 934537) B934537
theorem B1246067 : Blo 830350 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B1246097 : Blo 830350 1246097 := bstep (se 2 (by rfl) ⟨467286, by rfl⟩ : syracuseStep 1246097 = 934573) B934573
theorem B1246115 : Blo 830350 1246115 := bstep (se 1 (by rfl) ⟨934586, by rfl⟩ : syracuseStep 1246115 = 1869173) B1869173
theorem B1246145 : Blo 830350 1246145 := bstep (se 2 (by rfl) ⟨467304, by rfl⟩ : syracuseStep 1246145 = 934609) B934609
theorem B1246163 : Blo 830350 1246163 := bstep (se 1 (by rfl) ⟨934622, by rfl⟩ : syracuseStep 1246163 = 1869245) B1869245
theorem B1246193 : Blo 830350 1246193 := bstep (se 2 (by rfl) ⟨467322, by rfl⟩ : syracuseStep 1246193 = 934645) B934645
theorem B1246211 : Blo 830350 1246211 := bstep (se 1 (by rfl) ⟨934658, by rfl⟩ : syracuseStep 1246211 = 1869317) B1869317
theorem B1246241 : Blo 830350 1246241 := bstep (se 2 (by rfl) ⟨467340, by rfl⟩ : syracuseStep 1246241 = 934681) B934681
theorem B1868849 : Blo 830350 1868849 := bstep (se 2 (by rfl) ⟨700818, by rfl⟩ : syracuseStep 1868849 = 1401637) B1401637
theorem B1246259 : Blo 830350 1246259 := bstep (se 1 (by rfl) ⟨934694, by rfl⟩ : syracuseStep 1246259 = 1869389) B1869389
theorem B1868867 : Blo 830350 1868867 := bstep (se 1 (by rfl) ⟨1401650, by rfl⟩ : syracuseStep 1868867 = 2803301) B2803301
theorem B1246289 : Blo 830350 1246289 := bstep (se 2 (by rfl) ⟨467358, by rfl⟩ : syracuseStep 1246289 = 934717) B934717
theorem B1246307 : Blo 830350 1246307 := bstep (se 1 (by rfl) ⟨934730, by rfl⟩ : syracuseStep 1246307 = 1869461) B1869461
theorem B1246337 : Blo 830350 1246337 := bstep (se 2 (by rfl) ⟨467376, by rfl⟩ : syracuseStep 1246337 = 934753) B934753
theorem B1246355 : Blo 830350 1246355 := bstep (se 1 (by rfl) ⟨934766, by rfl⟩ : syracuseStep 1246355 = 1869533) B1869533
theorem B2131121 : Blo 830350 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B4490417 : Blo 830350 4490417 := bstep (se 2 (by rfl) ⟨1683906, by rfl⟩ : syracuseStep 4490417 = 3367813) B3367813
theorem B1246385 : Blo 830350 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B1246403 : Blo 830350 1246403 := bstep (se 1 (by rfl) ⟨934802, by rfl⟩ : syracuseStep 1246403 = 1869605) B1869605
theorem B1246433 : Blo 830350 1246433 := bstep (se 2 (by rfl) ⟨467412, by rfl⟩ : syracuseStep 1246433 = 934825) B934825
theorem B1246451 : Blo 830350 1246451 := bstep (se 1 (by rfl) ⟨934838, by rfl⟩ : syracuseStep 1246451 = 1869677) B1869677
theorem B1246481 : Blo 830350 1246481 := bstep (se 2 (by rfl) ⟨467430, by rfl⟩ : syracuseStep 1246481 = 934861) B934861
theorem B1246499 : Blo 830350 1246499 := bstep (se 1 (by rfl) ⟨934874, by rfl⟩ : syracuseStep 1246499 = 1869749) B1869749
theorem B1246529 : Blo 830350 1246529 := bstep (se 2 (by rfl) ⟨467448, by rfl⟩ : syracuseStep 1246529 = 934897) B934897
theorem B1869137 : Blo 830350 1869137 := bstep (se 2 (by rfl) ⟨700926, by rfl⟩ : syracuseStep 1869137 = 1401853) B1401853
theorem B2000209 : Blo 830350 2000209 := bstep (se 2 (by rfl) ⟨750078, by rfl⟩ : syracuseStep 2000209 = 1500157) B1500157
theorem B1246547 : Blo 830350 1246547 := bstep (se 1 (by rfl) ⟨934910, by rfl⟩ : syracuseStep 1246547 = 1869821) B1869821
theorem B1869155 : Blo 830350 1869155 := bstep (se 1 (by rfl) ⟨1401866, by rfl⟩ : syracuseStep 1869155 = 2803733) B2803733
theorem B1246577 : Blo 830350 1246577 := bstep (se 2 (by rfl) ⟨467466, by rfl⟩ : syracuseStep 1246577 = 934933) B934933
theorem B1246595 : Blo 830350 1246595 := bstep (se 1 (by rfl) ⟨934946, by rfl⟩ : syracuseStep 1246595 = 1869893) B1869893
theorem B1246625 : Blo 830350 1246625 := bstep (se 2 (by rfl) ⟨467484, by rfl⟩ : syracuseStep 1246625 = 934969) B934969
theorem B1901987 : Blo 830350 1901987 := bstep (se 1 (by rfl) ⟨1426490, by rfl⟩ : syracuseStep 1901987 = 2852981) B2852981
theorem B1246643 : Blo 830350 1246643 := bstep (se 1 (by rfl) ⟨934982, by rfl⟩ : syracuseStep 1246643 = 1869965) B1869965
theorem B1246673 : Blo 830350 1246673 := bstep (se 2 (by rfl) ⟨467502, by rfl⟩ : syracuseStep 1246673 = 935005) B935005
theorem B1246691 : Blo 830350 1246691 := bstep (se 1 (by rfl) ⟨935018, by rfl⟩ : syracuseStep 1246691 = 1870037) B1870037
theorem B5342705 : Blo 830350 5342705 := bstep (se 2 (by rfl) ⟨2003514, by rfl⟩ : syracuseStep 5342705 = 4007029) B4007029
theorem B1246721 : Blo 830350 1246721 := bstep (se 2 (by rfl) ⟨467520, by rfl⟩ : syracuseStep 1246721 = 935041) B935041
theorem B1246739 : Blo 830350 1246739 := bstep (se 1 (by rfl) ⟨935054, by rfl⟩ : syracuseStep 1246739 = 1870109) B1870109
theorem B1246769 : Blo 830350 1246769 := bstep (se 2 (by rfl) ⟨467538, by rfl⟩ : syracuseStep 1246769 = 935077) B935077
theorem B1246787 : Blo 830350 1246787 := bstep (se 1 (by rfl) ⟨935090, by rfl⟩ : syracuseStep 1246787 = 1870181) B1870181
theorem B1246817 : Blo 830350 1246817 := bstep (se 2 (by rfl) ⟨467556, by rfl⟩ : syracuseStep 1246817 = 935113) B935113
theorem B1869425 : Blo 830350 1869425 := bstep (se 2 (by rfl) ⟨701034, by rfl⟩ : syracuseStep 1869425 = 1402069) B1402069
theorem B1246835 : Blo 830350 1246835 := bstep (se 1 (by rfl) ⟨935126, by rfl⟩ : syracuseStep 1246835 = 1870253) B1870253
theorem B1869443 : Blo 830350 1869443 := bstep (se 1 (by rfl) ⟨1402082, by rfl⟩ : syracuseStep 1869443 = 2804165) B2804165
theorem B1246865 : Blo 830350 1246865 := bstep (se 2 (by rfl) ⟨467574, by rfl⟩ : syracuseStep 1246865 = 935149) B935149
theorem B1246883 : Blo 830350 1246883 := bstep (se 1 (by rfl) ⟨935162, by rfl⟩ : syracuseStep 1246883 = 1870325) B1870325
theorem B5703331 : Blo 830350 5703331 := bstep (se 1 (by rfl) ⟨4277498, by rfl⟩ : syracuseStep 5703331 = 8554997) B8554997
theorem B1246913 : Blo 830350 1246913 := bstep (se 2 (by rfl) ⟨467592, by rfl⟩ : syracuseStep 1246913 = 935185) B935185
theorem B1246931 : Blo 830350 1246931 := bstep (se 1 (by rfl) ⟨935198, by rfl⟩ : syracuseStep 1246931 = 1870397) B1870397
theorem B1246961 : Blo 830350 1246961 := bstep (se 2 (by rfl) ⟨467610, by rfl⟩ : syracuseStep 1246961 = 935221) B935221
theorem B1246979 : Blo 830350 1246979 := bstep (se 1 (by rfl) ⟨935234, by rfl⟩ : syracuseStep 1246979 = 1870469) B1870469
theorem B11405069 : Blo 830350 11405069 := bstep (se 3 (by rfl) ⟨2138450, by rfl⟩ : syracuseStep 11405069 = 4276901) B4276901
theorem B1247009 : Blo 830350 1247009 := bstep (se 2 (by rfl) ⟨467628, by rfl⟩ : syracuseStep 1247009 = 935257) B935257
theorem B1247027 : Blo 830350 1247027 := bstep (se 1 (by rfl) ⟨935270, by rfl⟩ : syracuseStep 1247027 = 1870541) B1870541
theorem B1247057 : Blo 830350 1247057 := bstep (se 2 (by rfl) ⟨467646, by rfl⟩ : syracuseStep 1247057 = 935293) B935293
theorem B1247075 : Blo 830350 1247075 := bstep (se 1 (by rfl) ⟨935306, by rfl⟩ : syracuseStep 1247075 = 1870613) B1870613
theorem B1247105 : Blo 830350 1247105 := bstep (se 2 (by rfl) ⟨467664, by rfl⟩ : syracuseStep 1247105 = 935329) B935329
theorem B1869713 : Blo 830350 1869713 := bstep (se 2 (by rfl) ⟨701142, by rfl⟩ : syracuseStep 1869713 = 1402285) B1402285
theorem B1247123 : Blo 830350 1247123 := bstep (se 1 (by rfl) ⟨935342, by rfl⟩ : syracuseStep 1247123 = 1870685) B1870685
theorem B1869731 : Blo 830350 1869731 := bstep (se 1 (by rfl) ⟨1402298, by rfl⟩ : syracuseStep 1869731 = 2804597) B2804597
theorem B1247153 : Blo 830350 1247153 := bstep (se 2 (by rfl) ⟨467682, by rfl⟩ : syracuseStep 1247153 = 935365) B935365
theorem B1247171 : Blo 830350 1247171 := bstep (se 1 (by rfl) ⟨935378, by rfl⟩ : syracuseStep 1247171 = 1870757) B1870757
theorem B1247201 : Blo 830350 1247201 := bstep (se 2 (by rfl) ⟨467700, by rfl⟩ : syracuseStep 1247201 = 935401) B935401
theorem B1247219 : Blo 830350 1247219 := bstep (se 1 (by rfl) ⟨935414, by rfl⟩ : syracuseStep 1247219 = 1870829) B1870829
theorem B1247249 : Blo 830350 1247249 := bstep (se 2 (by rfl) ⟨467718, by rfl⟩ : syracuseStep 1247249 = 935437) B935437
theorem B1247267 : Blo 830350 1247267 := bstep (se 1 (by rfl) ⟨935450, by rfl⟩ : syracuseStep 1247267 = 1870901) B1870901
theorem B1247297 : Blo 830350 1247297 := bstep (se 2 (by rfl) ⟨467736, by rfl⟩ : syracuseStep 1247297 = 935473) B935473
theorem B1247315 : Blo 830350 1247315 := bstep (se 1 (by rfl) ⟨935486, by rfl⟩ : syracuseStep 1247315 = 1870973) B1870973
theorem B1247345 : Blo 830350 1247345 := bstep (se 2 (by rfl) ⟨467754, by rfl⟩ : syracuseStep 1247345 = 935509) B935509
theorem B1247363 : Blo 830350 1247363 := bstep (se 1 (by rfl) ⟨935522, by rfl⟩ : syracuseStep 1247363 = 1871045) B1871045
theorem B1607825 : Blo 830350 1607825 := bstep (se 2 (by rfl) ⟨602934, by rfl⟩ : syracuseStep 1607825 = 1205869) B1205869
theorem B1247393 : Blo 830350 1247393 := bstep (se 2 (by rfl) ⟨467772, by rfl⟩ : syracuseStep 1247393 = 935545) B935545
theorem B1870001 : Blo 830350 1870001 := bstep (se 2 (by rfl) ⟨701250, by rfl⟩ : syracuseStep 1870001 = 1402501) B1402501
theorem B1247411 : Blo 830350 1247411 := bstep (se 1 (by rfl) ⟨935558, by rfl⟩ : syracuseStep 1247411 = 1871117) B1871117
theorem B1870019 : Blo 830350 1870019 := bstep (se 1 (by rfl) ⟨1402514, by rfl⟩ : syracuseStep 1870019 = 2805029) B2805029
theorem B1247441 : Blo 830350 1247441 := bstep (se 2 (by rfl) ⟨467790, by rfl⟩ : syracuseStep 1247441 = 935581) B935581
theorem B1247459 : Blo 830350 1247459 := bstep (se 1 (by rfl) ⟨935594, by rfl⟩ : syracuseStep 1247459 = 1871189) B1871189
theorem B1247489 : Blo 830350 1247489 := bstep (se 2 (by rfl) ⟨467808, by rfl⟩ : syracuseStep 1247489 = 935617) B935617
theorem B1247507 : Blo 830350 1247507 := bstep (se 1 (by rfl) ⟨935630, by rfl⟩ : syracuseStep 1247507 = 1871261) B1871261
theorem B1247537 : Blo 830350 1247537 := bstep (se 2 (by rfl) ⟨467826, by rfl⟩ : syracuseStep 1247537 = 935653) B935653
theorem B1247555 : Blo 830350 1247555 := bstep (se 1 (by rfl) ⟨935666, by rfl⟩ : syracuseStep 1247555 = 1871333) B1871333
theorem B1247585 : Blo 830350 1247585 := bstep (se 2 (by rfl) ⟨467844, by rfl⟩ : syracuseStep 1247585 = 935689) B935689
theorem B1050995 : Blo 830350 1050995 := bstep (se 1 (by rfl) ⟨788246, by rfl⟩ : syracuseStep 1050995 = 1576493) B1576493
theorem B1247603 : Blo 830350 1247603 := bstep (se 1 (by rfl) ⟨935702, by rfl⟩ : syracuseStep 1247603 = 1871405) B1871405
theorem B1247633 : Blo 830350 1247633 := bstep (se 2 (by rfl) ⟨467862, by rfl⟩ : syracuseStep 1247633 = 935725) B935725
theorem B2853265 : Blo 830350 2853265 := bstep (se 2 (by rfl) ⟨1069974, by rfl⟩ : syracuseStep 2853265 = 2139949) B2139949
theorem B1247651 : Blo 830350 1247651 := bstep (se 1 (by rfl) ⟨935738, by rfl⟩ : syracuseStep 1247651 = 1871477) B1871477
theorem B11372981 : Blo 830350 11372981 := bstep (se 5 (by rfl) ⟨533108, by rfl⟩ : syracuseStep 11372981 = 1066217) B1066217
theorem B1247681 : Blo 830350 1247681 := bstep (se 2 (by rfl) ⟨467880, by rfl⟩ : syracuseStep 1247681 = 935761) B935761
theorem B1870289 : Blo 830350 1870289 := bstep (se 2 (by rfl) ⟨701358, by rfl⟩ : syracuseStep 1870289 = 1402717) B1402717
theorem B1247699 : Blo 830350 1247699 := bstep (se 1 (by rfl) ⟨935774, by rfl⟩ : syracuseStep 1247699 = 1871549) B1871549
theorem B1870307 : Blo 830350 1870307 := bstep (se 1 (by rfl) ⟨1402730, by rfl⟩ : syracuseStep 1870307 = 2805461) B2805461
theorem B1247729 : Blo 830350 1247729 := bstep (se 2 (by rfl) ⟨467898, by rfl⟩ : syracuseStep 1247729 = 935797) B935797
theorem B1247747 : Blo 830350 1247747 := bstep (se 1 (by rfl) ⟨935810, by rfl⟩ : syracuseStep 1247747 = 1871621) B1871621
theorem B1247777 : Blo 830350 1247777 := bstep (se 2 (by rfl) ⟨467916, by rfl⟩ : syracuseStep 1247777 = 935833) B935833
theorem B1247795 : Blo 830350 1247795 := bstep (se 1 (by rfl) ⟨935846, by rfl⟩ : syracuseStep 1247795 = 1871693) B1871693
theorem B1247825 : Blo 830350 1247825 := bstep (se 2 (by rfl) ⟨467934, by rfl⟩ : syracuseStep 1247825 = 935869) B935869
theorem B1247843 : Blo 830350 1247843 := bstep (se 1 (by rfl) ⟨935882, by rfl⟩ : syracuseStep 1247843 = 1871765) B1871765
theorem B9472625 : Blo 830350 9472625 := bstep (se 2 (by rfl) ⟨3552234, by rfl⟩ : syracuseStep 9472625 = 7104469) B7104469
theorem B7998065 : Blo 830350 7998065 := bstep (se 2 (by rfl) ⟨2999274, by rfl⟩ : syracuseStep 7998065 = 5998549) B5998549
theorem B1247873 : Blo 830350 1247873 := bstep (se 2 (by rfl) ⟨467952, by rfl⟩ : syracuseStep 1247873 = 935905) B935905
theorem B1247891 : Blo 830350 1247891 := bstep (se 1 (by rfl) ⟨935918, by rfl⟩ : syracuseStep 1247891 = 1871837) B1871837
theorem B1247921 : Blo 830350 1247921 := bstep (se 2 (by rfl) ⟨467970, by rfl⟩ : syracuseStep 1247921 = 935941) B935941
theorem B1247939 : Blo 830350 1247939 := bstep (se 1 (by rfl) ⟨935954, by rfl⟩ : syracuseStep 1247939 = 1871909) B1871909
theorem B1182433 : Blo 830350 1182433 := bstep (se 2 (by rfl) ⟨443412, by rfl⟩ : syracuseStep 1182433 = 886825) B886825
theorem B1247969 : Blo 830350 1247969 := bstep (se 2 (by rfl) ⟨467988, by rfl⟩ : syracuseStep 1247969 = 935977) B935977
theorem B1870577 : Blo 830350 1870577 := bstep (se 2 (by rfl) ⟨701466, by rfl⟩ : syracuseStep 1870577 = 1402933) B1402933
theorem B1247987 : Blo 830350 1247987 := bstep (se 1 (by rfl) ⟨935990, by rfl⟩ : syracuseStep 1247987 = 1871981) B1871981
theorem B887555 : Blo 830350 887555 := bstep (se 1 (by rfl) ⟨665666, by rfl⟩ : syracuseStep 887555 = 1331333) B1331333
theorem B1870595 : Blo 830350 1870595 := bstep (se 1 (by rfl) ⟨1402946, by rfl⟩ : syracuseStep 1870595 = 2805893) B2805893
theorem B1248017 : Blo 830350 1248017 := bstep (se 2 (by rfl) ⟨468006, by rfl⟩ : syracuseStep 1248017 = 936013) B936013
theorem B1248035 : Blo 830350 1248035 := bstep (se 1 (by rfl) ⟨936026, by rfl⟩ : syracuseStep 1248035 = 1872053) B1872053
theorem B1182529 : Blo 830350 1182529 := bstep (se 2 (by rfl) ⟨443448, by rfl⟩ : syracuseStep 1182529 = 886897) B886897
theorem B1248065 : Blo 830350 1248065 := bstep (se 2 (by rfl) ⟨468024, by rfl⟩ : syracuseStep 1248065 = 936049) B936049
theorem B1248083 : Blo 830350 1248083 := bstep (se 1 (by rfl) ⟨936062, by rfl⟩ : syracuseStep 1248083 = 1872125) B1872125
theorem B1248113 : Blo 830350 1248113 := bstep (se 2 (by rfl) ⟨468042, by rfl⟩ : syracuseStep 1248113 = 936085) B936085
theorem B887683 : Blo 830350 887683 := bstep (se 1 (by rfl) ⟨665762, by rfl⟩ : syracuseStep 887683 = 1331525) B1331525
theorem B1248131 : Blo 830350 1248131 := bstep (se 1 (by rfl) ⟨936098, by rfl⟩ : syracuseStep 1248131 = 1872197) B1872197
theorem B1248161 : Blo 830350 1248161 := bstep (se 2 (by rfl) ⟨468060, by rfl⟩ : syracuseStep 1248161 = 936121) B936121
theorem B1248179 : Blo 830350 1248179 := bstep (se 1 (by rfl) ⟨936134, by rfl⟩ : syracuseStep 1248179 = 1872269) B1872269
theorem B1248209 : Blo 830350 1248209 := bstep (se 2 (by rfl) ⟨468078, by rfl⟩ : syracuseStep 1248209 = 936157) B936157
theorem B1248227 : Blo 830350 1248227 := bstep (se 1 (by rfl) ⟨936170, by rfl⟩ : syracuseStep 1248227 = 1872341) B1872341
theorem B3804131 : Blo 830350 3804131 := bstep (se 1 (by rfl) ⟨2853098, by rfl⟩ : syracuseStep 3804131 = 5706197) B5706197
theorem B1248257 : Blo 830350 1248257 := bstep (se 2 (by rfl) ⟨468096, by rfl⟩ : syracuseStep 1248257 = 936193) B936193
theorem B1870865 : Blo 830350 1870865 := bstep (se 2 (by rfl) ⟨701574, by rfl⟩ : syracuseStep 1870865 = 1403149) B1403149
theorem B1248275 : Blo 830350 1248275 := bstep (se 1 (by rfl) ⟨936206, by rfl⟩ : syracuseStep 1248275 = 1872413) B1872413
theorem B1870883 : Blo 830350 1870883 := bstep (se 1 (by rfl) ⟨1403162, by rfl⟩ : syracuseStep 1870883 = 2806325) B2806325
theorem B1248305 : Blo 830350 1248305 := bstep (se 2 (by rfl) ⟨468114, by rfl⟩ : syracuseStep 1248305 = 936229) B936229
theorem B1051699 : Blo 830350 1051699 := bstep (se 1 (by rfl) ⟨788774, by rfl⟩ : syracuseStep 1051699 = 1577549) B1577549
theorem B1248323 : Blo 830350 1248323 := bstep (se 1 (by rfl) ⟨936242, by rfl⟩ : syracuseStep 1248323 = 1872485) B1872485
theorem B1248353 : Blo 830350 1248353 := bstep (se 2 (by rfl) ⟨468132, by rfl⟩ : syracuseStep 1248353 = 936265) B936265
theorem B1248371 : Blo 830350 1248371 := bstep (se 1 (by rfl) ⟨936278, by rfl⟩ : syracuseStep 1248371 = 1872557) B1872557
theorem B1248401 : Blo 830350 1248401 := bstep (se 2 (by rfl) ⟨468150, by rfl⟩ : syracuseStep 1248401 = 936301) B936301
theorem B1051795 : Blo 830350 1051795 := bstep (se 1 (by rfl) ⟨788846, by rfl⟩ : syracuseStep 1051795 = 1577693) B1577693
theorem B1248419 : Blo 830350 1248419 := bstep (se 1 (by rfl) ⟨936314, by rfl⟩ : syracuseStep 1248419 = 1872629) B1872629
theorem B1248449 : Blo 830350 1248449 := bstep (se 2 (by rfl) ⟨468168, by rfl⟩ : syracuseStep 1248449 = 936337) B936337
theorem B4492493 : Blo 830350 4492493 := bstep (se 3 (by rfl) ⟨842342, by rfl⟩ : syracuseStep 4492493 = 1684685) B1684685
theorem B1248467 : Blo 830350 1248467 := bstep (se 1 (by rfl) ⟨936350, by rfl⟩ : syracuseStep 1248467 = 1872701) B1872701
theorem B1248497 : Blo 830350 1248497 := bstep (se 2 (by rfl) ⟨468186, by rfl⟩ : syracuseStep 1248497 = 936373) B936373
theorem B1248515 : Blo 830350 1248515 := bstep (se 1 (by rfl) ⟨936386, by rfl⟩ : syracuseStep 1248515 = 1872773) B1872773
theorem B1248545 : Blo 830350 1248545 := bstep (se 2 (by rfl) ⟨468204, by rfl⟩ : syracuseStep 1248545 = 936409) B936409
theorem B1183025 : Blo 830350 1183025 := bstep (se 2 (by rfl) ⟨443634, by rfl⟩ : syracuseStep 1183025 = 887269) B887269
theorem B1871153 : Blo 830350 1871153 := bstep (se 2 (by rfl) ⟨701682, by rfl⟩ : syracuseStep 1871153 = 1403365) B1403365
theorem B1248563 : Blo 830350 1248563 := bstep (se 1 (by rfl) ⟨936422, by rfl⟩ : syracuseStep 1248563 = 1872845) B1872845
theorem B1871171 : Blo 830350 1871171 := bstep (se 1 (by rfl) ⟨1403378, by rfl⟩ : syracuseStep 1871171 = 2806757) B2806757
theorem B1248593 : Blo 830350 1248593 := bstep (se 2 (by rfl) ⟨468222, by rfl⟩ : syracuseStep 1248593 = 936445) B936445
theorem B1248611 : Blo 830350 1248611 := bstep (se 1 (by rfl) ⟨936458, by rfl⟩ : syracuseStep 1248611 = 1872917) B1872917
theorem B8981873 : Blo 830350 8981873 := bstep (se 2 (by rfl) ⟨3368202, by rfl⟩ : syracuseStep 8981873 = 6736405) B6736405
theorem B1248641 : Blo 830350 1248641 := bstep (se 2 (by rfl) ⟨468240, by rfl⟩ : syracuseStep 1248641 = 936481) B936481
theorem B1248659 : Blo 830350 1248659 := bstep (se 1 (by rfl) ⟨936494, by rfl⟩ : syracuseStep 1248659 = 1872989) B1872989
theorem B3378595 : Blo 830350 3378595 := bstep (se 1 (by rfl) ⟨2533946, by rfl⟩ : syracuseStep 3378595 = 5067893) B5067893
theorem B1248689 : Blo 830350 1248689 := bstep (se 2 (by rfl) ⟨468258, by rfl⟩ : syracuseStep 1248689 = 936517) B936517
theorem B1248707 : Blo 830350 1248707 := bstep (se 1 (by rfl) ⟨936530, by rfl⟩ : syracuseStep 1248707 = 1873061) B1873061
theorem B855491 : Blo 830350 855491 := bstep (se 1 (by rfl) ⟨641618, by rfl⟩ : syracuseStep 855491 = 1283237) B1283237
theorem B1248737 : Blo 830350 1248737 := bstep (se 2 (by rfl) ⟨468276, by rfl⟩ : syracuseStep 1248737 = 936553) B936553
theorem B1248755 : Blo 830350 1248755 := bstep (se 1 (by rfl) ⟨936566, by rfl⟩ : syracuseStep 1248755 = 1873133) B1873133
theorem B1248785 : Blo 830350 1248785 := bstep (se 2 (by rfl) ⟨468294, by rfl⟩ : syracuseStep 1248785 = 936589) B936589
theorem B1248803 : Blo 830350 1248803 := bstep (se 1 (by rfl) ⟨936602, by rfl⟩ : syracuseStep 1248803 = 1873205) B1873205
theorem B1248833 : Blo 830350 1248833 := bstep (se 2 (by rfl) ⟨468312, by rfl⟩ : syracuseStep 1248833 = 936625) B936625
theorem B1871441 : Blo 830350 1871441 := bstep (se 2 (by rfl) ⟨701790, by rfl⟩ : syracuseStep 1871441 = 1403581) B1403581
theorem B1248851 : Blo 830350 1248851 := bstep (se 1 (by rfl) ⟨936638, by rfl⟩ : syracuseStep 1248851 = 1873277) B1873277
theorem B1871459 : Blo 830350 1871459 := bstep (se 1 (by rfl) ⟨1403594, by rfl⟩ : syracuseStep 1871459 = 2807189) B2807189
theorem B1248881 : Blo 830350 1248881 := bstep (se 2 (by rfl) ⟨468330, by rfl⟩ : syracuseStep 1248881 = 936661) B936661
theorem B1052291 : Blo 830350 1052291 := bstep (se 1 (by rfl) ⟨789218, by rfl⟩ : syracuseStep 1052291 = 1578437) B1578437
theorem B1248899 : Blo 830350 1248899 := bstep (se 1 (by rfl) ⟨936674, by rfl⟩ : syracuseStep 1248899 = 1873349) B1873349
theorem B1248929 : Blo 830350 1248929 := bstep (se 2 (by rfl) ⟨468348, by rfl⟩ : syracuseStep 1248929 = 936697) B936697
theorem B2526893 : Blo 830350 2526893 := bstep (se 3 (by rfl) ⟨473792, by rfl⟩ : syracuseStep 2526893 = 947585) B947585
theorem B888499 : Blo 830350 888499 := bstep (se 1 (by rfl) ⟨666374, by rfl⟩ : syracuseStep 888499 = 1332749) B1332749
theorem B1248947 : Blo 830350 1248947 := bstep (se 1 (by rfl) ⟨936710, by rfl⟩ : syracuseStep 1248947 = 1873421) B1873421
theorem B1248977 : Blo 830350 1248977 := bstep (se 2 (by rfl) ⟨468366, by rfl⟩ : syracuseStep 1248977 = 936733) B936733
theorem B1576675 : Blo 830350 1576675 := bstep (se 1 (by rfl) ⟨1182506, by rfl⟩ : syracuseStep 1576675 = 2365013) B2365013
theorem B1248995 : Blo 830350 1248995 := bstep (se 1 (by rfl) ⟨936746, by rfl⟩ : syracuseStep 1248995 = 1873493) B1873493
theorem B1249025 : Blo 830350 1249025 := bstep (se 2 (by rfl) ⟨468384, by rfl⟩ : syracuseStep 1249025 = 936769) B936769
theorem B1576721 : Blo 830350 1576721 := bstep (se 2 (by rfl) ⟨591270, by rfl⟩ : syracuseStep 1576721 = 1182541) B1182541
theorem B1249043 : Blo 830350 1249043 := bstep (se 1 (by rfl) ⟨936782, by rfl⟩ : syracuseStep 1249043 = 1873565) B1873565
theorem B1249073 : Blo 830350 1249073 := bstep (se 2 (by rfl) ⟨468402, by rfl⟩ : syracuseStep 1249073 = 936805) B936805
theorem B1249091 : Blo 830350 1249091 := bstep (se 1 (by rfl) ⟨936818, by rfl⟩ : syracuseStep 1249091 = 1873637) B1873637
theorem B1249121 : Blo 830350 1249121 := bstep (se 2 (by rfl) ⟨468420, by rfl⟩ : syracuseStep 1249121 = 936841) B936841
theorem B1871729 : Blo 830350 1871729 := bstep (se 2 (by rfl) ⟨701898, by rfl⟩ : syracuseStep 1871729 = 1403797) B1403797
theorem B1249139 : Blo 830350 1249139 := bstep (se 1 (by rfl) ⟨936854, by rfl⟩ : syracuseStep 1249139 = 1873709) B1873709
theorem B1871747 : Blo 830350 1871747 := bstep (se 1 (by rfl) ⟨1403810, by rfl⟩ : syracuseStep 1871747 = 2807621) B2807621
theorem B6328205 : Blo 830350 6328205 := bstep (se 3 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 6328205 = 2373077) B2373077
theorem B5345165 : Blo 830350 5345165 := bstep (se 3 (by rfl) ⟨1002218, by rfl⟩ : syracuseStep 5345165 = 2004437) B2004437
theorem B1249169 : Blo 830350 1249169 := bstep (se 2 (by rfl) ⟨468438, by rfl⟩ : syracuseStep 1249169 = 936877) B936877
theorem B1249187 : Blo 830350 1249187 := bstep (se 1 (by rfl) ⟨936890, by rfl⟩ : syracuseStep 1249187 = 1873781) B1873781
theorem B1249217 : Blo 830350 1249217 := bstep (se 2 (by rfl) ⟨468456, by rfl⟩ : syracuseStep 1249217 = 936913) B936913
theorem B1249235 : Blo 830350 1249235 := bstep (se 1 (by rfl) ⟨936926, by rfl⟩ : syracuseStep 1249235 = 1873853) B1873853
theorem B1249265 : Blo 830350 1249265 := bstep (se 2 (by rfl) ⟨468474, by rfl⟩ : syracuseStep 1249265 = 936949) B936949
theorem B1249283 : Blo 830350 1249283 := bstep (se 1 (by rfl) ⟨936962, by rfl⟩ : syracuseStep 1249283 = 1873925) B1873925
theorem B1249313 : Blo 830350 1249313 := bstep (se 2 (by rfl) ⟨468492, by rfl⟩ : syracuseStep 1249313 = 936985) B936985
theorem B1577009 : Blo 830350 1577009 := bstep (se 2 (by rfl) ⟨591378, by rfl⟩ : syracuseStep 1577009 = 1182757) B1182757
theorem B1249331 : Blo 830350 1249331 := bstep (se 1 (by rfl) ⟨936998, by rfl⟩ : syracuseStep 1249331 = 1873997) B1873997
theorem B1249361 : Blo 830350 1249361 := bstep (se 2 (by rfl) ⟨468510, by rfl⟩ : syracuseStep 1249361 = 937021) B937021
theorem B1249379 : Blo 830350 1249379 := bstep (se 1 (by rfl) ⟨937034, by rfl⟩ : syracuseStep 1249379 = 1874069) B1874069
theorem B1249409 : Blo 830350 1249409 := bstep (se 2 (by rfl) ⟨468528, by rfl⟩ : syracuseStep 1249409 = 937057) B937057
theorem B1216657 : Blo 830350 1216657 := bstep (se 2 (by rfl) ⟨456246, by rfl⟩ : syracuseStep 1216657 = 912493) B912493
theorem B1872017 : Blo 830350 1872017 := bstep (se 2 (by rfl) ⟨702006, by rfl⟩ : syracuseStep 1872017 = 1404013) B1404013
theorem B1183891 : Blo 830350 1183891 := bstep (se 1 (by rfl) ⟨887918, by rfl⟩ : syracuseStep 1183891 = 1775837) B1775837
theorem B1249427 : Blo 830350 1249427 := bstep (se 1 (by rfl) ⟨937070, by rfl⟩ : syracuseStep 1249427 = 1874141) B1874141
theorem B1872035 : Blo 830350 1872035 := bstep (se 1 (by rfl) ⟨1404026, by rfl⟩ : syracuseStep 1872035 = 2808053) B2808053
theorem B1249457 : Blo 830350 1249457 := bstep (se 2 (by rfl) ⟨468546, by rfl⟩ : syracuseStep 1249457 = 937093) B937093
theorem B1249475 : Blo 830350 1249475 := bstep (se 1 (by rfl) ⟨937106, by rfl⟩ : syracuseStep 1249475 = 1874213) B1874213
theorem B1249505 : Blo 830350 1249505 := bstep (se 2 (by rfl) ⟨468564, by rfl⟩ : syracuseStep 1249505 = 937129) B937129
theorem B1183987 : Blo 830350 1183987 := bstep (se 1 (by rfl) ⟨887990, by rfl⟩ : syracuseStep 1183987 = 1775981) B1775981
theorem B1249523 : Blo 830350 1249523 := bstep (se 1 (by rfl) ⟨937142, by rfl⟩ : syracuseStep 1249523 = 1874285) B1874285
theorem B1249553 : Blo 830350 1249553 := bstep (se 2 (by rfl) ⟨468582, by rfl⟩ : syracuseStep 1249553 = 937165) B937165
theorem B1249571 : Blo 830350 1249571 := bstep (se 1 (by rfl) ⟨937178, by rfl⟩ : syracuseStep 1249571 = 1874357) B1874357
theorem B5050673 : Blo 830350 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B1249601 : Blo 830350 1249601 := bstep (se 2 (by rfl) ⟨468600, by rfl⟩ : syracuseStep 1249601 = 937201) B937201
theorem B1052995 : Blo 830350 1052995 := bstep (se 1 (by rfl) ⟨789746, by rfl⟩ : syracuseStep 1052995 = 1579493) B1579493
theorem B1249619 : Blo 830350 1249619 := bstep (se 1 (by rfl) ⟨937214, by rfl⟩ : syracuseStep 1249619 = 1874429) B1874429
theorem B1249649 : Blo 830350 1249649 := bstep (se 2 (by rfl) ⟨468618, by rfl⟩ : syracuseStep 1249649 = 937237) B937237
theorem B1249667 : Blo 830350 1249667 := bstep (se 1 (by rfl) ⟨937250, by rfl⟩ : syracuseStep 1249667 = 1874501) B1874501
theorem B1249697 : Blo 830350 1249697 := bstep (se 2 (by rfl) ⟨468636, by rfl⟩ : syracuseStep 1249697 = 937273) B937273
theorem B1053091 : Blo 830350 1053091 := bstep (se 1 (by rfl) ⟨789818, by rfl⟩ : syracuseStep 1053091 = 1579637) B1579637
theorem B1872305 : Blo 830350 1872305 := bstep (se 2 (by rfl) ⟨702114, by rfl⟩ : syracuseStep 1872305 = 1404229) B1404229
theorem B1249715 : Blo 830350 1249715 := bstep (se 1 (by rfl) ⟨937286, by rfl⟩ : syracuseStep 1249715 = 1874573) B1874573
theorem B1872323 : Blo 830350 1872323 := bstep (se 1 (by rfl) ⟨1404242, by rfl⟩ : syracuseStep 1872323 = 2808485) B2808485
theorem B1249745 : Blo 830350 1249745 := bstep (se 2 (by rfl) ⟨468654, by rfl⟩ : syracuseStep 1249745 = 937309) B937309
theorem B1282529 : Blo 830350 1282529 := bstep (se 2 (by rfl) ⟨480948, by rfl⟩ : syracuseStep 1282529 = 961897) B961897
theorem B1249763 : Blo 830350 1249763 := bstep (se 1 (by rfl) ⟨937322, by rfl⟩ : syracuseStep 1249763 = 1874645) B1874645
theorem B2888173 : Blo 830350 2888173 := bstep (se 3 (by rfl) ⟨541532, by rfl⟩ : syracuseStep 2888173 = 1083065) B1083065
theorem B1249793 : Blo 830350 1249793 := bstep (se 2 (by rfl) ⟨468672, by rfl⟩ : syracuseStep 1249793 = 937345) B937345
theorem B1249811 : Blo 830350 1249811 := bstep (se 1 (by rfl) ⟨937358, by rfl⟩ : syracuseStep 1249811 = 1874717) B1874717
theorem B1249841 : Blo 830350 1249841 := bstep (se 2 (by rfl) ⟨468690, by rfl⟩ : syracuseStep 1249841 = 937381) B937381
theorem B1249859 : Blo 830350 1249859 := bstep (se 1 (by rfl) ⟨937394, by rfl⟩ : syracuseStep 1249859 = 1874789) B1874789
theorem B1249889 : Blo 830350 1249889 := bstep (se 2 (by rfl) ⟨468708, by rfl⟩ : syracuseStep 1249889 = 937417) B937417
theorem B2101859 : Blo 830350 2101859 := bstep (se 1 (by rfl) ⟨1576394, by rfl⟩ : syracuseStep 2101859 = 3152789) B3152789
theorem B9015907 : Blo 830350 9015907 := bstep (se 1 (by rfl) ⟨6761930, by rfl⟩ : syracuseStep 9015907 = 13523861) B13523861
theorem B1249907 : Blo 830350 1249907 := bstep (se 1 (by rfl) ⟨937430, by rfl⟩ : syracuseStep 1249907 = 1874861) B1874861
theorem B1249937 : Blo 830350 1249937 := bstep (se 2 (by rfl) ⟨468726, by rfl⟩ : syracuseStep 1249937 = 937453) B937453
theorem B1249955 : Blo 830350 1249955 := bstep (se 1 (by rfl) ⟨937466, by rfl⟩ : syracuseStep 1249955 = 1874933) B1874933
theorem B1249985 : Blo 830350 1249985 := bstep (se 2 (by rfl) ⟨468744, by rfl⟩ : syracuseStep 1249985 = 937489) B937489
theorem B1872593 : Blo 830350 1872593 := bstep (se 2 (by rfl) ⟨702222, by rfl⟩ : syracuseStep 1872593 = 1404445) B1404445
theorem B1250003 : Blo 830350 1250003 := bstep (se 1 (by rfl) ⟨937502, by rfl⟩ : syracuseStep 1250003 = 1875005) B1875005
theorem B1774307 : Blo 830350 1774307 := bstep (se 1 (by rfl) ⟨1330730, by rfl⟩ : syracuseStep 1774307 = 2661461) B2661461
theorem B1184483 : Blo 830350 1184483 := bstep (se 1 (by rfl) ⟨888362, by rfl⟩ : syracuseStep 1184483 = 1776725) B1776725
theorem B1872611 : Blo 830350 1872611 := bstep (se 1 (by rfl) ⟨1404458, by rfl⟩ : syracuseStep 1872611 = 2808917) B2808917
theorem B1250033 : Blo 830350 1250033 := bstep (se 2 (by rfl) ⟨468762, by rfl⟩ : syracuseStep 1250033 = 937525) B937525
theorem B1577731 : Blo 830350 1577731 := bstep (se 1 (by rfl) ⟨1183298, by rfl⟩ : syracuseStep 1577731 = 2366597) B2366597
theorem B1250051 : Blo 830350 1250051 := bstep (se 1 (by rfl) ⟨937538, by rfl⟩ : syracuseStep 1250051 = 1875077) B1875077
theorem B1250081 : Blo 830350 1250081 := bstep (se 2 (by rfl) ⟨468780, by rfl⟩ : syracuseStep 1250081 = 937561) B937561
theorem B2102051 : Blo 830350 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B1250099 : Blo 830350 1250099 := bstep (se 1 (by rfl) ⟨937574, by rfl⟩ : syracuseStep 1250099 = 1875149) B1875149
theorem B1250129 : Blo 830350 1250129 := bstep (se 2 (by rfl) ⟨468798, by rfl⟩ : syracuseStep 1250129 = 937597) B937597
theorem B1250147 : Blo 830350 1250147 := bstep (se 1 (by rfl) ⟨937610, by rfl⟩ : syracuseStep 1250147 = 1875221) B1875221
theorem B1250177 : Blo 830350 1250177 := bstep (se 2 (by rfl) ⟨468816, by rfl⟩ : syracuseStep 1250177 = 937633) B937633
theorem B1053587 : Blo 830350 1053587 := bstep (se 1 (by rfl) ⟨790190, by rfl⟩ : syracuseStep 1053587 = 1580381) B1580381
theorem B1250195 : Blo 830350 1250195 := bstep (se 1 (by rfl) ⟨937646, by rfl⟩ : syracuseStep 1250195 = 1875293) B1875293
theorem B1250225 : Blo 830350 1250225 := bstep (se 2 (by rfl) ⟨468834, by rfl⟩ : syracuseStep 1250225 = 937669) B937669
theorem B1250243 : Blo 830350 1250243 := bstep (se 1 (by rfl) ⟨937682, by rfl⟩ : syracuseStep 1250243 = 1875365) B1875365
theorem B1250273 : Blo 830350 1250273 := bstep (se 2 (by rfl) ⟨468852, by rfl⟩ : syracuseStep 1250273 = 937705) B937705
theorem B1872881 : Blo 830350 1872881 := bstep (se 2 (by rfl) ⟨702330, by rfl⟩ : syracuseStep 1872881 = 1404661) B1404661
theorem B1250291 : Blo 830350 1250291 := bstep (se 1 (by rfl) ⟨937718, by rfl⟩ : syracuseStep 1250291 = 1875437) B1875437
theorem B1872899 : Blo 830350 1872899 := bstep (se 1 (by rfl) ⟨1404674, by rfl⟩ : syracuseStep 1872899 = 2809349) B2809349
theorem B8000525 : Blo 830350 8000525 := bstep (se 3 (by rfl) ⟨1500098, by rfl⟩ : syracuseStep 8000525 = 3000197) B3000197
theorem B1250321 : Blo 830350 1250321 := bstep (se 2 (by rfl) ⟨468870, by rfl⟩ : syracuseStep 1250321 = 937741) B937741
theorem B1250339 : Blo 830350 1250339 := bstep (se 1 (by rfl) ⟨937754, by rfl⟩ : syracuseStep 1250339 = 1875509) B1875509
theorem B1250369 : Blo 830350 1250369 := bstep (se 2 (by rfl) ⟨468888, by rfl⟩ : syracuseStep 1250369 = 937777) B937777
theorem B1250387 : Blo 830350 1250387 := bstep (se 1 (by rfl) ⟨937790, by rfl⟩ : syracuseStep 1250387 = 1875581) B1875581
theorem B1250417 : Blo 830350 1250417 := bstep (se 2 (by rfl) ⟨468906, by rfl⟩ : syracuseStep 1250417 = 937813) B937813
theorem B1250435 : Blo 830350 1250435 := bstep (se 1 (by rfl) ⟨937826, by rfl⟩ : syracuseStep 1250435 = 1875653) B1875653
theorem B1250465 : Blo 830350 1250465 := bstep (se 2 (by rfl) ⟨468924, by rfl⟩ : syracuseStep 1250465 = 937849) B937849
theorem B1250483 : Blo 830350 1250483 := bstep (se 1 (by rfl) ⟨937862, by rfl⟩ : syracuseStep 1250483 = 1875725) B1875725
theorem B1578179 : Blo 830350 1578179 := bstep (se 1 (by rfl) ⟨1183634, by rfl⟩ : syracuseStep 1578179 = 2367269) B2367269
theorem B1250513 : Blo 830350 1250513 := bstep (se 2 (by rfl) ⟨468942, by rfl⟩ : syracuseStep 1250513 = 937885) B937885
theorem B1774819 : Blo 830350 1774819 := bstep (se 1 (by rfl) ⟨1331114, by rfl⟩ : syracuseStep 1774819 = 2662229) B2662229
theorem B1250531 : Blo 830350 1250531 := bstep (se 1 (by rfl) ⟨937898, by rfl⟩ : syracuseStep 1250531 = 1875797) B1875797
theorem B1250561 : Blo 830350 1250561 := bstep (se 2 (by rfl) ⟨468960, by rfl⟩ : syracuseStep 1250561 = 937921) B937921
theorem B2004227 : Blo 830350 2004227 := bstep (se 1 (by rfl) ⟨1503170, by rfl⟩ : syracuseStep 2004227 = 3006341) B3006341
theorem B1873169 : Blo 830350 1873169 := bstep (se 2 (by rfl) ⟨702438, by rfl⟩ : syracuseStep 1873169 = 1404877) B1404877
theorem B1250579 : Blo 830350 1250579 := bstep (se 1 (by rfl) ⟨937934, by rfl⟩ : syracuseStep 1250579 = 1875869) B1875869
theorem B1873187 : Blo 830350 1873187 := bstep (se 1 (by rfl) ⟨1404890, by rfl⟩ : syracuseStep 1873187 = 2809781) B2809781
theorem B1250609 : Blo 830350 1250609 := bstep (se 2 (by rfl) ⟨468978, by rfl⟩ : syracuseStep 1250609 = 937957) B937957
theorem B1250627 : Blo 830350 1250627 := bstep (se 1 (by rfl) ⟨937970, by rfl⟩ : syracuseStep 1250627 = 1875941) B1875941
theorem B1185121 : Blo 830350 1185121 := bstep (se 2 (by rfl) ⟨444420, by rfl⟩ : syracuseStep 1185121 = 888841) B888841
theorem B1250657 : Blo 830350 1250657 := bstep (se 2 (by rfl) ⟨468996, by rfl⟩ : syracuseStep 1250657 = 937993) B937993
theorem B2364785 : Blo 830350 2364785 := bstep (se 2 (by rfl) ⟨886794, by rfl⟩ : syracuseStep 2364785 = 1773589) B1773589
theorem B1250675 : Blo 830350 1250675 := bstep (se 1 (by rfl) ⟨938006, by rfl⟩ : syracuseStep 1250675 = 1876013) B1876013
theorem B1250705 : Blo 830350 1250705 := bstep (se 2 (by rfl) ⟨469014, by rfl⟩ : syracuseStep 1250705 = 938029) B938029
theorem B1250723 : Blo 830350 1250723 := bstep (se 1 (by rfl) ⟨938042, by rfl⟩ : syracuseStep 1250723 = 1876085) B1876085
theorem B1250753 : Blo 830350 1250753 := bstep (se 2 (by rfl) ⟨469032, by rfl⟩ : syracuseStep 1250753 = 938065) B938065
theorem B1250771 : Blo 830350 1250771 := bstep (se 1 (by rfl) ⟨938078, by rfl⟩ : syracuseStep 1250771 = 1876157) B1876157
theorem B1578467 : Blo 830350 1578467 := bstep (se 1 (by rfl) ⟨1183850, by rfl⟩ : syracuseStep 1578467 = 2367701) B2367701
theorem B1250801 : Blo 830350 1250801 := bstep (se 2 (by rfl) ⟨469050, by rfl⟩ : syracuseStep 1250801 = 938101) B938101
theorem B1250819 : Blo 830350 1250819 := bstep (se 1 (by rfl) ⟨938114, by rfl⟩ : syracuseStep 1250819 = 1876229) B1876229
theorem B1250849 : Blo 830350 1250849 := bstep (se 2 (by rfl) ⟨469068, by rfl⟩ : syracuseStep 1250849 = 938137) B938137
theorem B1873457 : Blo 830350 1873457 := bstep (se 2 (by rfl) ⟨702546, by rfl⟩ : syracuseStep 1873457 = 1405093) B1405093
theorem B1250867 : Blo 830350 1250867 := bstep (se 1 (by rfl) ⟨938150, by rfl⟩ : syracuseStep 1250867 = 1876301) B1876301
theorem B1873475 : Blo 830350 1873475 := bstep (se 1 (by rfl) ⟨1405106, by rfl⟩ : syracuseStep 1873475 = 2810213) B2810213
theorem B1250897 : Blo 830350 1250897 := bstep (se 2 (by rfl) ⟨469086, by rfl⟩ : syracuseStep 1250897 = 938173) B938173
theorem B1054291 : Blo 830350 1054291 := bstep (se 1 (by rfl) ⟨790718, by rfl⟩ : syracuseStep 1054291 = 1581437) B1581437
theorem B1250915 : Blo 830350 1250915 := bstep (se 1 (by rfl) ⟨938186, by rfl⟩ : syracuseStep 1250915 = 1876373) B1876373
theorem B1250945 : Blo 830350 1250945 := bstep (se 2 (by rfl) ⟨469104, by rfl⟩ : syracuseStep 1250945 = 938209) B938209
theorem B1250963 : Blo 830350 1250963 := bstep (se 1 (by rfl) ⟨938222, by rfl⟩ : syracuseStep 1250963 = 1876445) B1876445
theorem B1185457 : Blo 830350 1185457 := bstep (se 2 (by rfl) ⟨444546, by rfl⟩ : syracuseStep 1185457 = 889093) B889093
theorem B1250993 : Blo 830350 1250993 := bstep (se 2 (by rfl) ⟨469122, by rfl⟩ : syracuseStep 1250993 = 938245) B938245
theorem B1054387 : Blo 830350 1054387 := bstep (se 1 (by rfl) ⟨790790, by rfl⟩ : syracuseStep 1054387 = 1581581) B1581581
theorem B1251011 : Blo 830350 1251011 := bstep (se 1 (by rfl) ⟨938258, by rfl⟩ : syracuseStep 1251011 = 1876517) B1876517
theorem B2102993 : Blo 830350 2102993 := bstep (se 2 (by rfl) ⟨788622, by rfl⟩ : syracuseStep 2102993 = 1577245) B1577245
theorem B1251041 : Blo 830350 1251041 := bstep (se 2 (by rfl) ⟨469140, by rfl⟩ : syracuseStep 1251041 = 938281) B938281
theorem B1251059 : Blo 830350 1251059 := bstep (se 1 (by rfl) ⟨938294, by rfl⟩ : syracuseStep 1251059 = 1876589) B1876589
theorem B2103043 : Blo 830350 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B1251089 : Blo 830350 1251089 := bstep (se 2 (by rfl) ⟨469158, by rfl⟩ : syracuseStep 1251089 = 938317) B938317
theorem B1251107 : Blo 830350 1251107 := bstep (se 1 (by rfl) ⟨938330, by rfl⟩ : syracuseStep 1251107 = 1876661) B1876661
theorem B1251137 : Blo 830350 1251137 := bstep (se 2 (by rfl) ⟨469176, by rfl⟩ : syracuseStep 1251137 = 938353) B938353
theorem B1873745 : Blo 830350 1873745 := bstep (se 2 (by rfl) ⟨702654, by rfl⟩ : syracuseStep 1873745 = 1405309) B1405309
theorem B1251155 : Blo 830350 1251155 := bstep (se 1 (by rfl) ⟨938366, by rfl⟩ : syracuseStep 1251155 = 1876733) B1876733
theorem B6002531 : Blo 830350 6002531 := bstep (se 1 (by rfl) ⟨4501898, by rfl⟩ : syracuseStep 6002531 = 9003797) B9003797
theorem B1873763 : Blo 830350 1873763 := bstep (se 1 (by rfl) ⟨1405322, by rfl⟩ : syracuseStep 1873763 = 2810645) B2810645
theorem B1251185 : Blo 830350 1251185 := bstep (se 2 (by rfl) ⟨469194, by rfl⟩ : syracuseStep 1251185 = 938389) B938389
theorem B1251203 : Blo 830350 1251203 := bstep (se 1 (by rfl) ⟨938402, by rfl⟩ : syracuseStep 1251203 = 1876805) B1876805
theorem B2103185 : Blo 830350 2103185 := bstep (se 2 (by rfl) ⟨788694, by rfl⟩ : syracuseStep 2103185 = 1577389) B1577389
theorem B1251233 : Blo 830350 1251233 := bstep (se 2 (by rfl) ⟨469212, by rfl⟩ : syracuseStep 1251233 = 938425) B938425
theorem B1775537 : Blo 830350 1775537 := bstep (se 2 (by rfl) ⟨665826, by rfl⟩ : syracuseStep 1775537 = 1331653) B1331653
theorem B1251251 : Blo 830350 1251251 := bstep (se 1 (by rfl) ⟨938438, by rfl⟩ : syracuseStep 1251251 = 1876877) B1876877
theorem B1251281 : Blo 830350 1251281 := bstep (se 2 (by rfl) ⟨469230, by rfl⟩ : syracuseStep 1251281 = 938461) B938461
theorem B1251299 : Blo 830350 1251299 := bstep (se 1 (by rfl) ⟨938474, by rfl⟩ : syracuseStep 1251299 = 1876949) B1876949
theorem B1251329 : Blo 830350 1251329 := bstep (se 2 (by rfl) ⟨469248, by rfl⟩ : syracuseStep 1251329 = 938497) B938497
theorem B1251347 : Blo 830350 1251347 := bstep (se 1 (by rfl) ⟨938510, by rfl⟩ : syracuseStep 1251347 = 1877021) B1877021
theorem B1251377 : Blo 830350 1251377 := bstep (se 2 (by rfl) ⟨469266, by rfl⟩ : syracuseStep 1251377 = 938533) B938533
theorem B1251395 : Blo 830350 1251395 := bstep (se 1 (by rfl) ⟨938546, by rfl⟩ : syracuseStep 1251395 = 1877093) B1877093
theorem B8984675 : Blo 830350 8984675 := bstep (se 1 (by rfl) ⟨6738506, by rfl⟩ : syracuseStep 8984675 = 13477013) B13477013
theorem B1251425 : Blo 830350 1251425 := bstep (se 2 (by rfl) ⟨469284, by rfl⟩ : syracuseStep 1251425 = 938569) B938569
theorem B1874033 : Blo 830350 1874033 := bstep (se 2 (by rfl) ⟨702762, by rfl⟩ : syracuseStep 1874033 = 1405525) B1405525
theorem B1251443 : Blo 830350 1251443 := bstep (se 1 (by rfl) ⟨938582, by rfl⟩ : syracuseStep 1251443 = 1877165) B1877165
theorem B1874051 : Blo 830350 1874051 := bstep (se 1 (by rfl) ⟨1405538, by rfl⟩ : syracuseStep 1874051 = 2811077) B2811077
theorem B1251473 : Blo 830350 1251473 := bstep (se 2 (by rfl) ⟨469302, by rfl⟩ : syracuseStep 1251473 = 938605) B938605
theorem B1054883 : Blo 830350 1054883 := bstep (se 1 (by rfl) ⟨791162, by rfl⟩ : syracuseStep 1054883 = 1582325) B1582325
theorem B1251491 : Blo 830350 1251491 := bstep (se 1 (by rfl) ⟨938618, by rfl⟩ : syracuseStep 1251491 = 1877237) B1877237
theorem B1251521 : Blo 830350 1251521 := bstep (se 2 (by rfl) ⟨469320, by rfl⟩ : syracuseStep 1251521 = 938641) B938641
theorem B1186049 : Blo 830350 1186049 := bstep (se 2 (by rfl) ⟨444768, by rfl⟩ : syracuseStep 1186049 = 889537) B889537
theorem B3381581 : Blo 830350 3381581 := bstep (se 3 (by rfl) ⟨634046, by rfl⟩ : syracuseStep 3381581 = 1268093) B1268093
theorem B1579409 : Blo 830350 1579409 := bstep (se 2 (by rfl) ⟨592278, by rfl⟩ : syracuseStep 1579409 = 1184557) B1184557
theorem B1874321 : Blo 830350 1874321 := bstep (se 2 (by rfl) ⟨702870, by rfl⟩ : syracuseStep 1874321 = 1405741) B1405741
theorem B1874339 : Blo 830350 1874339 := bstep (se 1 (by rfl) ⟨1405754, by rfl⟩ : syracuseStep 1874339 = 2811509) B2811509
theorem B10131893 : Blo 830350 10131893 := bstep (se 5 (by rfl) ⟨474932, by rfl⟩ : syracuseStep 10131893 = 949865) B949865
theorem B2660845 : Blo 830350 2660845 := bstep (se 3 (by rfl) ⟨498908, by rfl⟩ : syracuseStep 2660845 = 997817) B997817
theorem B7608845 : Blo 830350 7608845 := bstep (se 3 (by rfl) ⟨1426658, by rfl⟩ : syracuseStep 7608845 = 2853317) B2853317
theorem B1874609 : Blo 830350 1874609 := bstep (se 2 (by rfl) ⟨702978, by rfl⟩ : syracuseStep 1874609 = 1405957) B1405957
theorem B1776323 : Blo 830350 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B1874627 : Blo 830350 1874627 := bstep (se 1 (by rfl) ⟨1405970, by rfl⟩ : syracuseStep 1874627 = 2811941) B2811941
theorem B9116387 : Blo 830350 9116387 := bstep (se 1 (by rfl) ⟨6837290, by rfl⟩ : syracuseStep 9116387 = 13674581) B13674581
theorem B2661101 : Blo 830350 2661101 := bstep (se 3 (by rfl) ⟨498956, by rfl⟩ : syracuseStep 2661101 = 997913) B997913
theorem B6331121 : Blo 830350 6331121 := bstep (se 2 (by rfl) ⟨2374170, by rfl⟩ : syracuseStep 6331121 = 4748341) B4748341
theorem B1186579 : Blo 830350 1186579 := bstep (se 1 (by rfl) ⟨889934, by rfl⟩ : syracuseStep 1186579 = 1779869) B1779869
theorem B2366243 : Blo 830350 2366243 := bstep (se 1 (by rfl) ⟨1774682, by rfl⟩ : syracuseStep 2366243 = 3549365) B3549365
theorem B1055587 : Blo 830350 1055587 := bstep (se 1 (by rfl) ⟨791690, by rfl⟩ : syracuseStep 1055587 = 1583381) B1583381
theorem B2104177 : Blo 830350 2104177 := bstep (se 2 (by rfl) ⟨789066, by rfl⟩ : syracuseStep 2104177 = 1578133) B1578133
theorem B3152803 : Blo 830350 3152803 := bstep (se 1 (by rfl) ⟨2364602, by rfl⟩ : syracuseStep 3152803 = 4729205) B4729205
theorem B1055683 : Blo 830350 1055683 := bstep (se 1 (by rfl) ⟨791762, by rfl⟩ : syracuseStep 1055683 = 1583525) B1583525
theorem B1874897 : Blo 830350 1874897 := bstep (se 2 (by rfl) ⟨703086, by rfl⟩ : syracuseStep 1874897 = 1406173) B1406173
theorem B1874915 : Blo 830350 1874915 := bstep (se 1 (by rfl) ⟨1406186, by rfl⟩ : syracuseStep 1874915 = 2812373) B2812373
theorem B1186915 : Blo 830350 1186915 := bstep (se 1 (by rfl) ⟨890186, by rfl⟩ : syracuseStep 1186915 = 1780373) B1780373
theorem B2104451 : Blo 830350 2104451 := bstep (se 1 (by rfl) ⟨1578338, by rfl⟩ : syracuseStep 2104451 = 3156677) B3156677
theorem B14228621 : Blo 830350 14228621 := bstep (se 3 (by rfl) ⟨2667866, by rfl⟩ : syracuseStep 14228621 = 5335733) B5335733
theorem B1875185 : Blo 830350 1875185 := bstep (se 2 (by rfl) ⟨703194, by rfl⟩ : syracuseStep 1875185 = 1406389) B1406389
theorem B1875203 : Blo 830350 1875203 := bstep (se 1 (by rfl) ⟨1406402, by rfl⟩ : syracuseStep 1875203 = 2812805) B2812805
theorem B1580305 : Blo 830350 1580305 := bstep (se 2 (by rfl) ⟨592614, by rfl⟩ : syracuseStep 1580305 = 1185229) B1185229
theorem B2104643 : Blo 830350 2104643 := bstep (se 1 (by rfl) ⟨1578482, by rfl⟩ : syracuseStep 2104643 = 3156965) B3156965
theorem B1580465 : Blo 830350 1580465 := bstep (se 2 (by rfl) ⟨592674, by rfl⟩ : syracuseStep 1580465 = 1185349) B1185349
theorem B7577101 : Blo 830350 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B1875473 : Blo 830350 1875473 := bstep (se 2 (by rfl) ⟨703302, by rfl⟩ : syracuseStep 1875473 = 1406605) B1406605
theorem B1875491 : Blo 830350 1875491 := bstep (se 1 (by rfl) ⟨1406618, by rfl⟩ : syracuseStep 1875491 = 2813237) B2813237
theorem B2367053 : Blo 830350 2367053 := bstep (se 3 (by rfl) ⟨443822, by rfl⟩ : syracuseStep 2367053 = 887645) B887645
theorem B1777297 : Blo 830350 1777297 := bstep (se 2 (by rfl) ⟨666486, by rfl⟩ : syracuseStep 1777297 = 1332973) B1332973
theorem B1187473 : Blo 830350 1187473 := bstep (se 2 (by rfl) ⟨445302, by rfl⟩ : syracuseStep 1187473 = 890605) B890605
theorem B1187507 : Blo 830350 1187507 := bstep (se 1 (by rfl) ⟨890630, by rfl⟩ : syracuseStep 1187507 = 1781261) B1781261
theorem B5119685 : Blo 830350 5119685 := bstep (se 4 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 5119685 = 959941) B959941
theorem B2367245 : Blo 830350 2367245 := bstep (se 3 (by rfl) ⟨443858, by rfl⟩ : syracuseStep 2367245 = 887717) B887717
theorem B10133261 : Blo 830350 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B1875761 : Blo 830350 1875761 := bstep (se 2 (by rfl) ⟨703410, by rfl⟩ : syracuseStep 1875761 = 1406821) B1406821
theorem B1580867 : Blo 830350 1580867 := bstep (se 1 (by rfl) ⟨1185650, by rfl⟩ : syracuseStep 1580867 = 2371301) B2371301
theorem B1875779 : Blo 830350 1875779 := bstep (se 1 (by rfl) ⟨1406834, by rfl⟩ : syracuseStep 1875779 = 2813669) B2813669
theorem B1777553 : Blo 830350 1777553 := bstep (se 2 (by rfl) ⟨666582, by rfl⟩ : syracuseStep 1777553 = 1333165) B1333165
theorem B1122275 : Blo 830350 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B1876049 : Blo 830350 1876049 := bstep (se 2 (by rfl) ⟨703518, by rfl⟩ : syracuseStep 1876049 = 1407037) B1407037
theorem B1876067 : Blo 830350 1876067 := bstep (se 1 (by rfl) ⟨1407050, by rfl⟩ : syracuseStep 1876067 = 2814101) B2814101
theorem B2662627 : Blo 830350 2662627 := bstep (se 1 (by rfl) ⟨1996970, by rfl⟩ : syracuseStep 2662627 = 3993941) B3993941
theorem B2105585 : Blo 830350 2105585 := bstep (se 2 (by rfl) ⟨789594, by rfl⟩ : syracuseStep 2105585 = 1579189) B1579189
theorem B2105635 : Blo 830350 2105635 := bstep (se 1 (by rfl) ⟨1579226, by rfl⟩ : syracuseStep 2105635 = 3158453) B3158453
theorem B1876337 : Blo 830350 1876337 := bstep (se 2 (by rfl) ⟨703626, by rfl⟩ : syracuseStep 1876337 = 1407253) B1407253
theorem B1876355 : Blo 830350 1876355 := bstep (se 1 (by rfl) ⟨1407266, by rfl⟩ : syracuseStep 1876355 = 2814533) B2814533
theorem B1122707 : Blo 830350 1122707 := bstep (se 1 (by rfl) ⟨842030, by rfl⟩ : syracuseStep 1122707 = 1684061) B1684061
theorem B2105777 : Blo 830350 2105777 := bstep (se 2 (by rfl) ⟨789666, by rfl⟩ : syracuseStep 2105777 = 1579333) B1579333
theorem B1876625 : Blo 830350 1876625 := bstep (se 2 (by rfl) ⟨703734, by rfl⟩ : syracuseStep 1876625 = 1407469) B1407469
theorem B1876643 : Blo 830350 1876643 := bstep (se 1 (by rfl) ⟨1407482, by rfl⟩ : syracuseStep 1876643 = 2814965) B2814965
theorem B1581763 : Blo 830350 1581763 := bstep (se 1 (by rfl) ⟨1186322, by rfl⟩ : syracuseStep 1581763 = 2372645) B2372645
theorem B2368237 : Blo 830350 2368237 := bstep (se 3 (by rfl) ⟨444044, by rfl⟩ : syracuseStep 2368237 = 888089) B888089
theorem B4006705 : Blo 830350 4006705 := bstep (se 2 (by rfl) ⟨1502514, by rfl⟩ : syracuseStep 4006705 = 3005029) B3005029
theorem B1581923 : Blo 830350 1581923 := bstep (se 1 (by rfl) ⟨1186442, by rfl⟩ : syracuseStep 1581923 = 2372885) B2372885
theorem B1876913 : Blo 830350 1876913 := bstep (se 2 (by rfl) ⟨703842, by rfl⟩ : syracuseStep 1876913 = 1407685) B1407685
theorem B1876931 : Blo 830350 1876931 := bstep (se 1 (by rfl) ⟨1407698, by rfl⟩ : syracuseStep 1876931 = 2815397) B2815397
theorem B5055437 : Blo 830350 5055437 := bstep (se 3 (by rfl) ⟨947894, by rfl⟩ : syracuseStep 5055437 = 1895789) B1895789
theorem B2663459 : Blo 830350 2663459 := bstep (se 1 (by rfl) ⟨1997594, by rfl⟩ : syracuseStep 2663459 = 3995189) B3995189
theorem B3155021 : Blo 830350 3155021 := bstep (se 3 (by rfl) ⟨591566, by rfl⟩ : syracuseStep 3155021 = 1183133) B1183133
theorem B5121157 : Blo 830350 5121157 := bstep (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) B960217
theorem B1778851 : Blo 830350 1778851 := bstep (se 1 (by rfl) ⟨1334138, by rfl⟩ : syracuseStep 1778851 = 2668277) B2668277
theorem B1877201 : Blo 830350 1877201 := bstep (se 2 (by rfl) ⟨703950, by rfl⟩ : syracuseStep 1877201 = 1407901) B1407901
theorem B1877219 : Blo 830350 1877219 := bstep (se 1 (by rfl) ⟨1407914, by rfl⟩ : syracuseStep 1877219 = 2815829) B2815829
theorem B3417329 : Blo 830350 3417329 := bstep (se 2 (by rfl) ⟨1281498, by rfl⟩ : syracuseStep 3417329 = 2562997) B2562997
theorem B2106769 : Blo 830350 2106769 := bstep (se 2 (by rfl) ⟨790038, by rfl⟩ : syracuseStep 2106769 = 1580077) B1580077
theorem B2663857 : Blo 830350 2663857 := bstep (se 2 (by rfl) ⟨998946, by rfl⟩ : syracuseStep 2663857 = 1997893) B1997893
theorem B7120325 : Blo 830350 7120325 := bstep (se 4 (by rfl) ⟨667530, by rfl⟩ : syracuseStep 7120325 = 1335061) B1335061
theorem B2663921 : Blo 830350 2663921 := bstep (se 2 (by rfl) ⟨998970, by rfl⟩ : syracuseStep 2663921 = 1997941) B1997941
theorem B1779185 : Blo 830350 1779185 := bstep (se 2 (by rfl) ⟨667194, by rfl⟩ : syracuseStep 1779185 = 1334389) B1334389
theorem B2107043 : Blo 830350 2107043 := bstep (se 1 (by rfl) ⟨1580282, by rfl⟩ : syracuseStep 2107043 = 3160565) B3160565
theorem B2533169 : Blo 830350 2533169 := bstep (se 2 (by rfl) ⟨949938, by rfl⟩ : syracuseStep 2533169 = 1899877) B1899877
theorem B2107235 : Blo 830350 2107235 := bstep (se 1 (by rfl) ⟨1580426, by rfl⟩ : syracuseStep 2107235 = 3160853) B3160853
theorem B1582993 : Blo 830350 1582993 := bstep (se 2 (by rfl) ⟨593622, by rfl⟩ : syracuseStep 1582993 = 1187245) B1187245
theorem B3549091 : Blo 830350 3549091 := bstep (se 1 (by rfl) ⟨2661818, by rfl⟩ : syracuseStep 3549091 = 5323637) B5323637
theorem B1124339 : Blo 830350 1124339 := bstep (se 1 (by rfl) ⟨843254, by rfl⟩ : syracuseStep 1124339 = 1686509) B1686509
theorem B1714403 : Blo 830350 1714403 := bstep (se 1 (by rfl) ⟨1285802, by rfl⟩ : syracuseStep 1714403 = 2571605) B2571605
theorem B2369969 : Blo 830350 2369969 := bstep (se 2 (by rfl) ⟨888738, by rfl⟩ : syracuseStep 2369969 = 1777477) B1777477
theorem B3648077 : Blo 830350 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B2370161 : Blo 830350 2370161 := bstep (se 2 (by rfl) ⟨888810, by rfl⟩ : syracuseStep 2370161 = 1777621) B1777621
theorem B1780355 : Blo 830350 1780355 := bstep (se 1 (by rfl) ⟨1335266, by rfl⟩ : syracuseStep 1780355 = 2670533) B2670533
theorem B2534033 : Blo 830350 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B2108177 : Blo 830350 2108177 := bstep (se 2 (by rfl) ⟨790566, by rfl⟩ : syracuseStep 2108177 = 1581133) B1581133
theorem B2108227 : Blo 830350 2108227 := bstep (se 1 (by rfl) ⟨1581170, by rfl⟩ : syracuseStep 2108227 = 3162341) B3162341
theorem B830355 : Blo 830350 830355 := bstep (se 1 (by rfl) ⟨622766, by rfl⟩ : syracuseStep 830355 = 1245533) B1245533
theorem B830371 : Blo 830350 830371 := bstep (se 1 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 830371 = 1245557) B1245557
theorem B830387 : Blo 830350 830387 := bstep (se 1 (by rfl) ⟨622790, by rfl⟩ : syracuseStep 830387 = 1245581) B1245581
theorem B830403 : Blo 830350 830403 := bstep (se 1 (by rfl) ⟨622802, by rfl⟩ : syracuseStep 830403 = 1245605) B1245605
theorem B10660805 : Blo 830350 10660805 := bstep (se 4 (by rfl) ⟨999450, by rfl⟩ : syracuseStep 10660805 = 1998901) B1998901
theorem B2108369 : Blo 830350 2108369 := bstep (se 2 (by rfl) ⟨790638, by rfl⟩ : syracuseStep 2108369 = 1581277) B1581277
theorem B830419 : Blo 830350 830419 := bstep (se 1 (by rfl) ⟨622814, by rfl⟩ : syracuseStep 830419 = 1245629) B1245629
theorem B830435 : Blo 830350 830435 := bstep (se 1 (by rfl) ⟨622826, by rfl⟩ : syracuseStep 830435 = 1245653) B1245653
theorem B830451 : Blo 830350 830451 := bstep (se 1 (by rfl) ⟨622838, by rfl⟩ : syracuseStep 830451 = 1245677) B1245677
theorem B830467 : Blo 830350 830467 := bstep (se 1 (by rfl) ⟨622850, by rfl⟩ : syracuseStep 830467 = 1245701) B1245701
theorem B830483 : Blo 830350 830483 := bstep (se 1 (by rfl) ⟨622862, by rfl⟩ : syracuseStep 830483 = 1245725) B1245725
theorem B830499 : Blo 830350 830499 := bstep (se 1 (by rfl) ⟨622874, by rfl⟩ : syracuseStep 830499 = 1245749) B1245749
theorem B830515 : Blo 830350 830515 := bstep (se 1 (by rfl) ⟨622886, by rfl⟩ : syracuseStep 830515 = 1245773) B1245773
theorem B830531 : Blo 830350 830531 := bstep (se 1 (by rfl) ⟨622898, by rfl⟩ : syracuseStep 830531 = 1245797) B1245797
theorem B830547 : Blo 830350 830547 := bstep (se 1 (by rfl) ⟨622910, by rfl⟩ : syracuseStep 830547 = 1245821) B1245821
theorem B830563 : Blo 830350 830563 := bstep (se 1 (by rfl) ⟨622922, by rfl⟩ : syracuseStep 830563 = 1245845) B1245845
theorem B4205681 : Blo 830350 4205681 := bstep (se 2 (by rfl) ⟨1577130, by rfl⟩ : syracuseStep 4205681 = 3154261) B3154261
theorem B3550321 : Blo 830350 3550321 := bstep (se 2 (by rfl) ⟨1331370, by rfl⟩ : syracuseStep 3550321 = 2662741) B2662741
theorem B830579 : Blo 830350 830579 := bstep (se 1 (by rfl) ⟨622934, by rfl⟩ : syracuseStep 830579 = 1245869) B1245869
theorem B830595 : Blo 830350 830595 := bstep (se 1 (by rfl) ⟨622946, by rfl⟩ : syracuseStep 830595 = 1245893) B1245893
theorem B5057677 : Blo 830350 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B830611 : Blo 830350 830611 := bstep (se 1 (by rfl) ⟨622958, by rfl⟩ : syracuseStep 830611 = 1245917) B1245917
theorem B830627 : Blo 830350 830627 := bstep (se 1 (by rfl) ⟨622970, by rfl⟩ : syracuseStep 830627 = 1245941) B1245941
theorem B830643 : Blo 830350 830643 := bstep (se 1 (by rfl) ⟨622982, by rfl⟩ : syracuseStep 830643 = 1245965) B1245965
theorem B830659 : Blo 830350 830659 := bstep (se 1 (by rfl) ⟨622994, by rfl⟩ : syracuseStep 830659 = 1245989) B1245989
theorem B830675 : Blo 830350 830675 := bstep (se 1 (by rfl) ⟨623006, by rfl⟩ : syracuseStep 830675 = 1246013) B1246013
theorem B830691 : Blo 830350 830691 := bstep (se 1 (by rfl) ⟨623018, by rfl⟩ : syracuseStep 830691 = 1246037) B1246037
theorem B830707 : Blo 830350 830707 := bstep (se 1 (by rfl) ⟨623030, by rfl⟩ : syracuseStep 830707 = 1246061) B1246061
theorem B830723 : Blo 830350 830723 := bstep (se 1 (by rfl) ⟨623042, by rfl⟩ : syracuseStep 830723 = 1246085) B1246085
theorem B830739 : Blo 830350 830739 := bstep (se 1 (by rfl) ⟨623054, by rfl⟩ : syracuseStep 830739 = 1246109) B1246109
theorem B830755 : Blo 830350 830755 := bstep (se 1 (by rfl) ⟨623066, by rfl⟩ : syracuseStep 830755 = 1246133) B1246133
theorem B830771 : Blo 830350 830771 := bstep (se 1 (by rfl) ⟨623078, by rfl⟩ : syracuseStep 830771 = 1246157) B1246157
theorem B830787 : Blo 830350 830787 := bstep (se 1 (by rfl) ⟨623090, by rfl⟩ : syracuseStep 830787 = 1246181) B1246181
theorem B830803 : Blo 830350 830803 := bstep (se 1 (by rfl) ⟨623102, by rfl⟩ : syracuseStep 830803 = 1246205) B1246205
theorem B830819 : Blo 830350 830819 := bstep (se 1 (by rfl) ⟨623114, by rfl⟩ : syracuseStep 830819 = 1246229) B1246229
theorem B830835 : Blo 830350 830835 := bstep (se 1 (by rfl) ⟨623126, by rfl⟩ : syracuseStep 830835 = 1246253) B1246253
theorem B830851 : Blo 830350 830851 := bstep (se 1 (by rfl) ⟨623138, by rfl⟩ : syracuseStep 830851 = 1246277) B1246277
theorem B830867 : Blo 830350 830867 := bstep (se 1 (by rfl) ⟨623150, by rfl⟩ : syracuseStep 830867 = 1246301) B1246301
theorem B830883 : Blo 830350 830883 := bstep (se 1 (by rfl) ⟨623162, by rfl⟩ : syracuseStep 830883 = 1246325) B1246325
theorem B830899 : Blo 830350 830899 := bstep (se 1 (by rfl) ⟨623174, by rfl⟩ : syracuseStep 830899 = 1246349) B1246349
theorem B830915 : Blo 830350 830915 := bstep (se 1 (by rfl) ⟨623186, by rfl⟩ : syracuseStep 830915 = 1246373) B1246373
theorem B830931 : Blo 830350 830931 := bstep (se 1 (by rfl) ⟨623198, by rfl⟩ : syracuseStep 830931 = 1246397) B1246397
theorem B830947 : Blo 830350 830947 := bstep (se 1 (by rfl) ⟨623210, by rfl⟩ : syracuseStep 830947 = 1246421) B1246421
theorem B830963 : Blo 830350 830963 := bstep (se 1 (by rfl) ⟨623222, by rfl⟩ : syracuseStep 830963 = 1246445) B1246445
theorem B830979 : Blo 830350 830979 := bstep (se 1 (by rfl) ⟨623234, by rfl⟩ : syracuseStep 830979 = 1246469) B1246469
theorem B830995 : Blo 830350 830995 := bstep (se 1 (by rfl) ⟨623246, by rfl⟩ : syracuseStep 830995 = 1246493) B1246493
theorem B831011 : Blo 830350 831011 := bstep (se 1 (by rfl) ⟨623258, by rfl⟩ : syracuseStep 831011 = 1246517) B1246517
theorem B831027 : Blo 830350 831027 := bstep (se 1 (by rfl) ⟨623270, by rfl⟩ : syracuseStep 831027 = 1246541) B1246541
theorem B831043 : Blo 830350 831043 := bstep (se 1 (by rfl) ⟨623282, by rfl⟩ : syracuseStep 831043 = 1246565) B1246565
theorem B2371153 : Blo 830350 2371153 := bstep (se 2 (by rfl) ⟨889182, by rfl⟩ : syracuseStep 2371153 = 1778365) B1778365
theorem B831059 : Blo 830350 831059 := bstep (se 1 (by rfl) ⟨623294, by rfl⟩ : syracuseStep 831059 = 1246589) B1246589
theorem B831075 : Blo 830350 831075 := bstep (se 1 (by rfl) ⟨623306, by rfl⟩ : syracuseStep 831075 = 1246613) B1246613
theorem B831091 : Blo 830350 831091 := bstep (se 1 (by rfl) ⟨623318, by rfl⟩ : syracuseStep 831091 = 1246637) B1246637
theorem B831107 : Blo 830350 831107 := bstep (se 1 (by rfl) ⟨623330, by rfl⟩ : syracuseStep 831107 = 1246661) B1246661
theorem B831123 : Blo 830350 831123 := bstep (se 1 (by rfl) ⟨623342, by rfl⟩ : syracuseStep 831123 = 1246685) B1246685
theorem B831139 : Blo 830350 831139 := bstep (se 1 (by rfl) ⟨623354, by rfl⟩ : syracuseStep 831139 = 1246709) B1246709
theorem B831155 : Blo 830350 831155 := bstep (se 1 (by rfl) ⟨623366, by rfl⟩ : syracuseStep 831155 = 1246733) B1246733
theorem B831171 : Blo 830350 831171 := bstep (se 1 (by rfl) ⟨623378, by rfl⟩ : syracuseStep 831171 = 1246757) B1246757
theorem B831187 : Blo 830350 831187 := bstep (se 1 (by rfl) ⟨623390, by rfl⟩ : syracuseStep 831187 = 1246781) B1246781
theorem B831203 : Blo 830350 831203 := bstep (se 1 (by rfl) ⟨623402, by rfl⟩ : syracuseStep 831203 = 1246805) B1246805
theorem B831219 : Blo 830350 831219 := bstep (se 1 (by rfl) ⟨623414, by rfl⟩ : syracuseStep 831219 = 1246829) B1246829
theorem B831235 : Blo 830350 831235 := bstep (se 1 (by rfl) ⟨623426, by rfl⟩ : syracuseStep 831235 = 1246853) B1246853
theorem B831251 : Blo 830350 831251 := bstep (se 1 (by rfl) ⟨623438, by rfl⟩ : syracuseStep 831251 = 1246877) B1246877
theorem B831267 : Blo 830350 831267 := bstep (se 1 (by rfl) ⟨623450, by rfl⟩ : syracuseStep 831267 = 1246901) B1246901
theorem B2993969 : Blo 830350 2993969 := bstep (se 2 (by rfl) ⟨1122738, by rfl⟩ : syracuseStep 2993969 = 2245477) B2245477
theorem B831283 : Blo 830350 831283 := bstep (se 1 (by rfl) ⟨623462, by rfl⟩ : syracuseStep 831283 = 1246925) B1246925
theorem B831299 : Blo 830350 831299 := bstep (se 1 (by rfl) ⟨623474, by rfl⟩ : syracuseStep 831299 = 1246949) B1246949
theorem B831315 : Blo 830350 831315 := bstep (se 1 (by rfl) ⟨623486, by rfl⟩ : syracuseStep 831315 = 1246973) B1246973
theorem B831331 : Blo 830350 831331 := bstep (se 1 (by rfl) ⟨623498, by rfl⟩ : syracuseStep 831331 = 1246997) B1246997
theorem B2371427 : Blo 830350 2371427 := bstep (se 1 (by rfl) ⟨1778570, by rfl⟩ : syracuseStep 2371427 = 3557141) B3557141
theorem B5320561 : Blo 830350 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B831347 : Blo 830350 831347 := bstep (se 1 (by rfl) ⟨623510, by rfl⟩ : syracuseStep 831347 = 1247021) B1247021
theorem B831363 : Blo 830350 831363 := bstep (se 1 (by rfl) ⟨623522, by rfl⟩ : syracuseStep 831363 = 1247045) B1247045
theorem B831379 : Blo 830350 831379 := bstep (se 1 (by rfl) ⟨623534, by rfl⟩ : syracuseStep 831379 = 1247069) B1247069
theorem B831395 : Blo 830350 831395 := bstep (se 1 (by rfl) ⟨623546, by rfl⟩ : syracuseStep 831395 = 1247093) B1247093
theorem B3157937 : Blo 830350 3157937 := bstep (se 2 (by rfl) ⟨1184226, by rfl⟩ : syracuseStep 3157937 = 2368453) B2368453
theorem B2109361 : Blo 830350 2109361 := bstep (se 2 (by rfl) ⟨791010, by rfl⟩ : syracuseStep 2109361 = 1582021) B1582021
theorem B831411 : Blo 830350 831411 := bstep (se 1 (by rfl) ⟨623558, by rfl⟩ : syracuseStep 831411 = 1247117) B1247117
theorem B831427 : Blo 830350 831427 := bstep (se 1 (by rfl) ⟨623570, by rfl⟩ : syracuseStep 831427 = 1247141) B1247141
theorem B831443 : Blo 830350 831443 := bstep (se 1 (by rfl) ⟨623582, by rfl⟩ : syracuseStep 831443 = 1247165) B1247165
theorem B831459 : Blo 830350 831459 := bstep (se 1 (by rfl) ⟨623594, by rfl⟩ : syracuseStep 831459 = 1247189) B1247189
theorem B831475 : Blo 830350 831475 := bstep (se 1 (by rfl) ⟨623606, by rfl⟩ : syracuseStep 831475 = 1247213) B1247213
theorem B831491 : Blo 830350 831491 := bstep (se 1 (by rfl) ⟨623618, by rfl⟩ : syracuseStep 831491 = 1247237) B1247237
theorem B831507 : Blo 830350 831507 := bstep (se 1 (by rfl) ⟨623630, by rfl⟩ : syracuseStep 831507 = 1247261) B1247261
theorem B831523 : Blo 830350 831523 := bstep (se 1 (by rfl) ⟨623642, by rfl⟩ : syracuseStep 831523 = 1247285) B1247285
theorem B2371619 : Blo 830350 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B2404397 : Blo 830350 2404397 := bstep (se 3 (by rfl) ⟨450824, by rfl⟩ : syracuseStep 2404397 = 901649) B901649
theorem B831539 : Blo 830350 831539 := bstep (se 1 (by rfl) ⟨623654, by rfl⟩ : syracuseStep 831539 = 1247309) B1247309
theorem B831555 : Blo 830350 831555 := bstep (se 1 (by rfl) ⟨623666, by rfl⟩ : syracuseStep 831555 = 1247333) B1247333
theorem B831571 : Blo 830350 831571 := bstep (se 1 (by rfl) ⟨623678, by rfl⟩ : syracuseStep 831571 = 1247357) B1247357
theorem B831587 : Blo 830350 831587 := bstep (se 1 (by rfl) ⟨623690, by rfl⟩ : syracuseStep 831587 = 1247381) B1247381
theorem B831603 : Blo 830350 831603 := bstep (se 1 (by rfl) ⟨623702, by rfl⟩ : syracuseStep 831603 = 1247405) B1247405
theorem B831619 : Blo 830350 831619 := bstep (se 1 (by rfl) ⟨623714, by rfl⟩ : syracuseStep 831619 = 1247429) B1247429
theorem B831635 : Blo 830350 831635 := bstep (se 1 (by rfl) ⟨623726, by rfl⟩ : syracuseStep 831635 = 1247453) B1247453
theorem B831651 : Blo 830350 831651 := bstep (se 1 (by rfl) ⟨623738, by rfl⟩ : syracuseStep 831651 = 1247477) B1247477
theorem B831667 : Blo 830350 831667 := bstep (se 1 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 831667 = 1247501) B1247501
theorem B831683 : Blo 830350 831683 := bstep (se 1 (by rfl) ⟨623762, by rfl⟩ : syracuseStep 831683 = 1247525) B1247525
theorem B2109635 : Blo 830350 2109635 := bstep (se 1 (by rfl) ⟨1582226, by rfl⟩ : syracuseStep 2109635 = 3164453) B3164453
theorem B831699 : Blo 830350 831699 := bstep (se 1 (by rfl) ⟨623774, by rfl⟩ : syracuseStep 831699 = 1247549) B1247549
theorem B831715 : Blo 830350 831715 := bstep (se 1 (by rfl) ⟨623786, by rfl⟩ : syracuseStep 831715 = 1247573) B1247573
theorem B831731 : Blo 830350 831731 := bstep (se 1 (by rfl) ⟨623798, by rfl⟩ : syracuseStep 831731 = 1247597) B1247597
theorem B831747 : Blo 830350 831747 := bstep (se 1 (by rfl) ⟨623810, by rfl⟩ : syracuseStep 831747 = 1247621) B1247621
theorem B831763 : Blo 830350 831763 := bstep (se 1 (by rfl) ⟨623822, by rfl⟩ : syracuseStep 831763 = 1247645) B1247645
theorem B831779 : Blo 830350 831779 := bstep (se 1 (by rfl) ⟨623834, by rfl⟩ : syracuseStep 831779 = 1247669) B1247669
theorem B831795 : Blo 830350 831795 := bstep (se 1 (by rfl) ⟨623846, by rfl⟩ : syracuseStep 831795 = 1247693) B1247693
theorem B831811 : Blo 830350 831811 := bstep (se 1 (by rfl) ⟨623858, by rfl⟩ : syracuseStep 831811 = 1247717) B1247717
theorem B831827 : Blo 830350 831827 := bstep (se 1 (by rfl) ⟨623870, by rfl⟩ : syracuseStep 831827 = 1247741) B1247741
theorem B831843 : Blo 830350 831843 := bstep (se 1 (by rfl) ⟨623882, by rfl⟩ : syracuseStep 831843 = 1247765) B1247765
theorem B831859 : Blo 830350 831859 := bstep (se 1 (by rfl) ⟨623894, by rfl⟩ : syracuseStep 831859 = 1247789) B1247789
theorem B831875 : Blo 830350 831875 := bstep (se 1 (by rfl) ⟨623906, by rfl⟩ : syracuseStep 831875 = 1247813) B1247813
theorem B2109827 : Blo 830350 2109827 := bstep (se 1 (by rfl) ⟨1582370, by rfl⟩ : syracuseStep 2109827 = 3164741) B3164741
theorem B831891 : Blo 830350 831891 := bstep (se 1 (by rfl) ⟨623918, by rfl⟩ : syracuseStep 831891 = 1247837) B1247837
theorem B831907 : Blo 830350 831907 := bstep (se 1 (by rfl) ⟨623930, by rfl⟩ : syracuseStep 831907 = 1247861) B1247861
theorem B831923 : Blo 830350 831923 := bstep (se 1 (by rfl) ⟨623942, by rfl⟩ : syracuseStep 831923 = 1247885) B1247885
theorem B1421761 : Blo 830350 1421761 := bstep (se 2 (by rfl) ⟨533160, by rfl⟩ : syracuseStep 1421761 = 1066321) B1066321
theorem B831939 : Blo 830350 831939 := bstep (se 1 (by rfl) ⟨623954, by rfl⟩ : syracuseStep 831939 = 1247909) B1247909
theorem B831955 : Blo 830350 831955 := bstep (se 1 (by rfl) ⟨623966, by rfl⟩ : syracuseStep 831955 = 1247933) B1247933
theorem B831971 : Blo 830350 831971 := bstep (se 1 (by rfl) ⟨623978, by rfl⟩ : syracuseStep 831971 = 1247957) B1247957
theorem B831987 : Blo 830350 831987 := bstep (se 1 (by rfl) ⟨623990, by rfl⟩ : syracuseStep 831987 = 1247981) B1247981
theorem B832003 : Blo 830350 832003 := bstep (se 1 (by rfl) ⟨624002, by rfl⟩ : syracuseStep 832003 = 1248005) B1248005
theorem B832019 : Blo 830350 832019 := bstep (se 1 (by rfl) ⟨624014, by rfl⟩ : syracuseStep 832019 = 1248029) B1248029
theorem B4207139 : Blo 830350 4207139 := bstep (se 1 (by rfl) ⟨3155354, by rfl⟩ : syracuseStep 4207139 = 6310709) B6310709
theorem B832035 : Blo 830350 832035 := bstep (se 1 (by rfl) ⟨624026, by rfl⟩ : syracuseStep 832035 = 1248053) B1248053
theorem B832051 : Blo 830350 832051 := bstep (se 1 (by rfl) ⟨624038, by rfl⟩ : syracuseStep 832051 = 1248077) B1248077
theorem B1421891 : Blo 830350 1421891 := bstep (se 1 (by rfl) ⟨1066418, by rfl⟩ : syracuseStep 1421891 = 2132837) B2132837
theorem B832067 : Blo 830350 832067 := bstep (se 1 (by rfl) ⟨624050, by rfl⟩ : syracuseStep 832067 = 1248101) B1248101
theorem B832083 : Blo 830350 832083 := bstep (se 1 (by rfl) ⟨624062, by rfl⟩ : syracuseStep 832083 = 1248125) B1248125
theorem B832099 : Blo 830350 832099 := bstep (se 1 (by rfl) ⟨624074, by rfl⟩ : syracuseStep 832099 = 1248149) B1248149
theorem B832115 : Blo 830350 832115 := bstep (se 1 (by rfl) ⟨624086, by rfl⟩ : syracuseStep 832115 = 1248173) B1248173
theorem B832131 : Blo 830350 832131 := bstep (se 1 (by rfl) ⟨624098, by rfl⟩ : syracuseStep 832131 = 1248197) B1248197
theorem B832147 : Blo 830350 832147 := bstep (se 1 (by rfl) ⟨624110, by rfl⟩ : syracuseStep 832147 = 1248221) B1248221
theorem B832163 : Blo 830350 832163 := bstep (se 1 (by rfl) ⟨624122, by rfl⟩ : syracuseStep 832163 = 1248245) B1248245
theorem B4502179 : Blo 830350 4502179 := bstep (se 1 (by rfl) ⟨3376634, by rfl⟩ : syracuseStep 4502179 = 6753269) B6753269
theorem B832179 : Blo 830350 832179 := bstep (se 1 (by rfl) ⟨624134, by rfl⟩ : syracuseStep 832179 = 1248269) B1248269
theorem B832195 : Blo 830350 832195 := bstep (se 1 (by rfl) ⟨624146, by rfl⟩ : syracuseStep 832195 = 1248293) B1248293
theorem B12169925 : Blo 830350 12169925 := bstep (se 4 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 12169925 = 2281861) B2281861
theorem B832211 : Blo 830350 832211 := bstep (se 1 (by rfl) ⟨624158, by rfl⟩ : syracuseStep 832211 = 1248317) B1248317
theorem B832227 : Blo 830350 832227 := bstep (se 1 (by rfl) ⟨624170, by rfl⟩ : syracuseStep 832227 = 1248341) B1248341
theorem B832243 : Blo 830350 832243 := bstep (se 1 (by rfl) ⟨624182, by rfl⟩ : syracuseStep 832243 = 1248365) B1248365
theorem B832259 : Blo 830350 832259 := bstep (se 1 (by rfl) ⟨624194, by rfl⟩ : syracuseStep 832259 = 1248389) B1248389
theorem B832275 : Blo 830350 832275 := bstep (se 1 (by rfl) ⟨624206, by rfl⟩ : syracuseStep 832275 = 1248413) B1248413
theorem B832291 : Blo 830350 832291 := bstep (se 1 (by rfl) ⟨624218, by rfl⟩ : syracuseStep 832291 = 1248437) B1248437
theorem B1422131 : Blo 830350 1422131 := bstep (se 1 (by rfl) ⟨1066598, by rfl⟩ : syracuseStep 1422131 = 2133197) B2133197
theorem B832307 : Blo 830350 832307 := bstep (se 1 (by rfl) ⟨624230, by rfl⟩ : syracuseStep 832307 = 1248461) B1248461
theorem B832323 : Blo 830350 832323 := bstep (se 1 (by rfl) ⟨624242, by rfl⟩ : syracuseStep 832323 = 1248485) B1248485
theorem B2372429 : Blo 830350 2372429 := bstep (se 3 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 2372429 = 889661) B889661
theorem B832339 : Blo 830350 832339 := bstep (se 1 (by rfl) ⟨624254, by rfl⟩ : syracuseStep 832339 = 1248509) B1248509
theorem B832355 : Blo 830350 832355 := bstep (se 1 (by rfl) ⟨624266, by rfl⟩ : syracuseStep 832355 = 1248533) B1248533
theorem B832371 : Blo 830350 832371 := bstep (se 1 (by rfl) ⟨624278, by rfl⟩ : syracuseStep 832371 = 1248557) B1248557
theorem B832387 : Blo 830350 832387 := bstep (se 1 (by rfl) ⟨624290, by rfl⟩ : syracuseStep 832387 = 1248581) B1248581
theorem B832403 : Blo 830350 832403 := bstep (se 1 (by rfl) ⟨624302, by rfl⟩ : syracuseStep 832403 = 1248605) B1248605
theorem B832419 : Blo 830350 832419 := bstep (se 1 (by rfl) ⟨624314, by rfl⟩ : syracuseStep 832419 = 1248629) B1248629
theorem B832435 : Blo 830350 832435 := bstep (se 1 (by rfl) ⟨624326, by rfl⟩ : syracuseStep 832435 = 1248653) B1248653
theorem B832451 : Blo 830350 832451 := bstep (se 1 (by rfl) ⟨624338, by rfl⟩ : syracuseStep 832451 = 1248677) B1248677
theorem B832467 : Blo 830350 832467 := bstep (se 1 (by rfl) ⟨624350, by rfl⟩ : syracuseStep 832467 = 1248701) B1248701
theorem B832483 : Blo 830350 832483 := bstep (se 1 (by rfl) ⟨624362, by rfl⟩ : syracuseStep 832483 = 1248725) B1248725
theorem B832499 : Blo 830350 832499 := bstep (se 1 (by rfl) ⟨624374, by rfl⟩ : syracuseStep 832499 = 1248749) B1248749
theorem B832515 : Blo 830350 832515 := bstep (se 1 (by rfl) ⟨624386, by rfl⟩ : syracuseStep 832515 = 1248773) B1248773
theorem B2372611 : Blo 830350 2372611 := bstep (se 1 (by rfl) ⟨1779458, by rfl⟩ : syracuseStep 2372611 = 3558917) B3558917
theorem B6927373 : Blo 830350 6927373 := bstep (se 3 (by rfl) ⟨1298882, by rfl⟩ : syracuseStep 6927373 = 2597765) B2597765
theorem B832531 : Blo 830350 832531 := bstep (se 1 (by rfl) ⟨624398, by rfl⟩ : syracuseStep 832531 = 1248797) B1248797
theorem B832547 : Blo 830350 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B832563 : Blo 830350 832563 := bstep (se 1 (by rfl) ⟨624422, by rfl⟩ : syracuseStep 832563 = 1248845) B1248845
theorem B832579 : Blo 830350 832579 := bstep (se 1 (by rfl) ⟨624434, by rfl⟩ : syracuseStep 832579 = 1248869) B1248869
theorem B832595 : Blo 830350 832595 := bstep (se 1 (by rfl) ⟨624446, by rfl⟩ : syracuseStep 832595 = 1248893) B1248893
theorem B832611 : Blo 830350 832611 := bstep (se 1 (by rfl) ⟨624458, by rfl⟩ : syracuseStep 832611 = 1248917) B1248917
theorem B832627 : Blo 830350 832627 := bstep (se 1 (by rfl) ⟨624470, by rfl⟩ : syracuseStep 832627 = 1248941) B1248941
theorem B832643 : Blo 830350 832643 := bstep (se 1 (by rfl) ⟨624482, by rfl⟩ : syracuseStep 832643 = 1248965) B1248965
theorem B832659 : Blo 830350 832659 := bstep (se 1 (by rfl) ⟨624494, by rfl⟩ : syracuseStep 832659 = 1248989) B1248989
theorem B832675 : Blo 830350 832675 := bstep (se 1 (by rfl) ⟨624506, by rfl⟩ : syracuseStep 832675 = 1249013) B1249013
theorem B832691 : Blo 830350 832691 := bstep (se 1 (by rfl) ⟨624518, by rfl⟩ : syracuseStep 832691 = 1249037) B1249037
theorem B832707 : Blo 830350 832707 := bstep (se 1 (by rfl) ⟨624530, by rfl⟩ : syracuseStep 832707 = 1249061) B1249061
theorem B15971525 : Blo 830350 15971525 := bstep (se 4 (by rfl) ⟨1497330, by rfl⟩ : syracuseStep 15971525 = 2994661) B2994661
theorem B832723 : Blo 830350 832723 := bstep (se 1 (by rfl) ⟨624542, by rfl⟩ : syracuseStep 832723 = 1249085) B1249085
theorem B832739 : Blo 830350 832739 := bstep (se 1 (by rfl) ⟨624554, by rfl⟩ : syracuseStep 832739 = 1249109) B1249109
theorem B832755 : Blo 830350 832755 := bstep (se 1 (by rfl) ⟨624566, by rfl⟩ : syracuseStep 832755 = 1249133) B1249133
theorem B832771 : Blo 830350 832771 := bstep (se 1 (by rfl) ⟨624578, by rfl⟩ : syracuseStep 832771 = 1249157) B1249157
theorem B2995469 : Blo 830350 2995469 := bstep (se 3 (by rfl) ⟨561650, by rfl⟩ : syracuseStep 2995469 = 1123301) B1123301
theorem B832787 : Blo 830350 832787 := bstep (se 1 (by rfl) ⟨624590, by rfl⟩ : syracuseStep 832787 = 1249181) B1249181
theorem B832803 : Blo 830350 832803 := bstep (se 1 (by rfl) ⟨624602, by rfl⟩ : syracuseStep 832803 = 1249205) B1249205
theorem B2110769 : Blo 830350 2110769 := bstep (se 2 (by rfl) ⟨791538, by rfl⟩ : syracuseStep 2110769 = 1583077) B1583077
theorem B832819 : Blo 830350 832819 := bstep (se 1 (by rfl) ⟨624614, by rfl⟩ : syracuseStep 832819 = 1249229) B1249229
theorem B832835 : Blo 830350 832835 := bstep (se 1 (by rfl) ⟨624626, by rfl⟩ : syracuseStep 832835 = 1249253) B1249253
theorem B4207949 : Blo 830350 4207949 := bstep (se 3 (by rfl) ⟨788990, by rfl⟩ : syracuseStep 4207949 = 1577981) B1577981
theorem B832851 : Blo 830350 832851 := bstep (se 1 (by rfl) ⟨624638, by rfl⟩ : syracuseStep 832851 = 1249277) B1249277
theorem B3159395 : Blo 830350 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B832867 : Blo 830350 832867 := bstep (se 1 (by rfl) ⟨624650, by rfl⟩ : syracuseStep 832867 = 1249301) B1249301
theorem B2110819 : Blo 830350 2110819 := bstep (se 1 (by rfl) ⟨1583114, by rfl⟩ : syracuseStep 2110819 = 3166229) B3166229
theorem B832883 : Blo 830350 832883 := bstep (se 1 (by rfl) ⟨624662, by rfl⟩ : syracuseStep 832883 = 1249325) B1249325
theorem B832899 : Blo 830350 832899 := bstep (se 1 (by rfl) ⟨624674, by rfl⟩ : syracuseStep 832899 = 1249349) B1249349
theorem B832915 : Blo 830350 832915 := bstep (se 1 (by rfl) ⟨624686, by rfl⟩ : syracuseStep 832915 = 1249373) B1249373
theorem B832931 : Blo 830350 832931 := bstep (se 1 (by rfl) ⟨624698, by rfl⟩ : syracuseStep 832931 = 1249397) B1249397
theorem B832947 : Blo 830350 832947 := bstep (se 1 (by rfl) ⟨624710, by rfl⟩ : syracuseStep 832947 = 1249421) B1249421
theorem B832963 : Blo 830350 832963 := bstep (se 1 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 832963 = 1249445) B1249445
theorem B832979 : Blo 830350 832979 := bstep (se 1 (by rfl) ⟨624734, by rfl⟩ : syracuseStep 832979 = 1249469) B1249469
theorem B832995 : Blo 830350 832995 := bstep (se 1 (by rfl) ⟨624746, by rfl⟩ : syracuseStep 832995 = 1249493) B1249493
theorem B2373101 : Blo 830350 2373101 := bstep (se 3 (by rfl) ⟨444956, by rfl⟩ : syracuseStep 2373101 = 889913) B889913
theorem B2110961 : Blo 830350 2110961 := bstep (se 2 (by rfl) ⟨791610, by rfl⟩ : syracuseStep 2110961 = 1583221) B1583221
theorem B833011 : Blo 830350 833011 := bstep (se 1 (by rfl) ⟨624758, by rfl⟩ : syracuseStep 833011 = 1249517) B1249517
theorem B833027 : Blo 830350 833027 := bstep (se 1 (by rfl) ⟨624770, by rfl⟩ : syracuseStep 833027 = 1249541) B1249541
theorem B833043 : Blo 830350 833043 := bstep (se 1 (by rfl) ⟨624782, by rfl⟩ : syracuseStep 833043 = 1249565) B1249565
theorem B833059 : Blo 830350 833059 := bstep (se 1 (by rfl) ⟨624794, by rfl⟩ : syracuseStep 833059 = 1249589) B1249589
theorem B833075 : Blo 830350 833075 := bstep (se 1 (by rfl) ⟨624806, by rfl⟩ : syracuseStep 833075 = 1249613) B1249613
theorem B2668099 : Blo 830350 2668099 := bstep (se 1 (by rfl) ⟨2001074, by rfl⟩ : syracuseStep 2668099 = 4002149) B4002149
theorem B833091 : Blo 830350 833091 := bstep (se 1 (by rfl) ⟨624818, by rfl⟩ : syracuseStep 833091 = 1249637) B1249637
theorem B833107 : Blo 830350 833107 := bstep (se 1 (by rfl) ⟨624830, by rfl⟩ : syracuseStep 833107 = 1249661) B1249661
theorem B833123 : Blo 830350 833123 := bstep (se 1 (by rfl) ⟨624842, by rfl⟩ : syracuseStep 833123 = 1249685) B1249685
theorem B833139 : Blo 830350 833139 := bstep (se 1 (by rfl) ⟨624854, by rfl⟩ : syracuseStep 833139 = 1249709) B1249709
theorem B833155 : Blo 830350 833155 := bstep (se 1 (by rfl) ⟨624866, by rfl⟩ : syracuseStep 833155 = 1249733) B1249733
theorem B833171 : Blo 830350 833171 := bstep (se 1 (by rfl) ⟨624878, by rfl⟩ : syracuseStep 833171 = 1249757) B1249757
theorem B833187 : Blo 830350 833187 := bstep (se 1 (by rfl) ⟨624890, by rfl⟩ : syracuseStep 833187 = 1249781) B1249781
theorem B833203 : Blo 830350 833203 := bstep (se 1 (by rfl) ⟨624902, by rfl⟩ : syracuseStep 833203 = 1249805) B1249805
theorem B833219 : Blo 830350 833219 := bstep (se 1 (by rfl) ⟨624914, by rfl⟩ : syracuseStep 833219 = 1249829) B1249829
theorem B833235 : Blo 830350 833235 := bstep (se 1 (by rfl) ⟨624926, by rfl⟩ : syracuseStep 833235 = 1249853) B1249853
theorem B833251 : Blo 830350 833251 := bstep (se 1 (by rfl) ⟨624938, by rfl⟩ : syracuseStep 833251 = 1249877) B1249877
theorem B833267 : Blo 830350 833267 := bstep (se 1 (by rfl) ⟨624950, by rfl⟩ : syracuseStep 833267 = 1249901) B1249901
theorem B833283 : Blo 830350 833283 := bstep (se 1 (by rfl) ⟨624962, by rfl⟩ : syracuseStep 833283 = 1249925) B1249925
theorem B833299 : Blo 830350 833299 := bstep (se 1 (by rfl) ⟨624974, by rfl⟩ : syracuseStep 833299 = 1249949) B1249949
theorem B833315 : Blo 830350 833315 := bstep (se 1 (by rfl) ⟨624986, by rfl⟩ : syracuseStep 833315 = 1249973) B1249973
theorem B833331 : Blo 830350 833331 := bstep (se 1 (by rfl) ⟨624998, by rfl⟩ : syracuseStep 833331 = 1249997) B1249997
theorem B833347 : Blo 830350 833347 := bstep (se 1 (by rfl) ⟨625010, by rfl⟩ : syracuseStep 833347 = 1250021) B1250021
theorem B833363 : Blo 830350 833363 := bstep (se 1 (by rfl) ⟨625022, by rfl⟩ : syracuseStep 833363 = 1250045) B1250045
theorem B833379 : Blo 830350 833379 := bstep (se 1 (by rfl) ⟨625034, by rfl⟩ : syracuseStep 833379 = 1250069) B1250069
theorem B833395 : Blo 830350 833395 := bstep (se 1 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 833395 = 1250093) B1250093
theorem B833411 : Blo 830350 833411 := bstep (se 1 (by rfl) ⟨625058, by rfl⟩ : syracuseStep 833411 = 1250117) B1250117
theorem B833427 : Blo 830350 833427 := bstep (se 1 (by rfl) ⟨625070, by rfl⟩ : syracuseStep 833427 = 1250141) B1250141
theorem B833443 : Blo 830350 833443 := bstep (se 1 (by rfl) ⟨625082, by rfl⟩ : syracuseStep 833443 = 1250165) B1250165
theorem B833459 : Blo 830350 833459 := bstep (se 1 (by rfl) ⟨625094, by rfl⟩ : syracuseStep 833459 = 1250189) B1250189
theorem B833475 : Blo 830350 833475 := bstep (se 1 (by rfl) ⟨625106, by rfl⟩ : syracuseStep 833475 = 1250213) B1250213
theorem B833491 : Blo 830350 833491 := bstep (se 1 (by rfl) ⟨625118, by rfl⟩ : syracuseStep 833491 = 1250237) B1250237
theorem B833507 : Blo 830350 833507 := bstep (se 1 (by rfl) ⟨625130, by rfl⟩ : syracuseStep 833507 = 1250261) B1250261
theorem B833523 : Blo 830350 833523 := bstep (se 1 (by rfl) ⟨625142, by rfl⟩ : syracuseStep 833523 = 1250285) B1250285
theorem B833539 : Blo 830350 833539 := bstep (se 1 (by rfl) ⟨625154, by rfl⟩ : syracuseStep 833539 = 1250309) B1250309
theorem B833555 : Blo 830350 833555 := bstep (se 1 (by rfl) ⟨625166, by rfl⟩ : syracuseStep 833555 = 1250333) B1250333
theorem B833571 : Blo 830350 833571 := bstep (se 1 (by rfl) ⟨625178, by rfl⟩ : syracuseStep 833571 = 1250357) B1250357
theorem B833587 : Blo 830350 833587 := bstep (se 1 (by rfl) ⟨625190, by rfl⟩ : syracuseStep 833587 = 1250381) B1250381
theorem B833603 : Blo 830350 833603 := bstep (se 1 (by rfl) ⟨625202, by rfl⟩ : syracuseStep 833603 = 1250405) B1250405
theorem B833619 : Blo 830350 833619 := bstep (se 1 (by rfl) ⟨625214, by rfl⟩ : syracuseStep 833619 = 1250429) B1250429
theorem B833635 : Blo 830350 833635 := bstep (se 1 (by rfl) ⟨625226, by rfl⟩ : syracuseStep 833635 = 1250453) B1250453
theorem B833651 : Blo 830350 833651 := bstep (se 1 (by rfl) ⟨625238, by rfl⟩ : syracuseStep 833651 = 1250477) B1250477
theorem B833667 : Blo 830350 833667 := bstep (se 1 (by rfl) ⟨625250, by rfl⟩ : syracuseStep 833667 = 1250501) B1250501
theorem B833683 : Blo 830350 833683 := bstep (se 1 (by rfl) ⟨625262, by rfl⟩ : syracuseStep 833683 = 1250525) B1250525
theorem B833699 : Blo 830350 833699 := bstep (se 1 (by rfl) ⟨625274, by rfl⟩ : syracuseStep 833699 = 1250549) B1250549
theorem B833715 : Blo 830350 833715 := bstep (se 1 (by rfl) ⟨625286, by rfl⟩ : syracuseStep 833715 = 1250573) B1250573
theorem B833731 : Blo 830350 833731 := bstep (se 1 (by rfl) ⟨625298, by rfl⟩ : syracuseStep 833731 = 1250597) B1250597
theorem B833747 : Blo 830350 833747 := bstep (se 1 (by rfl) ⟨625310, by rfl⟩ : syracuseStep 833747 = 1250621) B1250621
theorem B1685731 : Blo 830350 1685731 := bstep (se 1 (by rfl) ⟨1264298, by rfl⟩ : syracuseStep 1685731 = 2528597) B2528597
theorem B833763 : Blo 830350 833763 := bstep (se 1 (by rfl) ⟨625322, by rfl⟩ : syracuseStep 833763 = 1250645) B1250645
theorem B833779 : Blo 830350 833779 := bstep (se 1 (by rfl) ⟨625334, by rfl⟩ : syracuseStep 833779 = 1250669) B1250669
theorem B833795 : Blo 830350 833795 := bstep (se 1 (by rfl) ⟨625346, by rfl⟩ : syracuseStep 833795 = 1250693) B1250693
theorem B833811 : Blo 830350 833811 := bstep (se 1 (by rfl) ⟨625358, by rfl⟩ : syracuseStep 833811 = 1250717) B1250717
theorem B833827 : Blo 830350 833827 := bstep (se 1 (by rfl) ⟨625370, by rfl⟩ : syracuseStep 833827 = 1250741) B1250741
theorem B833843 : Blo 830350 833843 := bstep (se 1 (by rfl) ⟨625382, by rfl⟩ : syracuseStep 833843 = 1250765) B1250765
theorem B833859 : Blo 830350 833859 := bstep (se 1 (by rfl) ⟨625394, by rfl⟩ : syracuseStep 833859 = 1250789) B1250789
theorem B4733261 : Blo 830350 4733261 := bstep (se 3 (by rfl) ⟨887486, by rfl⟩ : syracuseStep 4733261 = 1774973) B1774973
theorem B3160397 : Blo 830350 3160397 := bstep (se 3 (by rfl) ⟨592574, by rfl⟩ : syracuseStep 3160397 = 1185149) B1185149
theorem B833875 : Blo 830350 833875 := bstep (se 1 (by rfl) ⟨625406, by rfl⟩ : syracuseStep 833875 = 1250813) B1250813
theorem B833891 : Blo 830350 833891 := bstep (se 1 (by rfl) ⟨625418, by rfl⟩ : syracuseStep 833891 = 1250837) B1250837
theorem B833907 : Blo 830350 833907 := bstep (se 1 (by rfl) ⟨625430, by rfl⟩ : syracuseStep 833907 = 1250861) B1250861
theorem B833923 : Blo 830350 833923 := bstep (se 1 (by rfl) ⟨625442, by rfl⟩ : syracuseStep 833923 = 1250885) B1250885
theorem B833939 : Blo 830350 833939 := bstep (se 1 (by rfl) ⟨625454, by rfl⟩ : syracuseStep 833939 = 1250909) B1250909
theorem B833955 : Blo 830350 833955 := bstep (se 1 (by rfl) ⟨625466, by rfl⟩ : syracuseStep 833955 = 1250933) B1250933
theorem B833971 : Blo 830350 833971 := bstep (se 1 (by rfl) ⟨625478, by rfl⟩ : syracuseStep 833971 = 1250957) B1250957
theorem B833987 : Blo 830350 833987 := bstep (se 1 (by rfl) ⟨625490, by rfl⟩ : syracuseStep 833987 = 1250981) B1250981
theorem B834003 : Blo 830350 834003 := bstep (se 1 (by rfl) ⟨625502, by rfl⟩ : syracuseStep 834003 = 1251005) B1251005
theorem B834019 : Blo 830350 834019 := bstep (se 1 (by rfl) ⟨625514, by rfl⟩ : syracuseStep 834019 = 1251029) B1251029
theorem B834035 : Blo 830350 834035 := bstep (se 1 (by rfl) ⟨625526, by rfl⟩ : syracuseStep 834035 = 1251053) B1251053
theorem B834051 : Blo 830350 834051 := bstep (se 1 (by rfl) ⟨625538, by rfl⟩ : syracuseStep 834051 = 1251077) B1251077
theorem B834067 : Blo 830350 834067 := bstep (se 1 (by rfl) ⟨625550, by rfl⟩ : syracuseStep 834067 = 1251101) B1251101
theorem B834083 : Blo 830350 834083 := bstep (se 1 (by rfl) ⟨625562, by rfl⟩ : syracuseStep 834083 = 1251125) B1251125
theorem B834099 : Blo 830350 834099 := bstep (se 1 (by rfl) ⟨625574, by rfl⟩ : syracuseStep 834099 = 1251149) B1251149
theorem B834115 : Blo 830350 834115 := bstep (se 1 (by rfl) ⟨625586, by rfl⟩ : syracuseStep 834115 = 1251173) B1251173
theorem B834131 : Blo 830350 834131 := bstep (se 1 (by rfl) ⟨625598, by rfl⟩ : syracuseStep 834131 = 1251197) B1251197
theorem B834147 : Blo 830350 834147 := bstep (se 1 (by rfl) ⟨625610, by rfl⟩ : syracuseStep 834147 = 1251221) B1251221
theorem B834163 : Blo 830350 834163 := bstep (se 1 (by rfl) ⟨625622, by rfl⟩ : syracuseStep 834163 = 1251245) B1251245
theorem B834179 : Blo 830350 834179 := bstep (se 1 (by rfl) ⟨625634, by rfl⟩ : syracuseStep 834179 = 1251269) B1251269
theorem B2374285 : Blo 830350 2374285 := bstep (se 3 (by rfl) ⟨445178, by rfl⟩ : syracuseStep 2374285 = 890357) B890357
theorem B834195 : Blo 830350 834195 := bstep (se 1 (by rfl) ⟨625646, by rfl⟩ : syracuseStep 834195 = 1251293) B1251293
theorem B834211 : Blo 830350 834211 := bstep (se 1 (by rfl) ⟨625658, by rfl⟩ : syracuseStep 834211 = 1251317) B1251317
theorem B834227 : Blo 830350 834227 := bstep (se 1 (by rfl) ⟨625670, by rfl⟩ : syracuseStep 834227 = 1251341) B1251341
theorem B834243 : Blo 830350 834243 := bstep (se 1 (by rfl) ⟨625682, by rfl⟩ : syracuseStep 834243 = 1251365) B1251365
theorem B1424081 : Blo 830350 1424081 := bstep (se 2 (by rfl) ⟨534030, by rfl⟩ : syracuseStep 1424081 = 1068061) B1068061
theorem B834259 : Blo 830350 834259 := bstep (se 1 (by rfl) ⟨625694, by rfl⟩ : syracuseStep 834259 = 1251389) B1251389
theorem B834275 : Blo 830350 834275 := bstep (se 1 (by rfl) ⟨625706, by rfl⟩ : syracuseStep 834275 = 1251413) B1251413
theorem B834291 : Blo 830350 834291 := bstep (se 1 (by rfl) ⟨625718, by rfl⟩ : syracuseStep 834291 = 1251437) B1251437
theorem B834307 : Blo 830350 834307 := bstep (se 1 (by rfl) ⟨625730, by rfl⟩ : syracuseStep 834307 = 1251461) B1251461
theorem B834323 : Blo 830350 834323 := bstep (se 1 (by rfl) ⟨625742, by rfl⟩ : syracuseStep 834323 = 1251485) B1251485
theorem B834339 : Blo 830350 834339 := bstep (se 1 (by rfl) ⟨625754, by rfl⟩ : syracuseStep 834339 = 1251509) B1251509
theorem B1424225 : Blo 830350 1424225 := bstep (se 2 (by rfl) ⟨534084, by rfl⟩ : syracuseStep 1424225 = 1068169) B1068169
theorem B2702605 : Blo 830350 2702605 := bstep (se 3 (by rfl) ⟨506738, by rfl⟩ : syracuseStep 2702605 = 1013477) B1013477
theorem B10665269 : Blo 830350 10665269 := bstep (se 5 (by rfl) ⟨499934, by rfl⟩ : syracuseStep 10665269 = 999869) B999869
theorem B5684579 : Blo 830350 5684579 := bstep (se 1 (by rfl) ⟨4263434, by rfl⟩ : syracuseStep 5684579 = 8526869) B8526869
theorem B3554765 : Blo 830350 3554765 := bstep (se 3 (by rfl) ⟨666518, by rfl⟩ : syracuseStep 3554765 = 1333037) B1333037
theorem B2080337 : Blo 830350 2080337 := bstep (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) B1560253
theorem B2375345 : Blo 830350 2375345 := bstep (se 2 (by rfl) ⟨890754, by rfl⟩ : syracuseStep 2375345 = 1781509) B1781509
theorem B2670317 : Blo 830350 2670317 := bstep (se 3 (by rfl) ⟨500684, by rfl⟩ : syracuseStep 2670317 = 1001369) B1001369
theorem B4505357 : Blo 830350 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B1425539 : Blo 830350 1425539 := bstep (se 1 (by rfl) ⟨1069154, by rfl⟩ : syracuseStep 1425539 = 2138309) B2138309
theorem B2670737 : Blo 830350 2670737 := bstep (se 2 (by rfl) ⟨1001526, by rfl⟩ : syracuseStep 2670737 = 2003053) B2003053
theorem B4210865 : Blo 830350 4210865 := bstep (se 2 (by rfl) ⟨1579074, by rfl⟩ : syracuseStep 4210865 = 3158149) B3158149
theorem B8110307 : Blo 830350 8110307 := bstep (se 1 (by rfl) ⟨6082730, by rfl⟩ : syracuseStep 8110307 = 12165461) B12165461
theorem B934195 : Blo 830350 934195 := bstep (se 1 (by rfl) ⟨700646, by rfl⟩ : syracuseStep 934195 = 1401293) B1401293
theorem B3162509 : Blo 830350 3162509 := bstep (se 3 (by rfl) ⟨592970, by rfl⟩ : syracuseStep 3162509 = 1185941) B1185941
theorem B934339 : Blo 830350 934339 := bstep (se 1 (by rfl) ⟨700754, by rfl⟩ : syracuseStep 934339 = 1401509) B1401509
theorem B4735493 : Blo 830350 4735493 := bstep (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) B887905
theorem B1688131 : Blo 830350 1688131 := bstep (se 1 (by rfl) ⟨1266098, by rfl⟩ : syracuseStep 1688131 = 2532197) B2532197
theorem B934483 : Blo 830350 934483 := bstep (se 1 (by rfl) ⟨700862, by rfl⟩ : syracuseStep 934483 = 1401725) B1401725
theorem B934627 : Blo 830350 934627 := bstep (se 1 (by rfl) ⟨700970, by rfl⟩ : syracuseStep 934627 = 1401941) B1401941
theorem B4506353 : Blo 830350 4506353 := bstep (se 2 (by rfl) ⟨1689882, by rfl⟩ : syracuseStep 4506353 = 3379765) B3379765
theorem B2802545 : Blo 830350 2802545 := bstep (se 2 (by rfl) ⟨1050954, by rfl⟩ : syracuseStep 2802545 = 2101909) B2101909
theorem B1622897 : Blo 830350 1622897 := bstep (se 2 (by rfl) ⟨608586, by rfl⟩ : syracuseStep 1622897 = 1217173) B1217173
theorem B934771 : Blo 830350 934771 := bstep (se 1 (by rfl) ⟨701078, by rfl⟩ : syracuseStep 934771 = 1402157) B1402157
theorem B934915 : Blo 830350 934915 := bstep (se 1 (by rfl) ⟨701186, by rfl⟩ : syracuseStep 934915 = 1402373) B1402373
theorem B935059 : Blo 830350 935059 := bstep (se 1 (by rfl) ⟨701294, by rfl⟩ : syracuseStep 935059 = 1402589) B1402589
theorem B4736177 : Blo 830350 4736177 := bstep (se 2 (by rfl) ⟨1776066, by rfl⟩ : syracuseStep 4736177 = 3552133) B3552133
theorem B3163313 : Blo 830350 3163313 := bstep (se 2 (by rfl) ⟨1186242, by rfl⟩ : syracuseStep 3163313 = 2372485) B2372485
theorem B935203 : Blo 830350 935203 := bstep (se 1 (by rfl) ⟨701402, by rfl⟩ : syracuseStep 935203 = 1402805) B1402805
theorem B2803085 : Blo 830350 2803085 := bstep (se 3 (by rfl) ⟨525578, by rfl⟩ : syracuseStep 2803085 = 1051157) B1051157
theorem B935347 : Blo 830350 935347 := bstep (se 1 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 935347 = 1403021) B1403021
theorem B1000883 : Blo 830350 1000883 := bstep (se 1 (by rfl) ⟨750662, by rfl⟩ : syracuseStep 1000883 = 1501325) B1501325
theorem B2803139 : Blo 830350 2803139 := bstep (se 1 (by rfl) ⟨2102354, by rfl⟩ : syracuseStep 2803139 = 4204709) B4204709
theorem B935491 : Blo 830350 935491 := bstep (se 1 (by rfl) ⟨701618, by rfl⟩ : syracuseStep 935491 = 1403237) B1403237
theorem B1689169 : Blo 830350 1689169 := bstep (se 2 (by rfl) ⟨633438, by rfl⟩ : syracuseStep 1689169 = 1266877) B1266877
theorem B4212323 : Blo 830350 4212323 := bstep (se 1 (by rfl) ⟨3159242, by rfl⟩ : syracuseStep 4212323 = 6318485) B6318485
theorem B11388529 : Blo 830350 11388529 := bstep (se 2 (by rfl) ⟨4270698, by rfl⟩ : syracuseStep 11388529 = 8541397) B8541397
theorem B2803409 : Blo 830350 2803409 := bstep (se 2 (by rfl) ⟨1051278, by rfl⟩ : syracuseStep 2803409 = 2102557) B2102557
theorem B935635 : Blo 830350 935635 := bstep (se 1 (by rfl) ⟨701726, by rfl⟩ : syracuseStep 935635 = 1403453) B1403453
theorem B1001219 : Blo 830350 1001219 := bstep (se 1 (by rfl) ⟨750914, by rfl⟩ : syracuseStep 1001219 = 1501829) B1501829
theorem B3163981 : Blo 830350 3163981 := bstep (se 3 (by rfl) ⟨593246, by rfl⟩ : syracuseStep 3163981 = 1186493) B1186493
theorem B935779 : Blo 830350 935779 := bstep (se 1 (by rfl) ⟨701834, by rfl⟩ : syracuseStep 935779 = 1403669) B1403669
theorem B1066979 : Blo 830350 1066979 := bstep (se 1 (by rfl) ⟨800234, by rfl⟩ : syracuseStep 1066979 = 1600469) B1600469
theorem B935923 : Blo 830350 935923 := bstep (se 1 (by rfl) ⟨701942, by rfl⟩ : syracuseStep 935923 = 1403885) B1403885
theorem B936067 : Blo 830350 936067 := bstep (se 1 (by rfl) ⟨702050, by rfl⟩ : syracuseStep 936067 = 1404101) B1404101
theorem B2803949 : Blo 830350 2803949 := bstep (se 3 (by rfl) ⟨525740, by rfl⟩ : syracuseStep 2803949 = 1051481) B1051481
theorem B936211 : Blo 830350 936211 := bstep (se 1 (by rfl) ⟨702158, by rfl⟩ : syracuseStep 936211 = 1404317) B1404317
theorem B2804003 : Blo 830350 2804003 := bstep (se 1 (by rfl) ⟨2103002, by rfl⟩ : syracuseStep 2804003 = 4206005) B4206005
theorem B1067347 : Blo 830350 1067347 := bstep (se 1 (by rfl) ⟨800510, by rfl⟩ : syracuseStep 1067347 = 1601021) B1601021
theorem B4213133 : Blo 830350 4213133 := bstep (se 3 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 4213133 = 1579925) B1579925
theorem B936355 : Blo 830350 936355 := bstep (se 1 (by rfl) ⟨702266, by rfl⟩ : syracuseStep 936355 = 1404533) B1404533
theorem B2804273 : Blo 830350 2804273 := bstep (se 2 (by rfl) ⟨1051602, by rfl⟩ : syracuseStep 2804273 = 2103205) B2103205
theorem B936499 : Blo 830350 936499 := bstep (se 1 (by rfl) ⟨702374, by rfl⟩ : syracuseStep 936499 = 1404749) B1404749
theorem B4737635 : Blo 830350 4737635 := bstep (se 1 (by rfl) ⟨3553226, by rfl⟩ : syracuseStep 4737635 = 7106453) B7106453
theorem B3164771 : Blo 830350 3164771 := bstep (se 1 (by rfl) ⟨2373578, by rfl⟩ : syracuseStep 3164771 = 4747157) B4747157
theorem B2312813 : Blo 830350 2312813 := bstep (se 3 (by rfl) ⟨433652, by rfl⟩ : syracuseStep 2312813 = 867305) B867305
theorem B1460867 : Blo 830350 1460867 := bstep (se 1 (by rfl) ⟨1095650, by rfl⟩ : syracuseStep 1460867 = 2191301) B2191301
theorem B11553461 : Blo 830350 11553461 := bstep (se 5 (by rfl) ⟨541568, by rfl⟩ : syracuseStep 11553461 = 1083137) B1083137
theorem B936643 : Blo 830350 936643 := bstep (se 1 (by rfl) ⟨702482, by rfl⟩ : syracuseStep 936643 = 1404965) B1404965
theorem B936787 : Blo 830350 936787 := bstep (se 1 (by rfl) ⟨702590, by rfl⟩ : syracuseStep 936787 = 1405181) B1405181
theorem B936931 : Blo 830350 936931 := bstep (se 1 (by rfl) ⟨702698, by rfl⟩ : syracuseStep 936931 = 1405397) B1405397
theorem B2804813 : Blo 830350 2804813 := bstep (se 3 (by rfl) ⟨525902, by rfl⟩ : syracuseStep 2804813 = 1051805) B1051805
theorem B937075 : Blo 830350 937075 := bstep (se 1 (by rfl) ⟨702806, by rfl⟩ : syracuseStep 937075 = 1405613) B1405613
theorem B2804867 : Blo 830350 2804867 := bstep (se 1 (by rfl) ⟨2103650, by rfl⟩ : syracuseStep 2804867 = 4207301) B4207301
theorem B2280611 : Blo 830350 2280611 := bstep (se 1 (by rfl) ⟨1710458, by rfl⟩ : syracuseStep 2280611 = 3420917) B3420917
theorem B3165425 : Blo 830350 3165425 := bstep (se 2 (by rfl) ⟨1187034, by rfl⟩ : syracuseStep 3165425 = 2374069) B2374069
theorem B937219 : Blo 830350 937219 := bstep (se 1 (by rfl) ⟨702914, by rfl⟩ : syracuseStep 937219 = 1405829) B1405829
theorem B2805137 : Blo 830350 2805137 := bstep (se 2 (by rfl) ⟨1051926, by rfl⟩ : syracuseStep 2805137 = 2103853) B2103853
theorem B1330577 : Blo 830350 1330577 := bstep (se 2 (by rfl) ⟨498966, by rfl⟩ : syracuseStep 1330577 = 997933) B997933
theorem B937363 : Blo 830350 937363 := bstep (se 1 (by rfl) ⟨703022, by rfl⟩ : syracuseStep 937363 = 1406045) B1406045
theorem B937507 : Blo 830350 937507 := bstep (se 1 (by rfl) ⟨703130, by rfl⟩ : syracuseStep 937507 = 1406261) B1406261
theorem B1330769 : Blo 830350 1330769 := bstep (se 2 (by rfl) ⟨499038, by rfl⟩ : syracuseStep 1330769 = 998077) B998077
theorem B937651 : Blo 830350 937651 := bstep (se 1 (by rfl) ⟨703238, by rfl⟩ : syracuseStep 937651 = 1406477) B1406477
theorem B5328611 : Blo 830350 5328611 := bstep (se 1 (by rfl) ⟨3996458, by rfl⟩ : syracuseStep 5328611 = 7992917) B7992917
theorem B3559139 : Blo 830350 3559139 := bstep (se 1 (by rfl) ⟨2669354, by rfl⟩ : syracuseStep 3559139 = 5338709) B5338709
theorem B937795 : Blo 830350 937795 := bstep (se 1 (by rfl) ⟨703346, by rfl⟩ : syracuseStep 937795 = 1406693) B1406693
theorem B1953649 : Blo 830350 1953649 := bstep (se 2 (by rfl) ⟨732618, by rfl⟩ : syracuseStep 1953649 = 1465237) B1465237
theorem B4509553 : Blo 830350 4509553 := bstep (se 2 (by rfl) ⟨1691082, by rfl⟩ : syracuseStep 4509553 = 3382165) B3382165
theorem B2805677 : Blo 830350 2805677 := bstep (se 3 (by rfl) ⟨526064, by rfl⟩ : syracuseStep 2805677 = 1052129) B1052129
theorem B937939 : Blo 830350 937939 := bstep (se 1 (by rfl) ⟨703454, by rfl⟩ : syracuseStep 937939 = 1406909) B1406909
theorem B2805731 : Blo 830350 2805731 := bstep (se 1 (by rfl) ⟨2104298, by rfl⟩ : syracuseStep 2805731 = 4208597) B4208597
theorem B938083 : Blo 830350 938083 := bstep (se 1 (by rfl) ⟨703562, by rfl⟩ : syracuseStep 938083 = 1407125) B1407125
theorem B2806001 : Blo 830350 2806001 := bstep (se 2 (by rfl) ⟨1052250, by rfl⟩ : syracuseStep 2806001 = 2104501) B2104501
theorem B938227 : Blo 830350 938227 := bstep (se 1 (by rfl) ⟨703670, by rfl⟩ : syracuseStep 938227 = 1407341) B1407341
theorem B1266049 : Blo 830350 1266049 := bstep (se 2 (by rfl) ⟨474768, by rfl⟩ : syracuseStep 1266049 = 949537) B949537
theorem B938371 : Blo 830350 938371 := bstep (se 1 (by rfl) ⟨703778, by rfl⟩ : syracuseStep 938371 = 1407557) B1407557
theorem B17125829 : Blo 830350 17125829 := bstep (se 4 (by rfl) ⟨1605546, by rfl⟩ : syracuseStep 17125829 = 3211093) B3211093
theorem B938515 : Blo 830350 938515 := bstep (se 1 (by rfl) ⟨703886, by rfl⟩ : syracuseStep 938515 = 1407773) B1407773
theorem B3166883 : Blo 830350 3166883 := bstep (se 1 (by rfl) ⟨2375162, by rfl⟩ : syracuseStep 3166883 = 4750325) B4750325
theorem B3166897 : Blo 830350 3166897 := bstep (se 2 (by rfl) ⟨1187586, by rfl⟩ : syracuseStep 3166897 = 2375173) B2375173
theorem B2806541 : Blo 830350 2806541 := bstep (se 3 (by rfl) ⟨526226, by rfl⟩ : syracuseStep 2806541 = 1052453) B1052453
theorem B2806595 : Blo 830350 2806595 := bstep (se 1 (by rfl) ⟨2104946, by rfl⟩ : syracuseStep 2806595 = 4209893) B4209893
theorem B2806865 : Blo 830350 2806865 := bstep (se 2 (by rfl) ⟨1052574, by rfl⟩ : syracuseStep 2806865 = 2105149) B2105149
theorem B1332371 : Blo 830350 1332371 := bstep (se 1 (by rfl) ⟨999278, by rfl⟩ : syracuseStep 1332371 = 1998557) B1998557
theorem B4216049 : Blo 830350 4216049 := bstep (se 2 (by rfl) ⟨1581018, by rfl⟩ : syracuseStep 4216049 = 3162037) B3162037
theorem B1922417 : Blo 830350 1922417 := bstep (se 2 (by rfl) ⟨720906, by rfl⟩ : syracuseStep 1922417 = 1441813) B1441813
theorem B3560881 : Blo 830350 3560881 := bstep (se 2 (by rfl) ⟨1335330, by rfl⟩ : syracuseStep 3560881 = 2670661) B2670661
theorem B1332755 : Blo 830350 1332755 := bstep (se 1 (by rfl) ⟨999566, by rfl⟩ : syracuseStep 1332755 = 1999133) B1999133
theorem B2807405 : Blo 830350 2807405 := bstep (se 3 (by rfl) ⟨526388, by rfl⟩ : syracuseStep 2807405 = 1052777) B1052777
theorem B1332883 : Blo 830350 1332883 := bstep (se 1 (by rfl) ⟨999662, by rfl⟩ : syracuseStep 1332883 = 1999325) B1999325
theorem B2807459 : Blo 830350 2807459 := bstep (se 1 (by rfl) ⟨2105594, by rfl⟩ : syracuseStep 2807459 = 4211189) B4211189
theorem B5330609 : Blo 830350 5330609 := bstep (se 2 (by rfl) ⟨1998978, by rfl⟩ : syracuseStep 5330609 = 3997957) B3997957
theorem B4740869 : Blo 830350 4740869 := bstep (se 4 (by rfl) ⟨444456, by rfl⟩ : syracuseStep 4740869 = 888913) B888913
theorem B2807729 : Blo 830350 2807729 := bstep (se 2 (by rfl) ⟨1052898, by rfl⟩ : syracuseStep 2807729 = 2105797) B2105797
theorem B14211125 : Blo 830350 14211125 := bstep (se 5 (by rfl) ⟨666146, by rfl⟩ : syracuseStep 14211125 = 1332293) B1332293
theorem B2250929 : Blo 830350 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B4741325 : Blo 830350 4741325 := bstep (se 3 (by rfl) ⟨888998, by rfl⟩ : syracuseStep 4741325 = 1777997) B1777997
theorem B1497361 : Blo 830350 1497361 := bstep (se 2 (by rfl) ⟨561510, by rfl⟩ : syracuseStep 1497361 = 1123021) B1123021
theorem B1333601 : Blo 830350 1333601 := bstep (se 2 (by rfl) ⟨500100, by rfl⟩ : syracuseStep 1333601 = 1000201) B1000201
theorem B1825187 : Blo 830350 1825187 := bstep (se 1 (by rfl) ⟨1368890, by rfl⟩ : syracuseStep 1825187 = 2737781) B2737781
theorem B2808269 : Blo 830350 2808269 := bstep (se 3 (by rfl) ⟨526550, by rfl⟩ : syracuseStep 2808269 = 1053101) B1053101
theorem B9624035 : Blo 830350 9624035 := bstep (se 1 (by rfl) ⟨7218026, by rfl⟩ : syracuseStep 9624035 = 14436053) B14436053
theorem B2808323 : Blo 830350 2808323 := bstep (se 1 (by rfl) ⟨2106242, by rfl⟩ : syracuseStep 2808323 = 4212485) B4212485
theorem B1333793 : Blo 830350 1333793 := bstep (se 2 (by rfl) ⟨500172, by rfl⟩ : syracuseStep 1333793 = 1000345) B1000345
theorem B1497649 : Blo 830350 1497649 := bstep (se 2 (by rfl) ⟨561618, by rfl⟩ : syracuseStep 1497649 = 1123237) B1123237
theorem B3005041 : Blo 830350 3005041 := bstep (se 2 (by rfl) ⟨1126890, by rfl⟩ : syracuseStep 3005041 = 2253781) B2253781
theorem B4217507 : Blo 830350 4217507 := bstep (se 1 (by rfl) ⟨3163130, by rfl⟩ : syracuseStep 4217507 = 6326261) B6326261
theorem B2808593 : Blo 830350 2808593 := bstep (se 2 (by rfl) ⟨1053222, by rfl⟩ : syracuseStep 2808593 = 2106445) B2106445
theorem B1268531 : Blo 830350 1268531 := bstep (se 1 (by rfl) ⟨951398, by rfl⟩ : syracuseStep 1268531 = 1902797) B1902797
theorem B2251793 : Blo 830350 2251793 := bstep (se 2 (by rfl) ⟨844422, by rfl⟩ : syracuseStep 2251793 = 1688845) B1688845
theorem B2841635 : Blo 830350 2841635 := bstep (se 1 (by rfl) ⟨2131226, by rfl⟩ : syracuseStep 2841635 = 4262453) B4262453
theorem B2284817 : Blo 830350 2284817 := bstep (se 2 (by rfl) ⟨856806, by rfl⟩ : syracuseStep 2284817 = 1713613) B1713613
theorem B2809133 : Blo 830350 2809133 := bstep (se 3 (by rfl) ⟨526712, by rfl⟩ : syracuseStep 2809133 = 1053425) B1053425
theorem B5332301 : Blo 830350 5332301 := bstep (se 3 (by rfl) ⟨999806, by rfl⟩ : syracuseStep 5332301 = 1999613) B1999613
theorem B3562829 : Blo 830350 3562829 := bstep (se 3 (by rfl) ⟨668030, by rfl⟩ : syracuseStep 3562829 = 1336061) B1336061
theorem B2809187 : Blo 830350 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B4218317 : Blo 830350 4218317 := bstep (se 3 (by rfl) ⟨790934, by rfl⟩ : syracuseStep 4218317 = 1581869) B1581869
theorem B2252333 : Blo 830350 2252333 := bstep (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) B844625
theorem B2809457 : Blo 830350 2809457 := bstep (se 2 (by rfl) ⟨1053546, by rfl⟩ : syracuseStep 2809457 = 2107093) B2107093
theorem B1498961 : Blo 830350 1498961 := bstep (se 2 (by rfl) ⟨562110, by rfl⟩ : syracuseStep 1498961 = 1124221) B1124221
theorem B1499249 : Blo 830350 1499249 := bstep (se 2 (by rfl) ⟨562218, by rfl⟩ : syracuseStep 1499249 = 1124437) B1124437
theorem B2809997 : Blo 830350 2809997 := bstep (se 3 (by rfl) ⟨526874, by rfl⟩ : syracuseStep 2809997 = 1053749) B1053749
theorem B2810051 : Blo 830350 2810051 := bstep (se 1 (by rfl) ⟨2107538, by rfl⟩ : syracuseStep 2810051 = 4215077) B4215077
theorem B2253005 : Blo 830350 2253005 := bstep (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) B844877
theorem B1335523 : Blo 830350 1335523 := bstep (se 1 (by rfl) ⟨1001642, by rfl⟩ : syracuseStep 1335523 = 2003285) B2003285
theorem B4055309 : Blo 830350 4055309 := bstep (se 3 (by rfl) ⟨760370, by rfl⟩ : syracuseStep 4055309 = 1520741) B1520741
theorem B1335619 : Blo 830350 1335619 := bstep (se 1 (by rfl) ⟨1001714, by rfl⟩ : syracuseStep 1335619 = 2003429) B2003429
theorem B2810321 : Blo 830350 2810321 := bstep (se 2 (by rfl) ⟨1053870, by rfl⟩ : syracuseStep 2810321 = 2107741) B2107741
theorem B1401313 : Blo 830350 1401313 := bstep (se 2 (by rfl) ⟨525492, by rfl⟩ : syracuseStep 1401313 = 1050985) B1050985
theorem B1335779 : Blo 830350 1335779 := bstep (se 1 (by rfl) ⟨1001834, by rfl⟩ : syracuseStep 1335779 = 2003669) B2003669
theorem B1401347 : Blo 830350 1401347 := bstep (se 1 (by rfl) ⟨1051010, by rfl⟩ : syracuseStep 1401347 = 2102021) B2102021
theorem B12182069 : Blo 830350 12182069 := bstep (se 5 (by rfl) ⟨571034, by rfl⟩ : syracuseStep 12182069 = 1142069) B1142069
theorem B1401475 : Blo 830350 1401475 := bstep (se 1 (by rfl) ⟨1051106, by rfl⟩ : syracuseStep 1401475 = 2102213) B2102213
theorem B1401617 : Blo 830350 1401617 := bstep (se 2 (by rfl) ⟨525606, by rfl⟩ : syracuseStep 1401617 = 1051213) B1051213
theorem B1401745 : Blo 830350 1401745 := bstep (se 2 (by rfl) ⟨525654, by rfl⟩ : syracuseStep 1401745 = 1051309) B1051309
theorem B1401779 : Blo 830350 1401779 := bstep (se 1 (by rfl) ⟨1051334, by rfl⟩ : syracuseStep 1401779 = 2102669) B2102669
theorem B6317027 : Blo 830350 6317027 := bstep (se 1 (by rfl) ⟨4737770, by rfl⟩ : syracuseStep 6317027 = 9475541) B9475541
theorem B2810861 : Blo 830350 2810861 := bstep (se 3 (by rfl) ⟨527036, by rfl⟩ : syracuseStep 2810861 = 1054073) B1054073
theorem B2810915 : Blo 830350 2810915 := bstep (se 1 (by rfl) ⟨2108186, by rfl⟩ : syracuseStep 2810915 = 4216373) B4216373
theorem B4744241 : Blo 830350 4744241 := bstep (se 2 (by rfl) ⟨1779090, by rfl⟩ : syracuseStep 4744241 = 3558181) B3558181
theorem B1401907 : Blo 830350 1401907 := bstep (se 1 (by rfl) ⟨1051430, by rfl⟩ : syracuseStep 1401907 = 2102861) B2102861
theorem B1402049 : Blo 830350 1402049 := bstep (se 2 (by rfl) ⟨525768, by rfl⟩ : syracuseStep 1402049 = 1051537) B1051537
theorem B2811185 : Blo 830350 2811185 := bstep (se 2 (by rfl) ⟨1054194, by rfl⟩ : syracuseStep 2811185 = 2108389) B2108389
theorem B1402177 : Blo 830350 1402177 := bstep (se 2 (by rfl) ⟨525816, by rfl⟩ : syracuseStep 1402177 = 1051633) B1051633
theorem B3990883 : Blo 830350 3990883 := bstep (se 1 (by rfl) ⟨2993162, by rfl⟩ : syracuseStep 3990883 = 5986325) B5986325
theorem B1402211 : Blo 830350 1402211 := bstep (se 1 (by rfl) ⟨1051658, by rfl⟩ : syracuseStep 1402211 = 2103317) B2103317
theorem B1402339 : Blo 830350 1402339 := bstep (se 1 (by rfl) ⟨1051754, by rfl⟩ : syracuseStep 1402339 = 2103509) B2103509
theorem B1402481 : Blo 830350 1402481 := bstep (se 2 (by rfl) ⟨525930, by rfl⟩ : syracuseStep 1402481 = 1051861) B1051861
theorem B1402609 : Blo 830350 1402609 := bstep (se 2 (by rfl) ⟨525978, by rfl⟩ : syracuseStep 1402609 = 1051957) B1051957
theorem B1402643 : Blo 830350 1402643 := bstep (se 1 (by rfl) ⟨1051982, by rfl⟩ : syracuseStep 1402643 = 2103965) B2103965
theorem B2811725 : Blo 830350 2811725 := bstep (se 3 (by rfl) ⟨527198, by rfl⟩ : syracuseStep 2811725 = 1054397) B1054397
theorem B2811779 : Blo 830350 2811779 := bstep (se 1 (by rfl) ⟨2108834, by rfl⟩ : syracuseStep 2811779 = 4217669) B4217669
theorem B1402771 : Blo 830350 1402771 := bstep (se 1 (by rfl) ⟨1052078, by rfl⟩ : syracuseStep 1402771 = 2104157) B2104157
theorem B1140689 : Blo 830350 1140689 := bstep (se 2 (by rfl) ⟨427758, by rfl⟩ : syracuseStep 1140689 = 855517) B855517
theorem B2254819 : Blo 830350 2254819 := bstep (se 1 (by rfl) ⟨1691114, by rfl⟩ : syracuseStep 2254819 = 3382229) B3382229
theorem B1894403 : Blo 830350 1894403 := bstep (se 1 (by rfl) ⟨1420802, by rfl⟩ : syracuseStep 1894403 = 2841605) B2841605
theorem B1402913 : Blo 830350 1402913 := bstep (se 2 (by rfl) ⟨526092, by rfl⟩ : syracuseStep 1402913 = 1052185) B1052185
theorem B9463877 : Blo 830350 9463877 := bstep (se 4 (by rfl) ⟨887238, by rfl⟩ : syracuseStep 9463877 = 1774477) B1774477
theorem B2812049 : Blo 830350 2812049 := bstep (se 2 (by rfl) ⟨1054518, by rfl⟩ : syracuseStep 2812049 = 2109037) B2109037
theorem B1403041 : Blo 830350 1403041 := bstep (se 2 (by rfl) ⟨526140, by rfl⟩ : syracuseStep 1403041 = 1052281) B1052281
theorem B1403075 : Blo 830350 1403075 := bstep (se 1 (by rfl) ⟨1052306, by rfl⟩ : syracuseStep 1403075 = 2104613) B2104613
theorem B2844877 : Blo 830350 2844877 := bstep (se 3 (by rfl) ⟨533414, by rfl⟩ : syracuseStep 2844877 = 1066829) B1066829
theorem B4221233 : Blo 830350 4221233 := bstep (se 2 (by rfl) ⟨1582962, by rfl⟩ : syracuseStep 4221233 = 3165925) B3165925
theorem B1403203 : Blo 830350 1403203 := bstep (se 1 (by rfl) ⟨1052402, by rfl⟩ : syracuseStep 1403203 = 2104805) B2104805
theorem B1894769 : Blo 830350 1894769 := bstep (se 2 (by rfl) ⟨710538, by rfl⟩ : syracuseStep 1894769 = 1421077) B1421077
theorem B51243461 : Blo 830350 51243461 := bstep (se 4 (by rfl) ⟨4804074, by rfl⟩ : syracuseStep 51243461 = 9608149) B9608149
theorem B1403345 : Blo 830350 1403345 := bstep (se 2 (by rfl) ⟨526254, by rfl⟩ : syracuseStep 1403345 = 1052509) B1052509
theorem B4745699 : Blo 830350 4745699 := bstep (se 1 (by rfl) ⟨3559274, by rfl⟩ : syracuseStep 4745699 = 7118549) B7118549
theorem B2845219 : Blo 830350 2845219 := bstep (se 1 (by rfl) ⟨2133914, by rfl⟩ : syracuseStep 2845219 = 4267829) B4267829
theorem B1403473 : Blo 830350 1403473 := bstep (se 2 (by rfl) ⟨526302, by rfl⟩ : syracuseStep 1403473 = 1052605) B1052605
theorem B1403507 : Blo 830350 1403507 := bstep (se 1 (by rfl) ⟨1052630, by rfl⟩ : syracuseStep 1403507 = 2105261) B2105261
theorem B2812589 : Blo 830350 2812589 := bstep (se 3 (by rfl) ⟨527360, by rfl⟩ : syracuseStep 2812589 = 1054721) B1054721
theorem B2812643 : Blo 830350 2812643 := bstep (se 1 (by rfl) ⟨2109482, by rfl⟩ : syracuseStep 2812643 = 4218965) B4218965
theorem B1403635 : Blo 830350 1403635 := bstep (se 1 (by rfl) ⟨1052726, by rfl⟩ : syracuseStep 1403635 = 2105453) B2105453
theorem B20573041 : Blo 830350 20573041 := bstep (se 2 (by rfl) ⟨7714890, by rfl⟩ : syracuseStep 20573041 = 15429781) B15429781
theorem B1403777 : Blo 830350 1403777 := bstep (se 2 (by rfl) ⟨526416, by rfl⟩ : syracuseStep 1403777 = 1052833) B1052833
theorem B1502147 : Blo 830350 1502147 := bstep (se 1 (by rfl) ⟨1126610, by rfl⟩ : syracuseStep 1502147 = 2253221) B2253221
theorem B2812913 : Blo 830350 2812913 := bstep (se 2 (by rfl) ⟨1054842, by rfl⟩ : syracuseStep 2812913 = 2109685) B2109685
theorem B1403905 : Blo 830350 1403905 := bstep (se 2 (by rfl) ⟨526464, by rfl⟩ : syracuseStep 1403905 = 1052929) B1052929
theorem B1403939 : Blo 830350 1403939 := bstep (se 1 (by rfl) ⟨1052954, by rfl⟩ : syracuseStep 1403939 = 2105909) B2105909
theorem B1404067 : Blo 830350 1404067 := bstep (se 1 (by rfl) ⟨1053050, by rfl⟩ : syracuseStep 1404067 = 2106101) B2106101
theorem B4058275 : Blo 830350 4058275 := bstep (se 1 (by rfl) ⟨3043706, by rfl⟩ : syracuseStep 4058275 = 6087413) B6087413
theorem B1502435 : Blo 830350 1502435 := bstep (se 1 (by rfl) ⟨1126826, by rfl⟩ : syracuseStep 1502435 = 2253653) B2253653
theorem B9268465 : Blo 830350 9268465 := bstep (se 2 (by rfl) ⟨3475674, by rfl⟩ : syracuseStep 9268465 = 6951349) B6951349
theorem B7105805 : Blo 830350 7105805 := bstep (se 3 (by rfl) ⟨1332338, by rfl⟩ : syracuseStep 7105805 = 2664677) B2664677
theorem B1404209 : Blo 830350 1404209 := bstep (se 2 (by rfl) ⟨526578, by rfl⟩ : syracuseStep 1404209 = 1053157) B1053157
theorem B1142147 : Blo 830350 1142147 := bstep (se 1 (by rfl) ⟨856610, by rfl⟩ : syracuseStep 1142147 = 1713221) B1713221
theorem B1404337 : Blo 830350 1404337 := bstep (se 2 (by rfl) ⟨526626, by rfl⟩ : syracuseStep 1404337 = 1053253) B1053253
theorem B4746701 : Blo 830350 4746701 := bstep (se 3 (by rfl) ⟨890006, by rfl⟩ : syracuseStep 4746701 = 1780013) B1780013
theorem B1404371 : Blo 830350 1404371 := bstep (se 1 (by rfl) ⟨1053278, by rfl⟩ : syracuseStep 1404371 = 2106557) B2106557
theorem B2813453 : Blo 830350 2813453 := bstep (se 3 (by rfl) ⟨527522, by rfl⟩ : syracuseStep 2813453 = 1055045) B1055045
theorem B2813507 : Blo 830350 2813507 := bstep (se 1 (by rfl) ⟨2110130, by rfl⟩ : syracuseStep 2813507 = 4220261) B4220261
theorem B1404499 : Blo 830350 1404499 := bstep (se 1 (by rfl) ⟨1053374, by rfl⟩ : syracuseStep 1404499 = 2106749) B2106749
theorem B1830595 : Blo 830350 1830595 := bstep (se 1 (by rfl) ⟨1372946, by rfl⟩ : syracuseStep 1830595 = 2745893) B2745893
theorem B1404641 : Blo 830350 1404641 := bstep (se 2 (by rfl) ⟨526740, by rfl⟩ : syracuseStep 1404641 = 1053481) B1053481
theorem B4222691 : Blo 830350 4222691 := bstep (se 1 (by rfl) ⟨3167018, by rfl⟩ : syracuseStep 4222691 = 6334037) B6334037
theorem B1601297 : Blo 830350 1601297 := bstep (se 2 (by rfl) ⟨600486, by rfl⟩ : syracuseStep 1601297 = 1200973) B1200973
theorem B3993421 : Blo 830350 3993421 := bstep (se 3 (by rfl) ⟨748766, by rfl⟩ : syracuseStep 3993421 = 1497533) B1497533
theorem B2813777 : Blo 830350 2813777 := bstep (se 2 (by rfl) ⟨1055166, by rfl⟩ : syracuseStep 2813777 = 2110333) B2110333
theorem B1404769 : Blo 830350 1404769 := bstep (se 2 (by rfl) ⟨526788, by rfl⟩ : syracuseStep 1404769 = 1053577) B1053577
theorem B1404803 : Blo 830350 1404803 := bstep (se 1 (by rfl) ⟨1053602, by rfl⟩ : syracuseStep 1404803 = 2107205) B2107205
theorem B56323981 : Blo 830350 56323981 := bstep (se 3 (by rfl) ⟨10560746, by rfl⟩ : syracuseStep 56323981 = 21121493) B21121493
theorem B1404931 : Blo 830350 1404931 := bstep (se 1 (by rfl) ⟨1053698, by rfl⟩ : syracuseStep 1404931 = 2107397) B2107397
theorem B1405073 : Blo 830350 1405073 := bstep (se 2 (by rfl) ⟨526902, by rfl⟩ : syracuseStep 1405073 = 1053805) B1053805
theorem B1405201 : Blo 830350 1405201 := bstep (se 2 (by rfl) ⟨526950, by rfl⟩ : syracuseStep 1405201 = 1053901) B1053901
theorem B1405235 : Blo 830350 1405235 := bstep (se 1 (by rfl) ⟨1053926, by rfl⟩ : syracuseStep 1405235 = 2107853) B2107853
theorem B2814317 : Blo 830350 2814317 := bstep (se 3 (by rfl) ⟨527684, by rfl⟩ : syracuseStep 2814317 = 1055369) B1055369
theorem B2814371 : Blo 830350 2814371 := bstep (se 1 (by rfl) ⟨2110778, by rfl⟩ : syracuseStep 2814371 = 4221557) B4221557
theorem B2879921 : Blo 830350 2879921 := bstep (se 2 (by rfl) ⟨1079970, by rfl⟩ : syracuseStep 2879921 = 2159941) B2159941
theorem B1405363 : Blo 830350 1405363 := bstep (se 1 (by rfl) ⟨1054022, by rfl⟩ : syracuseStep 1405363 = 2108045) B2108045
theorem B4223501 : Blo 830350 4223501 := bstep (se 3 (by rfl) ⟨791906, by rfl⟩ : syracuseStep 4223501 = 1583813) B1583813
theorem B1405505 : Blo 830350 1405505 := bstep (se 2 (by rfl) ⟨527064, by rfl⟩ : syracuseStep 1405505 = 1054129) B1054129
theorem B2814641 : Blo 830350 2814641 := bstep (se 2 (by rfl) ⟨1055490, by rfl⟩ : syracuseStep 2814641 = 2110981) B2110981
theorem B1405633 : Blo 830350 1405633 := bstep (se 2 (by rfl) ⟨527112, by rfl⟩ : syracuseStep 1405633 = 1054225) B1054225
theorem B2847437 : Blo 830350 2847437 := bstep (se 3 (by rfl) ⟨533894, by rfl⟩ : syracuseStep 2847437 = 1067789) B1067789
theorem B1405667 : Blo 830350 1405667 := bstep (se 1 (by rfl) ⟨1054250, by rfl⟩ : syracuseStep 1405667 = 2108501) B2108501
theorem B1995587 : Blo 830350 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B1405795 : Blo 830350 1405795 := bstep (se 1 (by rfl) ⟨1054346, by rfl⟩ : syracuseStep 1405795 = 2108693) B2108693
theorem B1405937 : Blo 830350 1405937 := bstep (se 2 (by rfl) ⟨527226, by rfl⟩ : syracuseStep 1405937 = 1054453) B1054453
theorem B7599217 : Blo 830350 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B1406065 : Blo 830350 1406065 := bstep (se 2 (by rfl) ⟨527274, by rfl⟩ : syracuseStep 1406065 = 1054549) B1054549
theorem B1406099 : Blo 830350 1406099 := bstep (se 1 (by rfl) ⟨1054574, by rfl⟩ : syracuseStep 1406099 = 2109149) B2109149
theorem B2815181 : Blo 830350 2815181 := bstep (se 3 (by rfl) ⟨527846, by rfl⟩ : syracuseStep 2815181 = 1055693) B1055693
theorem B3994865 : Blo 830350 3994865 := bstep (se 2 (by rfl) ⟨1498074, by rfl⟩ : syracuseStep 3994865 = 2996149) B2996149
theorem B2815235 : Blo 830350 2815235 := bstep (se 1 (by rfl) ⟨2111426, by rfl⟩ : syracuseStep 2815235 = 4222853) B4222853
theorem B1406227 : Blo 830350 1406227 := bstep (se 1 (by rfl) ⟨1054670, by rfl⟩ : syracuseStep 1406227 = 2109341) B2109341
theorem B1406369 : Blo 830350 1406369 := bstep (se 2 (by rfl) ⟨527388, by rfl⟩ : syracuseStep 1406369 = 1054777) B1054777
theorem B2815505 : Blo 830350 2815505 := bstep (se 2 (by rfl) ⟨1055814, by rfl⟩ : syracuseStep 2815505 = 2111629) B2111629
theorem B1406497 : Blo 830350 1406497 := bstep (se 2 (by rfl) ⟨527436, by rfl⟩ : syracuseStep 1406497 = 1054873) B1054873
theorem B1406531 : Blo 830350 1406531 := bstep (se 1 (by rfl) ⟨1054898, by rfl⟩ : syracuseStep 1406531 = 2109797) B2109797
theorem B11368117 : Blo 830350 11368117 := bstep (se 5 (by rfl) ⟨532880, by rfl⟩ : syracuseStep 11368117 = 1065761) B1065761
theorem B1406659 : Blo 830350 1406659 := bstep (se 1 (by rfl) ⟨1054994, by rfl⟩ : syracuseStep 1406659 = 2109989) B2109989
theorem B1406801 : Blo 830350 1406801 := bstep (se 2 (by rfl) ⟨527550, by rfl⟩ : syracuseStep 1406801 = 1055101) B1055101
theorem B1898417 : Blo 830350 1898417 := bstep (se 2 (by rfl) ⟨711906, by rfl⟩ : syracuseStep 1898417 = 1423813) B1423813
theorem B1406929 : Blo 830350 1406929 := bstep (se 2 (by rfl) ⟨527598, by rfl⟩ : syracuseStep 1406929 = 1055197) B1055197
theorem B1406963 : Blo 830350 1406963 := bstep (se 1 (by rfl) ⟨1055222, by rfl⟩ : syracuseStep 1406963 = 2110445) B2110445
theorem B1407091 : Blo 830350 1407091 := bstep (se 1 (by rfl) ⟨1055318, by rfl⟩ : syracuseStep 1407091 = 2110637) B2110637
theorem B6322373 : Blo 830350 6322373 := bstep (se 4 (by rfl) ⟨592722, by rfl⟩ : syracuseStep 6322373 = 1185445) B1185445
theorem B1407233 : Blo 830350 1407233 := bstep (se 2 (by rfl) ⟨527712, by rfl⟩ : syracuseStep 1407233 = 1055425) B1055425
theorem B4749617 : Blo 830350 4749617 := bstep (se 2 (by rfl) ⟨1781106, by rfl⟩ : syracuseStep 4749617 = 3562213) B3562213
theorem B3602765 : Blo 830350 3602765 := bstep (se 3 (by rfl) ⟨675518, by rfl⟩ : syracuseStep 3602765 = 1351037) B1351037
theorem B1407361 : Blo 830350 1407361 := bstep (se 2 (by rfl) ⟨527760, by rfl⟩ : syracuseStep 1407361 = 1055521) B1055521
theorem B1407395 : Blo 830350 1407395 := bstep (se 1 (by rfl) ⟨1055546, by rfl⟩ : syracuseStep 1407395 = 2111093) B2111093
theorem B1407523 : Blo 830350 1407523 := bstep (se 1 (by rfl) ⟨1055642, by rfl⟩ : syracuseStep 1407523 = 2111285) B2111285
theorem B1407665 : Blo 830350 1407665 := bstep (se 2 (by rfl) ⟨527874, by rfl⟩ : syracuseStep 1407665 = 1055749) B1055749
theorem B5995205 : Blo 830350 5995205 := bstep (se 4 (by rfl) ⟨562050, by rfl⟩ : syracuseStep 5995205 = 1124101) B1124101
theorem B1407793 : Blo 830350 1407793 := bstep (se 2 (by rfl) ⟨527922, by rfl⟩ : syracuseStep 1407793 = 1055845) B1055845
theorem B1407827 : Blo 830350 1407827 := bstep (se 1 (by rfl) ⟨1055870, by rfl⟩ : syracuseStep 1407827 = 2111741) B2111741
theorem B1407955 : Blo 830350 1407955 := bstep (se 1 (by rfl) ⟨1055966, by rfl⟩ : syracuseStep 1407955 = 2111933) B2111933
theorem B4815949 : Blo 830350 4815949 := bstep (se 3 (by rfl) ⟨902990, by rfl⟩ : syracuseStep 4815949 = 1805981) B1805981
theorem B1900241 : Blo 830350 1900241 := bstep (se 2 (by rfl) ⟨712590, by rfl⟩ : syracuseStep 1900241 = 1425181) B1425181
theorem B4751075 : Blo 830350 4751075 := bstep (se 1 (by rfl) ⟨3563306, by rfl⟩ : syracuseStep 4751075 = 7126613) B7126613
theorem B9469709 : Blo 830350 9469709 := bstep (se 3 (by rfl) ⟨1775570, by rfl⟩ : syracuseStep 9469709 = 3551141) B3551141
theorem B1605539 : Blo 830350 1605539 := bstep (se 1 (by rfl) ⟨1204154, by rfl⟩ : syracuseStep 1605539 = 2408309) B2408309
theorem B950359 : Blo 830350 950359 := bstep (se 1 (by rfl) ⟨712769, by rfl⟩ : syracuseStep 950359 = 1425539) B1425539
theorem B6324317 : Blo 830350 6324317 := bstep (se 3 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 6324317 = 2371619) B2371619
theorem B3997997 : Blo 830350 3997997 := bstep (se 3 (by rfl) ⟨749624, by rfl⟩ : syracuseStep 3997997 = 1499249) B1499249
theorem B1245527 : Blo 830350 1245527 := bstep (se 1 (by rfl) ⟨934145, by rfl⟩ : syracuseStep 1245527 = 1868291) B1868291
theorem B1245593 : Blo 830350 1245593 := bstep (se 2 (by rfl) ⟨467097, by rfl⟩ : syracuseStep 1245593 = 934195) B934195
theorem B1245707 : Blo 830350 1245707 := bstep (se 1 (by rfl) ⟨934280, by rfl⟩ : syracuseStep 1245707 = 1868561) B1868561
theorem B1245719 : Blo 830350 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B1868363 : Blo 830350 1868363 := bstep (se 1 (by rfl) ⟨1401272, by rfl⟩ : syracuseStep 1868363 = 2802545) B2802545
theorem B1081931 : Blo 830350 1081931 := bstep (se 1 (by rfl) ⟨811448, by rfl⟩ : syracuseStep 1081931 = 1622897) B1622897
theorem B1245785 : Blo 830350 1245785 := bstep (se 2 (by rfl) ⟨467169, by rfl⟩ : syracuseStep 1245785 = 934339) B934339
theorem B21627485 : Blo 830350 21627485 := bstep (se 3 (by rfl) ⟨4055153, by rfl⟩ : syracuseStep 21627485 = 8110307) B8110307
theorem B1868417 : Blo 830350 1868417 := bstep (se 2 (by rfl) ⟨700656, by rfl⟩ : syracuseStep 1868417 = 1401313) B1401313
theorem B1245899 : Blo 830350 1245899 := bstep (se 1 (by rfl) ⟨934424, by rfl⟩ : syracuseStep 1245899 = 1868849) B1868849
theorem B1245911 : Blo 830350 1245911 := bstep (se 1 (by rfl) ⟨934433, by rfl⟩ : syracuseStep 1245911 = 1868867) B1868867
theorem B1245977 : Blo 830350 1245977 := bstep (se 2 (by rfl) ⟨467241, by rfl⟩ : syracuseStep 1245977 = 934483) B934483
theorem B1868633 : Blo 830350 1868633 := bstep (se 2 (by rfl) ⟨700737, by rfl⟩ : syracuseStep 1868633 = 1401475) B1401475
theorem B1246091 : Blo 830350 1246091 := bstep (se 1 (by rfl) ⟨934568, by rfl⟩ : syracuseStep 1246091 = 1869137) B1869137
theorem B1246103 : Blo 830350 1246103 := bstep (se 1 (by rfl) ⟨934577, by rfl⟩ : syracuseStep 1246103 = 1869155) B1869155
theorem B1868723 : Blo 830350 1868723 := bstep (se 1 (by rfl) ⟨1401542, by rfl⟩ : syracuseStep 1868723 = 2803085) B2803085
theorem B1868759 : Blo 830350 1868759 := bstep (se 1 (by rfl) ⟨1401569, by rfl⟩ : syracuseStep 1868759 = 2803139) B2803139
theorem B1246169 : Blo 830350 1246169 := bstep (se 2 (by rfl) ⟨467313, by rfl⟩ : syracuseStep 1246169 = 934627) B934627
theorem B5342273 : Blo 830350 5342273 := bstep (se 2 (by rfl) ⟨2003352, by rfl⟩ : syracuseStep 5342273 = 4006705) B4006705
theorem B1246283 : Blo 830350 1246283 := bstep (se 1 (by rfl) ⟨934712, by rfl⟩ : syracuseStep 1246283 = 1869425) B1869425
theorem B1246295 : Blo 830350 1246295 := bstep (se 1 (by rfl) ⟨934721, by rfl⟩ : syracuseStep 1246295 = 1869443) B1869443
theorem B1868939 : Blo 830350 1868939 := bstep (se 1 (by rfl) ⟨1401704, by rfl⟩ : syracuseStep 1868939 = 2803409) B2803409
theorem B1246361 : Blo 830350 1246361 := bstep (se 2 (by rfl) ⟨467385, by rfl⟩ : syracuseStep 1246361 = 934771) B934771
theorem B7603379 : Blo 830350 7603379 := bstep (se 1 (by rfl) ⟨5702534, by rfl⟩ : syracuseStep 7603379 = 11405069) B11405069
theorem B1868993 : Blo 830350 1868993 := bstep (se 2 (by rfl) ⟨700872, by rfl⟩ : syracuseStep 1868993 = 1401745) B1401745
theorem B1246475 : Blo 830350 1246475 := bstep (se 1 (by rfl) ⟨934856, by rfl⟩ : syracuseStep 1246475 = 1869713) B1869713
theorem B1246487 : Blo 830350 1246487 := bstep (se 1 (by rfl) ⟨934865, by rfl⟩ : syracuseStep 1246487 = 1869731) B1869731
theorem B1246553 : Blo 830350 1246553 := bstep (se 2 (by rfl) ⟨467457, by rfl⟩ : syracuseStep 1246553 = 934915) B934915
theorem B1869209 : Blo 830350 1869209 := bstep (se 2 (by rfl) ⟨700953, by rfl⟩ : syracuseStep 1869209 = 1401907) B1401907
theorem B1246667 : Blo 830350 1246667 := bstep (se 1 (by rfl) ⟨935000, by rfl⟩ : syracuseStep 1246667 = 1870001) B1870001
theorem B1246679 : Blo 830350 1246679 := bstep (se 1 (by rfl) ⟨935009, by rfl⟩ : syracuseStep 1246679 = 1870019) B1870019
theorem B1869299 : Blo 830350 1869299 := bstep (se 1 (by rfl) ⟨1401974, by rfl⟩ : syracuseStep 1869299 = 2803949) B2803949
theorem B1869335 : Blo 830350 1869335 := bstep (se 1 (by rfl) ⟨1402001, by rfl⟩ : syracuseStep 1869335 = 2804003) B2804003
theorem B1246745 : Blo 830350 1246745 := bstep (se 2 (by rfl) ⟨467529, by rfl⟩ : syracuseStep 1246745 = 935059) B935059
theorem B1246859 : Blo 830350 1246859 := bstep (se 1 (by rfl) ⟨935144, by rfl⟩ : syracuseStep 1246859 = 1870289) B1870289
theorem B1246871 : Blo 830350 1246871 := bstep (se 1 (by rfl) ⟨935153, by rfl⟩ : syracuseStep 1246871 = 1870307) B1870307
theorem B1869515 : Blo 830350 1869515 := bstep (se 1 (by rfl) ⟨1402136, by rfl⟩ : syracuseStep 1869515 = 2804273) B2804273
theorem B1246937 : Blo 830350 1246937 := bstep (se 2 (by rfl) ⟨467601, by rfl⟩ : syracuseStep 1246937 = 935203) B935203
theorem B1869569 : Blo 830350 1869569 := bstep (se 2 (by rfl) ⟨701088, by rfl⟩ : syracuseStep 1869569 = 1402177) B1402177
theorem B7702307 : Blo 830350 7702307 := bstep (se 1 (by rfl) ⟨5776730, by rfl⟩ : syracuseStep 7702307 = 11553461) B11553461
theorem B1247051 : Blo 830350 1247051 := bstep (se 1 (by rfl) ⟨935288, by rfl⟩ : syracuseStep 1247051 = 1870577) B1870577
theorem B1247063 : Blo 830350 1247063 := bstep (se 1 (by rfl) ⟨935297, by rfl⟩ : syracuseStep 1247063 = 1870595) B1870595
theorem B1247129 : Blo 830350 1247129 := bstep (se 2 (by rfl) ⟨467673, by rfl⟩ : syracuseStep 1247129 = 935347) B935347
theorem B1869785 : Blo 830350 1869785 := bstep (se 2 (by rfl) ⟨701169, by rfl⟩ : syracuseStep 1869785 = 1402339) B1402339
theorem B6752261 : Blo 830350 6752261 := bstep (se 4 (by rfl) ⟨633024, by rfl⟩ : syracuseStep 6752261 = 1266049) B1266049
theorem B1247243 : Blo 830350 1247243 := bstep (se 1 (by rfl) ⟨935432, by rfl⟩ : syracuseStep 1247243 = 1870865) B1870865
theorem B1247255 : Blo 830350 1247255 := bstep (se 1 (by rfl) ⟨935441, by rfl⟩ : syracuseStep 1247255 = 1870883) B1870883
theorem B1869875 : Blo 830350 1869875 := bstep (se 1 (by rfl) ⟨1402406, by rfl⟩ : syracuseStep 1869875 = 2804813) B2804813
theorem B1869911 : Blo 830350 1869911 := bstep (se 1 (by rfl) ⟨1402433, by rfl⟩ : syracuseStep 1869911 = 2804867) B2804867
theorem B1247321 : Blo 830350 1247321 := bstep (se 2 (by rfl) ⟨467745, by rfl⟩ : syracuseStep 1247321 = 935491) B935491
theorem B1247435 : Blo 830350 1247435 := bstep (se 1 (by rfl) ⟨935576, by rfl⟩ : syracuseStep 1247435 = 1871153) B1871153
theorem B1247447 : Blo 830350 1247447 := bstep (se 1 (by rfl) ⟨935585, by rfl⟩ : syracuseStep 1247447 = 1871171) B1871171
theorem B7604441 : Blo 830350 7604441 := bstep (se 2 (by rfl) ⟨2851665, by rfl⟩ : syracuseStep 7604441 = 5703331) B5703331
theorem B887051 : Blo 830350 887051 := bstep (se 1 (by rfl) ⟨665288, by rfl⟩ : syracuseStep 887051 = 1330577) B1330577
theorem B1870091 : Blo 830350 1870091 := bstep (se 1 (by rfl) ⟨1402568, by rfl⟩ : syracuseStep 1870091 = 2805137) B2805137
theorem B1247513 : Blo 830350 1247513 := bstep (se 2 (by rfl) ⟨467817, by rfl⟩ : syracuseStep 1247513 = 935635) B935635
theorem B1870145 : Blo 830350 1870145 := bstep (se 2 (by rfl) ⟨701304, by rfl⟩ : syracuseStep 1870145 = 1402609) B1402609
theorem B1247627 : Blo 830350 1247627 := bstep (se 1 (by rfl) ⟨935720, by rfl⟩ : syracuseStep 1247627 = 1871441) B1871441
theorem B1247639 : Blo 830350 1247639 := bstep (se 1 (by rfl) ⟨935729, by rfl⟩ : syracuseStep 1247639 = 1871459) B1871459
theorem B1247705 : Blo 830350 1247705 := bstep (se 2 (by rfl) ⟨467889, by rfl⟩ : syracuseStep 1247705 = 935779) B935779
theorem B1051147 : Blo 830350 1051147 := bstep (se 1 (by rfl) ⟨788360, by rfl⟩ : syracuseStep 1051147 = 1576721) B1576721
theorem B1870361 : Blo 830350 1870361 := bstep (se 2 (by rfl) ⟨701385, by rfl⟩ : syracuseStep 1870361 = 1402771) B1402771
theorem B1247819 : Blo 830350 1247819 := bstep (se 1 (by rfl) ⟨935864, by rfl⟩ : syracuseStep 1247819 = 1871729) B1871729
theorem B1247831 : Blo 830350 1247831 := bstep (se 1 (by rfl) ⟨935873, by rfl⟩ : syracuseStep 1247831 = 1871747) B1871747
theorem B1870451 : Blo 830350 1870451 := bstep (se 1 (by rfl) ⟨1402838, by rfl⟩ : syracuseStep 1870451 = 2805677) B2805677
theorem B1870487 : Blo 830350 1870487 := bstep (se 1 (by rfl) ⟨1402865, by rfl⟩ : syracuseStep 1870487 = 2805731) B2805731
theorem B1247897 : Blo 830350 1247897 := bstep (se 2 (by rfl) ⟨467961, by rfl⟩ : syracuseStep 1247897 = 935923) B935923
theorem B1248011 : Blo 830350 1248011 := bstep (se 1 (by rfl) ⟨936008, by rfl⟩ : syracuseStep 1248011 = 1872017) B1872017
theorem B1248023 : Blo 830350 1248023 := bstep (se 1 (by rfl) ⟨936017, by rfl⟩ : syracuseStep 1248023 = 1872035) B1872035
theorem B1870667 : Blo 830350 1870667 := bstep (se 1 (by rfl) ⟨1403000, by rfl⟩ : syracuseStep 1870667 = 2806001) B2806001
theorem B1248089 : Blo 830350 1248089 := bstep (se 2 (by rfl) ⟨468033, by rfl⟩ : syracuseStep 1248089 = 936067) B936067
theorem B1870721 : Blo 830350 1870721 := bstep (se 2 (by rfl) ⟨701520, by rfl⟩ : syracuseStep 1870721 = 1403041) B1403041
theorem B1248203 : Blo 830350 1248203 := bstep (se 1 (by rfl) ⟨936152, by rfl⟩ : syracuseStep 1248203 = 1872305) B1872305
theorem B1248215 : Blo 830350 1248215 := bstep (se 1 (by rfl) ⟨936161, by rfl⟩ : syracuseStep 1248215 = 1872323) B1872323
theorem B855019 : Blo 830350 855019 := bstep (se 1 (by rfl) ⟨641264, by rfl⟩ : syracuseStep 855019 = 1282529) B1282529
theorem B1248281 : Blo 830350 1248281 := bstep (se 2 (by rfl) ⟨468105, by rfl⟩ : syracuseStep 1248281 = 936211) B936211
theorem B1870937 : Blo 830350 1870937 := bstep (se 2 (by rfl) ⟨701601, by rfl⟩ : syracuseStep 1870937 = 1403203) B1403203
theorem B1248395 : Blo 830350 1248395 := bstep (se 1 (by rfl) ⟨936296, by rfl⟩ : syracuseStep 1248395 = 1872593) B1872593
theorem B1182871 : Blo 830350 1182871 := bstep (se 1 (by rfl) ⟨887153, by rfl⟩ : syracuseStep 1182871 = 1774307) B1774307
theorem B1248407 : Blo 830350 1248407 := bstep (se 1 (by rfl) ⟨936305, by rfl⟩ : syracuseStep 1248407 = 1872611) B1872611
theorem B1871027 : Blo 830350 1871027 := bstep (se 1 (by rfl) ⟨1403270, by rfl⟩ : syracuseStep 1871027 = 2806541) B2806541
theorem B3804353 : Blo 830350 3804353 := bstep (se 2 (by rfl) ⟨1426632, by rfl⟩ : syracuseStep 3804353 = 2853265) B2853265
theorem B1871063 : Blo 830350 1871063 := bstep (se 1 (by rfl) ⟨1403297, by rfl⟩ : syracuseStep 1871063 = 2806595) B2806595
theorem B1248473 : Blo 830350 1248473 := bstep (se 2 (by rfl) ⟨468177, by rfl⟩ : syracuseStep 1248473 = 936355) B936355
theorem B1248587 : Blo 830350 1248587 := bstep (se 1 (by rfl) ⟨936440, by rfl⟩ : syracuseStep 1248587 = 1872881) B1872881
theorem B1248599 : Blo 830350 1248599 := bstep (se 1 (by rfl) ⟨936449, by rfl⟩ : syracuseStep 1248599 = 1872899) B1872899
theorem B1871243 : Blo 830350 1871243 := bstep (se 1 (by rfl) ⟨1403432, by rfl⟩ : syracuseStep 1871243 = 2806865) B2806865
theorem B1248665 : Blo 830350 1248665 := bstep (se 2 (by rfl) ⟨468249, by rfl⟩ : syracuseStep 1248665 = 936499) B936499
theorem B888247 : Blo 830350 888247 := bstep (se 1 (by rfl) ⟨666185, by rfl⟩ : syracuseStep 888247 = 1332371) B1332371
theorem B1871297 : Blo 830350 1871297 := bstep (se 2 (by rfl) ⟨701736, by rfl⟩ : syracuseStep 1871297 = 1403473) B1403473
theorem B1052119 : Blo 830350 1052119 := bstep (se 1 (by rfl) ⟨789089, by rfl⟩ : syracuseStep 1052119 = 1578179) B1578179
theorem B1248779 : Blo 830350 1248779 := bstep (se 1 (by rfl) ⟨936584, by rfl⟩ : syracuseStep 1248779 = 1873169) B1873169
theorem B1248791 : Blo 830350 1248791 := bstep (se 1 (by rfl) ⟨936593, by rfl⟩ : syracuseStep 1248791 = 1873187) B1873187
theorem B1576523 : Blo 830350 1576523 := bstep (se 1 (by rfl) ⟨1182392, by rfl⟩ : syracuseStep 1576523 = 2364785) B2364785
theorem B1281611 : Blo 830350 1281611 := bstep (se 1 (by rfl) ⟨961208, by rfl⟩ : syracuseStep 1281611 = 1922417) B1922417
theorem B1248857 : Blo 830350 1248857 := bstep (se 2 (by rfl) ⟨468321, by rfl⟩ : syracuseStep 1248857 = 936643) B936643
theorem B1576577 : Blo 830350 1576577 := bstep (se 2 (by rfl) ⟨591216, by rfl⟩ : syracuseStep 1576577 = 1182433) B1182433
theorem B1871513 : Blo 830350 1871513 := bstep (se 2 (by rfl) ⟨701817, by rfl⟩ : syracuseStep 1871513 = 1403635) B1403635
theorem B888503 : Blo 830350 888503 := bstep (se 1 (by rfl) ⟨666377, by rfl⟩ : syracuseStep 888503 = 1332755) B1332755
theorem B1248971 : Blo 830350 1248971 := bstep (se 1 (by rfl) ⟨936728, by rfl⟩ : syracuseStep 1248971 = 1873457) B1873457
theorem B1248983 : Blo 830350 1248983 := bstep (se 1 (by rfl) ⟨936737, by rfl⟩ : syracuseStep 1248983 = 1873475) B1873475
theorem B1871603 : Blo 830350 1871603 := bstep (se 1 (by rfl) ⟨1403702, by rfl⟩ : syracuseStep 1871603 = 2807405) B2807405
theorem B1871639 : Blo 830350 1871639 := bstep (se 1 (by rfl) ⟨1403729, by rfl⟩ : syracuseStep 1871639 = 2807459) B2807459
theorem B1249049 : Blo 830350 1249049 := bstep (se 2 (by rfl) ⟨468393, by rfl⟩ : syracuseStep 1249049 = 936787) B936787
theorem B27430721 : Blo 830350 27430721 := bstep (se 2 (by rfl) ⟨10286520, by rfl⟩ : syracuseStep 27430721 = 20573041) B20573041
theorem B1183577 : Blo 830350 1183577 := bstep (se 2 (by rfl) ⟨443841, by rfl⟩ : syracuseStep 1183577 = 887683) B887683
theorem B1249163 : Blo 830350 1249163 := bstep (se 1 (by rfl) ⟨936872, by rfl⟩ : syracuseStep 1249163 = 1873745) B1873745
theorem B4001687 : Blo 830350 4001687 := bstep (se 1 (by rfl) ⟨3001265, by rfl⟩ : syracuseStep 4001687 = 6002531) B6002531
theorem B1249175 : Blo 830350 1249175 := bstep (se 1 (by rfl) ⟨936881, by rfl⟩ : syracuseStep 1249175 = 1873763) B1873763
theorem B1183691 : Blo 830350 1183691 := bstep (se 1 (by rfl) ⟨887768, by rfl⟩ : syracuseStep 1183691 = 1775537) B1775537
theorem B1871819 : Blo 830350 1871819 := bstep (se 1 (by rfl) ⟨1403864, by rfl⟩ : syracuseStep 1871819 = 2807729) B2807729
theorem B1249241 : Blo 830350 1249241 := bstep (se 2 (by rfl) ⟨468465, by rfl⟩ : syracuseStep 1249241 = 936931) B936931
theorem B1871873 : Blo 830350 1871873 := bstep (se 2 (by rfl) ⟨701952, by rfl⟩ : syracuseStep 1871873 = 1403905) B1403905
theorem B9474083 : Blo 830350 9474083 := bstep (se 1 (by rfl) ⟨7105562, by rfl⟩ : syracuseStep 9474083 = 14211125) B14211125
theorem B1249355 : Blo 830350 1249355 := bstep (se 1 (by rfl) ⟨937016, by rfl⟩ : syracuseStep 1249355 = 1874033) B1874033
theorem B1249367 : Blo 830350 1249367 := bstep (se 1 (by rfl) ⟨937025, by rfl⟩ : syracuseStep 1249367 = 1874051) B1874051
theorem B1249433 : Blo 830350 1249433 := bstep (se 2 (by rfl) ⟨468537, by rfl⟩ : syracuseStep 1249433 = 937075) B937075
theorem B1872089 : Blo 830350 1872089 := bstep (se 2 (by rfl) ⟨702033, by rfl⟩ : syracuseStep 1872089 = 1404067) B1404067
theorem B5411033 : Blo 830350 5411033 := bstep (se 2 (by rfl) ⟨2029137, by rfl⟩ : syracuseStep 5411033 = 4058275) B4058275
theorem B889067 : Blo 830350 889067 := bstep (se 1 (by rfl) ⟨666800, by rfl⟩ : syracuseStep 889067 = 1333601) B1333601
theorem B1052939 : Blo 830350 1052939 := bstep (se 1 (by rfl) ⟨789704, by rfl⟩ : syracuseStep 1052939 = 1579409) B1579409
theorem B1249547 : Blo 830350 1249547 := bstep (se 1 (by rfl) ⟨937160, by rfl⟩ : syracuseStep 1249547 = 1874321) B1874321
theorem B1249559 : Blo 830350 1249559 := bstep (se 1 (by rfl) ⟨937169, by rfl⟩ : syracuseStep 1249559 = 1874339) B1874339
theorem B6754595 : Blo 830350 6754595 := bstep (se 1 (by rfl) ⟨5065946, by rfl⟩ : syracuseStep 6754595 = 10131893) B10131893
theorem B1872179 : Blo 830350 1872179 := bstep (se 1 (by rfl) ⟨1404134, by rfl⟩ : syracuseStep 1872179 = 2808269) B2808269
theorem B12357953 : Blo 830350 12357953 := bstep (se 2 (by rfl) ⟨4634232, by rfl⟩ : syracuseStep 12357953 = 9268465) B9268465
theorem B1872215 : Blo 830350 1872215 := bstep (se 1 (by rfl) ⟨1404161, by rfl⟩ : syracuseStep 1872215 = 2808323) B2808323
theorem B1249625 : Blo 830350 1249625 := bstep (se 2 (by rfl) ⟨468609, by rfl⟩ : syracuseStep 1249625 = 937219) B937219
theorem B1249739 : Blo 830350 1249739 := bstep (se 1 (by rfl) ⟨937304, by rfl⟩ : syracuseStep 1249739 = 1874609) B1874609
theorem B1184215 : Blo 830350 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B1249751 : Blo 830350 1249751 := bstep (se 1 (by rfl) ⟨937313, by rfl⟩ : syracuseStep 1249751 = 1874627) B1874627
theorem B1774067 : Blo 830350 1774067 := bstep (se 1 (by rfl) ⟨1330550, by rfl⟩ : syracuseStep 1774067 = 2661101) B2661101
theorem B1872395 : Blo 830350 1872395 := bstep (se 1 (by rfl) ⟨1404296, by rfl⟩ : syracuseStep 1872395 = 2808593) B2808593
theorem B1577495 : Blo 830350 1577495 := bstep (se 1 (by rfl) ⟨1183121, by rfl⟩ : syracuseStep 1577495 = 2366243) B2366243
theorem B1249817 : Blo 830350 1249817 := bstep (se 2 (by rfl) ⟨468681, by rfl⟩ : syracuseStep 1249817 = 937363) B937363
theorem B1872449 : Blo 830350 1872449 := bstep (se 2 (by rfl) ⟨702168, by rfl⟩ : syracuseStep 1872449 = 1404337) B1404337
theorem B1249931 : Blo 830350 1249931 := bstep (se 1 (by rfl) ⟨937448, by rfl⟩ : syracuseStep 1249931 = 1874897) B1874897
theorem B1249943 : Blo 830350 1249943 := bstep (se 1 (by rfl) ⟨937457, by rfl⟩ : syracuseStep 1249943 = 1874915) B1874915
theorem B1250009 : Blo 830350 1250009 := bstep (se 2 (by rfl) ⟨468753, by rfl⟩ : syracuseStep 1250009 = 937507) B937507
theorem B1872665 : Blo 830350 1872665 := bstep (se 2 (by rfl) ⟨702249, by rfl⟩ : syracuseStep 1872665 = 1404499) B1404499
theorem B1250123 : Blo 830350 1250123 := bstep (se 1 (by rfl) ⟨937592, by rfl⟩ : syracuseStep 1250123 = 1875185) B1875185
theorem B1250135 : Blo 830350 1250135 := bstep (se 1 (by rfl) ⟨937601, by rfl⟩ : syracuseStep 1250135 = 1875203) B1875203
theorem B1872755 : Blo 830350 1872755 := bstep (se 1 (by rfl) ⟨1404566, by rfl⟩ : syracuseStep 1872755 = 2809133) B2809133
theorem B1872791 : Blo 830350 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B1250201 : Blo 830350 1250201 := bstep (se 2 (by rfl) ⟨468825, by rfl⟩ : syracuseStep 1250201 = 937651) B937651
theorem B1053643 : Blo 830350 1053643 := bstep (se 1 (by rfl) ⟨790232, by rfl⟩ : syracuseStep 1053643 = 1580465) B1580465
theorem B2102233 : Blo 830350 2102233 := bstep (se 2 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 2102233 = 1576675) B1576675
theorem B1250315 : Blo 830350 1250315 := bstep (se 1 (by rfl) ⟨937736, by rfl⟩ : syracuseStep 1250315 = 1875473) B1875473
theorem B1250327 : Blo 830350 1250327 := bstep (se 1 (by rfl) ⟨937745, by rfl⟩ : syracuseStep 1250327 = 1875491) B1875491
theorem B1578035 : Blo 830350 1578035 := bstep (se 1 (by rfl) ⟨1183526, by rfl⟩ : syracuseStep 1578035 = 2367053) B2367053
theorem B1872971 : Blo 830350 1872971 := bstep (se 1 (by rfl) ⟨1404728, by rfl⟩ : syracuseStep 1872971 = 2809457) B2809457
theorem B1250393 : Blo 830350 1250393 := bstep (se 2 (by rfl) ⟨468897, by rfl⟩ : syracuseStep 1250393 = 937795) B937795
theorem B1873025 : Blo 830350 1873025 := bstep (se 2 (by rfl) ⟨702384, by rfl⟩ : syracuseStep 1873025 = 1404769) B1404769
theorem B3413123 : Blo 830350 3413123 := bstep (se 1 (by rfl) ⟨2559842, by rfl⟩ : syracuseStep 3413123 = 5119685) B5119685
theorem B6755507 : Blo 830350 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B1250507 : Blo 830350 1250507 := bstep (se 1 (by rfl) ⟨937880, by rfl⟩ : syracuseStep 1250507 = 1875761) B1875761
theorem B1053911 : Blo 830350 1053911 := bstep (se 1 (by rfl) ⟨790433, by rfl⟩ : syracuseStep 1053911 = 1580867) B1580867
theorem B1250519 : Blo 830350 1250519 := bstep (se 1 (by rfl) ⟨937889, by rfl⟩ : syracuseStep 1250519 = 1875779) B1875779
theorem B1185035 : Blo 830350 1185035 := bstep (se 1 (by rfl) ⟨888776, by rfl⟩ : syracuseStep 1185035 = 1777553) B1777553
theorem B1250585 : Blo 830350 1250585 := bstep (se 2 (by rfl) ⟨468969, by rfl⟩ : syracuseStep 1250585 = 937939) B937939
theorem B1873241 : Blo 830350 1873241 := bstep (se 2 (by rfl) ⟨702465, by rfl⟩ : syracuseStep 1873241 = 1404931) B1404931
theorem B1250699 : Blo 830350 1250699 := bstep (se 1 (by rfl) ⟨938024, by rfl⟩ : syracuseStep 1250699 = 1876049) B1876049
theorem B1250711 : Blo 830350 1250711 := bstep (se 1 (by rfl) ⟨938033, by rfl⟩ : syracuseStep 1250711 = 1876067) B1876067
theorem B1873331 : Blo 830350 1873331 := bstep (se 1 (by rfl) ⟨1404998, by rfl⟩ : syracuseStep 1873331 = 2809997) B2809997
theorem B1873367 : Blo 830350 1873367 := bstep (se 1 (by rfl) ⟨1405025, by rfl⟩ : syracuseStep 1873367 = 2810051) B2810051
theorem B1250777 : Blo 830350 1250777 := bstep (se 2 (by rfl) ⟨469041, by rfl⟩ : syracuseStep 1250777 = 938083) B938083
theorem B1578521 : Blo 830350 1578521 := bstep (se 2 (by rfl) ⟨591945, by rfl⟩ : syracuseStep 1578521 = 1183891) B1183891
theorem B1250891 : Blo 830350 1250891 := bstep (se 1 (by rfl) ⟨938168, by rfl⟩ : syracuseStep 1250891 = 1876337) B1876337
theorem B1250903 : Blo 830350 1250903 := bstep (se 1 (by rfl) ⟨938177, by rfl⟩ : syracuseStep 1250903 = 1876355) B1876355
theorem B1873547 : Blo 830350 1873547 := bstep (se 1 (by rfl) ⟨1405160, by rfl⟩ : syracuseStep 1873547 = 2810321) B2810321
theorem B890519 : Blo 830350 890519 := bstep (se 1 (by rfl) ⟨667889, by rfl⟩ : syracuseStep 890519 = 1335779) B1335779
theorem B1250969 : Blo 830350 1250969 := bstep (se 2 (by rfl) ⟨469113, by rfl⟩ : syracuseStep 1250969 = 938227) B938227
theorem B1873601 : Blo 830350 1873601 := bstep (se 2 (by rfl) ⟨702600, by rfl⟩ : syracuseStep 1873601 = 1405201) B1405201
theorem B1251083 : Blo 830350 1251083 := bstep (se 1 (by rfl) ⟨938312, by rfl⟩ : syracuseStep 1251083 = 1876625) B1876625
theorem B1251095 : Blo 830350 1251095 := bstep (se 1 (by rfl) ⟨938321, by rfl⟩ : syracuseStep 1251095 = 1876643) B1876643
theorem B1251161 : Blo 830350 1251161 := bstep (se 2 (by rfl) ⟨469185, by rfl⟩ : syracuseStep 1251161 = 938371) B938371
theorem B1054615 : Blo 830350 1054615 := bstep (se 1 (by rfl) ⟨790961, by rfl⟩ : syracuseStep 1054615 = 1581923) B1581923
theorem B1873817 : Blo 830350 1873817 := bstep (se 2 (by rfl) ⟨702681, by rfl⟩ : syracuseStep 1873817 = 1405363) B1405363
theorem B1251275 : Blo 830350 1251275 := bstep (se 1 (by rfl) ⟨938456, by rfl⟩ : syracuseStep 1251275 = 1876913) B1876913
theorem B1251287 : Blo 830350 1251287 := bstep (se 1 (by rfl) ⟨938465, by rfl⟩ : syracuseStep 1251287 = 1876931) B1876931
theorem B1873907 : Blo 830350 1873907 := bstep (se 1 (by rfl) ⟨1405430, by rfl⟩ : syracuseStep 1873907 = 2810861) B2810861
theorem B1775639 : Blo 830350 1775639 := bstep (se 1 (by rfl) ⟨1331729, by rfl⟩ : syracuseStep 1775639 = 2663459) B2663459
theorem B1873943 : Blo 830350 1873943 := bstep (se 1 (by rfl) ⟨1405457, by rfl⟩ : syracuseStep 1873943 = 2810915) B2810915
theorem B1251353 : Blo 830350 1251353 := bstep (se 2 (by rfl) ⟨469257, by rfl⟩ : syracuseStep 1251353 = 938515) B938515
theorem B2103347 : Blo 830350 2103347 := bstep (se 1 (by rfl) ⟨1577510, by rfl⟩ : syracuseStep 2103347 = 3155021) B3155021
theorem B1251467 : Blo 830350 1251467 := bstep (se 1 (by rfl) ⟨938600, by rfl⟩ : syracuseStep 1251467 = 1877201) B1877201
theorem B1251479 : Blo 830350 1251479 := bstep (se 1 (by rfl) ⟨938609, by rfl⟩ : syracuseStep 1251479 = 1877219) B1877219
theorem B1874123 : Blo 830350 1874123 := bstep (se 1 (by rfl) ⟨1405592, by rfl⟩ : syracuseStep 1874123 = 2811185) B2811185
theorem B9607373 : Blo 830350 9607373 := bstep (se 3 (by rfl) ⟨1801382, by rfl⟩ : syracuseStep 9607373 = 3602765) B3602765
theorem B6002905 : Blo 830350 6002905 := bstep (se 2 (by rfl) ⟨2251089, by rfl⟩ : syracuseStep 6002905 = 4502179) B4502179
theorem B1874177 : Blo 830350 1874177 := bstep (se 2 (by rfl) ⟨702816, by rfl⟩ : syracuseStep 1874177 = 1405633) B1405633
theorem B1775947 : Blo 830350 1775947 := bstep (se 1 (by rfl) ⟨1331960, by rfl⟩ : syracuseStep 1775947 = 2663921) B2663921
theorem B2103641 : Blo 830350 2103641 := bstep (se 2 (by rfl) ⟨788865, by rfl⟩ : syracuseStep 2103641 = 1577731) B1577731
theorem B1874393 : Blo 830350 1874393 := bstep (se 2 (by rfl) ⟨702897, by rfl⟩ : syracuseStep 1874393 = 1405795) B1405795
theorem B1874483 : Blo 830350 1874483 := bstep (se 1 (by rfl) ⟨1405862, by rfl⟩ : syracuseStep 1874483 = 2811725) B2811725
theorem B1874519 : Blo 830350 1874519 := bstep (se 1 (by rfl) ⟨1405889, by rfl⟩ : syracuseStep 1874519 = 2811779) B2811779
theorem B1874699 : Blo 830350 1874699 := bstep (se 1 (by rfl) ⟨1406024, by rfl⟩ : syracuseStep 1874699 = 2812049) B2812049
theorem B10132289 : Blo 830350 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B1874753 : Blo 830350 1874753 := bstep (se 2 (by rfl) ⟨703032, by rfl⟩ : syracuseStep 1874753 = 1406065) B1406065
theorem B1579979 : Blo 830350 1579979 := bstep (se 1 (by rfl) ⟨1184984, by rfl⟩ : syracuseStep 1579979 = 2369969) B2369969
theorem B6167501 : Blo 830350 6167501 := bstep (se 3 (by rfl) ⟨1156406, by rfl⟩ : syracuseStep 6167501 = 2312813) B2312813
theorem B2366425 : Blo 830350 2366425 := bstep (se 2 (by rfl) ⟨887409, by rfl⟩ : syracuseStep 2366425 = 1774819) B1774819
theorem B1874969 : Blo 830350 1874969 := bstep (se 2 (by rfl) ⟨703113, by rfl⟩ : syracuseStep 1874969 = 1406227) B1406227
theorem B2432051 : Blo 830350 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B1186903 : Blo 830350 1186903 := bstep (se 1 (by rfl) ⟨890177, by rfl⟩ : syracuseStep 1186903 = 1780355) B1780355
theorem B1875059 : Blo 830350 1875059 := bstep (se 1 (by rfl) ⟨1406294, by rfl⟩ : syracuseStep 1875059 = 2812589) B2812589
theorem B1580161 : Blo 830350 1580161 := bstep (se 2 (by rfl) ⟨592560, by rfl⟩ : syracuseStep 1580161 = 1185121) B1185121
theorem B1875095 : Blo 830350 1875095 := bstep (se 1 (by rfl) ⟨1406321, by rfl⟩ : syracuseStep 1875095 = 2812643) B2812643
theorem B1875275 : Blo 830350 1875275 := bstep (se 1 (by rfl) ⟨1406456, by rfl⟩ : syracuseStep 1875275 = 2812913) B2812913
theorem B2366813 : Blo 830350 2366813 := bstep (se 3 (by rfl) ⟨443777, by rfl⟩ : syracuseStep 2366813 = 887555) B887555
theorem B1875329 : Blo 830350 1875329 := bstep (se 2 (by rfl) ⟨703248, by rfl⟩ : syracuseStep 1875329 = 1406497) B1406497
theorem B1777177 : Blo 830350 1777177 := bstep (se 2 (by rfl) ⟨666441, by rfl⟩ : syracuseStep 1777177 = 1332883) B1332883
theorem B1580609 : Blo 830350 1580609 := bstep (se 2 (by rfl) ⟨592728, by rfl⟩ : syracuseStep 1580609 = 1185457) B1185457
theorem B1875545 : Blo 830350 1875545 := bstep (se 2 (by rfl) ⟨703329, by rfl⟩ : syracuseStep 1875545 = 1406659) B1406659
theorem B1875635 : Blo 830350 1875635 := bstep (se 1 (by rfl) ⟨1406726, by rfl⟩ : syracuseStep 1875635 = 2813453) B2813453
theorem B1875671 : Blo 830350 1875671 := bstep (se 1 (by rfl) ⟨1406753, by rfl⟩ : syracuseStep 1875671 = 2813507) B2813507
theorem B1875851 : Blo 830350 1875851 := bstep (se 1 (by rfl) ⟨1406888, by rfl⟩ : syracuseStep 1875851 = 2813777) B2813777
theorem B1580951 : Blo 830350 1580951 := bstep (se 1 (by rfl) ⟨1185713, by rfl⟩ : syracuseStep 1580951 = 2371427) B2371427
theorem B1875905 : Blo 830350 1875905 := bstep (se 2 (by rfl) ⟨703464, by rfl⟩ : syracuseStep 1875905 = 1406929) B1406929
theorem B2105291 : Blo 830350 2105291 := bstep (se 1 (by rfl) ⟨1578968, by rfl⟩ : syracuseStep 2105291 = 3157937) B3157937
theorem B1876121 : Blo 830350 1876121 := bstep (se 2 (by rfl) ⟨703545, by rfl⟩ : syracuseStep 1876121 = 1407091) B1407091
theorem B1876211 : Blo 830350 1876211 := bstep (se 1 (by rfl) ⟨1407158, by rfl⟩ : syracuseStep 1876211 = 2814317) B2814317
theorem B1876247 : Blo 830350 1876247 := bstep (se 1 (by rfl) ⟨1407185, by rfl⟩ : syracuseStep 1876247 = 2814371) B2814371
theorem B1876427 : Blo 830350 1876427 := bstep (se 1 (by rfl) ⟨1407320, by rfl⟩ : syracuseStep 1876427 = 2814641) B2814641
theorem B1876481 : Blo 830350 1876481 := bstep (se 2 (by rfl) ⟨703680, by rfl⟩ : syracuseStep 1876481 = 1407361) B1407361
theorem B1581619 : Blo 830350 1581619 := bstep (se 1 (by rfl) ⟨1186214, by rfl⟩ : syracuseStep 1581619 = 2372429) B2372429
theorem B4006493 : Blo 830350 4006493 := bstep (se 3 (by rfl) ⟨751217, by rfl⟩ : syracuseStep 4006493 = 1502435) B1502435
theorem B3547793 : Blo 830350 3547793 := bstep (se 2 (by rfl) ⟨1330422, by rfl⟩ : syracuseStep 3547793 = 2660845) B2660845
theorem B1876697 : Blo 830350 1876697 := bstep (se 2 (by rfl) ⟨703761, by rfl⟩ : syracuseStep 1876697 = 1407523) B1407523
theorem B3154733 : Blo 830350 3154733 := bstep (se 3 (by rfl) ⟨591512, by rfl⟩ : syracuseStep 3154733 = 1183025) B1183025
theorem B1876787 : Blo 830350 1876787 := bstep (se 1 (by rfl) ⟨1407590, by rfl⟩ : syracuseStep 1876787 = 2815181) B2815181
theorem B4006721 : Blo 830350 4006721 := bstep (se 2 (by rfl) ⟨1502520, by rfl⟩ : syracuseStep 4006721 = 3005041) B3005041
theorem B2663243 : Blo 830350 2663243 := bstep (se 1 (by rfl) ⟨1997432, by rfl⟩ : syracuseStep 2663243 = 3994865) B3994865
theorem B1876823 : Blo 830350 1876823 := bstep (se 1 (by rfl) ⟨1407617, by rfl⟩ : syracuseStep 1876823 = 2815235) B2815235
theorem B2106263 : Blo 830350 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B1582067 : Blo 830350 1582067 := bstep (se 1 (by rfl) ⟨1186550, by rfl⟩ : syracuseStep 1582067 = 2373101) B2373101
theorem B1877003 : Blo 830350 1877003 := bstep (se 1 (by rfl) ⟨1407752, by rfl⟩ : syracuseStep 1877003 = 2815505) B2815505
theorem B1582105 : Blo 830350 1582105 := bstep (se 2 (by rfl) ⟨593289, by rfl⟩ : syracuseStep 1582105 = 1186579) B1186579
theorem B1877057 : Blo 830350 1877057 := bstep (se 2 (by rfl) ⟨703896, by rfl⟩ : syracuseStep 1877057 = 1407793) B1407793
theorem B4203737 : Blo 830350 4203737 := bstep (se 2 (by rfl) ⟨1576401, by rfl⟩ : syracuseStep 4203737 = 3152803) B3152803
theorem B1877273 : Blo 830350 1877273 := bstep (se 2 (by rfl) ⟨703977, by rfl⟩ : syracuseStep 1877273 = 1407955) B1407955
theorem B6006221 : Blo 830350 6006221 := bstep (se 3 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 6006221 = 2252333) B2252333
theorem B1582553 : Blo 830350 1582553 := bstep (se 2 (by rfl) ⟨593457, by rfl⟩ : syracuseStep 1582553 = 1186915) B1186915
theorem B3548717 : Blo 830350 3548717 := bstep (se 3 (by rfl) ⟨665384, by rfl⟩ : syracuseStep 3548717 = 1330769) B1330769
theorem B5547565 : Blo 830350 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B3155507 : Blo 830350 3155507 := bstep (se 1 (by rfl) ⟨2366630, by rfl⟩ : syracuseStep 3155507 = 4733261) B4733261
theorem B2106931 : Blo 830350 2106931 := bstep (se 1 (by rfl) ⟨1580198, by rfl⟩ : syracuseStep 2106931 = 3160397) B3160397
theorem B2107073 : Blo 830350 2107073 := bstep (se 2 (by rfl) ⟨790152, by rfl⟩ : syracuseStep 2107073 = 1580305) B1580305
theorem B10102801 : Blo 830350 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B300394565 : Blo 830350 300394565 := bstep (se 4 (by rfl) ⟨28161990, by rfl⟩ : syracuseStep 300394565 = 56323981) B56323981
theorem B2369729 : Blo 830350 2369729 := bstep (se 2 (by rfl) ⟨888648, by rfl⟩ : syracuseStep 2369729 = 1777297) B1777297
theorem B1583297 : Blo 830350 1583297 := bstep (se 2 (by rfl) ⟨593736, by rfl⟩ : syracuseStep 1583297 = 1187473) B1187473
theorem B2369843 : Blo 830350 2369843 := bstep (se 1 (by rfl) ⟨1777382, by rfl⟩ : syracuseStep 2369843 = 3554765) B3554765
theorem B1583563 : Blo 830350 1583563 := bstep (se 1 (by rfl) ⟨1187672, by rfl⟩ : syracuseStep 1583563 = 2375345) B2375345
theorem B1780211 : Blo 830350 1780211 := bstep (se 1 (by rfl) ⟨1335158, by rfl⟩ : syracuseStep 1780211 = 2670317) B2670317
theorem B2992733 : Blo 830350 2992733 := bstep (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) B1122275
theorem B4205357 : Blo 830350 4205357 := bstep (se 3 (by rfl) ⟨788504, by rfl⟩ : syracuseStep 4205357 = 1577009) B1577009
theorem B830359 : Blo 830350 830359 := bstep (se 1 (by rfl) ⟨622769, by rfl⟩ : syracuseStep 830359 = 1245539) B1245539
theorem B830379 : Blo 830350 830379 := bstep (se 1 (by rfl) ⟨622784, by rfl⟩ : syracuseStep 830379 = 1245569) B1245569
theorem B2108339 : Blo 830350 2108339 := bstep (se 1 (by rfl) ⟨1581254, by rfl⟩ : syracuseStep 2108339 = 3162509) B3162509
theorem B830391 : Blo 830350 830391 := bstep (se 1 (by rfl) ⟨622793, by rfl⟩ : syracuseStep 830391 = 1245587) B1245587
theorem B830411 : Blo 830350 830411 := bstep (se 1 (by rfl) ⟨622808, by rfl⟩ : syracuseStep 830411 = 1245617) B1245617
theorem B830423 : Blo 830350 830423 := bstep (se 1 (by rfl) ⟨622817, by rfl⟩ : syracuseStep 830423 = 1245635) B1245635
theorem B3550169 : Blo 830350 3550169 := bstep (se 2 (by rfl) ⟨1331313, by rfl⟩ : syracuseStep 3550169 = 2662627) B2662627
theorem B1780697 : Blo 830350 1780697 := bstep (se 2 (by rfl) ⟨667761, by rfl⟩ : syracuseStep 1780697 = 1335523) B1335523
theorem B830443 : Blo 830350 830443 := bstep (se 1 (by rfl) ⟨622832, by rfl⟩ : syracuseStep 830443 = 1245665) B1245665
theorem B830455 : Blo 830350 830455 := bstep (se 1 (by rfl) ⟨622841, by rfl⟩ : syracuseStep 830455 = 1245683) B1245683
theorem B3156995 : Blo 830350 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B830475 : Blo 830350 830475 := bstep (se 1 (by rfl) ⟨622856, by rfl⟩ : syracuseStep 830475 = 1245713) B1245713
theorem B830487 : Blo 830350 830487 := bstep (se 1 (by rfl) ⟨622865, by rfl⟩ : syracuseStep 830487 = 1245731) B1245731
theorem B830507 : Blo 830350 830507 := bstep (se 1 (by rfl) ⟨622880, by rfl⟩ : syracuseStep 830507 = 1245761) B1245761
theorem B7121965 : Blo 830350 7121965 := bstep (se 3 (by rfl) ⟨1335368, by rfl⟩ : syracuseStep 7121965 = 2670737) B2670737
theorem B830519 : Blo 830350 830519 := bstep (se 1 (by rfl) ⟨622889, by rfl⟩ : syracuseStep 830519 = 1245779) B1245779
theorem B830539 : Blo 830350 830539 := bstep (se 1 (by rfl) ⟨622904, by rfl⟩ : syracuseStep 830539 = 1245809) B1245809
theorem B830551 : Blo 830350 830551 := bstep (se 1 (by rfl) ⟨622913, by rfl⟩ : syracuseStep 830551 = 1245827) B1245827
theorem B2665561 : Blo 830350 2665561 := bstep (se 2 (by rfl) ⟨999585, by rfl⟩ : syracuseStep 2665561 = 1999171) B1999171
theorem B830571 : Blo 830350 830571 := bstep (se 1 (by rfl) ⟨622928, by rfl⟩ : syracuseStep 830571 = 1245857) B1245857
theorem B830583 : Blo 830350 830583 := bstep (se 1 (by rfl) ⟨622937, by rfl⟩ : syracuseStep 830583 = 1245875) B1245875
theorem B830603 : Blo 830350 830603 := bstep (se 1 (by rfl) ⟨622952, by rfl⟩ : syracuseStep 830603 = 1245905) B1245905
theorem B830615 : Blo 830350 830615 := bstep (se 1 (by rfl) ⟨622961, by rfl⟩ : syracuseStep 830615 = 1245923) B1245923
theorem B830635 : Blo 830350 830635 := bstep (se 1 (by rfl) ⟨622976, by rfl⟩ : syracuseStep 830635 = 1245953) B1245953
theorem B830647 : Blo 830350 830647 := bstep (se 1 (by rfl) ⟨622985, by rfl⟩ : syracuseStep 830647 = 1245971) B1245971
theorem B830667 : Blo 830350 830667 := bstep (se 1 (by rfl) ⟨623000, by rfl⟩ : syracuseStep 830667 = 1246001) B1246001
theorem B830679 : Blo 830350 830679 := bstep (se 1 (by rfl) ⟨623009, by rfl⟩ : syracuseStep 830679 = 1246019) B1246019
theorem B830699 : Blo 830350 830699 := bstep (se 1 (by rfl) ⟨623024, by rfl⟩ : syracuseStep 830699 = 1246049) B1246049
theorem B830711 : Blo 830350 830711 := bstep (se 1 (by rfl) ⟨623033, by rfl⟩ : syracuseStep 830711 = 1246067) B1246067
theorem B830731 : Blo 830350 830731 := bstep (se 1 (by rfl) ⟨623048, by rfl⟩ : syracuseStep 830731 = 1246097) B1246097
theorem B830743 : Blo 830350 830743 := bstep (se 1 (by rfl) ⟨623057, by rfl⟩ : syracuseStep 830743 = 1246115) B1246115
theorem B830763 : Blo 830350 830763 := bstep (se 1 (by rfl) ⟨623072, by rfl⟩ : syracuseStep 830763 = 1246145) B1246145
theorem B830775 : Blo 830350 830775 := bstep (se 1 (by rfl) ⟨623081, by rfl⟩ : syracuseStep 830775 = 1246163) B1246163
theorem B830795 : Blo 830350 830795 := bstep (se 1 (by rfl) ⟨623096, by rfl⟩ : syracuseStep 830795 = 1246193) B1246193
theorem B830807 : Blo 830350 830807 := bstep (se 1 (by rfl) ⟨623105, by rfl⟩ : syracuseStep 830807 = 1246211) B1246211
theorem B830827 : Blo 830350 830827 := bstep (se 1 (by rfl) ⟨623120, by rfl⟩ : syracuseStep 830827 = 1246241) B1246241
theorem B830839 : Blo 830350 830839 := bstep (se 1 (by rfl) ⟨623129, by rfl⟩ : syracuseStep 830839 = 1246259) B1246259
theorem B830859 : Blo 830350 830859 := bstep (se 1 (by rfl) ⟨623144, by rfl⟩ : syracuseStep 830859 = 1246289) B1246289
theorem B830871 : Blo 830350 830871 := bstep (se 1 (by rfl) ⟨623153, by rfl⟩ : syracuseStep 830871 = 1246307) B1246307
theorem B830891 : Blo 830350 830891 := bstep (se 1 (by rfl) ⟨623168, by rfl⟩ : syracuseStep 830891 = 1246337) B1246337
theorem B830903 : Blo 830350 830903 := bstep (se 1 (by rfl) ⟨623177, by rfl⟩ : syracuseStep 830903 = 1246355) B1246355
theorem B1420747 : Blo 830350 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B2993611 : Blo 830350 2993611 := bstep (se 1 (by rfl) ⟨2245208, by rfl⟩ : syracuseStep 2993611 = 4490417) B4490417
theorem B830923 : Blo 830350 830923 := bstep (se 1 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 830923 = 1246385) B1246385
theorem B3157451 : Blo 830350 3157451 := bstep (se 1 (by rfl) ⟨2368088, by rfl⟩ : syracuseStep 3157451 = 4736177) B4736177
theorem B2108875 : Blo 830350 2108875 := bstep (se 1 (by rfl) ⟨1581656, by rfl⟩ : syracuseStep 2108875 = 3163313) B3163313
theorem B830935 : Blo 830350 830935 := bstep (se 1 (by rfl) ⟨623201, by rfl⟩ : syracuseStep 830935 = 1246403) B1246403
theorem B830955 : Blo 830350 830955 := bstep (se 1 (by rfl) ⟨623216, by rfl⟩ : syracuseStep 830955 = 1246433) B1246433
theorem B830967 : Blo 830350 830967 := bstep (se 1 (by rfl) ⟨623225, by rfl⟩ : syracuseStep 830967 = 1246451) B1246451
theorem B830987 : Blo 830350 830987 := bstep (se 1 (by rfl) ⟨623240, by rfl⟩ : syracuseStep 830987 = 1246481) B1246481
theorem B830999 : Blo 830350 830999 := bstep (se 1 (by rfl) ⟨623249, by rfl⟩ : syracuseStep 830999 = 1246499) B1246499
theorem B831019 : Blo 830350 831019 := bstep (se 1 (by rfl) ⟨623264, by rfl⟩ : syracuseStep 831019 = 1246529) B1246529
theorem B831031 : Blo 830350 831031 := bstep (se 1 (by rfl) ⟨623273, by rfl⟩ : syracuseStep 831031 = 1246547) B1246547
theorem B831051 : Blo 830350 831051 := bstep (se 1 (by rfl) ⟨623288, by rfl⟩ : syracuseStep 831051 = 1246577) B1246577
theorem B831063 : Blo 830350 831063 := bstep (se 1 (by rfl) ⟨623297, by rfl⟩ : syracuseStep 831063 = 1246595) B1246595
theorem B2109017 : Blo 830350 2109017 := bstep (se 2 (by rfl) ⟨790881, by rfl⟩ : syracuseStep 2109017 = 1581763) B1581763
theorem B831083 : Blo 830350 831083 := bstep (se 1 (by rfl) ⟨623312, by rfl⟩ : syracuseStep 831083 = 1246625) B1246625
theorem B831095 : Blo 830350 831095 := bstep (se 1 (by rfl) ⟨623321, by rfl⟩ : syracuseStep 831095 = 1246643) B1246643
theorem B831115 : Blo 830350 831115 := bstep (se 1 (by rfl) ⟨623336, by rfl⟩ : syracuseStep 831115 = 1246673) B1246673
theorem B3157649 : Blo 830350 3157649 := bstep (se 2 (by rfl) ⟨1184118, by rfl⟩ : syracuseStep 3157649 = 2368237) B2368237
theorem B831127 : Blo 830350 831127 := bstep (se 1 (by rfl) ⟨623345, by rfl⟩ : syracuseStep 831127 = 1246691) B1246691
theorem B831147 : Blo 830350 831147 := bstep (se 1 (by rfl) ⟨623360, by rfl⟩ : syracuseStep 831147 = 1246721) B1246721
theorem B831159 : Blo 830350 831159 := bstep (se 1 (by rfl) ⟨623369, by rfl⟩ : syracuseStep 831159 = 1246739) B1246739
theorem B831179 : Blo 830350 831179 := bstep (se 1 (by rfl) ⟨623384, by rfl⟩ : syracuseStep 831179 = 1246769) B1246769
theorem B831191 : Blo 830350 831191 := bstep (se 1 (by rfl) ⟨623393, by rfl⟩ : syracuseStep 831191 = 1246787) B1246787
theorem B2993885 : Blo 830350 2993885 := bstep (se 3 (by rfl) ⟨561353, by rfl⟩ : syracuseStep 2993885 = 1122707) B1122707
theorem B831211 : Blo 830350 831211 := bstep (se 1 (by rfl) ⟨623408, by rfl⟩ : syracuseStep 831211 = 1246817) B1246817
theorem B831223 : Blo 830350 831223 := bstep (se 1 (by rfl) ⟨623417, by rfl⟩ : syracuseStep 831223 = 1246835) B1246835
theorem B831243 : Blo 830350 831243 := bstep (se 1 (by rfl) ⟨623432, by rfl⟩ : syracuseStep 831243 = 1246865) B1246865
theorem B831255 : Blo 830350 831255 := bstep (se 1 (by rfl) ⟨623441, by rfl⟩ : syracuseStep 831255 = 1246883) B1246883
theorem B831275 : Blo 830350 831275 := bstep (se 1 (by rfl) ⟨623456, by rfl⟩ : syracuseStep 831275 = 1246913) B1246913
theorem B831287 : Blo 830350 831287 := bstep (se 1 (by rfl) ⟨623465, by rfl⟩ : syracuseStep 831287 = 1246931) B1246931
theorem B831307 : Blo 830350 831307 := bstep (se 1 (by rfl) ⟨623480, by rfl⟩ : syracuseStep 831307 = 1246961) B1246961
theorem B831319 : Blo 830350 831319 := bstep (se 1 (by rfl) ⟨623489, by rfl⟩ : syracuseStep 831319 = 1246979) B1246979
theorem B831339 : Blo 830350 831339 := bstep (se 1 (by rfl) ⟨623504, by rfl⟩ : syracuseStep 831339 = 1247009) B1247009
theorem B831351 : Blo 830350 831351 := bstep (se 1 (by rfl) ⟨623513, by rfl⟩ : syracuseStep 831351 = 1247027) B1247027
theorem B831371 : Blo 830350 831371 := bstep (se 1 (by rfl) ⟨623528, by rfl⟩ : syracuseStep 831371 = 1247057) B1247057
theorem B831383 : Blo 830350 831383 := bstep (se 1 (by rfl) ⟨623537, by rfl⟩ : syracuseStep 831383 = 1247075) B1247075
theorem B831403 : Blo 830350 831403 := bstep (se 1 (by rfl) ⟨623552, by rfl⟩ : syracuseStep 831403 = 1247105) B1247105
theorem B831415 : Blo 830350 831415 := bstep (se 1 (by rfl) ⟨623561, by rfl⟩ : syracuseStep 831415 = 1247123) B1247123
theorem B831435 : Blo 830350 831435 := bstep (se 1 (by rfl) ⟨623576, by rfl⟩ : syracuseStep 831435 = 1247153) B1247153
theorem B831447 : Blo 830350 831447 := bstep (se 1 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 831447 = 1247171) B1247171
theorem B831467 : Blo 830350 831467 := bstep (se 1 (by rfl) ⟨623600, by rfl⟩ : syracuseStep 831467 = 1247201) B1247201
theorem B831479 : Blo 830350 831479 := bstep (se 1 (by rfl) ⟨623609, by rfl⟩ : syracuseStep 831479 = 1247219) B1247219
theorem B831499 : Blo 830350 831499 := bstep (se 1 (by rfl) ⟨623624, by rfl⟩ : syracuseStep 831499 = 1247249) B1247249
theorem B831511 : Blo 830350 831511 := bstep (se 1 (by rfl) ⟨623633, by rfl⟩ : syracuseStep 831511 = 1247267) B1247267
theorem B831531 : Blo 830350 831531 := bstep (se 1 (by rfl) ⟨623648, by rfl⟩ : syracuseStep 831531 = 1247297) B1247297
theorem B831543 : Blo 830350 831543 := bstep (se 1 (by rfl) ⟨623657, by rfl⟩ : syracuseStep 831543 = 1247315) B1247315
theorem B831563 : Blo 830350 831563 := bstep (se 1 (by rfl) ⟨623672, by rfl⟩ : syracuseStep 831563 = 1247345) B1247345
theorem B831575 : Blo 830350 831575 := bstep (se 1 (by rfl) ⟨623681, by rfl⟩ : syracuseStep 831575 = 1247363) B1247363
theorem B831595 : Blo 830350 831595 := bstep (se 1 (by rfl) ⟨623696, by rfl⟩ : syracuseStep 831595 = 1247393) B1247393
theorem B831607 : Blo 830350 831607 := bstep (se 1 (by rfl) ⟨623705, by rfl⟩ : syracuseStep 831607 = 1247411) B1247411
theorem B831627 : Blo 830350 831627 := bstep (se 1 (by rfl) ⟨623720, by rfl⟩ : syracuseStep 831627 = 1247441) B1247441
theorem B831639 : Blo 830350 831639 := bstep (se 1 (by rfl) ⟨623729, by rfl⟩ : syracuseStep 831639 = 1247459) B1247459
theorem B831659 : Blo 830350 831659 := bstep (se 1 (by rfl) ⟨623744, by rfl⟩ : syracuseStep 831659 = 1247489) B1247489
theorem B6828209 : Blo 830350 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B831671 : Blo 830350 831671 := bstep (se 1 (by rfl) ⟨623753, by rfl⟩ : syracuseStep 831671 = 1247507) B1247507
theorem B831691 : Blo 830350 831691 := bstep (se 1 (by rfl) ⟨623768, by rfl⟩ : syracuseStep 831691 = 1247537) B1247537
theorem B831703 : Blo 830350 831703 := bstep (se 1 (by rfl) ⟨623777, by rfl⟩ : syracuseStep 831703 = 1247555) B1247555
theorem B831723 : Blo 830350 831723 := bstep (se 1 (by rfl) ⟨623792, by rfl⟩ : syracuseStep 831723 = 1247585) B1247585
theorem B831735 : Blo 830350 831735 := bstep (se 1 (by rfl) ⟨623801, by rfl⟩ : syracuseStep 831735 = 1247603) B1247603
theorem B831755 : Blo 830350 831755 := bstep (se 1 (by rfl) ⟨623816, by rfl⟩ : syracuseStep 831755 = 1247633) B1247633
theorem B831767 : Blo 830350 831767 := bstep (se 1 (by rfl) ⟨623825, by rfl⟩ : syracuseStep 831767 = 1247651) B1247651
theorem B831787 : Blo 830350 831787 := bstep (se 1 (by rfl) ⟨623840, by rfl⟩ : syracuseStep 831787 = 1247681) B1247681
theorem B831799 : Blo 830350 831799 := bstep (se 1 (by rfl) ⟨623849, by rfl⟩ : syracuseStep 831799 = 1247699) B1247699
theorem B831819 : Blo 830350 831819 := bstep (se 1 (by rfl) ⟨623864, by rfl⟩ : syracuseStep 831819 = 1247729) B1247729
theorem B831831 : Blo 830350 831831 := bstep (se 1 (by rfl) ⟨623873, by rfl⟩ : syracuseStep 831831 = 1247747) B1247747
theorem B7123301 : Blo 830350 7123301 := bstep (se 4 (by rfl) ⟨667809, by rfl⟩ : syracuseStep 7123301 = 1335619) B1335619
theorem B831851 : Blo 830350 831851 := bstep (se 1 (by rfl) ⟨623888, by rfl⟩ : syracuseStep 831851 = 1247777) B1247777
theorem B831863 : Blo 830350 831863 := bstep (se 1 (by rfl) ⟨623897, by rfl⟩ : syracuseStep 831863 = 1247795) B1247795
theorem B831883 : Blo 830350 831883 := bstep (se 1 (by rfl) ⟨623912, by rfl⟩ : syracuseStep 831883 = 1247825) B1247825
theorem B3158423 : Blo 830350 3158423 := bstep (se 1 (by rfl) ⟨2368817, by rfl⟩ : syracuseStep 3158423 = 4737635) B4737635
theorem B831895 : Blo 830350 831895 := bstep (se 1 (by rfl) ⟨623921, by rfl⟩ : syracuseStep 831895 = 1247843) B1247843
theorem B2109847 : Blo 830350 2109847 := bstep (se 1 (by rfl) ⟨1582385, by rfl⟩ : syracuseStep 2109847 = 3164771) B3164771
theorem B831915 : Blo 830350 831915 := bstep (se 1 (by rfl) ⟨623936, by rfl⟩ : syracuseStep 831915 = 1247873) B1247873
theorem B831927 : Blo 830350 831927 := bstep (se 1 (by rfl) ⟨623945, by rfl⟩ : syracuseStep 831927 = 1247891) B1247891
theorem B2666945 : Blo 830350 2666945 := bstep (se 2 (by rfl) ⟨1000104, by rfl⟩ : syracuseStep 2666945 = 2000209) B2000209
theorem B831947 : Blo 830350 831947 := bstep (se 1 (by rfl) ⟨623960, by rfl⟩ : syracuseStep 831947 = 1247921) B1247921
theorem B831959 : Blo 830350 831959 := bstep (se 1 (by rfl) ⟨623969, by rfl⟩ : syracuseStep 831959 = 1247939) B1247939
theorem B5321177 : Blo 830350 5321177 := bstep (se 2 (by rfl) ⟨1995441, by rfl⟩ : syracuseStep 5321177 = 3990883) B3990883
theorem B831979 : Blo 830350 831979 := bstep (se 1 (by rfl) ⟨623984, by rfl⟩ : syracuseStep 831979 = 1247969) B1247969
theorem B831991 : Blo 830350 831991 := bstep (se 1 (by rfl) ⟨623993, by rfl⟩ : syracuseStep 831991 = 1247987) B1247987
theorem B832011 : Blo 830350 832011 := bstep (se 1 (by rfl) ⟨624008, by rfl⟩ : syracuseStep 832011 = 1248017) B1248017
theorem B832023 : Blo 830350 832023 := bstep (se 1 (by rfl) ⟨624017, by rfl⟩ : syracuseStep 832023 = 1248035) B1248035
theorem B832043 : Blo 830350 832043 := bstep (se 1 (by rfl) ⟨624032, by rfl⟩ : syracuseStep 832043 = 1248065) B1248065
theorem B832055 : Blo 830350 832055 := bstep (se 1 (by rfl) ⟨624041, by rfl⟩ : syracuseStep 832055 = 1248083) B1248083
theorem B3551809 : Blo 830350 3551809 := bstep (se 2 (by rfl) ⟨1331928, by rfl⟩ : syracuseStep 3551809 = 2663857) B2663857
theorem B832075 : Blo 830350 832075 := bstep (se 1 (by rfl) ⟨624056, by rfl⟩ : syracuseStep 832075 = 1248113) B1248113
theorem B832087 : Blo 830350 832087 := bstep (se 1 (by rfl) ⟨624065, by rfl⟩ : syracuseStep 832087 = 1248131) B1248131
theorem B3158621 : Blo 830350 3158621 := bstep (se 3 (by rfl) ⟨592241, by rfl⟩ : syracuseStep 3158621 = 1184483) B1184483
theorem B832107 : Blo 830350 832107 := bstep (se 1 (by rfl) ⟨624080, by rfl⟩ : syracuseStep 832107 = 1248161) B1248161
theorem B832119 : Blo 830350 832119 := bstep (se 1 (by rfl) ⟨624089, by rfl⟩ : syracuseStep 832119 = 1248179) B1248179
theorem B832139 : Blo 830350 832139 := bstep (se 1 (by rfl) ⟨624104, by rfl⟩ : syracuseStep 832139 = 1248209) B1248209
theorem B832151 : Blo 830350 832151 := bstep (se 1 (by rfl) ⟨624113, by rfl⟩ : syracuseStep 832151 = 1248227) B1248227
theorem B832171 : Blo 830350 832171 := bstep (se 1 (by rfl) ⟨624128, by rfl⟩ : syracuseStep 832171 = 1248257) B1248257
theorem B832183 : Blo 830350 832183 := bstep (se 1 (by rfl) ⟨624137, by rfl⟩ : syracuseStep 832183 = 1248275) B1248275
theorem B832203 : Blo 830350 832203 := bstep (se 1 (by rfl) ⟨624152, by rfl⟩ : syracuseStep 832203 = 1248305) B1248305
theorem B832215 : Blo 830350 832215 := bstep (se 1 (by rfl) ⟨624161, by rfl⟩ : syracuseStep 832215 = 1248323) B1248323
theorem B832235 : Blo 830350 832235 := bstep (se 1 (by rfl) ⟨624176, by rfl⟩ : syracuseStep 832235 = 1248353) B1248353
theorem B832247 : Blo 830350 832247 := bstep (se 1 (by rfl) ⟨624185, by rfl⟩ : syracuseStep 832247 = 1248371) B1248371
theorem B832267 : Blo 830350 832267 := bstep (se 1 (by rfl) ⟨624200, by rfl⟩ : syracuseStep 832267 = 1248401) B1248401
theorem B832279 : Blo 830350 832279 := bstep (se 1 (by rfl) ⟨624209, by rfl⟩ : syracuseStep 832279 = 1248419) B1248419
theorem B1520407 : Blo 830350 1520407 := bstep (se 1 (by rfl) ⟨1140305, by rfl⟩ : syracuseStep 1520407 = 2280611) B2280611
theorem B832299 : Blo 830350 832299 := bstep (se 1 (by rfl) ⟨624224, by rfl⟩ : syracuseStep 832299 = 1248449) B1248449
theorem B2994995 : Blo 830350 2994995 := bstep (se 1 (by rfl) ⟨2246246, by rfl⟩ : syracuseStep 2994995 = 4492493) B4492493
theorem B832311 : Blo 830350 832311 := bstep (se 1 (by rfl) ⟨624233, by rfl⟩ : syracuseStep 832311 = 1248467) B1248467
theorem B2110283 : Blo 830350 2110283 := bstep (se 1 (by rfl) ⟨1582712, by rfl⟩ : syracuseStep 2110283 = 3165425) B3165425
theorem B832331 : Blo 830350 832331 := bstep (se 1 (by rfl) ⟨624248, by rfl⟩ : syracuseStep 832331 = 1248497) B1248497
theorem B832343 : Blo 830350 832343 := bstep (se 1 (by rfl) ⟨624257, by rfl⟩ : syracuseStep 832343 = 1248515) B1248515
theorem B21672805 : Blo 830350 21672805 := bstep (se 4 (by rfl) ⟨2031825, by rfl⟩ : syracuseStep 21672805 = 4063651) B4063651
theorem B832363 : Blo 830350 832363 := bstep (se 1 (by rfl) ⟨624272, by rfl⟩ : syracuseStep 832363 = 1248545) B1248545
theorem B832375 : Blo 830350 832375 := bstep (se 1 (by rfl) ⟨624281, by rfl⟩ : syracuseStep 832375 = 1248563) B1248563
theorem B832395 : Blo 830350 832395 := bstep (se 1 (by rfl) ⟨624296, by rfl⟩ : syracuseStep 832395 = 1248593) B1248593
theorem B832407 : Blo 830350 832407 := bstep (se 1 (by rfl) ⟨624305, by rfl⟩ : syracuseStep 832407 = 1248611) B1248611
theorem B832427 : Blo 830350 832427 := bstep (se 1 (by rfl) ⟨624320, by rfl⟩ : syracuseStep 832427 = 1248641) B1248641
theorem B832439 : Blo 830350 832439 := bstep (se 1 (by rfl) ⟨624329, by rfl⟩ : syracuseStep 832439 = 1248659) B1248659
theorem B832459 : Blo 830350 832459 := bstep (se 1 (by rfl) ⟨624344, by rfl⟩ : syracuseStep 832459 = 1248689) B1248689
theorem B832471 : Blo 830350 832471 := bstep (se 1 (by rfl) ⟨624353, by rfl⟩ : syracuseStep 832471 = 1248707) B1248707
theorem B832491 : Blo 830350 832491 := bstep (se 1 (by rfl) ⟨624368, by rfl⟩ : syracuseStep 832491 = 1248737) B1248737
theorem B832503 : Blo 830350 832503 := bstep (se 1 (by rfl) ⟨624377, by rfl⟩ : syracuseStep 832503 = 1248755) B1248755
theorem B832523 : Blo 830350 832523 := bstep (se 1 (by rfl) ⟨624392, by rfl⟩ : syracuseStep 832523 = 1248785) B1248785
theorem B832535 : Blo 830350 832535 := bstep (se 1 (by rfl) ⟨624401, by rfl⟩ : syracuseStep 832535 = 1248803) B1248803
theorem B832555 : Blo 830350 832555 := bstep (se 1 (by rfl) ⟨624416, by rfl⟩ : syracuseStep 832555 = 1248833) B1248833
theorem B832567 : Blo 830350 832567 := bstep (se 1 (by rfl) ⟨624425, by rfl⟩ : syracuseStep 832567 = 1248851) B1248851
theorem B832587 : Blo 830350 832587 := bstep (se 1 (by rfl) ⟨624440, by rfl⟩ : syracuseStep 832587 = 1248881) B1248881
theorem B832599 : Blo 830350 832599 := bstep (se 1 (by rfl) ⟨624449, by rfl⟩ : syracuseStep 832599 = 1248899) B1248899
theorem B832619 : Blo 830350 832619 := bstep (se 1 (by rfl) ⟨624464, by rfl⟩ : syracuseStep 832619 = 1248929) B1248929
theorem B1684595 : Blo 830350 1684595 := bstep (se 1 (by rfl) ⟨1263446, by rfl⟩ : syracuseStep 1684595 = 2526893) B2526893
theorem B832631 : Blo 830350 832631 := bstep (se 1 (by rfl) ⟨624473, by rfl⟩ : syracuseStep 832631 = 1248947) B1248947
theorem B832651 : Blo 830350 832651 := bstep (se 1 (by rfl) ⟨624488, by rfl⟩ : syracuseStep 832651 = 1248977) B1248977
theorem B3552407 : Blo 830350 3552407 := bstep (se 1 (by rfl) ⟨2664305, by rfl⟩ : syracuseStep 3552407 = 5328611) B5328611
theorem B832663 : Blo 830350 832663 := bstep (se 1 (by rfl) ⟨624497, by rfl⟩ : syracuseStep 832663 = 1248995) B1248995
theorem B2372759 : Blo 830350 2372759 := bstep (se 1 (by rfl) ⟨1779569, by rfl⟩ : syracuseStep 2372759 = 3559139) B3559139
theorem B832683 : Blo 830350 832683 := bstep (se 1 (by rfl) ⟨624512, by rfl⟩ : syracuseStep 832683 = 1249025) B1249025
theorem B832695 : Blo 830350 832695 := bstep (se 1 (by rfl) ⟨624521, by rfl⟩ : syracuseStep 832695 = 1249043) B1249043
theorem B2110657 : Blo 830350 2110657 := bstep (se 2 (by rfl) ⟨791496, by rfl⟩ : syracuseStep 2110657 = 1582993) B1582993
theorem B832715 : Blo 830350 832715 := bstep (se 1 (by rfl) ⟨624536, by rfl⟩ : syracuseStep 832715 = 1249073) B1249073
theorem B832727 : Blo 830350 832727 := bstep (se 1 (by rfl) ⟨624545, by rfl⟩ : syracuseStep 832727 = 1249091) B1249091
theorem B4732121 : Blo 830350 4732121 := bstep (se 2 (by rfl) ⟨1774545, by rfl⟩ : syracuseStep 4732121 = 3549091) B3549091
theorem B832747 : Blo 830350 832747 := bstep (se 1 (by rfl) ⟨624560, by rfl⟩ : syracuseStep 832747 = 1249121) B1249121
theorem B832759 : Blo 830350 832759 := bstep (se 1 (by rfl) ⟨624569, by rfl⟩ : syracuseStep 832759 = 1249139) B1249139
theorem B832779 : Blo 830350 832779 := bstep (se 1 (by rfl) ⟨624584, by rfl⟩ : syracuseStep 832779 = 1249169) B1249169
theorem B832791 : Blo 830350 832791 := bstep (se 1 (by rfl) ⟨624593, by rfl⟩ : syracuseStep 832791 = 1249187) B1249187
theorem B832811 : Blo 830350 832811 := bstep (se 1 (by rfl) ⟨624608, by rfl⟩ : syracuseStep 832811 = 1249217) B1249217
theorem B832823 : Blo 830350 832823 := bstep (se 1 (by rfl) ⟨624617, by rfl⟩ : syracuseStep 832823 = 1249235) B1249235
theorem B832843 : Blo 830350 832843 := bstep (se 1 (by rfl) ⟨624632, by rfl⟩ : syracuseStep 832843 = 1249265) B1249265
theorem B832855 : Blo 830350 832855 := bstep (se 1 (by rfl) ⟨624641, by rfl⟩ : syracuseStep 832855 = 1249283) B1249283
theorem B832875 : Blo 830350 832875 := bstep (se 1 (by rfl) ⟨624656, by rfl⟩ : syracuseStep 832875 = 1249313) B1249313
theorem B832887 : Blo 830350 832887 := bstep (se 1 (by rfl) ⟨624665, by rfl⟩ : syracuseStep 832887 = 1249331) B1249331
theorem B832907 : Blo 830350 832907 := bstep (se 1 (by rfl) ⟨624680, by rfl⟩ : syracuseStep 832907 = 1249361) B1249361
theorem B832919 : Blo 830350 832919 := bstep (se 1 (by rfl) ⟨624689, by rfl⟩ : syracuseStep 832919 = 1249379) B1249379
theorem B832939 : Blo 830350 832939 := bstep (se 1 (by rfl) ⟨624704, by rfl⟩ : syracuseStep 832939 = 1249409) B1249409
theorem B832951 : Blo 830350 832951 := bstep (se 1 (by rfl) ⟨624713, by rfl⟩ : syracuseStep 832951 = 1249427) B1249427
theorem B832971 : Blo 830350 832971 := bstep (se 1 (by rfl) ⟨624728, by rfl⟩ : syracuseStep 832971 = 1249457) B1249457
theorem B832983 : Blo 830350 832983 := bstep (se 1 (by rfl) ⟨624737, by rfl⟩ : syracuseStep 832983 = 1249475) B1249475
theorem B833003 : Blo 830350 833003 := bstep (se 1 (by rfl) ⟨624752, by rfl⟩ : syracuseStep 833003 = 1249505) B1249505
theorem B833015 : Blo 830350 833015 := bstep (se 1 (by rfl) ⟨624761, by rfl⟩ : syracuseStep 833015 = 1249523) B1249523
theorem B833035 : Blo 830350 833035 := bstep (se 1 (by rfl) ⟨624776, by rfl⟩ : syracuseStep 833035 = 1249553) B1249553
theorem B833047 : Blo 830350 833047 := bstep (se 1 (by rfl) ⟨624785, by rfl⟩ : syracuseStep 833047 = 1249571) B1249571
theorem B833067 : Blo 830350 833067 := bstep (se 1 (by rfl) ⟨624800, by rfl⟩ : syracuseStep 833067 = 1249601) B1249601
theorem B833079 : Blo 830350 833079 := bstep (se 1 (by rfl) ⟨624809, by rfl⟩ : syracuseStep 833079 = 1249619) B1249619
theorem B833099 : Blo 830350 833099 := bstep (se 1 (by rfl) ⟨624824, by rfl⟩ : syracuseStep 833099 = 1249649) B1249649
theorem B833111 : Blo 830350 833111 := bstep (se 1 (by rfl) ⟨624833, by rfl⟩ : syracuseStep 833111 = 1249667) B1249667
theorem B833131 : Blo 830350 833131 := bstep (se 1 (by rfl) ⟨624848, by rfl⟩ : syracuseStep 833131 = 1249697) B1249697
theorem B833143 : Blo 830350 833143 := bstep (se 1 (by rfl) ⟨624857, by rfl⟩ : syracuseStep 833143 = 1249715) B1249715
theorem B11417219 : Blo 830350 11417219 := bstep (se 1 (by rfl) ⟨8562914, by rfl⟩ : syracuseStep 11417219 = 17125829) B17125829
theorem B833163 : Blo 830350 833163 := bstep (se 1 (by rfl) ⟨624872, by rfl⟩ : syracuseStep 833163 = 1249745) B1249745
theorem B833175 : Blo 830350 833175 := bstep (se 1 (by rfl) ⟨624881, by rfl⟩ : syracuseStep 833175 = 1249763) B1249763
theorem B833195 : Blo 830350 833195 := bstep (se 1 (by rfl) ⟨624896, by rfl⟩ : syracuseStep 833195 = 1249793) B1249793
theorem B833207 : Blo 830350 833207 := bstep (se 1 (by rfl) ⟨624905, by rfl⟩ : syracuseStep 833207 = 1249811) B1249811
theorem B833227 : Blo 830350 833227 := bstep (se 1 (by rfl) ⟨624920, by rfl⟩ : syracuseStep 833227 = 1249841) B1249841
theorem B833239 : Blo 830350 833239 := bstep (se 1 (by rfl) ⟨624929, by rfl⟩ : syracuseStep 833239 = 1249859) B1249859
theorem B833259 : Blo 830350 833259 := bstep (se 1 (by rfl) ⟨624944, by rfl⟩ : syracuseStep 833259 = 1249889) B1249889
theorem B833271 : Blo 830350 833271 := bstep (se 1 (by rfl) ⟨624953, by rfl⟩ : syracuseStep 833271 = 1249907) B1249907
theorem B833291 : Blo 830350 833291 := bstep (se 1 (by rfl) ⟨624968, by rfl⟩ : syracuseStep 833291 = 1249937) B1249937
theorem B833303 : Blo 830350 833303 := bstep (se 1 (by rfl) ⟨624977, by rfl⟩ : syracuseStep 833303 = 1249955) B1249955
theorem B2111255 : Blo 830350 2111255 := bstep (se 1 (by rfl) ⟨1583441, by rfl⟩ : syracuseStep 2111255 = 3166883) B3166883
theorem B833323 : Blo 830350 833323 := bstep (se 1 (by rfl) ⟨624992, by rfl⟩ : syracuseStep 833323 = 1249985) B1249985
theorem B833335 : Blo 830350 833335 := bstep (se 1 (by rfl) ⟨625001, by rfl⟩ : syracuseStep 833335 = 1250003) B1250003
theorem B833355 : Blo 830350 833355 := bstep (se 1 (by rfl) ⟨625016, by rfl⟩ : syracuseStep 833355 = 1250033) B1250033
theorem B833367 : Blo 830350 833367 := bstep (se 1 (by rfl) ⟨625025, by rfl⟩ : syracuseStep 833367 = 1250051) B1250051
theorem B833387 : Blo 830350 833387 := bstep (se 1 (by rfl) ⟨625040, by rfl⟩ : syracuseStep 833387 = 1250081) B1250081
theorem B833399 : Blo 830350 833399 := bstep (se 1 (by rfl) ⟨625049, by rfl⟩ : syracuseStep 833399 = 1250099) B1250099
theorem B833419 : Blo 830350 833419 := bstep (se 1 (by rfl) ⟨625064, by rfl⟩ : syracuseStep 833419 = 1250129) B1250129
theorem B833431 : Blo 830350 833431 := bstep (se 1 (by rfl) ⟨625073, by rfl⟩ : syracuseStep 833431 = 1250147) B1250147
theorem B833451 : Blo 830350 833451 := bstep (se 1 (by rfl) ⟨625088, by rfl⟩ : syracuseStep 833451 = 1250177) B1250177
theorem B833463 : Blo 830350 833463 := bstep (se 1 (by rfl) ⟨625097, by rfl⟩ : syracuseStep 833463 = 1250195) B1250195
theorem B833483 : Blo 830350 833483 := bstep (se 1 (by rfl) ⟨625112, by rfl⟩ : syracuseStep 833483 = 1250225) B1250225
theorem B833495 : Blo 830350 833495 := bstep (se 1 (by rfl) ⟨625121, by rfl⟩ : syracuseStep 833495 = 1250243) B1250243
theorem B833515 : Blo 830350 833515 := bstep (se 1 (by rfl) ⟨625136, by rfl⟩ : syracuseStep 833515 = 1250273) B1250273
theorem B833527 : Blo 830350 833527 := bstep (se 1 (by rfl) ⟨625145, by rfl⟩ : syracuseStep 833527 = 1250291) B1250291
theorem B833547 : Blo 830350 833547 := bstep (se 1 (by rfl) ⟨625160, by rfl⟩ : syracuseStep 833547 = 1250321) B1250321
theorem B833559 : Blo 830350 833559 := bstep (se 1 (by rfl) ⟨625169, by rfl⟩ : syracuseStep 833559 = 1250339) B1250339
theorem B833579 : Blo 830350 833579 := bstep (se 1 (by rfl) ⟨625184, by rfl⟩ : syracuseStep 833579 = 1250369) B1250369
theorem B833591 : Blo 830350 833591 := bstep (se 1 (by rfl) ⟨625193, by rfl⟩ : syracuseStep 833591 = 1250387) B1250387
theorem B833611 : Blo 830350 833611 := bstep (se 1 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 833611 = 1250417) B1250417
theorem B833623 : Blo 830350 833623 := bstep (se 1 (by rfl) ⟨625217, by rfl⟩ : syracuseStep 833623 = 1250435) B1250435
theorem B833643 : Blo 830350 833643 := bstep (se 1 (by rfl) ⟨625232, by rfl⟩ : syracuseStep 833643 = 1250465) B1250465
theorem B833655 : Blo 830350 833655 := bstep (se 1 (by rfl) ⟨625241, by rfl⟩ : syracuseStep 833655 = 1250483) B1250483
theorem B833675 : Blo 830350 833675 := bstep (se 1 (by rfl) ⟨625256, by rfl⟩ : syracuseStep 833675 = 1250513) B1250513
theorem B833687 : Blo 830350 833687 := bstep (se 1 (by rfl) ⟨625265, by rfl⟩ : syracuseStep 833687 = 1250531) B1250531
theorem B833707 : Blo 830350 833707 := bstep (se 1 (by rfl) ⟨625280, by rfl⟩ : syracuseStep 833707 = 1250561) B1250561
theorem B833719 : Blo 830350 833719 := bstep (se 1 (by rfl) ⟨625289, by rfl⟩ : syracuseStep 833719 = 1250579) B1250579
theorem B833739 : Blo 830350 833739 := bstep (se 1 (by rfl) ⟨625304, by rfl⟩ : syracuseStep 833739 = 1250609) B1250609
theorem B833751 : Blo 830350 833751 := bstep (se 1 (by rfl) ⟨625313, by rfl⟩ : syracuseStep 833751 = 1250627) B1250627
theorem B833771 : Blo 830350 833771 := bstep (se 1 (by rfl) ⟨625328, by rfl⟩ : syracuseStep 833771 = 1250657) B1250657
theorem B833783 : Blo 830350 833783 := bstep (se 1 (by rfl) ⟨625337, by rfl⟩ : syracuseStep 833783 = 1250675) B1250675
theorem B833803 : Blo 830350 833803 := bstep (se 1 (by rfl) ⟨625352, by rfl⟩ : syracuseStep 833803 = 1250705) B1250705
theorem B833815 : Blo 830350 833815 := bstep (se 1 (by rfl) ⟨625361, by rfl⟩ : syracuseStep 833815 = 1250723) B1250723
theorem B833835 : Blo 830350 833835 := bstep (se 1 (by rfl) ⟨625376, by rfl⟩ : syracuseStep 833835 = 1250753) B1250753
theorem B833847 : Blo 830350 833847 := bstep (se 1 (by rfl) ⟨625385, by rfl⟩ : syracuseStep 833847 = 1250771) B1250771
theorem B833867 : Blo 830350 833867 := bstep (se 1 (by rfl) ⟨625400, by rfl⟩ : syracuseStep 833867 = 1250801) B1250801
theorem B833879 : Blo 830350 833879 := bstep (se 1 (by rfl) ⟨625409, by rfl⟩ : syracuseStep 833879 = 1250819) B1250819
theorem B833899 : Blo 830350 833899 := bstep (se 1 (by rfl) ⟨625424, by rfl⟩ : syracuseStep 833899 = 1250849) B1250849
theorem B833911 : Blo 830350 833911 := bstep (se 1 (by rfl) ⟨625433, by rfl⟩ : syracuseStep 833911 = 1250867) B1250867
theorem B833931 : Blo 830350 833931 := bstep (se 1 (by rfl) ⟨625448, by rfl⟩ : syracuseStep 833931 = 1250897) B1250897
theorem B833943 : Blo 830350 833943 := bstep (se 1 (by rfl) ⟨625457, by rfl⟩ : syracuseStep 833943 = 1250915) B1250915
theorem B833963 : Blo 830350 833963 := bstep (se 1 (by rfl) ⟨625472, by rfl⟩ : syracuseStep 833963 = 1250945) B1250945
theorem B833975 : Blo 830350 833975 := bstep (se 1 (by rfl) ⟨625481, by rfl⟩ : syracuseStep 833975 = 1250963) B1250963
theorem B3553739 : Blo 830350 3553739 := bstep (se 1 (by rfl) ⟨2665304, by rfl⟩ : syracuseStep 3553739 = 5330609) B5330609
theorem B833995 : Blo 830350 833995 := bstep (se 1 (by rfl) ⟨625496, by rfl⟩ : syracuseStep 833995 = 1250993) B1250993
theorem B834007 : Blo 830350 834007 := bstep (se 1 (by rfl) ⟨625505, by rfl⟩ : syracuseStep 834007 = 1251011) B1251011
theorem B2669021 : Blo 830350 2669021 := bstep (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) B1000883
theorem B834027 : Blo 830350 834027 := bstep (se 1 (by rfl) ⟨625520, by rfl⟩ : syracuseStep 834027 = 1251041) B1251041
theorem B834039 : Blo 830350 834039 := bstep (se 1 (by rfl) ⟨625529, by rfl⟩ : syracuseStep 834039 = 1251059) B1251059
theorem B3160579 : Blo 830350 3160579 := bstep (se 1 (by rfl) ⟨2370434, by rfl⟩ : syracuseStep 3160579 = 4740869) B4740869
theorem B834059 : Blo 830350 834059 := bstep (se 1 (by rfl) ⟨625544, by rfl⟩ : syracuseStep 834059 = 1251089) B1251089
theorem B834071 : Blo 830350 834071 := bstep (se 1 (by rfl) ⟨625553, by rfl⟩ : syracuseStep 834071 = 1251107) B1251107
theorem B834091 : Blo 830350 834091 := bstep (se 1 (by rfl) ⟨625568, by rfl⟩ : syracuseStep 834091 = 1251137) B1251137
theorem B834103 : Blo 830350 834103 := bstep (se 1 (by rfl) ⟨625577, by rfl⟩ : syracuseStep 834103 = 1251155) B1251155
theorem B834123 : Blo 830350 834123 := bstep (se 1 (by rfl) ⟨625592, by rfl⟩ : syracuseStep 834123 = 1251185) B1251185
theorem B834135 : Blo 830350 834135 := bstep (se 1 (by rfl) ⟨625601, by rfl⟩ : syracuseStep 834135 = 1251203) B1251203
theorem B4209245 : Blo 830350 4209245 := bstep (se 3 (by rfl) ⟨789233, by rfl⟩ : syracuseStep 4209245 = 1578467) B1578467
theorem B834155 : Blo 830350 834155 := bstep (se 1 (by rfl) ⟨625616, by rfl⟩ : syracuseStep 834155 = 1251233) B1251233
theorem B834167 : Blo 830350 834167 := bstep (se 1 (by rfl) ⟨625625, by rfl⟩ : syracuseStep 834167 = 1251251) B1251251
theorem B834187 : Blo 830350 834187 := bstep (se 1 (by rfl) ⟨625640, by rfl⟩ : syracuseStep 834187 = 1251281) B1251281
theorem B834199 : Blo 830350 834199 := bstep (se 1 (by rfl) ⟨625649, by rfl⟩ : syracuseStep 834199 = 1251299) B1251299
theorem B834219 : Blo 830350 834219 := bstep (se 1 (by rfl) ⟨625664, by rfl⟩ : syracuseStep 834219 = 1251329) B1251329
theorem B834231 : Blo 830350 834231 := bstep (se 1 (by rfl) ⟨625673, by rfl⟩ : syracuseStep 834231 = 1251347) B1251347
theorem B834251 : Blo 830350 834251 := bstep (se 1 (by rfl) ⟨625688, by rfl⟩ : syracuseStep 834251 = 1251377) B1251377
theorem B834263 : Blo 830350 834263 := bstep (se 1 (by rfl) ⟨625697, by rfl⟩ : syracuseStep 834263 = 1251395) B1251395
theorem B834283 : Blo 830350 834283 := bstep (se 1 (by rfl) ⟨625712, by rfl⟩ : syracuseStep 834283 = 1251425) B1251425
theorem B834295 : Blo 830350 834295 := bstep (se 1 (by rfl) ⟨625721, by rfl⟩ : syracuseStep 834295 = 1251443) B1251443
theorem B834315 : Blo 830350 834315 := bstep (se 1 (by rfl) ⟨625736, by rfl⟩ : syracuseStep 834315 = 1251473) B1251473
theorem B834327 : Blo 830350 834327 := bstep (se 1 (by rfl) ⟨625745, by rfl⟩ : syracuseStep 834327 = 1251491) B1251491
theorem B834347 : Blo 830350 834347 := bstep (se 1 (by rfl) ⟨625760, by rfl⟩ : syracuseStep 834347 = 1251521) B1251521
theorem B3160883 : Blo 830350 3160883 := bstep (se 1 (by rfl) ⟨2370662, by rfl⟩ : syracuseStep 3160883 = 4741325) B4741325
theorem B4733761 : Blo 830350 4733761 := bstep (se 2 (by rfl) ⟨1775160, by rfl⟩ : syracuseStep 4733761 = 3550321) B3550321
theorem B6306821 : Blo 830350 6306821 := bstep (se 4 (by rfl) ⟨591264, by rfl⟩ : syracuseStep 6306821 = 1182529) B1182529
theorem B6077591 : Blo 830350 6077591 := bstep (se 1 (by rfl) ⟨4558193, by rfl⟩ : syracuseStep 6077591 = 9116387) B9116387
theorem B4504793 : Blo 830350 4504793 := bstep (se 2 (by rfl) ⟨1689297, by rfl⟩ : syracuseStep 4504793 = 3378595) B3378595
theorem B2669917 : Blo 830350 2669917 := bstep (se 3 (by rfl) ⟨500609, by rfl⟩ : syracuseStep 2669917 = 1001219) B1001219
theorem B9125237 : Blo 830350 9125237 := bstep (se 5 (by rfl) ⟨427745, by rfl⟩ : syracuseStep 9125237 = 855491) B855491
theorem B9485747 : Blo 830350 9485747 := bstep (se 1 (by rfl) ⟨7114310, by rfl⟩ : syracuseStep 9485747 = 14228621) B14228621
theorem B3161537 : Blo 830350 3161537 := bstep (se 2 (by rfl) ⟨1185576, by rfl⟩ : syracuseStep 3161537 = 2371153) B2371153
theorem B3554867 : Blo 830350 3554867 := bstep (se 1 (by rfl) ⟨2666150, by rfl⟩ : syracuseStep 3554867 = 5332301) B5332301
theorem B2375219 : Blo 830350 2375219 := bstep (se 1 (by rfl) ⟨1781414, by rfl⟩ : syracuseStep 2375219 = 3562829) B3562829
theorem B2440793 : Blo 830350 2440793 := bstep (se 2 (by rfl) ⟨915297, by rfl⟩ : syracuseStep 2440793 = 1830595) B1830595
theorem B5324561 : Blo 830350 5324561 := bstep (se 2 (by rfl) ⟨1996710, by rfl⟩ : syracuseStep 5324561 = 3993421) B3993421
theorem B5062445 : Blo 830350 5062445 := bstep (se 3 (by rfl) ⟨949208, by rfl⟩ : syracuseStep 5062445 = 1898417) B1898417
theorem B7094081 : Blo 830350 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B6012737 : Blo 830350 6012737 := bstep (se 2 (by rfl) ⟨2254776, by rfl⟩ : syracuseStep 6012737 = 4509553) B4509553
theorem B999307 : Blo 830350 999307 := bstep (se 1 (by rfl) ⟨749480, by rfl⟩ : syracuseStep 999307 = 1498961) B1498961
theorem B2998237 : Blo 830350 2998237 := bstep (se 3 (by rfl) ⟨562169, by rfl⟩ : syracuseStep 2998237 = 1124339) B1124339
theorem B2703539 : Blo 830350 2703539 := bstep (se 1 (by rfl) ⟨2027654, by rfl⟩ : syracuseStep 2703539 = 4055309) B4055309
theorem B1622209 : Blo 830350 1622209 := bstep (se 2 (by rfl) ⟨608328, by rfl⟩ : syracuseStep 1622209 = 1216657) B1216657
theorem B934231 : Blo 830350 934231 := bstep (se 1 (by rfl) ⟨700673, by rfl⟩ : syracuseStep 934231 = 1401347) B1401347
theorem B934411 : Blo 830350 934411 := bstep (se 1 (by rfl) ⟨700808, by rfl⟩ : syracuseStep 934411 = 1401617) B1401617
theorem B4571741 : Blo 830350 4571741 := bstep (se 3 (by rfl) ⟨857201, by rfl⟩ : syracuseStep 4571741 = 1714403) B1714403
theorem B934519 : Blo 830350 934519 := bstep (se 1 (by rfl) ⟨700889, by rfl⟩ : syracuseStep 934519 = 1401779) B1401779
theorem B3850897 : Blo 830350 3850897 := bstep (se 2 (by rfl) ⟨1444086, by rfl⟩ : syracuseStep 3850897 = 2888173) B2888173
theorem B4211351 : Blo 830350 4211351 := bstep (se 1 (by rfl) ⟨3158513, by rfl⟩ : syracuseStep 4211351 = 6317027) B6317027
theorem B3162797 : Blo 830350 3162797 := bstep (se 3 (by rfl) ⟨593024, by rfl⟩ : syracuseStep 3162797 = 1186049) B1186049
theorem B3162827 : Blo 830350 3162827 := bstep (se 1 (by rfl) ⟨2372120, by rfl⟩ : syracuseStep 3162827 = 4744241) B4744241
theorem B934699 : Blo 830350 934699 := bstep (se 1 (by rfl) ⟨701024, by rfl⟩ : syracuseStep 934699 = 1402049) B1402049
theorem B2278219 : Blo 830350 2278219 := bstep (se 1 (by rfl) ⟨1708664, by rfl⟩ : syracuseStep 2278219 = 3417329) B3417329
theorem B9487205 : Blo 830350 9487205 := bstep (se 4 (by rfl) ⟨889425, by rfl⟩ : syracuseStep 9487205 = 1778851) B1778851
theorem B934807 : Blo 830350 934807 := bstep (se 1 (by rfl) ⟨701105, by rfl⟩ : syracuseStep 934807 = 1402211) B1402211
theorem B2802653 : Blo 830350 2802653 := bstep (se 3 (by rfl) ⟨525497, by rfl⟩ : syracuseStep 2802653 = 1050995) B1050995
theorem B934987 : Blo 830350 934987 := bstep (se 1 (by rfl) ⟨701240, by rfl⟩ : syracuseStep 934987 = 1402481) B1402481
theorem B4867165 : Blo 830350 4867165 := bstep (se 3 (by rfl) ⟨912593, by rfl⟩ : syracuseStep 4867165 = 1825187) B1825187
theorem B30327949 : Blo 830350 30327949 := bstep (se 3 (by rfl) ⟨5686490, by rfl⟩ : syracuseStep 30327949 = 11372981) B11372981
theorem B935095 : Blo 830350 935095 := bstep (se 1 (by rfl) ⟨701321, by rfl⟩ : syracuseStep 935095 = 1402643) B1402643
theorem B1688779 : Blo 830350 1688779 := bstep (se 1 (by rfl) ⟨1266584, by rfl⟩ : syracuseStep 1688779 = 2533169) B2533169
theorem B1262935 : Blo 830350 1262935 := bstep (se 1 (by rfl) ⟨947201, by rfl⟩ : syracuseStep 1262935 = 1894403) B1894403
theorem B3163481 : Blo 830350 3163481 := bstep (se 2 (by rfl) ⟨1186305, by rfl⟩ : syracuseStep 3163481 = 2372611) B2372611
theorem B935275 : Blo 830350 935275 := bstep (se 1 (by rfl) ⟨701456, by rfl⟩ : syracuseStep 935275 = 1402913) B1402913
theorem B15582581 : Blo 830350 15582581 := bstep (se 5 (by rfl) ⟨730433, by rfl⟩ : syracuseStep 15582581 = 1460867) B1460867
theorem B6309251 : Blo 830350 6309251 := bstep (se 1 (by rfl) ⟨4731938, by rfl⟩ : syracuseStep 6309251 = 9463877) B9463877
theorem B3556781 : Blo 830350 3556781 := bstep (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) B1333793
theorem B935383 : Blo 830350 935383 := bstep (se 1 (by rfl) ⟨701537, by rfl⟩ : syracuseStep 935383 = 1403075) B1403075
theorem B1263179 : Blo 830350 1263179 := bstep (se 1 (by rfl) ⟨947384, by rfl⟩ : syracuseStep 1263179 = 1894769) B1894769
theorem B34162307 : Blo 830350 34162307 := bstep (se 1 (by rfl) ⟨25621730, by rfl⟩ : syracuseStep 34162307 = 51243461) B51243461
theorem B935563 : Blo 830350 935563 := bstep (se 1 (by rfl) ⟨701672, by rfl⟩ : syracuseStep 935563 = 1403345) B1403345
theorem B3163799 : Blo 830350 3163799 := bstep (se 1 (by rfl) ⟨2372849, by rfl⟩ : syracuseStep 3163799 = 4745699) B4745699
theorem B935671 : Blo 830350 935671 := bstep (se 1 (by rfl) ⟨701753, by rfl⟩ : syracuseStep 935671 = 1403507) B1403507
theorem B1689355 : Blo 830350 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B935851 : Blo 830350 935851 := bstep (se 1 (by rfl) ⟨701888, by rfl⟩ : syracuseStep 935851 = 1403777) B1403777
theorem B1001431 : Blo 830350 1001431 := bstep (se 1 (by rfl) ⟨751073, by rfl⟩ : syracuseStep 1001431 = 1502147) B1502147
theorem B935959 : Blo 830350 935959 := bstep (se 1 (by rfl) ⟨701969, by rfl⟩ : syracuseStep 935959 = 1403939) B1403939
theorem B2803787 : Blo 830350 2803787 := bstep (se 1 (by rfl) ⟨2102840, by rfl⟩ : syracuseStep 2803787 = 4205681) B4205681
theorem B3557465 : Blo 830350 3557465 := bstep (se 2 (by rfl) ⟨1334049, by rfl⟩ : syracuseStep 3557465 = 2668099) B2668099
theorem B4737203 : Blo 830350 4737203 := bstep (se 1 (by rfl) ⟨3552902, by rfl⟩ : syracuseStep 4737203 = 7105805) B7105805
theorem B20269237 : Blo 830350 20269237 := bstep (se 5 (by rfl) ⟨950120, by rfl⟩ : syracuseStep 20269237 = 1900241) B1900241
theorem B936139 : Blo 830350 936139 := bstep (se 1 (by rfl) ⟨702104, by rfl⟩ : syracuseStep 936139 = 1404209) B1404209
theorem B15157489 : Blo 830350 15157489 := bstep (se 2 (by rfl) ⟨5684058, by rfl⟩ : syracuseStep 15157489 = 11368117) B11368117
theorem B3164467 : Blo 830350 3164467 := bstep (se 1 (by rfl) ⟨2373350, by rfl⟩ : syracuseStep 3164467 = 4746701) B4746701
theorem B936247 : Blo 830350 936247 := bstep (se 1 (by rfl) ⟨702185, by rfl⟩ : syracuseStep 936247 = 1404371) B1404371
theorem B2804057 : Blo 830350 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B936427 : Blo 830350 936427 := bstep (se 1 (by rfl) ⟨702320, by rfl⟩ : syracuseStep 936427 = 1404641) B1404641
theorem B1067531 : Blo 830350 1067531 := bstep (se 1 (by rfl) ⟨800648, by rfl⟩ : syracuseStep 1067531 = 1601297) B1601297
theorem B936535 : Blo 830350 936535 := bstep (se 1 (by rfl) ⟨702401, by rfl⟩ : syracuseStep 936535 = 1404803) B1404803
theorem B10144349 : Blo 830350 10144349 := bstep (se 3 (by rfl) ⟨1902065, by rfl⟩ : syracuseStep 10144349 = 3804131) B3804131
theorem B936715 : Blo 830350 936715 := bstep (se 1 (by rfl) ⟨702536, by rfl⟩ : syracuseStep 936715 = 1405073) B1405073
theorem B936823 : Blo 830350 936823 := bstep (se 1 (by rfl) ⟨702617, by rfl⟩ : syracuseStep 936823 = 1405235) B1405235
theorem B1919947 : Blo 830350 1919947 := bstep (se 1 (by rfl) ⟨1439960, by rfl⟩ : syracuseStep 1919947 = 2879921) B2879921
theorem B2247641 : Blo 830350 2247641 := bstep (se 2 (by rfl) ⟨842865, by rfl⟩ : syracuseStep 2247641 = 1685731) B1685731
theorem B2804759 : Blo 830350 2804759 := bstep (se 1 (by rfl) ⟨2103569, by rfl⟩ : syracuseStep 2804759 = 4207139) B4207139
theorem B937003 : Blo 830350 937003 := bstep (se 1 (by rfl) ⟨702752, by rfl⟩ : syracuseStep 937003 = 1405505) B1405505
theorem B8113283 : Blo 830350 8113283 := bstep (se 1 (by rfl) ⟨6084962, by rfl⟩ : syracuseStep 8113283 = 12169925) B12169925
theorem B937111 : Blo 830350 937111 := bstep (se 1 (by rfl) ⟨702833, by rfl⟩ : syracuseStep 937111 = 1405667) B1405667
theorem B1330391 : Blo 830350 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B60738821 : Blo 830350 60738821 := bstep (se 4 (by rfl) ⟨5694264, by rfl⟩ : syracuseStep 60738821 = 11388529) B11388529
theorem B937291 : Blo 830350 937291 := bstep (se 1 (by rfl) ⟨702968, by rfl⟩ : syracuseStep 937291 = 1405937) B1405937
theorem B937399 : Blo 830350 937399 := bstep (se 1 (by rfl) ⟨703049, by rfl⟩ : syracuseStep 937399 = 1406099) B1406099
theorem B3165713 : Blo 830350 3165713 := bstep (se 2 (by rfl) ⟨1187142, by rfl⟩ : syracuseStep 3165713 = 2374285) B2374285
theorem B2805299 : Blo 830350 2805299 := bstep (se 1 (by rfl) ⟨2103974, by rfl⟩ : syracuseStep 2805299 = 4207949) B4207949
theorem B4738661 : Blo 830350 4738661 := bstep (se 4 (by rfl) ⟨444249, by rfl⟩ : syracuseStep 4738661 = 888499) B888499
theorem B937579 : Blo 830350 937579 := bstep (se 1 (by rfl) ⟨703184, by rfl⟩ : syracuseStep 937579 = 1406369) B1406369
theorem B937687 : Blo 830350 937687 := bstep (se 1 (by rfl) ⟨703265, by rfl⟩ : syracuseStep 937687 = 1406531) B1406531
theorem B2805569 : Blo 830350 2805569 := bstep (se 2 (by rfl) ⟨1052088, by rfl⟩ : syracuseStep 2805569 = 2104177) B2104177
theorem B937867 : Blo 830350 937867 := bstep (se 1 (by rfl) ⟨703400, by rfl⟩ : syracuseStep 937867 = 1406801) B1406801
theorem B937975 : Blo 830350 937975 := bstep (se 1 (by rfl) ⟨703481, by rfl⟩ : syracuseStep 937975 = 1406963) B1406963
theorem B4214915 : Blo 830350 4214915 := bstep (se 1 (by rfl) ⟨3161186, by rfl⟩ : syracuseStep 4214915 = 6322373) B6322373
theorem B938155 : Blo 830350 938155 := bstep (se 1 (by rfl) ⟨703616, by rfl⟩ : syracuseStep 938155 = 1407233) B1407233
theorem B3166411 : Blo 830350 3166411 := bstep (se 1 (by rfl) ⟨2374808, by rfl⟩ : syracuseStep 3166411 = 4749617) B4749617
theorem B938263 : Blo 830350 938263 := bstep (se 1 (by rfl) ⟨703697, by rfl⟩ : syracuseStep 938263 = 1407395) B1407395
theorem B2806109 : Blo 830350 2806109 := bstep (se 3 (by rfl) ⟨526145, by rfl⟩ : syracuseStep 2806109 = 1052291) B1052291
theorem B938443 : Blo 830350 938443 := bstep (se 1 (by rfl) ⟨703832, by rfl⟩ : syracuseStep 938443 = 1407665) B1407665
theorem B3166685 : Blo 830350 3166685 := bstep (se 3 (by rfl) ⟨593753, by rfl⟩ : syracuseStep 3166685 = 1187507) B1187507
theorem B938551 : Blo 830350 938551 := bstep (se 1 (by rfl) ⟨703913, by rfl⟩ : syracuseStep 938551 = 1407827) B1407827
theorem B6312653 : Blo 830350 6312653 := bstep (se 3 (by rfl) ⟨1183622, by rfl⟩ : syracuseStep 6312653 = 2367245) B2367245
theorem B7983917 : Blo 830350 7983917 := bstep (se 3 (by rfl) ⟨1496984, by rfl⟩ : syracuseStep 7983917 = 2993969) B2993969
theorem B3789719 : Blo 830350 3789719 := bstep (se 1 (by rfl) ⟨2842289, by rfl⟩ : syracuseStep 3789719 = 5684579) B5684579
theorem B4281437 : Blo 830350 4281437 := bstep (se 3 (by rfl) ⟨802769, by rfl⟩ : syracuseStep 4281437 = 1605539) B1605539
theorem B3167383 : Blo 830350 3167383 := bstep (se 1 (by rfl) ⟨2375537, by rfl⟩ : syracuseStep 3167383 = 4751075) B4751075
theorem B6313139 : Blo 830350 6313139 := bstep (se 1 (by rfl) ⟨4734854, by rfl⟩ : syracuseStep 6313139 = 9469709) B9469709
theorem B3003571 : Blo 830350 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B2807243 : Blo 830350 2807243 := bstep (se 1 (by rfl) ⟨2105432, by rfl⟩ : syracuseStep 2807243 = 4210865) B4210865
theorem B2807513 : Blo 830350 2807513 := bstep (se 2 (by rfl) ⟨1052817, by rfl⟩ : syracuseStep 2807513 = 2105635) B2105635
theorem B3004235 : Blo 830350 3004235 := bstep (se 1 (by rfl) ⟨2253176, by rfl⟩ : syracuseStep 3004235 = 4506353) B4506353
theorem B2250841 : Blo 830350 2250841 := bstep (se 2 (by rfl) ⟨844065, by rfl⟩ : syracuseStep 2250841 = 1688131) B1688131
theorem B1267991 : Blo 830350 1267991 := bstep (se 1 (by rfl) ⟨950993, by rfl⟩ : syracuseStep 1267991 = 1901987) B1901987
theorem B3561803 : Blo 830350 3561803 := bstep (se 1 (by rfl) ⟨2671352, by rfl⟩ : syracuseStep 3561803 = 5342705) B5342705
theorem B2808215 : Blo 830350 2808215 := bstep (se 1 (by rfl) ⟨2106161, by rfl⟩ : syracuseStep 2808215 = 4212323) B4212323
theorem B6314597 : Blo 830350 6314597 := bstep (se 4 (by rfl) ⟨591993, by rfl⟩ : syracuseStep 6314597 = 1183987) B1183987
theorem B1071883 : Blo 830350 1071883 := bstep (se 1 (by rfl) ⟨803912, by rfl⟩ : syracuseStep 1071883 = 1607825) B1607825
theorem B2808755 : Blo 830350 2808755 := bstep (se 1 (by rfl) ⟨2106566, by rfl⟩ : syracuseStep 2808755 = 4213133) B4213133
theorem B6315083 : Blo 830350 6315083 := bstep (se 1 (by rfl) ⟨4736312, by rfl⟩ : syracuseStep 6315083 = 9472625) B9472625
theorem B5332043 : Blo 830350 5332043 := bstep (se 1 (by rfl) ⟨3999032, by rfl⟩ : syracuseStep 5332043 = 7998065) B7998065
theorem B5692517 : Blo 830350 5692517 := bstep (se 4 (by rfl) ⟨533673, by rfl⟩ : syracuseStep 5692517 = 1067347) B1067347
theorem B2809025 : Blo 830350 2809025 := bstep (se 2 (by rfl) ⟨1053384, by rfl⟩ : syracuseStep 2809025 = 2106769) B2106769
theorem B9002285 : Blo 830350 9002285 := bstep (se 3 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 9002285 = 3375857) B3375857
theorem B2252225 : Blo 830350 2252225 := bstep (se 2 (by rfl) ⟨844584, by rfl⟩ : syracuseStep 2252225 = 1689169) B1689169
theorem B3792349 : Blo 830350 3792349 := bstep (se 3 (by rfl) ⟨711065, by rfl⟩ : syracuseStep 3792349 = 1422131) B1422131
theorem B5987915 : Blo 830350 5987915 := bstep (se 1 (by rfl) ⟨4490936, by rfl⟩ : syracuseStep 5987915 = 8981873) B8981873
theorem B2809565 : Blo 830350 2809565 := bstep (se 3 (by rfl) ⟨526793, by rfl⟩ : syracuseStep 2809565 = 1053587) B1053587
theorem B4218641 : Blo 830350 4218641 := bstep (se 2 (by rfl) ⟨1581990, by rfl⟩ : syracuseStep 4218641 = 3163981) B3163981
theorem B4218803 : Blo 830350 4218803 := bstep (se 1 (by rfl) ⟨3164102, by rfl⟩ : syracuseStep 4218803 = 6328205) B6328205
theorem B3563443 : Blo 830350 3563443 := bstep (se 1 (by rfl) ⟨2672582, by rfl⟩ : syracuseStep 3563443 = 5345165) B5345165
theorem B3006425 : Blo 830350 3006425 := bstep (se 2 (by rfl) ⟨1127409, by rfl⟩ : syracuseStep 3006425 = 2254819) B2254819
theorem B24371381 : Blo 830350 24371381 := bstep (se 5 (by rfl) ⟨1142408, by rfl⟩ : syracuseStep 24371381 = 2284817) B2284817
theorem B3367115 : Blo 830350 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B3793169 : Blo 830350 3793169 := bstep (se 2 (by rfl) ⟨1422438, by rfl⟩ : syracuseStep 3793169 = 2844877) B2844877
theorem B1401239 : Blo 830350 1401239 := bstep (se 1 (by rfl) ⟨1050929, by rfl⟩ : syracuseStep 1401239 = 2101859) B2101859
theorem B1401367 : Blo 830350 1401367 := bstep (se 1 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 1401367 = 2102051) B2102051
theorem B5333683 : Blo 830350 5333683 := bstep (se 1 (by rfl) ⟨4000262, by rfl⟩ : syracuseStep 5333683 = 8000525) B8000525
theorem B3793625 : Blo 830350 3793625 := bstep (se 2 (by rfl) ⟨1422609, by rfl⟩ : syracuseStep 3793625 = 2845219) B2845219
theorem B2810699 : Blo 830350 2810699 := bstep (se 1 (by rfl) ⟨2108024, by rfl⟩ : syracuseStep 2810699 = 4216049) B4216049
theorem B1336151 : Blo 830350 1336151 := bstep (se 1 (by rfl) ⟨1002113, by rfl⟩ : syracuseStep 1336151 = 2004227) B2004227
theorem B2810969 : Blo 830350 2810969 := bstep (se 2 (by rfl) ⟨1054113, by rfl⟩ : syracuseStep 2810969 = 2108227) B2108227
theorem B1401995 : Blo 830350 1401995 := bstep (se 1 (by rfl) ⟨1051496, by rfl⟩ : syracuseStep 1401995 = 2102993) B2102993
theorem B1402123 : Blo 830350 1402123 := bstep (se 1 (by rfl) ⟨1051592, by rfl⟩ : syracuseStep 1402123 = 2103185) B2103185
theorem B4744493 : Blo 830350 4744493 := bstep (se 3 (by rfl) ⟨889592, by rfl⟩ : syracuseStep 4744493 = 1779185) B1779185
theorem B5989783 : Blo 830350 5989783 := bstep (se 1 (by rfl) ⟨4492337, by rfl⟩ : syracuseStep 5989783 = 8984675) B8984675
theorem B1402265 : Blo 830350 1402265 := bstep (se 2 (by rfl) ⟨525849, by rfl⟩ : syracuseStep 1402265 = 1051699) B1051699
theorem B1500619 : Blo 830350 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B6743569 : Blo 830350 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B1402393 : Blo 830350 1402393 := bstep (se 2 (by rfl) ⟨525897, by rfl⟩ : syracuseStep 1402393 = 1051795) B1051795
theorem B2254387 : Blo 830350 2254387 := bstep (se 1 (by rfl) ⟨1690790, by rfl⟩ : syracuseStep 2254387 = 3381581) B3381581
theorem B6416023 : Blo 830350 6416023 := bstep (se 1 (by rfl) ⟨4812017, by rfl⟩ : syracuseStep 6416023 = 9624035) B9624035
theorem B5072563 : Blo 830350 5072563 := bstep (se 1 (by rfl) ⟨3804422, by rfl⟩ : syracuseStep 5072563 = 7608845) B7608845
theorem B2811671 : Blo 830350 2811671 := bstep (se 1 (by rfl) ⟨2108753, by rfl⟩ : syracuseStep 2811671 = 4217507) B4217507
theorem B4220747 : Blo 830350 4220747 := bstep (se 1 (by rfl) ⟨3165560, by rfl⟩ : syracuseStep 4220747 = 6331121) B6331121
theorem B845687 : Blo 830350 845687 := bstep (se 1 (by rfl) ⟨634265, by rfl⟩ : syracuseStep 845687 = 1268531) B1268531
theorem B1501195 : Blo 830350 1501195 := bstep (se 1 (by rfl) ⟨1125896, by rfl⟩ : syracuseStep 1501195 = 2251793) B2251793
theorem B1894423 : Blo 830350 1894423 := bstep (se 1 (by rfl) ⟨1420817, by rfl⟩ : syracuseStep 1894423 = 2841635) B2841635
theorem B1402967 : Blo 830350 1402967 := bstep (se 1 (by rfl) ⟨1052225, by rfl⟩ : syracuseStep 1402967 = 2104451) B2104451
theorem B1403095 : Blo 830350 1403095 := bstep (se 1 (by rfl) ⟨1052321, by rfl⟩ : syracuseStep 1403095 = 2104643) B2104643
theorem B2812211 : Blo 830350 2812211 := bstep (se 1 (by rfl) ⟨2109158, by rfl⟩ : syracuseStep 2812211 = 4218317) B4218317
theorem B3041837 : Blo 830350 3041837 := bstep (se 3 (by rfl) ⟨570344, by rfl⟩ : syracuseStep 3041837 = 1140689) B1140689
theorem B2812481 : Blo 830350 2812481 := bstep (se 2 (by rfl) ⟨1054680, by rfl⟩ : syracuseStep 2812481 = 2109361) B2109361
theorem B2845277 : Blo 830350 2845277 := bstep (se 3 (by rfl) ⟨533489, by rfl⟩ : syracuseStep 2845277 = 1066979) B1066979
theorem B1502003 : Blo 830350 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B1403723 : Blo 830350 1403723 := bstep (se 1 (by rfl) ⟨1052792, by rfl⟩ : syracuseStep 1403723 = 2105585) B2105585
theorem B1403851 : Blo 830350 1403851 := bstep (se 1 (by rfl) ⟨1052888, by rfl⟩ : syracuseStep 1403851 = 2105777) B2105777
theorem B8121379 : Blo 830350 8121379 := bstep (se 1 (by rfl) ⟨6091034, by rfl⟩ : syracuseStep 8121379 = 12182069) B12182069
theorem B1403993 : Blo 830350 1403993 := bstep (se 2 (by rfl) ⟨526497, by rfl⟩ : syracuseStep 1403993 = 1052995) B1052995
theorem B2813021 : Blo 830350 2813021 := bstep (se 3 (by rfl) ⟨527441, by rfl⟩ : syracuseStep 2813021 = 1054883) B1054883
theorem B1404121 : Blo 830350 1404121 := bstep (se 2 (by rfl) ⟨526545, by rfl⟩ : syracuseStep 1404121 = 1053091) B1053091
theorem B1895681 : Blo 830350 1895681 := bstep (se 2 (by rfl) ⟨710880, by rfl⟩ : syracuseStep 1895681 = 1421761) B1421761
theorem B3370291 : Blo 830350 3370291 := bstep (se 1 (by rfl) ⟨2527718, by rfl⟩ : syracuseStep 3370291 = 5055437) B5055437
theorem B12021209 : Blo 830350 12021209 := bstep (se 2 (by rfl) ⟨4507953, by rfl⟩ : syracuseStep 12021209 = 9015907) B9015907
theorem B4222529 : Blo 830350 4222529 := bstep (se 2 (by rfl) ⟨1583448, by rfl⟩ : syracuseStep 4222529 = 3166897) B3166897
theorem B4746883 : Blo 830350 4746883 := bstep (se 1 (by rfl) ⟨3560162, by rfl⟩ : syracuseStep 4746883 = 7120325) B7120325
theorem B1404695 : Blo 830350 1404695 := bstep (se 1 (by rfl) ⟨1053521, by rfl⟩ : syracuseStep 1404695 = 2107043) B2107043
theorem B1404823 : Blo 830350 1404823 := bstep (se 1 (by rfl) ⟨1053617, by rfl⟩ : syracuseStep 1404823 = 2107235) B2107235
theorem B9236497 : Blo 830350 9236497 := bstep (se 2 (by rfl) ⟨3463686, by rfl⟩ : syracuseStep 9236497 = 6927373) B6927373
theorem B2814155 : Blo 830350 2814155 := bstep (se 1 (by rfl) ⟨2110616, by rfl⟩ : syracuseStep 2814155 = 4221233) B4221233
theorem B6320429 : Blo 830350 6320429 := bstep (se 3 (by rfl) ⟨1185080, by rfl⟩ : syracuseStep 6320429 = 2370161) B2370161
theorem B2814425 : Blo 830350 2814425 := bstep (se 2 (by rfl) ⟨1055409, by rfl⟩ : syracuseStep 2814425 = 2110819) B2110819
theorem B1405451 : Blo 830350 1405451 := bstep (se 1 (by rfl) ⟨1054088, by rfl⟩ : syracuseStep 1405451 = 2108177) B2108177
theorem B3797549 : Blo 830350 3797549 := bstep (se 3 (by rfl) ⟨712040, by rfl⟩ : syracuseStep 3797549 = 1424081) B1424081
theorem B4747841 : Blo 830350 4747841 := bstep (se 2 (by rfl) ⟨1780440, by rfl⟩ : syracuseStep 4747841 = 3560881) B3560881
theorem B7107203 : Blo 830350 7107203 := bstep (se 1 (by rfl) ⟨5330402, by rfl⟩ : syracuseStep 7107203 = 10660805) B10660805
theorem B1405579 : Blo 830350 1405579 := bstep (se 1 (by rfl) ⟨1054184, by rfl⟩ : syracuseStep 1405579 = 2108369) B2108369
theorem B1405721 : Blo 830350 1405721 := bstep (se 2 (by rfl) ⟨527145, by rfl⟩ : syracuseStep 1405721 = 1054291) B1054291
theorem B1405849 : Blo 830350 1405849 := bstep (se 2 (by rfl) ⟨527193, by rfl⟩ : syracuseStep 1405849 = 1054387) B1054387
theorem B2815127 : Blo 830350 2815127 := bstep (se 1 (by rfl) ⟨2111345, by rfl⟩ : syracuseStep 2815127 = 4222691) B4222691
theorem B1602931 : Blo 830350 1602931 := bstep (se 1 (by rfl) ⟨1202198, by rfl⟩ : syracuseStep 1602931 = 2404397) B2404397
theorem B1406423 : Blo 830350 1406423 := bstep (se 1 (by rfl) ⟨1054817, by rfl⟩ : syracuseStep 1406423 = 2109635) B2109635
theorem B1406551 : Blo 830350 1406551 := bstep (se 1 (by rfl) ⟨1054913, by rfl⟩ : syracuseStep 1406551 = 2109827) B2109827
theorem B2815667 : Blo 830350 2815667 := bstep (se 1 (by rfl) ⟨2111750, by rfl⟩ : syracuseStep 2815667 = 4223501) B4223501
theorem B1996481 : Blo 830350 1996481 := bstep (se 2 (by rfl) ⟨748680, by rfl⟩ : syracuseStep 1996481 = 1497361) B1497361
theorem B947927 : Blo 830350 947927 := bstep (se 1 (by rfl) ⟨710945, by rfl⟩ : syracuseStep 947927 = 1421891) B1421891
theorem B1898291 : Blo 830350 1898291 := bstep (se 1 (by rfl) ⟨1423718, by rfl⟩ : syracuseStep 1898291 = 2847437) B2847437
theorem B1996865 : Blo 830350 1996865 := bstep (se 2 (by rfl) ⟨748824, by rfl⟩ : syracuseStep 1996865 = 1497649) B1497649
theorem B10647683 : Blo 830350 10647683 := bstep (se 1 (by rfl) ⟨7985762, by rfl⟩ : syracuseStep 10647683 = 15971525) B15971525
theorem B1996979 : Blo 830350 1996979 := bstep (se 1 (by rfl) ⟨1497734, by rfl⟩ : syracuseStep 1996979 = 2995469) B2995469
theorem B1407179 : Blo 830350 1407179 := bstep (se 1 (by rfl) ⟨1055384, by rfl⟩ : syracuseStep 1407179 = 2110769) B2110769
theorem B1407307 : Blo 830350 1407307 := bstep (se 1 (by rfl) ⟨1055480, by rfl⟩ : syracuseStep 1407307 = 2110961) B2110961
theorem B3045725 : Blo 830350 3045725 := bstep (se 3 (by rfl) ⟨571073, by rfl⟩ : syracuseStep 3045725 = 1142147) B1142147
theorem B1407449 : Blo 830350 1407449 := bstep (se 2 (by rfl) ⟨527793, by rfl⟩ : syracuseStep 1407449 = 1055587) B1055587
theorem B1407577 : Blo 830350 1407577 := bstep (se 2 (by rfl) ⟨527841, by rfl⟩ : syracuseStep 1407577 = 1055683) B1055683
theorem B6421265 : Blo 830350 6421265 := bstep (se 2 (by rfl) ⟨2407974, by rfl⟩ : syracuseStep 6421265 = 4815949) B4815949
theorem B3603473 : Blo 830350 3603473 := bstep (se 2 (by rfl) ⟨1351302, by rfl⟩ : syracuseStep 3603473 = 2702605) B2702605
theorem B3996803 : Blo 830350 3996803 := bstep (se 1 (by rfl) ⟨2997602, by rfl⟩ : syracuseStep 3996803 = 5995205) B5995205
theorem B949483 : Blo 830350 949483 := bstep (se 1 (by rfl) ⟨712112, by rfl⟩ : syracuseStep 949483 = 1424225) B1424225
theorem B10419461 : Blo 830350 10419461 := bstep (se 4 (by rfl) ⟨976824, by rfl⟩ : syracuseStep 10419461 = 1953649) B1953649
theorem B7110179 : Blo 830350 7110179 := bstep (se 1 (by rfl) ⟨5332634, by rfl⟩ : syracuseStep 7110179 = 10665269) B10665269
theorem B2162945 : Blo 830350 2162945 := bstep (se 2 (by rfl) ⟨811104, by rfl⟩ : syracuseStep 2162945 = 1622209) B1622209
theorem B1245575 : Blo 830350 1245575 := bstep (se 1 (by rfl) ⟨934181, by rfl⟩ : syracuseStep 1245575 = 1868363) B1868363
theorem B14418323 : Blo 830350 14418323 := bstep (se 1 (by rfl) ⟨10813742, by rfl⟩ : syracuseStep 14418323 = 21627485) B21627485
theorem B3047827 : Blo 830350 3047827 := bstep (se 1 (by rfl) ⟨2285870, by rfl⟩ : syracuseStep 3047827 = 4571741) B4571741
theorem B1245611 : Blo 830350 1245611 := bstep (se 1 (by rfl) ⟨934208, by rfl⟩ : syracuseStep 1245611 = 1868417) B1868417
theorem B1245641 : Blo 830350 1245641 := bstep (se 2 (by rfl) ⟨467115, by rfl⟩ : syracuseStep 1245641 = 934231) B934231
theorem B7209437 : Blo 830350 7209437 := bstep (se 3 (by rfl) ⟨1351769, by rfl⟩ : syracuseStep 7209437 = 2703539) B2703539
theorem B1245755 : Blo 830350 1245755 := bstep (se 1 (by rfl) ⟨934316, by rfl⟩ : syracuseStep 1245755 = 1868633) B1868633
theorem B6324803 : Blo 830350 6324803 := bstep (se 1 (by rfl) ⟨4743602, by rfl⟩ : syracuseStep 6324803 = 9487205) B9487205
theorem B1245815 : Blo 830350 1245815 := bstep (se 1 (by rfl) ⟨934361, by rfl⟩ : syracuseStep 1245815 = 1868723) B1868723
theorem B1245839 : Blo 830350 1245839 := bstep (se 1 (by rfl) ⟨934379, by rfl⟩ : syracuseStep 1245839 = 1868759) B1868759
theorem B1868435 : Blo 830350 1868435 := bstep (se 1 (by rfl) ⟨1401326, by rfl⟩ : syracuseStep 1868435 = 2802653) B2802653
theorem B1245881 : Blo 830350 1245881 := bstep (se 2 (by rfl) ⟨467205, by rfl⟩ : syracuseStep 1245881 = 934411) B934411
theorem B1868489 : Blo 830350 1868489 := bstep (se 2 (by rfl) ⟨700683, by rfl⟩ : syracuseStep 1868489 = 1401367) B1401367
theorem B1245959 : Blo 830350 1245959 := bstep (se 1 (by rfl) ⟨934469, by rfl⟩ : syracuseStep 1245959 = 1868939) B1868939
theorem B1245995 : Blo 830350 1245995 := bstep (se 1 (by rfl) ⟨934496, by rfl⟩ : syracuseStep 1245995 = 1868993) B1868993
theorem B1246025 : Blo 830350 1246025 := bstep (se 2 (by rfl) ⟨467259, by rfl⟩ : syracuseStep 1246025 = 934519) B934519
theorem B7111577 : Blo 830350 7111577 := bstep (se 2 (by rfl) ⟨2666841, by rfl⟩ : syracuseStep 7111577 = 5333683) B5333683
theorem B10388387 : Blo 830350 10388387 := bstep (se 1 (by rfl) ⟨7791290, by rfl⟩ : syracuseStep 10388387 = 15582581) B15582581
theorem B1246139 : Blo 830350 1246139 := bstep (se 1 (by rfl) ⟨934604, by rfl⟩ : syracuseStep 1246139 = 1869209) B1869209
theorem B1246199 : Blo 830350 1246199 := bstep (se 1 (by rfl) ⟨934649, by rfl⟩ : syracuseStep 1246199 = 1869299) B1869299
theorem B1246223 : Blo 830350 1246223 := bstep (se 1 (by rfl) ⟨934667, by rfl⟩ : syracuseStep 1246223 = 1869335) B1869335
theorem B1246265 : Blo 830350 1246265 := bstep (se 2 (by rfl) ⟨467349, by rfl⟩ : syracuseStep 1246265 = 934699) B934699
theorem B22774871 : Blo 830350 22774871 := bstep (se 1 (by rfl) ⟨17081153, by rfl⟩ : syracuseStep 22774871 = 34162307) B34162307
theorem B1246343 : Blo 830350 1246343 := bstep (se 1 (by rfl) ⟨934757, by rfl⟩ : syracuseStep 1246343 = 1869515) B1869515
theorem B1246379 : Blo 830350 1246379 := bstep (se 1 (by rfl) ⟨934784, by rfl⟩ : syracuseStep 1246379 = 1869569) B1869569
theorem B1246409 : Blo 830350 1246409 := bstep (se 2 (by rfl) ⟨467403, by rfl⟩ : syracuseStep 1246409 = 934807) B934807
theorem B1246523 : Blo 830350 1246523 := bstep (se 1 (by rfl) ⟨934892, by rfl⟩ : syracuseStep 1246523 = 1869785) B1869785
theorem B1246583 : Blo 830350 1246583 := bstep (se 1 (by rfl) ⟨934937, by rfl⟩ : syracuseStep 1246583 = 1869875) B1869875
theorem B1869191 : Blo 830350 1869191 := bstep (se 1 (by rfl) ⟨1401893, by rfl⟩ : syracuseStep 1869191 = 2803787) B2803787
theorem B1246607 : Blo 830350 1246607 := bstep (se 1 (by rfl) ⟨934955, by rfl⟩ : syracuseStep 1246607 = 1869911) B1869911
theorem B1246649 : Blo 830350 1246649 := bstep (se 2 (by rfl) ⟨467493, by rfl⟩ : syracuseStep 1246649 = 934987) B934987
theorem B6489553 : Blo 830350 6489553 := bstep (se 2 (by rfl) ⟨2433582, by rfl⟩ : syracuseStep 6489553 = 4867165) B4867165
theorem B1246727 : Blo 830350 1246727 := bstep (se 1 (by rfl) ⟨935045, by rfl⟩ : syracuseStep 1246727 = 1870091) B1870091
theorem B40437265 : Blo 830350 40437265 := bstep (se 2 (by rfl) ⟨15163974, by rfl⟩ : syracuseStep 40437265 = 30327949) B30327949
theorem B2885149 : Blo 830350 2885149 := bstep (se 3 (by rfl) ⟨540965, by rfl⟩ : syracuseStep 2885149 = 1081931) B1081931
theorem B1246763 : Blo 830350 1246763 := bstep (se 1 (by rfl) ⟨935072, by rfl⟩ : syracuseStep 1246763 = 1870145) B1870145
theorem B1869371 : Blo 830350 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B1246793 : Blo 830350 1246793 := bstep (se 2 (by rfl) ⟨467547, by rfl⟩ : syracuseStep 1246793 = 935095) B935095
theorem B1869497 : Blo 830350 1869497 := bstep (se 2 (by rfl) ⟨701061, by rfl⟩ : syracuseStep 1869497 = 1402123) B1402123
theorem B1246907 : Blo 830350 1246907 := bstep (se 1 (by rfl) ⟨935180, by rfl⟩ : syracuseStep 1246907 = 1870361) B1870361
theorem B1246967 : Blo 830350 1246967 := bstep (se 1 (by rfl) ⟨935225, by rfl⟩ : syracuseStep 1246967 = 1870451) B1870451
theorem B1246991 : Blo 830350 1246991 := bstep (se 1 (by rfl) ⟨935243, by rfl⟩ : syracuseStep 1246991 = 1870487) B1870487
theorem B1247033 : Blo 830350 1247033 := bstep (se 2 (by rfl) ⟨467637, by rfl⟩ : syracuseStep 1247033 = 935275) B935275
theorem B1247111 : Blo 830350 1247111 := bstep (se 1 (by rfl) ⟨935333, by rfl⟩ : syracuseStep 1247111 = 1870667) B1870667
theorem B1247147 : Blo 830350 1247147 := bstep (se 1 (by rfl) ⟨935360, by rfl⟩ : syracuseStep 1247147 = 1870721) B1870721
theorem B2000825 : Blo 830350 2000825 := bstep (se 2 (by rfl) ⟨750309, by rfl⟩ : syracuseStep 2000825 = 1500619) B1500619
theorem B1247177 : Blo 830350 1247177 := bstep (se 2 (by rfl) ⟨467691, by rfl⟩ : syracuseStep 1247177 = 935383) B935383
theorem B1869839 : Blo 830350 1869839 := bstep (se 1 (by rfl) ⟨1402379, by rfl⟩ : syracuseStep 1869839 = 2804759) B2804759
theorem B1869857 : Blo 830350 1869857 := bstep (se 2 (by rfl) ⟨701196, by rfl⟩ : syracuseStep 1869857 = 1402393) B1402393
theorem B1247291 : Blo 830350 1247291 := bstep (se 1 (by rfl) ⟨935468, by rfl⟩ : syracuseStep 1247291 = 1870937) B1870937
theorem B5408855 : Blo 830350 5408855 := bstep (se 1 (by rfl) ⟨4056641, by rfl⟩ : syracuseStep 5408855 = 8113283) B8113283
theorem B1247351 : Blo 830350 1247351 := bstep (se 1 (by rfl) ⟨935513, by rfl⟩ : syracuseStep 1247351 = 1871027) B1871027
theorem B1247375 : Blo 830350 1247375 := bstep (se 1 (by rfl) ⟨935531, by rfl⟩ : syracuseStep 1247375 = 1871063) B1871063
theorem B1247417 : Blo 830350 1247417 := bstep (se 2 (by rfl) ⟨467781, by rfl⟩ : syracuseStep 1247417 = 935563) B935563
theorem B8554697 : Blo 830350 8554697 := bstep (se 2 (by rfl) ⟨3208011, by rfl⟩ : syracuseStep 8554697 = 6416023) B6416023
theorem B1247495 : Blo 830350 1247495 := bstep (se 1 (by rfl) ⟨935621, by rfl⟩ : syracuseStep 1247495 = 1871243) B1871243
theorem B1247531 : Blo 830350 1247531 := bstep (se 1 (by rfl) ⟨935648, by rfl⟩ : syracuseStep 1247531 = 1871297) B1871297
theorem B1247561 : Blo 830350 1247561 := bstep (se 2 (by rfl) ⟨467835, by rfl⟩ : syracuseStep 1247561 = 935671) B935671
theorem B1870199 : Blo 830350 1870199 := bstep (se 1 (by rfl) ⟨1402649, by rfl⟩ : syracuseStep 1870199 = 2805299) B2805299
theorem B854407 : Blo 830350 854407 := bstep (se 1 (by rfl) ⟨640805, by rfl⟩ : syracuseStep 854407 = 1281611) B1281611
theorem B1051051 : Blo 830350 1051051 := bstep (se 1 (by rfl) ⟨788288, by rfl⟩ : syracuseStep 1051051 = 1576577) B1576577
theorem B1247675 : Blo 830350 1247675 := bstep (se 1 (by rfl) ⟨935756, by rfl⟩ : syracuseStep 1247675 = 1871513) B1871513
theorem B1247735 : Blo 830350 1247735 := bstep (se 1 (by rfl) ⟨935801, by rfl⟩ : syracuseStep 1247735 = 1871603) B1871603
theorem B1247759 : Blo 830350 1247759 := bstep (se 1 (by rfl) ⟨935819, by rfl⟩ : syracuseStep 1247759 = 1871639) B1871639
theorem B1870379 : Blo 830350 1870379 := bstep (se 1 (by rfl) ⟨1402784, by rfl⟩ : syracuseStep 1870379 = 2805569) B2805569
theorem B18287147 : Blo 830350 18287147 := bstep (se 1 (by rfl) ⟨13715360, by rfl⟩ : syracuseStep 18287147 = 27430721) B27430721
theorem B1247801 : Blo 830350 1247801 := bstep (se 2 (by rfl) ⟨467925, by rfl⟩ : syracuseStep 1247801 = 935851) B935851
theorem B1247879 : Blo 830350 1247879 := bstep (se 1 (by rfl) ⟨935909, by rfl⟩ : syracuseStep 1247879 = 1871819) B1871819
theorem B1247915 : Blo 830350 1247915 := bstep (se 1 (by rfl) ⟨935936, by rfl⟩ : syracuseStep 1247915 = 1871873) B1871873
theorem B2001593 : Blo 830350 2001593 := bstep (se 2 (by rfl) ⟨750597, by rfl⟩ : syracuseStep 2001593 = 1501195) B1501195
theorem B13470401 : Blo 830350 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B2525897 : Blo 830350 2525897 := bstep (se 2 (by rfl) ⟨947211, by rfl⟩ : syracuseStep 2525897 = 1894423) B1894423
theorem B1247945 : Blo 830350 1247945 := bstep (se 2 (by rfl) ⟨467979, by rfl⟩ : syracuseStep 1247945 = 935959) B935959
theorem B1248059 : Blo 830350 1248059 := bstep (se 1 (by rfl) ⟨936044, by rfl⟩ : syracuseStep 1248059 = 1872089) B1872089
theorem B3607355 : Blo 830350 3607355 := bstep (se 1 (by rfl) ⟨2705516, by rfl⟩ : syracuseStep 3607355 = 5411033) B5411033
theorem B1248119 : Blo 830350 1248119 := bstep (se 1 (by rfl) ⟨936089, by rfl⟩ : syracuseStep 1248119 = 1872179) B1872179
theorem B1248143 : Blo 830350 1248143 := bstep (se 1 (by rfl) ⟨936107, by rfl⟩ : syracuseStep 1248143 = 1872215) B1872215
theorem B1870739 : Blo 830350 1870739 := bstep (se 1 (by rfl) ⟨1403054, by rfl⟩ : syracuseStep 1870739 = 2806109) B2806109
theorem B1248185 : Blo 830350 1248185 := bstep (se 2 (by rfl) ⟨468069, by rfl⟩ : syracuseStep 1248185 = 936139) B936139
theorem B1870793 : Blo 830350 1870793 := bstep (se 2 (by rfl) ⟨701547, by rfl⟩ : syracuseStep 1870793 = 1403095) B1403095
theorem B4492253 : Blo 830350 4492253 := bstep (se 3 (by rfl) ⟨842297, by rfl⟩ : syracuseStep 4492253 = 1684595) B1684595
theorem B1248263 : Blo 830350 1248263 := bstep (se 1 (by rfl) ⟨936197, by rfl⟩ : syracuseStep 1248263 = 1872395) B1872395
theorem B1248299 : Blo 830350 1248299 := bstep (se 1 (by rfl) ⟨936224, by rfl⟩ : syracuseStep 1248299 = 1872449) B1872449
theorem B1248329 : Blo 830350 1248329 := bstep (se 2 (by rfl) ⟨468123, by rfl⟩ : syracuseStep 1248329 = 936247) B936247
theorem B1248443 : Blo 830350 1248443 := bstep (se 1 (by rfl) ⟨936332, by rfl⟩ : syracuseStep 1248443 = 1872665) B1872665
theorem B1248503 : Blo 830350 1248503 := bstep (se 1 (by rfl) ⟨936377, by rfl⟩ : syracuseStep 1248503 = 1872755) B1872755
theorem B2526479 : Blo 830350 2526479 := bstep (se 1 (by rfl) ⟨1894859, by rfl⟩ : syracuseStep 2526479 = 3789719) B3789719
theorem B1248527 : Blo 830350 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B1248569 : Blo 830350 1248569 := bstep (se 2 (by rfl) ⟨468213, by rfl⟩ : syracuseStep 1248569 = 936427) B936427
theorem B1052023 : Blo 830350 1052023 := bstep (se 1 (by rfl) ⟨789017, by rfl⟩ : syracuseStep 1052023 = 1578035) B1578035
theorem B1248647 : Blo 830350 1248647 := bstep (se 1 (by rfl) ⟨936485, by rfl⟩ : syracuseStep 1248647 = 1872971) B1872971
theorem B2854291 : Blo 830350 2854291 := bstep (se 1 (by rfl) ⟨2140718, by rfl⟩ : syracuseStep 2854291 = 4281437) B4281437
theorem B1248683 : Blo 830350 1248683 := bstep (se 1 (by rfl) ⟨936512, by rfl⟩ : syracuseStep 1248683 = 1873025) B1873025
theorem B1248713 : Blo 830350 1248713 := bstep (se 2 (by rfl) ⟨468267, by rfl⟩ : syracuseStep 1248713 = 936535) B936535
theorem B1248827 : Blo 830350 1248827 := bstep (se 1 (by rfl) ⟨936620, by rfl⟩ : syracuseStep 1248827 = 1873241) B1873241
theorem B1248887 : Blo 830350 1248887 := bstep (se 1 (by rfl) ⟨936665, by rfl⟩ : syracuseStep 1248887 = 1873331) B1873331
theorem B1871495 : Blo 830350 1871495 := bstep (se 1 (by rfl) ⟨1403621, by rfl⟩ : syracuseStep 1871495 = 2807243) B2807243
theorem B1248911 : Blo 830350 1248911 := bstep (se 1 (by rfl) ⟨936683, by rfl⟩ : syracuseStep 1248911 = 1873367) B1873367
theorem B1248953 : Blo 830350 1248953 := bstep (se 2 (by rfl) ⟨468357, by rfl⟩ : syracuseStep 1248953 = 936715) B936715
theorem B1052347 : Blo 830350 1052347 := bstep (se 1 (by rfl) ⟨789260, by rfl⟩ : syracuseStep 1052347 = 1578521) B1578521
theorem B1249031 : Blo 830350 1249031 := bstep (se 1 (by rfl) ⟨936773, by rfl⟩ : syracuseStep 1249031 = 1873547) B1873547
theorem B1249067 : Blo 830350 1249067 := bstep (se 1 (by rfl) ⟨936800, by rfl⟩ : syracuseStep 1249067 = 1873601) B1873601
theorem B1871675 : Blo 830350 1871675 := bstep (se 1 (by rfl) ⟨1403756, by rfl⟩ : syracuseStep 1871675 = 2807513) B2807513
theorem B1249097 : Blo 830350 1249097 := bstep (se 2 (by rfl) ⟨468411, by rfl⟩ : syracuseStep 1249097 = 936823) B936823
theorem B2002823 : Blo 830350 2002823 := bstep (se 1 (by rfl) ⟨1502117, by rfl⟩ : syracuseStep 2002823 = 3004235) B3004235
theorem B2559929 : Blo 830350 2559929 := bstep (se 2 (by rfl) ⟨959973, by rfl⟩ : syracuseStep 2559929 = 1919947) B1919947
theorem B1871801 : Blo 830350 1871801 := bstep (se 2 (by rfl) ⟨701925, by rfl⟩ : syracuseStep 1871801 = 1403851) B1403851
theorem B1249211 : Blo 830350 1249211 := bstep (se 1 (by rfl) ⟨936908, by rfl⟩ : syracuseStep 1249211 = 1873817) B1873817
theorem B1249271 : Blo 830350 1249271 := bstep (se 1 (by rfl) ⟨936953, by rfl⟩ : syracuseStep 1249271 = 1873907) B1873907
theorem B1249295 : Blo 830350 1249295 := bstep (se 1 (by rfl) ⟨936971, by rfl⟩ : syracuseStep 1249295 = 1873943) B1873943
theorem B1249337 : Blo 830350 1249337 := bstep (se 2 (by rfl) ⟨468501, by rfl⟩ : syracuseStep 1249337 = 937003) B937003
theorem B1249415 : Blo 830350 1249415 := bstep (se 1 (by rfl) ⟨937061, by rfl⟩ : syracuseStep 1249415 = 1874123) B1874123
theorem B1249451 : Blo 830350 1249451 := bstep (se 1 (by rfl) ⟨937088, by rfl⟩ : syracuseStep 1249451 = 1874177) B1874177
theorem B1577161 : Blo 830350 1577161 := bstep (se 2 (by rfl) ⟨591435, by rfl⟩ : syracuseStep 1577161 = 1182871) B1182871
theorem B1249481 : Blo 830350 1249481 := bstep (se 2 (by rfl) ⟨468555, by rfl⟩ : syracuseStep 1249481 = 937111) B937111
theorem B1872143 : Blo 830350 1872143 := bstep (se 1 (by rfl) ⟨1404107, by rfl⟩ : syracuseStep 1872143 = 2808215) B2808215
theorem B1872161 : Blo 830350 1872161 := bstep (se 2 (by rfl) ⟨702060, by rfl⟩ : syracuseStep 1872161 = 1404121) B1404121
theorem B1249595 : Blo 830350 1249595 := bstep (se 1 (by rfl) ⟨937196, by rfl⟩ : syracuseStep 1249595 = 1874393) B1874393
theorem B1249655 : Blo 830350 1249655 := bstep (se 1 (by rfl) ⟨937241, by rfl⟩ : syracuseStep 1249655 = 1874483) B1874483
theorem B1249679 : Blo 830350 1249679 := bstep (se 1 (by rfl) ⟨937259, by rfl⟩ : syracuseStep 1249679 = 1874519) B1874519
theorem B1249721 : Blo 830350 1249721 := bstep (se 2 (by rfl) ⟨468645, by rfl⟩ : syracuseStep 1249721 = 937291) B937291
theorem B1249799 : Blo 830350 1249799 := bstep (se 1 (by rfl) ⟨937349, by rfl⟩ : syracuseStep 1249799 = 1874699) B1874699
theorem B6754859 : Blo 830350 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B1249835 : Blo 830350 1249835 := bstep (se 1 (by rfl) ⟨937376, by rfl⟩ : syracuseStep 1249835 = 1874753) B1874753
theorem B2527805 : Blo 830350 2527805 := bstep (se 3 (by rfl) ⟨473963, by rfl⟩ : syracuseStep 2527805 = 947927) B947927
theorem B1184329 : Blo 830350 1184329 := bstep (se 2 (by rfl) ⟨444123, by rfl⟩ : syracuseStep 1184329 = 888247) B888247
theorem B1249865 : Blo 830350 1249865 := bstep (se 2 (by rfl) ⟨468699, by rfl⟩ : syracuseStep 1249865 = 937399) B937399
theorem B1872503 : Blo 830350 1872503 := bstep (se 1 (by rfl) ⟨1404377, by rfl⟩ : syracuseStep 1872503 = 2808755) B2808755
theorem B1053319 : Blo 830350 1053319 := bstep (se 1 (by rfl) ⟨789989, by rfl⟩ : syracuseStep 1053319 = 1579979) B1579979
theorem B1249979 : Blo 830350 1249979 := bstep (se 1 (by rfl) ⟨937484, by rfl⟩ : syracuseStep 1249979 = 1874969) B1874969
theorem B1250039 : Blo 830350 1250039 := bstep (se 1 (by rfl) ⟨937529, by rfl⟩ : syracuseStep 1250039 = 1875059) B1875059
theorem B1250063 : Blo 830350 1250063 := bstep (se 1 (by rfl) ⟨937547, by rfl⟩ : syracuseStep 1250063 = 1875095) B1875095
theorem B1872683 : Blo 830350 1872683 := bstep (se 1 (by rfl) ⟨1404512, by rfl⟩ : syracuseStep 1872683 = 2809025) B2809025
theorem B1250105 : Blo 830350 1250105 := bstep (se 2 (by rfl) ⟨468789, by rfl⟩ : syracuseStep 1250105 = 937579) B937579
theorem B6329177 : Blo 830350 6329177 := bstep (se 2 (by rfl) ⟨2373441, by rfl⟩ : syracuseStep 6329177 = 4746883) B4746883
theorem B6001523 : Blo 830350 6001523 := bstep (se 1 (by rfl) ⟨4501142, by rfl⟩ : syracuseStep 6001523 = 9002285) B9002285
theorem B1250183 : Blo 830350 1250183 := bstep (se 1 (by rfl) ⟨937637, by rfl⟩ : syracuseStep 1250183 = 1875275) B1875275
theorem B1577875 : Blo 830350 1577875 := bstep (se 1 (by rfl) ⟨1183406, by rfl⟩ : syracuseStep 1577875 = 2366813) B2366813
theorem B1250219 : Blo 830350 1250219 := bstep (se 1 (by rfl) ⟨937664, by rfl⟩ : syracuseStep 1250219 = 1875329) B1875329
theorem B1250249 : Blo 830350 1250249 := bstep (se 2 (by rfl) ⟨468843, by rfl⟩ : syracuseStep 1250249 = 937687) B937687
theorem B1053739 : Blo 830350 1053739 := bstep (se 1 (by rfl) ⟨790304, by rfl⟩ : syracuseStep 1053739 = 1580609) B1580609
theorem B1250363 : Blo 830350 1250363 := bstep (se 1 (by rfl) ⟨937772, by rfl⟩ : syracuseStep 1250363 = 1875545) B1875545
theorem B1250423 : Blo 830350 1250423 := bstep (se 1 (by rfl) ⟨937817, by rfl⟩ : syracuseStep 1250423 = 1875635) B1875635
theorem B1250447 : Blo 830350 1250447 := bstep (se 1 (by rfl) ⟨937835, by rfl⟩ : syracuseStep 1250447 = 1875671) B1875671
theorem B1873043 : Blo 830350 1873043 := bstep (se 1 (by rfl) ⟨1404782, by rfl⟩ : syracuseStep 1873043 = 2809565) B2809565
theorem B1250489 : Blo 830350 1250489 := bstep (se 2 (by rfl) ⟨468933, by rfl⟩ : syracuseStep 1250489 = 937867) B937867
theorem B1873097 : Blo 830350 1873097 := bstep (se 2 (by rfl) ⟨702411, by rfl⟩ : syracuseStep 1873097 = 1404823) B1404823
theorem B4560101 : Blo 830350 4560101 := bstep (se 4 (by rfl) ⟨427509, by rfl⟩ : syracuseStep 4560101 = 855019) B855019
theorem B1250567 : Blo 830350 1250567 := bstep (se 1 (by rfl) ⟨937925, by rfl⟩ : syracuseStep 1250567 = 1875851) B1875851
theorem B1053967 : Blo 830350 1053967 := bstep (se 1 (by rfl) ⟨790475, by rfl⟩ : syracuseStep 1053967 = 1580951) B1580951
theorem B1250603 : Blo 830350 1250603 := bstep (se 1 (by rfl) ⟨937952, by rfl⟩ : syracuseStep 1250603 = 1875905) B1875905
theorem B2004283 : Blo 830350 2004283 := bstep (se 1 (by rfl) ⟨1503212, by rfl⟩ : syracuseStep 2004283 = 3006425) B3006425
theorem B1250633 : Blo 830350 1250633 := bstep (se 2 (by rfl) ⟨468987, by rfl⟩ : syracuseStep 1250633 = 937975) B937975
theorem B1250747 : Blo 830350 1250747 := bstep (se 1 (by rfl) ⟨938060, by rfl⟩ : syracuseStep 1250747 = 1876121) B1876121
theorem B1250807 : Blo 830350 1250807 := bstep (se 1 (by rfl) ⟨938105, by rfl⟩ : syracuseStep 1250807 = 1876211) B1876211
theorem B1250831 : Blo 830350 1250831 := bstep (se 1 (by rfl) ⟨938123, by rfl⟩ : syracuseStep 1250831 = 1876247) B1876247
theorem B1250873 : Blo 830350 1250873 := bstep (se 2 (by rfl) ⟨469077, by rfl⟩ : syracuseStep 1250873 = 938155) B938155
theorem B1250951 : Blo 830350 1250951 := bstep (se 1 (by rfl) ⟨938213, by rfl⟩ : syracuseStep 1250951 = 1876427) B1876427
theorem B1250987 : Blo 830350 1250987 := bstep (se 1 (by rfl) ⟨938240, by rfl⟩ : syracuseStep 1250987 = 1876481) B1876481
theorem B1251017 : Blo 830350 1251017 := bstep (se 2 (by rfl) ⟨469131, by rfl⟩ : syracuseStep 1251017 = 938263) B938263
theorem B2365195 : Blo 830350 2365195 := bstep (se 1 (by rfl) ⟨1773896, by rfl⟩ : syracuseStep 2365195 = 3547793) B3547793
theorem B6330149 : Blo 830350 6330149 := bstep (se 4 (by rfl) ⟨593451, by rfl⟩ : syracuseStep 6330149 = 1186903) B1186903
theorem B2529083 : Blo 830350 2529083 := bstep (se 1 (by rfl) ⟨1896812, by rfl⟩ : syracuseStep 2529083 = 3793625) B3793625
theorem B1251131 : Blo 830350 1251131 := bstep (se 1 (by rfl) ⟨938348, by rfl⟩ : syracuseStep 1251131 = 1876697) B1876697
theorem B2103155 : Blo 830350 2103155 := bstep (se 1 (by rfl) ⟨1577366, by rfl⟩ : syracuseStep 2103155 = 3154733) B3154733
theorem B1251191 : Blo 830350 1251191 := bstep (se 1 (by rfl) ⟨938393, by rfl⟩ : syracuseStep 1251191 = 1876787) B1876787
theorem B1775495 : Blo 830350 1775495 := bstep (se 1 (by rfl) ⟨1331621, by rfl⟩ : syracuseStep 1775495 = 2663243) B2663243
theorem B1873799 : Blo 830350 1873799 := bstep (se 1 (by rfl) ⟨1405349, by rfl⟩ : syracuseStep 1873799 = 2810699) B2810699
theorem B1251215 : Blo 830350 1251215 := bstep (se 1 (by rfl) ⟨938411, by rfl⟩ : syracuseStep 1251215 = 1876823) B1876823
theorem B890767 : Blo 830350 890767 := bstep (se 1 (by rfl) ⟨668075, by rfl⟩ : syracuseStep 890767 = 1336151) B1336151
theorem B1251257 : Blo 830350 1251257 := bstep (se 2 (by rfl) ⟨469221, by rfl⟩ : syracuseStep 1251257 = 938443) B938443
theorem B1578953 : Blo 830350 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B1054711 : Blo 830350 1054711 := bstep (se 1 (by rfl) ⟨791033, by rfl⟩ : syracuseStep 1054711 = 1582067) B1582067
theorem B1251335 : Blo 830350 1251335 := bstep (se 1 (by rfl) ⟨938501, by rfl⟩ : syracuseStep 1251335 = 1877003) B1877003
theorem B2365469 : Blo 830350 2365469 := bstep (se 3 (by rfl) ⟨443525, by rfl⟩ : syracuseStep 2365469 = 887051) B887051
theorem B1251371 : Blo 830350 1251371 := bstep (se 1 (by rfl) ⟨938528, by rfl⟩ : syracuseStep 1251371 = 1877057) B1877057
theorem B1873979 : Blo 830350 1873979 := bstep (se 1 (by rfl) ⟨1405484, by rfl⟩ : syracuseStep 1873979 = 2810969) B2810969
theorem B1251401 : Blo 830350 1251401 := bstep (se 2 (by rfl) ⟨469275, by rfl⟩ : syracuseStep 1251401 = 938551) B938551
theorem B1874105 : Blo 830350 1874105 := bstep (se 2 (by rfl) ⟨702789, by rfl⟩ : syracuseStep 1874105 = 1405579) B1405579
theorem B1251515 : Blo 830350 1251515 := bstep (se 1 (by rfl) ⟨938636, by rfl⟩ : syracuseStep 1251515 = 1877273) B1877273
theorem B4004147 : Blo 830350 4004147 := bstep (se 1 (by rfl) ⟨3003110, by rfl⟩ : syracuseStep 4004147 = 6006221) B6006221
theorem B1055035 : Blo 830350 1055035 := bstep (se 1 (by rfl) ⟨791276, by rfl⟩ : syracuseStep 1055035 = 1582553) B1582553
theorem B2365811 : Blo 830350 2365811 := bstep (se 1 (by rfl) ⟨1774358, by rfl⟩ : syracuseStep 2365811 = 3548717) B3548717
theorem B2103671 : Blo 830350 2103671 := bstep (se 1 (by rfl) ⟨1577753, by rfl⟩ : syracuseStep 2103671 = 3155507) B3155507
theorem B1874447 : Blo 830350 1874447 := bstep (se 1 (by rfl) ⟨1405835, by rfl⟩ : syracuseStep 1874447 = 2811671) B2811671
theorem B1874465 : Blo 830350 1874465 := bstep (se 2 (by rfl) ⟨702924, by rfl⟩ : syracuseStep 1874465 = 1405849) B1405849
theorem B1579819 : Blo 830350 1579819 := bstep (se 1 (by rfl) ⟨1184864, by rfl⟩ : syracuseStep 1579819 = 2369729) B2369729
theorem B1055531 : Blo 830350 1055531 := bstep (se 1 (by rfl) ⟨791648, by rfl⟩ : syracuseStep 1055531 = 1583297) B1583297
theorem B1579895 : Blo 830350 1579895 := bstep (se 1 (by rfl) ⟨1184921, by rfl⟩ : syracuseStep 1579895 = 2369843) B2369843
theorem B1874807 : Blo 830350 1874807 := bstep (se 1 (by rfl) ⟨1406105, by rfl⟩ : syracuseStep 1874807 = 2812211) B2812211
theorem B1186807 : Blo 830350 1186807 := bstep (se 1 (by rfl) ⟨890105, by rfl⟩ : syracuseStep 1186807 = 1780211) B1780211
theorem B1874987 : Blo 830350 1874987 := bstep (se 1 (by rfl) ⟨1406240, by rfl⟩ : syracuseStep 1874987 = 2812481) B2812481
theorem B2137241 : Blo 830350 2137241 := bstep (se 2 (by rfl) ⟨801465, by rfl⟩ : syracuseStep 2137241 = 1602931) B1602931
theorem B2366779 : Blo 830350 2366779 := bstep (se 1 (by rfl) ⟨1775084, by rfl⟩ : syracuseStep 2366779 = 3550169) B3550169
theorem B1187131 : Blo 830350 1187131 := bstep (se 1 (by rfl) ⟨890348, by rfl⟩ : syracuseStep 1187131 = 1780697) B1780697
theorem B2104663 : Blo 830350 2104663 := bstep (se 1 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 2104663 = 3156995) B3156995
theorem B1875347 : Blo 830350 1875347 := bstep (se 1 (by rfl) ⟨1406510, by rfl⟩ : syracuseStep 1875347 = 2813021) B2813021
theorem B1875401 : Blo 830350 1875401 := bstep (se 2 (by rfl) ⟨703275, by rfl⟩ : syracuseStep 1875401 = 1406551) B1406551
theorem B2104967 : Blo 830350 2104967 := bstep (se 1 (by rfl) ⟨1578725, by rfl⟩ : syracuseStep 2104967 = 3157451) B3157451
theorem B7577317 : Blo 830350 7577317 := bstep (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) B1420747
theorem B2105099 : Blo 830350 2105099 := bstep (se 1 (by rfl) ⟨1578824, by rfl⟩ : syracuseStep 2105099 = 3157649) B3157649
theorem B1876103 : Blo 830350 1876103 := bstep (se 1 (by rfl) ⟨1407077, by rfl⟩ : syracuseStep 1876103 = 2814155) B2814155
theorem B2105615 : Blo 830350 2105615 := bstep (se 1 (by rfl) ⟨1579211, by rfl⟩ : syracuseStep 2105615 = 3158423) B3158423
theorem B8003873 : Blo 830350 8003873 := bstep (se 2 (by rfl) ⟨3001452, by rfl⟩ : syracuseStep 8003873 = 6002905) B6002905
theorem B1777963 : Blo 830350 1777963 := bstep (se 1 (by rfl) ⟨1333472, by rfl⟩ : syracuseStep 1777963 = 2666945) B2666945
theorem B3547451 : Blo 830350 3547451 := bstep (se 1 (by rfl) ⟨2660588, by rfl⟩ : syracuseStep 3547451 = 5321177) B5321177
theorem B1876283 : Blo 830350 1876283 := bstep (se 1 (by rfl) ⟨1407212, by rfl⟩ : syracuseStep 1876283 = 2814425) B2814425
theorem B10658141 : Blo 830350 10658141 := bstep (se 3 (by rfl) ⟨1998401, by rfl⟩ : syracuseStep 10658141 = 3996803) B3996803
theorem B2531699 : Blo 830350 2531699 := bstep (se 1 (by rfl) ⟨1898774, by rfl⟩ : syracuseStep 2531699 = 3797549) B3797549
theorem B2105747 : Blo 830350 2105747 := bstep (se 1 (by rfl) ⟨1579310, by rfl⟩ : syracuseStep 2105747 = 3158621) B3158621
theorem B2367929 : Blo 830350 2367929 := bstep (se 2 (by rfl) ⟨887973, by rfl⟩ : syracuseStep 2367929 = 1775947) B1775947
theorem B1876409 : Blo 830350 1876409 := bstep (se 2 (by rfl) ⟨703653, by rfl⟩ : syracuseStep 1876409 = 1407307) B1407307
theorem B3547709 : Blo 830350 3547709 := bstep (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) B1330391
theorem B5055149 : Blo 830350 5055149 := bstep (se 3 (by rfl) ⟨947840, by rfl⟩ : syracuseStep 5055149 = 1895681) B1895681
theorem B2368271 : Blo 830350 2368271 := bstep (se 1 (by rfl) ⟨1776203, by rfl⟩ : syracuseStep 2368271 = 3552407) B3552407
theorem B1581839 : Blo 830350 1581839 := bstep (se 1 (by rfl) ⟨1186379, by rfl⟩ : syracuseStep 1581839 = 2372759) B2372759
theorem B1876751 : Blo 830350 1876751 := bstep (se 1 (by rfl) ⟨1407563, by rfl⟩ : syracuseStep 1876751 = 2815127) B2815127
theorem B1876769 : Blo 830350 1876769 := bstep (se 2 (by rfl) ⟨703788, by rfl⟩ : syracuseStep 1876769 = 1407577) B1407577
theorem B3154747 : Blo 830350 3154747 := bstep (se 1 (by rfl) ⟨2366060, by rfl⟩ : syracuseStep 3154747 = 4732121) B4732121
theorem B7611479 : Blo 830350 7611479 := bstep (se 1 (by rfl) ⟨5708609, by rfl⟩ : syracuseStep 7611479 = 11417219) B11417219
theorem B1877111 : Blo 830350 1877111 := bstep (se 1 (by rfl) ⟨1407833, by rfl⟩ : syracuseStep 1877111 = 2815667) B2815667
theorem B3155233 : Blo 830350 3155233 := bstep (se 2 (by rfl) ⟨1183212, by rfl⟩ : syracuseStep 3155233 = 2366425) B2366425
theorem B2106881 : Blo 830350 2106881 := bstep (se 2 (by rfl) ⟨790080, by rfl⟩ : syracuseStep 2106881 = 1580161) B1580161
theorem B4204061 : Blo 830350 4204061 := bstep (se 3 (by rfl) ⟨788261, by rfl⟩ : syracuseStep 4204061 = 1576523) B1576523
theorem B2369159 : Blo 830350 2369159 := bstep (se 1 (by rfl) ⟨1776869, by rfl⟩ : syracuseStep 2369159 = 3553739) B3553739
theorem B1779347 : Blo 830350 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B2369341 : Blo 830350 2369341 := bstep (se 3 (by rfl) ⟨444251, by rfl⟩ : syracuseStep 2369341 = 888503) B888503
theorem B2107255 : Blo 830350 2107255 := bstep (se 1 (by rfl) ⟨1580441, by rfl⟩ : syracuseStep 2107255 = 3160883) B3160883
theorem B5056465 : Blo 830350 5056465 := bstep (se 2 (by rfl) ⟨1896174, by rfl⟩ : syracuseStep 5056465 = 3792349) B3792349
theorem B4204547 : Blo 830350 4204547 := bstep (se 1 (by rfl) ⟨3153410, by rfl⟩ : syracuseStep 4204547 = 6306821) B6306821
theorem B2402315 : Blo 830350 2402315 := bstep (se 1 (by rfl) ⟨1801736, by rfl⟩ : syracuseStep 2402315 = 3603473) B3603473
theorem B2369569 : Blo 830350 2369569 := bstep (se 2 (by rfl) ⟨888588, by rfl⟩ : syracuseStep 2369569 = 1777177) B1777177
theorem B3156205 : Blo 830350 3156205 := bstep (se 3 (by rfl) ⟨591788, by rfl⟩ : syracuseStep 3156205 = 1183577) B1183577
theorem B2107691 : Blo 830350 2107691 := bstep (se 1 (by rfl) ⟨1580768, by rfl⟩ : syracuseStep 2107691 = 3161537) B3161537
theorem B2369911 : Blo 830350 2369911 := bstep (se 1 (by rfl) ⟨1777433, by rfl⟩ : syracuseStep 2369911 = 3554867) B3554867
theorem B1583479 : Blo 830350 1583479 := bstep (se 1 (by rfl) ⟨1187609, by rfl⟩ : syracuseStep 1583479 = 2375219) B2375219
theorem B3549707 : Blo 830350 3549707 := bstep (se 1 (by rfl) ⟨2662280, by rfl⟩ : syracuseStep 3549707 = 5324561) B5324561
theorem B3156509 : Blo 830350 3156509 := bstep (se 3 (by rfl) ⟨591845, by rfl⟩ : syracuseStep 3156509 = 1183691) B1183691
theorem B4729387 : Blo 830350 4729387 := bstep (se 1 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 4729387 = 7094081) B7094081
theorem B4008491 : Blo 830350 4008491 := bstep (se 1 (by rfl) ⟨3006368, by rfl⟩ : syracuseStep 4008491 = 6012737) B6012737
theorem B2665331 : Blo 830350 2665331 := bstep (se 1 (by rfl) ⟨1998998, by rfl⟩ : syracuseStep 2665331 = 3997997) B3997997
theorem B830351 : Blo 830350 830351 := bstep (se 1 (by rfl) ⟨622763, by rfl⟩ : syracuseStep 830351 = 1245527) B1245527
theorem B830395 : Blo 830350 830395 := bstep (se 1 (by rfl) ⟨622796, by rfl⟩ : syracuseStep 830395 = 1245593) B1245593
theorem B830471 : Blo 830350 830471 := bstep (se 1 (by rfl) ⟨622853, by rfl⟩ : syracuseStep 830471 = 1245707) B1245707
theorem B830479 : Blo 830350 830479 := bstep (se 1 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 830479 = 1245719) B1245719
theorem B830523 : Blo 830350 830523 := bstep (se 1 (by rfl) ⟨622892, by rfl⟩ : syracuseStep 830523 = 1245785) B1245785
theorem B2108531 : Blo 830350 2108531 := bstep (se 1 (by rfl) ⟨1581398, by rfl⟩ : syracuseStep 2108531 = 3162797) B3162797
theorem B830599 : Blo 830350 830599 := bstep (se 1 (by rfl) ⟨622949, by rfl⟩ : syracuseStep 830599 = 1245899) B1245899
theorem B2108551 : Blo 830350 2108551 := bstep (se 1 (by rfl) ⟨1581413, by rfl⟩ : syracuseStep 2108551 = 3162827) B3162827
theorem B64990349 : Blo 830350 64990349 := bstep (se 3 (by rfl) ⟨12185690, by rfl⟩ : syracuseStep 64990349 = 24371381) B24371381
theorem B830607 : Blo 830350 830607 := bstep (se 1 (by rfl) ⟨622955, by rfl⟩ : syracuseStep 830607 = 1245911) B1245911
theorem B830651 : Blo 830350 830651 := bstep (se 1 (by rfl) ⟨622988, by rfl⟩ : syracuseStep 830651 = 1245977) B1245977
theorem B830727 : Blo 830350 830727 := bstep (se 1 (by rfl) ⟨623045, by rfl⟩ : syracuseStep 830727 = 1246091) B1246091
theorem B830735 : Blo 830350 830735 := bstep (se 1 (by rfl) ⟨623051, by rfl⟩ : syracuseStep 830735 = 1246103) B1246103
theorem B2370845 : Blo 830350 2370845 := bstep (se 3 (by rfl) ⟨444533, by rfl⟩ : syracuseStep 2370845 = 889067) B889067
theorem B830779 : Blo 830350 830779 := bstep (se 1 (by rfl) ⟨623084, by rfl⟩ : syracuseStep 830779 = 1246169) B1246169
theorem B830855 : Blo 830350 830855 := bstep (se 1 (by rfl) ⟨623141, by rfl⟩ : syracuseStep 830855 = 1246283) B1246283
theorem B830863 : Blo 830350 830863 := bstep (se 1 (by rfl) ⟨623147, by rfl⟩ : syracuseStep 830863 = 1246295) B1246295
theorem B2108825 : Blo 830350 2108825 := bstep (se 2 (by rfl) ⟨790809, by rfl⟩ : syracuseStep 2108825 = 1581619) B1581619
theorem B830907 : Blo 830350 830907 := bstep (se 1 (by rfl) ⟨623180, by rfl⟩ : syracuseStep 830907 = 1246361) B1246361
theorem B830983 : Blo 830350 830983 := bstep (se 1 (by rfl) ⟨623237, by rfl⟩ : syracuseStep 830983 = 1246475) B1246475
theorem B830991 : Blo 830350 830991 := bstep (se 1 (by rfl) ⟨623243, by rfl⟩ : syracuseStep 830991 = 1246487) B1246487
theorem B831035 : Blo 830350 831035 := bstep (se 1 (by rfl) ⟨623276, by rfl⟩ : syracuseStep 831035 = 1246553) B1246553
theorem B2108987 : Blo 830350 2108987 := bstep (se 1 (by rfl) ⟨1581740, by rfl⟩ : syracuseStep 2108987 = 3163481) B3163481
theorem B4206167 : Blo 830350 4206167 := bstep (se 1 (by rfl) ⟨3154625, by rfl⟩ : syracuseStep 4206167 = 6309251) B6309251
theorem B2371187 : Blo 830350 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B831111 : Blo 830350 831111 := bstep (se 1 (by rfl) ⟨623333, by rfl⟩ : syracuseStep 831111 = 1246667) B1246667
theorem B831119 : Blo 830350 831119 := bstep (se 1 (by rfl) ⟨623339, by rfl⟩ : syracuseStep 831119 = 1246679) B1246679
theorem B831163 : Blo 830350 831163 := bstep (se 1 (by rfl) ⟨623372, by rfl⟩ : syracuseStep 831163 = 1246745) B1246745
theorem B831239 : Blo 830350 831239 := bstep (se 1 (by rfl) ⟨623429, by rfl⟩ : syracuseStep 831239 = 1246859) B1246859
theorem B831247 : Blo 830350 831247 := bstep (se 1 (by rfl) ⟨623435, by rfl⟩ : syracuseStep 831247 = 1246871) B1246871
theorem B2109199 : Blo 830350 2109199 := bstep (se 1 (by rfl) ⟨1581899, by rfl⟩ : syracuseStep 2109199 = 3163799) B3163799
theorem B831291 : Blo 830350 831291 := bstep (se 1 (by rfl) ⟨623468, by rfl⟩ : syracuseStep 831291 = 1246937) B1246937
theorem B831367 : Blo 830350 831367 := bstep (se 1 (by rfl) ⟨623525, by rfl⟩ : syracuseStep 831367 = 1247051) B1247051
theorem B831375 : Blo 830350 831375 := bstep (se 1 (by rfl) ⟨623531, by rfl⟩ : syracuseStep 831375 = 1247063) B1247063
theorem B831419 : Blo 830350 831419 := bstep (se 1 (by rfl) ⟨623564, by rfl⟩ : syracuseStep 831419 = 1247129) B1247129
theorem B4730845 : Blo 830350 4730845 := bstep (se 3 (by rfl) ⟨887033, by rfl⟩ : syracuseStep 4730845 = 1774067) B1774067
theorem B4501507 : Blo 830350 4501507 := bstep (se 1 (by rfl) ⟨3376130, by rfl⟩ : syracuseStep 4501507 = 6752261) B6752261
theorem B831495 : Blo 830350 831495 := bstep (se 1 (by rfl) ⟨623621, by rfl⟩ : syracuseStep 831495 = 1247243) B1247243
theorem B831503 : Blo 830350 831503 := bstep (se 1 (by rfl) ⟨623627, by rfl⟩ : syracuseStep 831503 = 1247255) B1247255
theorem B2109473 : Blo 830350 2109473 := bstep (se 2 (by rfl) ⟨791052, by rfl⟩ : syracuseStep 2109473 = 1582105) B1582105
theorem B831547 : Blo 830350 831547 := bstep (se 1 (by rfl) ⟨623660, by rfl⟩ : syracuseStep 831547 = 1247321) B1247321
theorem B2371643 : Blo 830350 2371643 := bstep (se 1 (by rfl) ⟨1778732, by rfl⟩ : syracuseStep 2371643 = 3557465) B3557465
theorem B4206653 : Blo 830350 4206653 := bstep (se 3 (by rfl) ⟨788747, by rfl⟩ : syracuseStep 4206653 = 1577495) B1577495
theorem B3158135 : Blo 830350 3158135 := bstep (se 1 (by rfl) ⟨2368601, by rfl⟩ : syracuseStep 3158135 = 4737203) B4737203
theorem B831623 : Blo 830350 831623 := bstep (se 1 (by rfl) ⟨623717, by rfl⟩ : syracuseStep 831623 = 1247435) B1247435
theorem B831631 : Blo 830350 831631 := bstep (se 1 (by rfl) ⟨623723, by rfl⟩ : syracuseStep 831631 = 1247447) B1247447
theorem B831675 : Blo 830350 831675 := bstep (se 1 (by rfl) ⟨623756, by rfl⟩ : syracuseStep 831675 = 1247513) B1247513
theorem B831751 : Blo 830350 831751 := bstep (se 1 (by rfl) ⟨623813, by rfl⟩ : syracuseStep 831751 = 1247627) B1247627
theorem B831759 : Blo 830350 831759 := bstep (se 1 (by rfl) ⟨623819, by rfl⟩ : syracuseStep 831759 = 1247639) B1247639
theorem B831803 : Blo 830350 831803 := bstep (se 1 (by rfl) ⟨623852, by rfl⟩ : syracuseStep 831803 = 1247705) B1247705
theorem B831879 : Blo 830350 831879 := bstep (se 1 (by rfl) ⟨623909, by rfl⟩ : syracuseStep 831879 = 1247819) B1247819
theorem B831887 : Blo 830350 831887 := bstep (se 1 (by rfl) ⟨623915, by rfl⟩ : syracuseStep 831887 = 1247831) B1247831
theorem B6762899 : Blo 830350 6762899 := bstep (se 1 (by rfl) ⟨5072174, by rfl⟩ : syracuseStep 6762899 = 10144349) B10144349
theorem B831931 : Blo 830350 831931 := bstep (se 1 (by rfl) ⟨623948, by rfl⟩ : syracuseStep 831931 = 1247897) B1247897
theorem B832007 : Blo 830350 832007 := bstep (se 1 (by rfl) ⟨624005, by rfl⟩ : syracuseStep 832007 = 1248011) B1248011
theorem B832015 : Blo 830350 832015 := bstep (se 1 (by rfl) ⟨624011, by rfl⟩ : syracuseStep 832015 = 1248023) B1248023
theorem B832059 : Blo 830350 832059 := bstep (se 1 (by rfl) ⟨624044, by rfl⟩ : syracuseStep 832059 = 1248089) B1248089
theorem B832135 : Blo 830350 832135 := bstep (se 1 (by rfl) ⟨624101, by rfl⟩ : syracuseStep 832135 = 1248203) B1248203
theorem B832143 : Blo 830350 832143 := bstep (se 1 (by rfl) ⟨624107, by rfl⟩ : syracuseStep 832143 = 1248215) B1248215
theorem B832187 : Blo 830350 832187 := bstep (se 1 (by rfl) ⟨624140, by rfl⟩ : syracuseStep 832187 = 1248281) B1248281
theorem B8991425 : Blo 830350 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B832263 : Blo 830350 832263 := bstep (se 1 (by rfl) ⟨624197, by rfl⟩ : syracuseStep 832263 = 1248395) B1248395
theorem B832271 : Blo 830350 832271 := bstep (se 1 (by rfl) ⟨624203, by rfl⟩ : syracuseStep 832271 = 1248407) B1248407
theorem B2536235 : Blo 830350 2536235 := bstep (se 1 (by rfl) ⟨1902176, by rfl⟩ : syracuseStep 2536235 = 3804353) B3804353
theorem B832315 : Blo 830350 832315 := bstep (se 1 (by rfl) ⟨624236, by rfl⟩ : syracuseStep 832315 = 1248473) B1248473
theorem B832391 : Blo 830350 832391 := bstep (se 1 (by rfl) ⟨624293, by rfl⟩ : syracuseStep 832391 = 1248587) B1248587
theorem B832399 : Blo 830350 832399 := bstep (se 1 (by rfl) ⟨624299, by rfl⟩ : syracuseStep 832399 = 1248599) B1248599
theorem B832443 : Blo 830350 832443 := bstep (se 1 (by rfl) ⟨624332, by rfl⟩ : syracuseStep 832443 = 1248665) B1248665
theorem B832519 : Blo 830350 832519 := bstep (se 1 (by rfl) ⟨624389, by rfl⟩ : syracuseStep 832519 = 1248779) B1248779
theorem B2110475 : Blo 830350 2110475 := bstep (se 1 (by rfl) ⟨1582856, by rfl⟩ : syracuseStep 2110475 = 3165713) B3165713
theorem B832527 : Blo 830350 832527 := bstep (se 1 (by rfl) ⟨624395, by rfl⟩ : syracuseStep 832527 = 1248791) B1248791
theorem B832571 : Blo 830350 832571 := bstep (se 1 (by rfl) ⟨624428, by rfl⟩ : syracuseStep 832571 = 1248857) B1248857
theorem B3159107 : Blo 830350 3159107 := bstep (se 1 (by rfl) ⟨2369330, by rfl⟩ : syracuseStep 3159107 = 4738661) B4738661
theorem B832647 : Blo 830350 832647 := bstep (se 1 (by rfl) ⟨624485, by rfl⟩ : syracuseStep 832647 = 1248971) B1248971
theorem B832655 : Blo 830350 832655 := bstep (se 1 (by rfl) ⟨624491, by rfl⟩ : syracuseStep 832655 = 1248983) B1248983
theorem B832699 : Blo 830350 832699 := bstep (se 1 (by rfl) ⟨624524, by rfl⟩ : syracuseStep 832699 = 1249049) B1249049
theorem B832775 : Blo 830350 832775 := bstep (se 1 (by rfl) ⟨624581, by rfl⟩ : syracuseStep 832775 = 1249163) B1249163
theorem B2667791 : Blo 830350 2667791 := bstep (se 1 (by rfl) ⟨2000843, by rfl⟩ : syracuseStep 2667791 = 4001687) B4001687
theorem B832783 : Blo 830350 832783 := bstep (se 1 (by rfl) ⟨624587, by rfl⟩ : syracuseStep 832783 = 1249175) B1249175
theorem B832827 : Blo 830350 832827 := bstep (se 1 (by rfl) ⟨624620, by rfl⟩ : syracuseStep 832827 = 1249241) B1249241
theorem B832903 : Blo 830350 832903 := bstep (se 1 (by rfl) ⟨624677, by rfl⟩ : syracuseStep 832903 = 1249355) B1249355
theorem B832911 : Blo 830350 832911 := bstep (se 1 (by rfl) ⟨624683, by rfl⟩ : syracuseStep 832911 = 1249367) B1249367
theorem B832955 : Blo 830350 832955 := bstep (se 1 (by rfl) ⟨624716, by rfl⟩ : syracuseStep 832955 = 1249433) B1249433
theorem B833031 : Blo 830350 833031 := bstep (se 1 (by rfl) ⟨624773, by rfl⟩ : syracuseStep 833031 = 1249547) B1249547
theorem B833039 : Blo 830350 833039 := bstep (se 1 (by rfl) ⟨624779, by rfl⟩ : syracuseStep 833039 = 1249559) B1249559
theorem B8238635 : Blo 830350 8238635 := bstep (se 1 (by rfl) ⟨6178976, by rfl⟩ : syracuseStep 8238635 = 12357953) B12357953
theorem B833083 : Blo 830350 833083 := bstep (se 1 (by rfl) ⟨624812, by rfl⟩ : syracuseStep 833083 = 1249625) B1249625
theorem B833159 : Blo 830350 833159 := bstep (se 1 (by rfl) ⟨624869, by rfl⟩ : syracuseStep 833159 = 1249739) B1249739
theorem B833167 : Blo 830350 833167 := bstep (se 1 (by rfl) ⟨624875, by rfl⟩ : syracuseStep 833167 = 1249751) B1249751
theorem B2111123 : Blo 830350 2111123 := bstep (se 1 (by rfl) ⟨1583342, by rfl⟩ : syracuseStep 2111123 = 3166685) B3166685
theorem B833211 : Blo 830350 833211 := bstep (se 1 (by rfl) ⟨624908, by rfl⟩ : syracuseStep 833211 = 1249817) B1249817
theorem B833287 : Blo 830350 833287 := bstep (se 1 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 833287 = 1249931) B1249931
theorem B833295 : Blo 830350 833295 := bstep (se 1 (by rfl) ⟨624971, by rfl⟩ : syracuseStep 833295 = 1249943) B1249943
theorem B4208435 : Blo 830350 4208435 := bstep (se 1 (by rfl) ⟨3156326, by rfl⟩ : syracuseStep 4208435 = 6312653) B6312653
theorem B833339 : Blo 830350 833339 := bstep (se 1 (by rfl) ⟨625004, by rfl⟩ : syracuseStep 833339 = 1250009) B1250009
theorem B5322611 : Blo 830350 5322611 := bstep (se 1 (by rfl) ⟨3991958, by rfl⟩ : syracuseStep 5322611 = 7983917) B7983917
theorem B833415 : Blo 830350 833415 := bstep (se 1 (by rfl) ⟨625061, by rfl⟩ : syracuseStep 833415 = 1250123) B1250123
theorem B833423 : Blo 830350 833423 := bstep (se 1 (by rfl) ⟨625067, by rfl⟩ : syracuseStep 833423 = 1250135) B1250135
theorem B2111417 : Blo 830350 2111417 := bstep (se 2 (by rfl) ⟨791781, by rfl⟩ : syracuseStep 2111417 = 1583563) B1583563
theorem B833467 : Blo 830350 833467 := bstep (se 1 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 833467 = 1250201) B1250201
theorem B833543 : Blo 830350 833543 := bstep (se 1 (by rfl) ⟨625157, by rfl⟩ : syracuseStep 833543 = 1250315) B1250315
theorem B833551 : Blo 830350 833551 := bstep (se 1 (by rfl) ⟨625163, by rfl⟩ : syracuseStep 833551 = 1250327) B1250327
theorem B3160093 : Blo 830350 3160093 := bstep (se 3 (by rfl) ⟨592517, by rfl⟩ : syracuseStep 3160093 = 1185035) B1185035
theorem B833595 : Blo 830350 833595 := bstep (se 1 (by rfl) ⟨625196, by rfl⟩ : syracuseStep 833595 = 1250393) B1250393
theorem B2275415 : Blo 830350 2275415 := bstep (se 1 (by rfl) ⟨1706561, by rfl⟩ : syracuseStep 2275415 = 3413123) B3413123
theorem B4208759 : Blo 830350 4208759 := bstep (se 1 (by rfl) ⟨3156569, by rfl⟩ : syracuseStep 4208759 = 6313139) B6313139
theorem B4503671 : Blo 830350 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B833671 : Blo 830350 833671 := bstep (se 1 (by rfl) ⟨625253, by rfl⟩ : syracuseStep 833671 = 1250507) B1250507
theorem B833679 : Blo 830350 833679 := bstep (se 1 (by rfl) ⟨625259, by rfl⟩ : syracuseStep 833679 = 1250519) B1250519
theorem B833723 : Blo 830350 833723 := bstep (se 1 (by rfl) ⟨625292, by rfl⟩ : syracuseStep 833723 = 1250585) B1250585
theorem B833799 : Blo 830350 833799 := bstep (se 1 (by rfl) ⟨625349, by rfl⟩ : syracuseStep 833799 = 1250699) B1250699
theorem B833807 : Blo 830350 833807 := bstep (se 1 (by rfl) ⟨625355, by rfl⟩ : syracuseStep 833807 = 1250711) B1250711
theorem B833851 : Blo 830350 833851 := bstep (se 1 (by rfl) ⟨625388, by rfl⟩ : syracuseStep 833851 = 1250777) B1250777
theorem B833927 : Blo 830350 833927 := bstep (se 1 (by rfl) ⟨625445, by rfl⟩ : syracuseStep 833927 = 1250891) B1250891
theorem B833935 : Blo 830350 833935 := bstep (se 1 (by rfl) ⟨625451, by rfl⟩ : syracuseStep 833935 = 1250903) B1250903
theorem B833979 : Blo 830350 833979 := bstep (se 1 (by rfl) ⟨625484, by rfl⟩ : syracuseStep 833979 = 1250969) B1250969
theorem B834055 : Blo 830350 834055 := bstep (se 1 (by rfl) ⟨625541, by rfl⟩ : syracuseStep 834055 = 1251083) B1251083
theorem B834063 : Blo 830350 834063 := bstep (se 1 (by rfl) ⟨625547, by rfl⟩ : syracuseStep 834063 = 1251095) B1251095
theorem B834107 : Blo 830350 834107 := bstep (se 1 (by rfl) ⟨625580, by rfl⟩ : syracuseStep 834107 = 1251161) B1251161
theorem B834183 : Blo 830350 834183 := bstep (se 1 (by rfl) ⟨625637, by rfl⟩ : syracuseStep 834183 = 1251275) B1251275
theorem B834191 : Blo 830350 834191 := bstep (se 1 (by rfl) ⟨625643, by rfl⟩ : syracuseStep 834191 = 1251287) B1251287
theorem B834235 : Blo 830350 834235 := bstep (se 1 (by rfl) ⟨625676, by rfl⟩ : syracuseStep 834235 = 1251353) B1251353
theorem B10828505 : Blo 830350 10828505 := bstep (se 2 (by rfl) ⟨4060689, by rfl⟩ : syracuseStep 10828505 = 8121379) B8121379
theorem B834311 : Blo 830350 834311 := bstep (se 1 (by rfl) ⟨625733, by rfl⟩ : syracuseStep 834311 = 1251467) B1251467
theorem B834319 : Blo 830350 834319 := bstep (se 1 (by rfl) ⟨625739, by rfl⟩ : syracuseStep 834319 = 1251479) B1251479
theorem B3554081 : Blo 830350 3554081 := bstep (se 2 (by rfl) ⟨1332780, by rfl⟩ : syracuseStep 3554081 = 2665561) B2665561
theorem B6404915 : Blo 830350 6404915 := bstep (se 1 (by rfl) ⟨4803686, by rfl⟩ : syracuseStep 6404915 = 9607373) B9607373
theorem B2374535 : Blo 830350 2374535 := bstep (se 1 (by rfl) ⟨1780901, by rfl⟩ : syracuseStep 2374535 = 3561803) B3561803
theorem B4209731 : Blo 830350 4209731 := bstep (se 1 (by rfl) ⟨3157298, by rfl⟩ : syracuseStep 4209731 = 6314597) B6314597
theorem B4111667 : Blo 830350 4111667 := bstep (se 1 (by rfl) ⟨3083750, by rfl⟩ : syracuseStep 4111667 = 6167501) B6167501
theorem B1621367 : Blo 830350 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B4210055 : Blo 830350 4210055 := bstep (se 1 (by rfl) ⟨3157541, by rfl⟩ : syracuseStep 4210055 = 6315083) B6315083
theorem B3554695 : Blo 830350 3554695 := bstep (se 1 (by rfl) ⟨2666021, by rfl⟩ : syracuseStep 3554695 = 5332043) B5332043
theorem B4735037 : Blo 830350 4735037 := bstep (se 3 (by rfl) ⟨887819, by rfl⟩ : syracuseStep 4735037 = 1775639) B1775639
theorem B2244743 : Blo 830350 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B934159 : Blo 830350 934159 := bstep (se 1 (by rfl) ⟨700619, by rfl⟩ : syracuseStep 934159 = 1401239) B1401239
theorem B2670995 : Blo 830350 2670995 := bstep (se 1 (by rfl) ⟨2003246, by rfl⟩ : syracuseStep 2670995 = 4006493) B4006493
theorem B5325277 : Blo 830350 5325277 := bstep (se 3 (by rfl) ⟨998489, by rfl⟩ : syracuseStep 5325277 = 1996979) B1996979
theorem B2671147 : Blo 830350 2671147 := bstep (se 1 (by rfl) ⟨2003360, by rfl⟩ : syracuseStep 2671147 = 4006721) B4006721
theorem B4735745 : Blo 830350 4735745 := bstep (se 2 (by rfl) ⟨1775904, by rfl⟩ : syracuseStep 4735745 = 3551809) B3551809
theorem B934663 : Blo 830350 934663 := bstep (se 1 (by rfl) ⟨700997, by rfl⟩ : syracuseStep 934663 = 1401995) B1401995
theorem B2802491 : Blo 830350 2802491 := bstep (se 1 (by rfl) ⟨2101868, by rfl⟩ : syracuseStep 2802491 = 4203737) B4203737
theorem B3162995 : Blo 830350 3162995 := bstep (se 1 (by rfl) ⟨2372246, by rfl⟩ : syracuseStep 3162995 = 4744493) B4744493
theorem B934843 : Blo 830350 934843 := bstep (se 1 (by rfl) ⟨701132, by rfl⟩ : syracuseStep 934843 = 1402265) B1402265
theorem B2802977 : Blo 830350 2802977 := bstep (se 2 (by rfl) ⟨1051116, by rfl⟩ : syracuseStep 2802977 = 2102233) B2102233
theorem B200263043 : Blo 830350 200263043 := bstep (se 1 (by rfl) ⟨150197282, by rfl⟩ : syracuseStep 200263043 = 300394565) B300394565
theorem B935311 : Blo 830350 935311 := bstep (se 1 (by rfl) ⟨701483, by rfl⟩ : syracuseStep 935311 = 1402967) B1402967
theorem B17974885 : Blo 830350 17974885 := bstep (se 4 (by rfl) ⟨1685145, by rfl⟩ : syracuseStep 17974885 = 3370291) B3370291
theorem B6735653 : Blo 830350 6735653 := bstep (se 4 (by rfl) ⟨631467, by rfl⟩ : syracuseStep 6735653 = 1262935) B1262935
theorem B2803571 : Blo 830350 2803571 := bstep (se 1 (by rfl) ⟨2102678, by rfl⟩ : syracuseStep 2803571 = 4205357) B4205357
theorem B1001335 : Blo 830350 1001335 := bstep (se 1 (by rfl) ⟨751001, by rfl⟩ : syracuseStep 1001335 = 1502003) B1502003
theorem B935815 : Blo 830350 935815 := bstep (se 1 (by rfl) ⟨701861, by rfl⟩ : syracuseStep 935815 = 1403723) B1403723
theorem B935995 : Blo 830350 935995 := bstep (se 1 (by rfl) ⟨701996, by rfl⟩ : syracuseStep 935995 = 1403993) B1403993
theorem B8014139 : Blo 830350 8014139 := bstep (se 1 (by rfl) ⟨6010604, by rfl⟩ : syracuseStep 8014139 = 12021209) B12021209
theorem B936463 : Blo 830350 936463 := bstep (se 1 (by rfl) ⟨702347, by rfl⟩ : syracuseStep 936463 = 1404695) B1404695
theorem B3001121 : Blo 830350 3001121 := bstep (se 2 (by rfl) ⟨1125420, by rfl⟩ : syracuseStep 3001121 = 2250841) B2250841
theorem B4213619 : Blo 830350 4213619 := bstep (se 1 (by rfl) ⟨3160214, by rfl⟩ : syracuseStep 4213619 = 6320429) B6320429
theorem B936967 : Blo 830350 936967 := bstep (se 1 (by rfl) ⟨702725, by rfl⟩ : syracuseStep 936967 = 1405451) B1405451
theorem B3165227 : Blo 830350 3165227 := bstep (se 1 (by rfl) ⟨2373920, by rfl⟩ : syracuseStep 3165227 = 4747841) B4747841
theorem B4738135 : Blo 830350 4738135 := bstep (se 1 (by rfl) ⟨3553601, by rfl⟩ : syracuseStep 4738135 = 7107203) B7107203
theorem B937147 : Blo 830350 937147 := bstep (se 1 (by rfl) ⟨702860, by rfl⟩ : syracuseStep 937147 = 1405721) B1405721
theorem B12012781 : Blo 830350 12012781 := bstep (se 3 (by rfl) ⟨2252396, by rfl⟩ : syracuseStep 12012781 = 4504793) B4504793
theorem B4214105 : Blo 830350 4214105 := bstep (se 2 (by rfl) ⟨1580289, by rfl⟩ : syracuseStep 4214105 = 3160579) B3160579
theorem B27053669 : Blo 830350 27053669 := bstep (se 4 (by rfl) ⟨2536281, by rfl⟩ : syracuseStep 27053669 = 5072563) B5072563
theorem B24333965 : Blo 830350 24333965 := bstep (se 3 (by rfl) ⟨4562618, by rfl⟩ : syracuseStep 24333965 = 9125237) B9125237
theorem B937615 : Blo 830350 937615 := bstep (se 1 (by rfl) ⟨703211, by rfl⟩ : syracuseStep 937615 = 1406423) B1406423
theorem B1429177 : Blo 830350 1429177 := bstep (se 2 (by rfl) ⟨535941, by rfl⟩ : syracuseStep 1429177 = 1071883) B1071883
theorem B6311681 : Blo 830350 6311681 := bstep (se 2 (by rfl) ⟨2366880, by rfl⟩ : syracuseStep 6311681 = 4733761) B4733761
theorem B1330987 : Blo 830350 1330987 := bstep (se 1 (by rfl) ⟨998240, by rfl⟩ : syracuseStep 1330987 = 1996481) B1996481
theorem B1265527 : Blo 830350 1265527 := bstep (se 1 (by rfl) ⟨949145, by rfl⟩ : syracuseStep 1265527 = 1898291) B1898291
theorem B1331243 : Blo 830350 1331243 := bstep (se 1 (by rfl) ⟨998432, by rfl⟩ : syracuseStep 1331243 = 1996865) B1996865
theorem B7098455 : Blo 830350 7098455 := bstep (se 1 (by rfl) ⟨5323841, by rfl⟩ : syracuseStep 7098455 = 10647683) B10647683
theorem B938119 : Blo 830350 938119 := bstep (se 1 (by rfl) ⟨703589, by rfl⟩ : syracuseStep 938119 = 1407179) B1407179
theorem B1265977 : Blo 830350 1265977 := bstep (se 2 (by rfl) ⟨474741, by rfl⟩ : syracuseStep 1265977 = 949483) B949483
theorem B938299 : Blo 830350 938299 := bstep (se 1 (by rfl) ⟨703724, by rfl⟩ : syracuseStep 938299 = 1407449) B1407449
theorem B2806163 : Blo 830350 2806163 := bstep (se 1 (by rfl) ⟨2104622, by rfl⟩ : syracuseStep 2806163 = 4209245) B4209245
theorem B3559889 : Blo 830350 3559889 := bstep (se 2 (by rfl) ⟨1334958, by rfl⟩ : syracuseStep 3559889 = 2669917) B2669917
theorem B4280843 : Blo 830350 4280843 := bstep (se 1 (by rfl) ⟨3210632, by rfl⟩ : syracuseStep 4280843 = 6421265) B6421265
theorem B5329637 : Blo 830350 5329637 := bstep (se 4 (by rfl) ⟨499653, by rfl⟩ : syracuseStep 5329637 = 999307) B999307
theorem B4051727 : Blo 830350 4051727 := bstep (se 1 (by rfl) ⟨3038795, by rfl⟩ : syracuseStep 4051727 = 6077591) B6077591
theorem B4740119 : Blo 830350 4740119 := bstep (se 1 (by rfl) ⟨3555089, by rfl⟩ : syracuseStep 4740119 = 7110179) B7110179
theorem B1627195 : Blo 830350 1627195 := bstep (se 1 (by rfl) ⟨1220396, by rfl⟩ : syracuseStep 1627195 = 2440793) B2440793
theorem B4216211 : Blo 830350 4216211 := bstep (se 1 (by rfl) ⟨3162158, by rfl⟩ : syracuseStep 4216211 = 6324317) B6324317
theorem B1267145 : Blo 830350 1267145 := bstep (se 2 (by rfl) ⟨475179, by rfl⟩ : syracuseStep 1267145 = 950359) B950359
theorem B2807567 : Blo 830350 2807567 := bstep (se 1 (by rfl) ⟨2105675, by rfl⟩ : syracuseStep 2807567 = 4211351) B4211351
theorem B2807837 : Blo 830350 2807837 := bstep (se 3 (by rfl) ⟨526469, by rfl⟩ : syracuseStep 2807837 = 1052939) B1052939
theorem B3561515 : Blo 830350 3561515 := bstep (se 1 (by rfl) ⟨2671136, by rfl⟩ : syracuseStep 3561515 = 5342273) B5342273
theorem B10115117 : Blo 830350 10115117 := bstep (se 3 (by rfl) ⟨1896584, by rfl⟩ : syracuseStep 10115117 = 3793169) B3793169
theorem B18012253 : Blo 830350 18012253 := bstep (se 3 (by rfl) ⟨3377297, by rfl⟩ : syracuseStep 18012253 = 6754595) B6754595
theorem B5068919 : Blo 830350 5068919 := bstep (se 1 (by rfl) ⟨3801689, by rfl⟩ : syracuseStep 5068919 = 7603379) B7603379
theorem B5134529 : Blo 830350 5134529 := bstep (se 2 (by rfl) ⟨1925448, by rfl⟩ : syracuseStep 5134529 = 3850897) B3850897
theorem B842119 : Blo 830350 842119 := bstep (se 1 (by rfl) ⟨631589, by rfl⟩ : syracuseStep 842119 = 1263179) B1263179
theorem B3037625 : Blo 830350 3037625 := bstep (se 2 (by rfl) ⟨1139109, by rfl⟩ : syracuseStep 3037625 = 2278219) B2278219
theorem B5134871 : Blo 830350 5134871 := bstep (se 1 (by rfl) ⟨3851153, by rfl⟩ : syracuseStep 5134871 = 7702307) B7702307
theorem B5069627 : Blo 830350 5069627 := bstep (se 1 (by rfl) ⟨3802220, by rfl⟩ : syracuseStep 5069627 = 7604441) B7604441
theorem B2251705 : Blo 830350 2251705 := bstep (se 2 (by rfl) ⟨844389, by rfl⟩ : syracuseStep 2251705 = 1688779) B1688779
theorem B7986377 : Blo 830350 7986377 := bstep (se 2 (by rfl) ⟨2994891, by rfl⟩ : syracuseStep 7986377 = 5989783) B5989783
theorem B1498427 : Blo 830350 1498427 := bstep (se 1 (by rfl) ⟨1123820, by rfl⟩ : syracuseStep 1498427 = 2247641) B2247641
theorem B7396753 : Blo 830350 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B2809241 : Blo 830350 2809241 := bstep (se 2 (by rfl) ⟨1053465, by rfl⟩ : syracuseStep 2809241 = 2106931) B2106931
theorem B3005849 : Blo 830350 3005849 := bstep (se 2 (by rfl) ⟨1127193, by rfl⟩ : syracuseStep 3005849 = 2254387) B2254387
theorem B40492547 : Blo 830350 40492547 := bstep (se 1 (by rfl) ⟨30369410, by rfl⟩ : syracuseStep 40492547 = 60738821) B60738821
theorem B1335241 : Blo 830350 1335241 := bstep (se 2 (by rfl) ⟨500715, by rfl⟩ : syracuseStep 1335241 = 1001431) B1001431
theorem B6316055 : Blo 830350 6316055 := bstep (se 1 (by rfl) ⟨4737041, by rfl⟩ : syracuseStep 6316055 = 9474083) B9474083
theorem B2809943 : Blo 830350 2809943 := bstep (se 1 (by rfl) ⟨2107457, by rfl⟩ : syracuseStep 2809943 = 4214915) B4214915
theorem B27025649 : Blo 830350 27025649 := bstep (se 2 (by rfl) ⟨10134618, by rfl⟩ : syracuseStep 27025649 = 20269237) B20269237
theorem B20209985 : Blo 830350 20209985 := bstep (se 2 (by rfl) ⟨7578744, by rfl⟩ : syracuseStep 20209985 = 15157489) B15157489
theorem B4219289 : Blo 830350 4219289 := bstep (se 2 (by rfl) ⟨1582233, by rfl⟩ : syracuseStep 4219289 = 3164467) B3164467
theorem B2810429 : Blo 830350 2810429 := bstep (se 3 (by rfl) ⟨526955, by rfl⟩ : syracuseStep 2810429 = 1053911) B1053911
theorem B1401529 : Blo 830350 1401529 := bstep (se 2 (by rfl) ⟨525573, by rfl⟩ : syracuseStep 1401529 = 1051147) B1051147
theorem B1402231 : Blo 830350 1402231 := bstep (se 1 (by rfl) ⟨1051673, by rfl⟩ : syracuseStep 1402231 = 2103347) B2103347
theorem B9495953 : Blo 830350 9495953 := bstep (se 2 (by rfl) ⟨3560982, by rfl⟩ : syracuseStep 9495953 = 7121965) B7121965
theorem B845327 : Blo 830350 845327 := bstep (se 1 (by rfl) ⟨633995, by rfl⟩ : syracuseStep 845327 = 1267991) B1267991
theorem B1402427 : Blo 830350 1402427 := bstep (se 1 (by rfl) ⟨1051820, by rfl⟩ : syracuseStep 1402427 = 2103641) B2103641
theorem B3991481 : Blo 830350 3991481 := bstep (se 2 (by rfl) ⟨1496805, by rfl⟩ : syracuseStep 3991481 = 2993611) B2993611
theorem B2811833 : Blo 830350 2811833 := bstep (se 2 (by rfl) ⟨1054437, by rfl⟩ : syracuseStep 2811833 = 2108875) B2108875
theorem B1402825 : Blo 830350 1402825 := bstep (se 2 (by rfl) ⟨526059, by rfl⟩ : syracuseStep 1402825 = 1052119) B1052119
theorem B3795011 : Blo 830350 3795011 := bstep (se 1 (by rfl) ⟨2846258, by rfl⟩ : syracuseStep 3795011 = 5692517) B5692517
theorem B1501483 : Blo 830350 1501483 := bstep (se 1 (by rfl) ⟨1126112, by rfl⟩ : syracuseStep 1501483 = 2252225) B2252225
theorem B2255165 : Blo 830350 2255165 := bstep (se 3 (by rfl) ⟨422843, by rfl⟩ : syracuseStep 2255165 = 845687) B845687
theorem B3991943 : Blo 830350 3991943 := bstep (se 1 (by rfl) ⟨2993957, by rfl⟩ : syracuseStep 3991943 = 5987915) B5987915
theorem B2812427 : Blo 830350 2812427 := bstep (se 1 (by rfl) ⟨2109320, by rfl⟩ : syracuseStep 2812427 = 4218641) B4218641
theorem B2812535 : Blo 830350 2812535 := bstep (se 1 (by rfl) ⟨2109401, by rfl⟩ : syracuseStep 2812535 = 4218803) B4218803
theorem B1403527 : Blo 830350 1403527 := bstep (se 1 (by rfl) ⟨1052645, by rfl⟩ : syracuseStep 1403527 = 2105291) B2105291
theorem B12315329 : Blo 830350 12315329 := bstep (se 2 (by rfl) ⟨4618248, by rfl⟩ : syracuseStep 12315329 = 9236497) B9236497
theorem B4221881 : Blo 830350 4221881 := bstep (se 2 (by rfl) ⟨1583205, by rfl⟩ : syracuseStep 4221881 = 3166411) B3166411
theorem B2813129 : Blo 830350 2813129 := bstep (se 2 (by rfl) ⟨1054923, by rfl⟩ : syracuseStep 2813129 = 2109847) B2109847
theorem B1404175 : Blo 830350 1404175 := bstep (se 1 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 1404175 = 2106263) B2106263
theorem B16019045 : Blo 830350 16019045 := bstep (se 4 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 16019045 = 3003571) B3003571
theorem B2027209 : Blo 830350 2027209 := bstep (se 2 (by rfl) ⟨760203, by rfl⟩ : syracuseStep 2027209 = 1520407) B1520407
theorem B1404715 : Blo 830350 1404715 := bstep (se 1 (by rfl) ⟨1053536, by rfl⟩ : syracuseStep 1404715 = 2107073) B2107073
theorem B28897073 : Blo 830350 28897073 := bstep (se 2 (by rfl) ⟨10836402, by rfl⟩ : syracuseStep 28897073 = 21672805) B21672805
theorem B2813831 : Blo 830350 2813831 := bstep (se 1 (by rfl) ⟨2110373, by rfl⟩ : syracuseStep 2813831 = 4220747) B4220747
theorem B1404857 : Blo 830350 1404857 := bstep (se 2 (by rfl) ⟨526821, by rfl⟩ : syracuseStep 1404857 = 1053643) B1053643
theorem B2846749 : Blo 830350 2846749 := bstep (se 3 (by rfl) ⟨533765, by rfl⟩ : syracuseStep 2846749 = 1067531) B1067531
theorem B4223177 : Blo 830350 4223177 := bstep (se 2 (by rfl) ⟨1583691, by rfl⟩ : syracuseStep 4223177 = 3167383) B3167383
theorem B9498869 : Blo 830350 9498869 := bstep (se 5 (by rfl) ⟨445259, by rfl⟩ : syracuseStep 9498869 = 890519) B890519
theorem B2814209 : Blo 830350 2814209 := bstep (se 2 (by rfl) ⟨1055328, by rfl⟩ : syracuseStep 2814209 = 2110657) B2110657
theorem B2027891 : Blo 830350 2027891 := bstep (se 1 (by rfl) ⟨1520918, by rfl⟩ : syracuseStep 2027891 = 3041837) B3041837
theorem B1995155 : Blo 830350 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B1896851 : Blo 830350 1896851 := bstep (se 1 (by rfl) ⟨1422638, by rfl⟩ : syracuseStep 1896851 = 2845277) B2845277
theorem B1405559 : Blo 830350 1405559 := bstep (se 1 (by rfl) ⟨1054169, by rfl⟩ : syracuseStep 1405559 = 2108339) B2108339
theorem B2815019 : Blo 830350 2815019 := bstep (se 1 (by rfl) ⟨2111264, by rfl⟩ : syracuseStep 2815019 = 4222529) B4222529
theorem B1406011 : Blo 830350 1406011 := bstep (se 1 (by rfl) ⟨1054508, by rfl⟩ : syracuseStep 1406011 = 2109017) B2109017
theorem B1995923 : Blo 830350 1995923 := bstep (se 1 (by rfl) ⟨1496942, by rfl⟩ : syracuseStep 1995923 = 2993885) B2993885
theorem B1406153 : Blo 830350 1406153 := bstep (se 2 (by rfl) ⟨527307, by rfl⟩ : syracuseStep 1406153 = 1054615) B1054615
theorem B4552139 : Blo 830350 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B4748867 : Blo 830350 4748867 := bstep (se 1 (by rfl) ⟨3561650, by rfl⟩ : syracuseStep 4748867 = 7123301) B7123301
theorem B1996663 : Blo 830350 1996663 := bstep (se 1 (by rfl) ⟨1497497, by rfl⟩ : syracuseStep 1996663 = 2994995) B2994995
theorem B1406855 : Blo 830350 1406855 := bstep (se 1 (by rfl) ⟨1055141, by rfl⟩ : syracuseStep 1406855 = 2110283) B2110283
theorem B1407503 : Blo 830350 1407503 := bstep (se 1 (by rfl) ⟨1055627, by rfl⟩ : syracuseStep 1407503 = 2111255) B2111255
theorem B9009893 : Blo 830350 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B2030483 : Blo 830350 2030483 := bstep (se 1 (by rfl) ⟨1522862, by rfl⟩ : syracuseStep 2030483 = 3045725) B3045725
theorem B6946307 : Blo 830350 6946307 := bstep (se 1 (by rfl) ⟨5209730, by rfl⟩ : syracuseStep 6946307 = 10419461) B10419461
theorem B6323831 : Blo 830350 6323831 := bstep (se 1 (by rfl) ⟨4742873, by rfl⟩ : syracuseStep 6323831 = 9485747) B9485747
theorem B3374963 : Blo 830350 3374963 := bstep (se 1 (by rfl) ⟨2531222, by rfl⟩ : syracuseStep 3374963 = 5062445) B5062445
theorem B4751257 : Blo 830350 4751257 := bstep (se 2 (by rfl) ⟨1781721, by rfl⟩ : syracuseStep 4751257 = 3563443) B3563443
theorem B3997649 : Blo 830350 3997649 := bstep (se 2 (by rfl) ⟨1499118, by rfl⟩ : syracuseStep 3997649 = 2998237) B2998237
theorem B1441963 : Blo 830350 1441963 := bstep (se 1 (by rfl) ⟨1081472, by rfl⟩ : syracuseStep 1441963 = 2162945) B2162945
theorem B1245545 : Blo 830350 1245545 := bstep (se 2 (by rfl) ⟨467079, by rfl⟩ : syracuseStep 1245545 = 934159) B934159
theorem B1245623 : Blo 830350 1245623 := bstep (se 1 (by rfl) ⟨934217, by rfl⟩ : syracuseStep 1245623 = 1868435) B1868435
theorem B1245659 : Blo 830350 1245659 := bstep (se 1 (by rfl) ⟨934244, by rfl⟩ : syracuseStep 1245659 = 1868489) B1868489
theorem B4063769 : Blo 830350 4063769 := bstep (se 2 (by rfl) ⟨1523913, by rfl⟩ : syracuseStep 4063769 = 3047827) B3047827
theorem B1868327 : Blo 830350 1868327 := bstep (se 1 (by rfl) ⟨1401245, by rfl⟩ : syracuseStep 1868327 = 2802491) B2802491
theorem B1868651 : Blo 830350 1868651 := bstep (se 1 (by rfl) ⟨1401488, by rfl⟩ : syracuseStep 1868651 = 2802977) B2802977
theorem B1868705 : Blo 830350 1868705 := bstep (se 2 (by rfl) ⟨700764, by rfl⟩ : syracuseStep 1868705 = 1401529) B1401529
theorem B1246127 : Blo 830350 1246127 := bstep (se 1 (by rfl) ⟨934595, by rfl⟩ : syracuseStep 1246127 = 1869191) B1869191
theorem B1246217 : Blo 830350 1246217 := bstep (se 2 (by rfl) ⟨467331, by rfl⟩ : syracuseStep 1246217 = 934663) B934663
theorem B1246247 : Blo 830350 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B1246331 : Blo 830350 1246331 := bstep (se 1 (by rfl) ⟨934748, by rfl⟩ : syracuseStep 1246331 = 1869497) B1869497
theorem B4490435 : Blo 830350 4490435 := bstep (se 1 (by rfl) ⟨3367826, by rfl⟩ : syracuseStep 4490435 = 6735653) B6735653
theorem B1869047 : Blo 830350 1869047 := bstep (se 1 (by rfl) ⟨1401785, by rfl⟩ : syracuseStep 1869047 = 2803571) B2803571
theorem B1246457 : Blo 830350 1246457 := bstep (se 2 (by rfl) ⟨467421, by rfl⟩ : syracuseStep 1246457 = 934843) B934843
theorem B1246559 : Blo 830350 1246559 := bstep (se 1 (by rfl) ⟨934919, by rfl⟩ : syracuseStep 1246559 = 1869839) B1869839
theorem B1246571 : Blo 830350 1246571 := bstep (se 1 (by rfl) ⟨934928, by rfl⟩ : syracuseStep 1246571 = 1869857) B1869857
theorem B3605903 : Blo 830350 3605903 := bstep (se 1 (by rfl) ⟨2704427, by rfl⟩ : syracuseStep 3605903 = 5408855) B5408855
theorem B5703131 : Blo 830350 5703131 := bstep (se 1 (by rfl) ⟨4277348, by rfl⟩ : syracuseStep 5703131 = 8554697) B8554697
theorem B5342759 : Blo 830350 5342759 := bstep (se 1 (by rfl) ⟨4007069, by rfl⟩ : syracuseStep 5342759 = 8014139) B8014139
theorem B1246799 : Blo 830350 1246799 := bstep (se 1 (by rfl) ⟨935099, by rfl⟩ : syracuseStep 1246799 = 1870199) B1870199
theorem B1246919 : Blo 830350 1246919 := bstep (se 1 (by rfl) ⟨935189, by rfl⟩ : syracuseStep 1246919 = 1870379) B1870379
theorem B12191431 : Blo 830350 12191431 := bstep (se 1 (by rfl) ⟨9143573, by rfl⟩ : syracuseStep 12191431 = 18287147) B18287147
theorem B8980267 : Blo 830350 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B1869641 : Blo 830350 1869641 := bstep (se 2 (by rfl) ⟨701115, by rfl⟩ : syracuseStep 1869641 = 1402231) B1402231
theorem B1247081 : Blo 830350 1247081 := bstep (se 2 (by rfl) ⟨467655, by rfl⟩ : syracuseStep 1247081 = 935311) B935311
theorem B2000747 : Blo 830350 2000747 := bstep (se 1 (by rfl) ⟨1500560, by rfl⟩ : syracuseStep 2000747 = 3001121) B3001121
theorem B1247159 : Blo 830350 1247159 := bstep (se 1 (by rfl) ⟨935369, by rfl⟩ : syracuseStep 1247159 = 1870739) B1870739
theorem B8652737 : Blo 830350 8652737 := bstep (se 2 (by rfl) ⟨3244776, by rfl⟩ : syracuseStep 8652737 = 6489553) B6489553
theorem B1247195 : Blo 830350 1247195 := bstep (se 1 (by rfl) ⟨935396, by rfl⟩ : syracuseStep 1247195 = 1870793) B1870793
theorem B4491301 : Blo 830350 4491301 := bstep (se 4 (by rfl) ⟨421059, by rfl⟩ : syracuseStep 4491301 = 842119) B842119
theorem B4556837 : Blo 830350 4556837 := bstep (se 4 (by rfl) ⟨427203, by rfl⟩ : syracuseStep 4556837 = 854407) B854407
theorem B1247663 : Blo 830350 1247663 := bstep (se 1 (by rfl) ⟨935747, by rfl⟩ : syracuseStep 1247663 = 1871495) B1871495
theorem B16222643 : Blo 830350 16222643 := bstep (se 1 (by rfl) ⟨12166982, by rfl⟩ : syracuseStep 16222643 = 24333965) B24333965
theorem B1247753 : Blo 830350 1247753 := bstep (se 2 (by rfl) ⟨467907, by rfl⟩ : syracuseStep 1247753 = 935815) B935815
theorem B1247783 : Blo 830350 1247783 := bstep (se 1 (by rfl) ⟨935837, by rfl⟩ : syracuseStep 1247783 = 1871675) B1871675
theorem B1870433 : Blo 830350 1870433 := bstep (se 2 (by rfl) ⟨701412, by rfl⟩ : syracuseStep 1870433 = 1402825) B1402825
theorem B1247867 : Blo 830350 1247867 := bstep (se 1 (by rfl) ⟨935900, by rfl⟩ : syracuseStep 1247867 = 1871801) B1871801
theorem B887495 : Blo 830350 887495 := bstep (se 1 (by rfl) ⟨665621, by rfl⟩ : syracuseStep 887495 = 1331243) B1331243
theorem B1247993 : Blo 830350 1247993 := bstep (se 2 (by rfl) ⟨467997, by rfl⟩ : syracuseStep 1247993 = 935995) B935995
theorem B1248095 : Blo 830350 1248095 := bstep (se 1 (by rfl) ⟨936071, by rfl⟩ : syracuseStep 1248095 = 1872143) B1872143
theorem B1248107 : Blo 830350 1248107 := bstep (se 1 (by rfl) ⟨936080, by rfl⟩ : syracuseStep 1248107 = 1872161) B1872161
theorem B1870775 : Blo 830350 1870775 := bstep (se 1 (by rfl) ⟨1403081, by rfl⟩ : syracuseStep 1870775 = 2806163) B2806163
theorem B2853895 : Blo 830350 2853895 := bstep (se 1 (by rfl) ⟨2140421, by rfl⟩ : syracuseStep 2853895 = 4280843) B4280843
theorem B2001977 : Blo 830350 2001977 := bstep (se 2 (by rfl) ⟨750741, by rfl⟩ : syracuseStep 2001977 = 1501483) B1501483
theorem B1248335 : Blo 830350 1248335 := bstep (se 1 (by rfl) ⟨936251, by rfl⟩ : syracuseStep 1248335 = 1872503) B1872503
theorem B1248455 : Blo 830350 1248455 := bstep (se 1 (by rfl) ⟨936341, by rfl⟩ : syracuseStep 1248455 = 1872683) B1872683
theorem B4001015 : Blo 830350 4001015 := bstep (se 1 (by rfl) ⟨3000761, by rfl⟩ : syracuseStep 4001015 = 6001523) B6001523
theorem B1248617 : Blo 830350 1248617 := bstep (se 2 (by rfl) ⟨468231, by rfl⟩ : syracuseStep 1248617 = 936463) B936463
theorem B1248695 : Blo 830350 1248695 := bstep (se 1 (by rfl) ⟨936521, by rfl⟩ : syracuseStep 1248695 = 1873043) B1873043
theorem B1248731 : Blo 830350 1248731 := bstep (se 1 (by rfl) ⟨936548, by rfl⟩ : syracuseStep 1248731 = 1873097) B1873097
theorem B1871369 : Blo 830350 1871369 := bstep (se 2 (by rfl) ⟨701763, by rfl⟩ : syracuseStep 1871369 = 1403527) B1403527
theorem B1871711 : Blo 830350 1871711 := bstep (se 1 (by rfl) ⟨1403783, by rfl⟩ : syracuseStep 1871711 = 2807567) B2807567
theorem B1183663 : Blo 830350 1183663 := bstep (se 1 (by rfl) ⟨887747, by rfl⟩ : syracuseStep 1183663 = 1775495) B1775495
theorem B1249199 : Blo 830350 1249199 := bstep (se 1 (by rfl) ⟨936899, by rfl⟩ : syracuseStep 1249199 = 1873799) B1873799
theorem B1249289 : Blo 830350 1249289 := bstep (se 2 (by rfl) ⟨468483, by rfl⟩ : syracuseStep 1249289 = 936967) B936967
theorem B1576979 : Blo 830350 1576979 := bstep (se 1 (by rfl) ⟨1182734, by rfl⟩ : syracuseStep 1576979 = 2365469) B2365469
theorem B1871891 : Blo 830350 1871891 := bstep (se 1 (by rfl) ⟨1403918, by rfl⟩ : syracuseStep 1871891 = 2807837) B2807837
theorem B1249319 : Blo 830350 1249319 := bstep (se 1 (by rfl) ⟨936989, by rfl⟩ : syracuseStep 1249319 = 1873979) B1873979
theorem B1249403 : Blo 830350 1249403 := bstep (se 1 (by rfl) ⟨937052, by rfl⟩ : syracuseStep 1249403 = 1874105) B1874105
theorem B1577207 : Blo 830350 1577207 := bstep (se 1 (by rfl) ⟨1182905, by rfl⟩ : syracuseStep 1577207 = 2365811) B2365811
theorem B1249529 : Blo 830350 1249529 := bstep (se 2 (by rfl) ⟨468573, by rfl⟩ : syracuseStep 1249529 = 937147) B937147
theorem B1249631 : Blo 830350 1249631 := bstep (se 1 (by rfl) ⟨937223, by rfl⟩ : syracuseStep 1249631 = 1874447) B1874447
theorem B1872233 : Blo 830350 1872233 := bstep (se 2 (by rfl) ⟨702087, by rfl⟩ : syracuseStep 1872233 = 1404175) B1404175
theorem B1249643 : Blo 830350 1249643 := bstep (se 1 (by rfl) ⟨937232, by rfl⟩ : syracuseStep 1249643 = 1874465) B1874465
theorem B3805721 : Blo 830350 3805721 := bstep (se 2 (by rfl) ⟨1427145, by rfl⟩ : syracuseStep 3805721 = 2854291) B2854291
theorem B3379751 : Blo 830350 3379751 := bstep (se 1 (by rfl) ⟨2534813, by rfl⟩ : syracuseStep 3379751 = 5069627) B5069627
theorem B1053263 : Blo 830350 1053263 := bstep (se 1 (by rfl) ⟨789947, by rfl⟩ : syracuseStep 1053263 = 1579895) B1579895
theorem B1249871 : Blo 830350 1249871 := bstep (se 1 (by rfl) ⟨937403, by rfl⟩ : syracuseStep 1249871 = 1874807) B1874807
theorem B1249991 : Blo 830350 1249991 := bstep (se 1 (by rfl) ⟨937493, by rfl⟩ : syracuseStep 1249991 = 1874987) B1874987
theorem B1250153 : Blo 830350 1250153 := bstep (se 2 (by rfl) ⟨468807, by rfl⟩ : syracuseStep 1250153 = 937615) B937615
theorem B1905569 : Blo 830350 1905569 := bstep (se 2 (by rfl) ⟨714588, by rfl⟩ : syracuseStep 1905569 = 1429177) B1429177
theorem B1250231 : Blo 830350 1250231 := bstep (se 1 (by rfl) ⟨937673, by rfl⟩ : syracuseStep 1250231 = 1875347) B1875347
theorem B1872827 : Blo 830350 1872827 := bstep (se 1 (by rfl) ⟨1404620, by rfl⟩ : syracuseStep 1872827 = 2809241) B2809241
theorem B1250267 : Blo 830350 1250267 := bstep (se 1 (by rfl) ⟨937700, by rfl⟩ : syracuseStep 1250267 = 1875401) B1875401
theorem B14193629 : Blo 830350 14193629 := bstep (se 3 (by rfl) ⟨2661305, by rfl⟩ : syracuseStep 14193629 = 5322611) B5322611
theorem B1774649 : Blo 830350 1774649 := bstep (se 2 (by rfl) ⟨665493, by rfl⟩ : syracuseStep 1774649 = 1330987) B1330987
theorem B1872953 : Blo 830350 1872953 := bstep (se 2 (by rfl) ⟨702357, by rfl⟩ : syracuseStep 1872953 = 1404715) B1404715
theorem B6002009 : Blo 830350 6002009 := bstep (se 2 (by rfl) ⟨2250753, by rfl⟩ : syracuseStep 6002009 = 4501507) B4501507
theorem B1873295 : Blo 830350 1873295 := bstep (se 1 (by rfl) ⟨1404971, by rfl⟩ : syracuseStep 1873295 = 2809943) B2809943
theorem B1250735 : Blo 830350 1250735 := bstep (se 1 (by rfl) ⟨938051, by rfl⟩ : syracuseStep 1250735 = 1876103) B1876103
theorem B1250825 : Blo 830350 1250825 := bstep (se 2 (by rfl) ⟨469059, by rfl⟩ : syracuseStep 1250825 = 938119) B938119
theorem B2364967 : Blo 830350 2364967 := bstep (se 1 (by rfl) ⟨1773725, by rfl⟩ : syracuseStep 2364967 = 3547451) B3547451
theorem B1250855 : Blo 830350 1250855 := bstep (se 1 (by rfl) ⟨938141, by rfl⟩ : syracuseStep 1250855 = 1876283) B1876283
theorem B13473323 : Blo 830350 13473323 := bstep (se 1 (by rfl) ⟨10104992, by rfl⟩ : syracuseStep 13473323 = 20209985) B20209985
theorem B2102881 : Blo 830350 2102881 := bstep (se 2 (by rfl) ⟨788580, by rfl⟩ : syracuseStep 2102881 = 1577161) B1577161
theorem B1578619 : Blo 830350 1578619 := bstep (se 1 (by rfl) ⟨1183964, by rfl⟩ : syracuseStep 1578619 = 2367929) B2367929
theorem B1250939 : Blo 830350 1250939 := bstep (se 1 (by rfl) ⟨938204, by rfl⟩ : syracuseStep 1250939 = 1876409) B1876409
theorem B2365139 : Blo 830350 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B1873619 : Blo 830350 1873619 := bstep (se 1 (by rfl) ⟨1405214, by rfl⟩ : syracuseStep 1873619 = 2810429) B2810429
theorem B1251065 : Blo 830350 1251065 := bstep (se 2 (by rfl) ⟨469149, by rfl⟩ : syracuseStep 1251065 = 938299) B938299
theorem B1578847 : Blo 830350 1578847 := bstep (se 1 (by rfl) ⟨1184135, by rfl⟩ : syracuseStep 1578847 = 2368271) B2368271
theorem B1054559 : Blo 830350 1054559 := bstep (se 1 (by rfl) ⟨790919, by rfl⟩ : syracuseStep 1054559 = 1581839) B1581839
theorem B1251167 : Blo 830350 1251167 := bstep (se 1 (by rfl) ⟨938375, by rfl⟩ : syracuseStep 1251167 = 1876751) B1876751
theorem B1251179 : Blo 830350 1251179 := bstep (se 1 (by rfl) ⟨938384, by rfl⟩ : syracuseStep 1251179 = 1876769) B1876769
theorem B1251407 : Blo 830350 1251407 := bstep (se 1 (by rfl) ⟨938555, by rfl⟩ : syracuseStep 1251407 = 1877111) B1877111
theorem B1579105 : Blo 830350 1579105 := bstep (se 2 (by rfl) ⟨592164, by rfl⟩ : syracuseStep 1579105 = 1184329) B1184329
theorem B6330635 : Blo 830350 6330635 := bstep (se 1 (by rfl) ⟨4747976, by rfl⟩ : syracuseStep 6330635 = 9495953) B9495953
theorem B1579439 : Blo 830350 1579439 := bstep (se 1 (by rfl) ⟨1184579, by rfl⟩ : syracuseStep 1579439 = 2369159) B2369159
theorem B2103833 : Blo 830350 2103833 := bstep (se 2 (by rfl) ⟨788937, by rfl⟩ : syracuseStep 2103833 = 1577875) B1577875
theorem B2660987 : Blo 830350 2660987 := bstep (se 1 (by rfl) ⟨1995740, by rfl⟩ : syracuseStep 2660987 = 3991481) B3991481
theorem B1874555 : Blo 830350 1874555 := bstep (se 1 (by rfl) ⟨1405916, by rfl⟩ : syracuseStep 1874555 = 2811833) B2811833
theorem B2530007 : Blo 830350 2530007 := bstep (se 1 (by rfl) ⟨1897505, by rfl⟩ : syracuseStep 2530007 = 3795011) B3795011
theorem B1874681 : Blo 830350 1874681 := bstep (se 2 (by rfl) ⟨703005, by rfl⟩ : syracuseStep 1874681 = 1406011) B1406011
theorem B2169593 : Blo 830350 2169593 := bstep (se 2 (by rfl) ⟨813597, by rfl⟩ : syracuseStep 2169593 = 1627195) B1627195
theorem B2661295 : Blo 830350 2661295 := bstep (se 1 (by rfl) ⟨1995971, by rfl⟩ : syracuseStep 2661295 = 3991943) B3991943
theorem B10689509 : Blo 830350 10689509 := bstep (se 4 (by rfl) ⟨1002141, by rfl⟩ : syracuseStep 10689509 = 2004283) B2004283
theorem B2366471 : Blo 830350 2366471 := bstep (se 1 (by rfl) ⟨1774853, by rfl⟩ : syracuseStep 2366471 = 3549707) B3549707
theorem B1874951 : Blo 830350 1874951 := bstep (se 1 (by rfl) ⟨1406213, by rfl⟩ : syracuseStep 1874951 = 2812427) B2812427
theorem B2104339 : Blo 830350 2104339 := bstep (se 1 (by rfl) ⟨1578254, by rfl⟩ : syracuseStep 2104339 = 3156509) B3156509
theorem B1875023 : Blo 830350 1875023 := bstep (se 1 (by rfl) ⟨1406267, by rfl⟩ : syracuseStep 1875023 = 2812535) B2812535
theorem B1776887 : Blo 830350 1776887 := bstep (se 1 (by rfl) ⟨1332665, by rfl⟩ : syracuseStep 1776887 = 2665331) B2665331
theorem B24026381 : Blo 830350 24026381 := bstep (se 3 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 24026381 = 9009893) B9009893
theorem B43326899 : Blo 830350 43326899 := bstep (se 1 (by rfl) ⟨32495174, by rfl⟩ : syracuseStep 43326899 = 64990349) B64990349
theorem B1875419 : Blo 830350 1875419 := bstep (se 1 (by rfl) ⟨1406564, by rfl⟩ : syracuseStep 1875419 = 2813129) B2813129
theorem B1580563 : Blo 830350 1580563 := bstep (se 1 (by rfl) ⟨1185422, by rfl⟩ : syracuseStep 1580563 = 2370845) B2370845
theorem B3153593 : Blo 830350 3153593 := bstep (se 2 (by rfl) ⟨1182597, by rfl⟩ : syracuseStep 3153593 = 2365195) B2365195
theorem B6332093 : Blo 830350 6332093 := bstep (se 3 (by rfl) ⟨1187267, by rfl⟩ : syracuseStep 6332093 = 2374535) B2374535
theorem B1580791 : Blo 830350 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B2662217 : Blo 830350 2662217 := bstep (se 2 (by rfl) ⟨998331, by rfl⟩ : syracuseStep 2662217 = 1996663) B1996663
theorem B1875887 : Blo 830350 1875887 := bstep (se 1 (by rfl) ⟨1406915, by rfl⟩ : syracuseStep 1875887 = 2813831) B2813831
theorem B1581095 : Blo 830350 1581095 := bstep (se 1 (by rfl) ⟨1185821, by rfl⟩ : syracuseStep 1581095 = 2371643) B2371643
theorem B2105423 : Blo 830350 2105423 := bstep (se 1 (by rfl) ⟨1579067, by rfl⟩ : syracuseStep 2105423 = 3158135) B3158135
theorem B6332579 : Blo 830350 6332579 := bstep (se 1 (by rfl) ⟨4749434, by rfl⟩ : syracuseStep 6332579 = 9498869) B9498869
theorem B1876139 : Blo 830350 1876139 := bstep (se 1 (by rfl) ⟨1407104, by rfl⟩ : syracuseStep 1876139 = 2814209) B2814209
theorem B1351927 : Blo 830350 1351927 := bstep (se 1 (by rfl) ⟨1013945, by rfl⟩ : syracuseStep 1351927 = 2027891) B2027891
theorem B1876679 : Blo 830350 1876679 := bstep (se 1 (by rfl) ⟨1407509, by rfl⟩ : syracuseStep 1876679 = 2815019) B2815019
theorem B2106071 : Blo 830350 2106071 := bstep (se 1 (by rfl) ⟨1579553, by rfl⟩ : syracuseStep 2106071 = 3159107) B3159107
theorem B1778527 : Blo 830350 1778527 := bstep (se 1 (by rfl) ⟨1333895, by rfl⟩ : syracuseStep 1778527 = 2667791) B2667791
theorem B2106425 : Blo 830350 2106425 := bstep (se 2 (by rfl) ⟨789909, by rfl⟩ : syracuseStep 2106425 = 1579819) B1579819
theorem B40412357 : Blo 830350 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B1582409 : Blo 830350 1582409 := bstep (se 2 (by rfl) ⟨593403, by rfl⟩ : syracuseStep 1582409 = 1186807) B1186807
theorem B1516943 : Blo 830350 1516943 := bstep (se 1 (by rfl) ⟨1137707, by rfl⟩ : syracuseStep 1516943 = 2275415) B2275415
theorem B3155705 : Blo 830350 3155705 := bstep (se 2 (by rfl) ⟨1183389, by rfl⟩ : syracuseStep 3155705 = 2366779) B2366779
theorem B1582841 : Blo 830350 1582841 := bstep (se 2 (by rfl) ⟨593565, by rfl⟩ : syracuseStep 1582841 = 1187131) B1187131
theorem B7219003 : Blo 830350 7219003 := bstep (se 1 (by rfl) ⟨5414252, by rfl⟩ : syracuseStep 7219003 = 10828505) B10828505
theorem B2369387 : Blo 830350 2369387 := bstep (se 1 (by rfl) ⟨1777040, by rfl⟩ : syracuseStep 2369387 = 3554081) B3554081
theorem B4269943 : Blo 830350 4269943 := bstep (se 1 (by rfl) ⟨3202457, by rfl⟩ : syracuseStep 4269943 = 6404915) B6404915
theorem B1353655 : Blo 830350 1353655 := bstep (se 1 (by rfl) ⟨1015241, by rfl⟩ : syracuseStep 1353655 = 2030483) B2030483
theorem B4630871 : Blo 830350 4630871 := bstep (se 1 (by rfl) ⟨3473153, by rfl⟩ : syracuseStep 4630871 = 6946307) B6946307
theorem B6826477 : Blo 830350 6826477 := bstep (se 3 (by rfl) ⟨1279964, by rfl⟩ : syracuseStep 6826477 = 2559929) B2559929
theorem B6335009 : Blo 830350 6335009 := bstep (se 2 (by rfl) ⟨2375628, by rfl⟩ : syracuseStep 6335009 = 4751257) B4751257
theorem B1780321 : Blo 830350 1780321 := bstep (se 2 (by rfl) ⟨667620, by rfl⟩ : syracuseStep 1780321 = 1335241) B1335241
theorem B2665099 : Blo 830350 2665099 := bstep (se 1 (by rfl) ⟨1998824, by rfl⟩ : syracuseStep 2665099 = 3997649) B3997649
theorem B3156691 : Blo 830350 3156691 := bstep (se 1 (by rfl) ⟨2367518, by rfl⟩ : syracuseStep 3156691 = 4735037) B4735037
theorem B830383 : Blo 830350 830383 := bstep (se 1 (by rfl) ⟨622787, by rfl⟩ : syracuseStep 830383 = 1245575) B1245575
theorem B9612215 : Blo 830350 9612215 := bstep (se 1 (by rfl) ⟨7209161, by rfl⟩ : syracuseStep 9612215 = 14418323) B14418323
theorem B1780663 : Blo 830350 1780663 := bstep (se 1 (by rfl) ⟨1335497, by rfl⟩ : syracuseStep 1780663 = 2670995) B2670995
theorem B830407 : Blo 830350 830407 := bstep (se 1 (by rfl) ⟨622805, by rfl⟩ : syracuseStep 830407 = 1245611) B1245611
theorem B830427 : Blo 830350 830427 := bstep (se 1 (by rfl) ⟨622820, by rfl⟩ : syracuseStep 830427 = 1245641) B1245641
theorem B830503 : Blo 830350 830503 := bstep (se 1 (by rfl) ⟨622877, by rfl⟩ : syracuseStep 830503 = 1245755) B1245755
theorem B2370617 : Blo 830350 2370617 := bstep (se 2 (by rfl) ⟨888981, by rfl⟩ : syracuseStep 2370617 = 1777963) B1777963
theorem B830543 : Blo 830350 830543 := bstep (se 1 (by rfl) ⟨622907, by rfl⟩ : syracuseStep 830543 = 1245815) B1245815
theorem B830559 : Blo 830350 830559 := bstep (se 1 (by rfl) ⟨622919, by rfl⟩ : syracuseStep 830559 = 1245839) B1245839
theorem B830587 : Blo 830350 830587 := bstep (se 1 (by rfl) ⟨622940, by rfl⟩ : syracuseStep 830587 = 1245881) B1245881
theorem B3157163 : Blo 830350 3157163 := bstep (se 1 (by rfl) ⟨2367872, by rfl⟩ : syracuseStep 3157163 = 4735745) B4735745
theorem B830639 : Blo 830350 830639 := bstep (se 1 (by rfl) ⟨622979, by rfl⟩ : syracuseStep 830639 = 1245959) B1245959
theorem B830663 : Blo 830350 830663 := bstep (se 1 (by rfl) ⟨622997, by rfl⟩ : syracuseStep 830663 = 1245995) B1245995
theorem B830683 : Blo 830350 830683 := bstep (se 1 (by rfl) ⟨623012, by rfl⟩ : syracuseStep 830683 = 1246025) B1246025
theorem B2108663 : Blo 830350 2108663 := bstep (se 1 (by rfl) ⟨1581497, by rfl⟩ : syracuseStep 2108663 = 3162995) B3162995
theorem B6925591 : Blo 830350 6925591 := bstep (se 1 (by rfl) ⟨5194193, by rfl⟩ : syracuseStep 6925591 = 10388387) B10388387
theorem B830759 : Blo 830350 830759 := bstep (se 1 (by rfl) ⟨623069, by rfl⟩ : syracuseStep 830759 = 1246139) B1246139
theorem B830799 : Blo 830350 830799 := bstep (se 1 (by rfl) ⟨623099, by rfl⟩ : syracuseStep 830799 = 1246199) B1246199
theorem B830815 : Blo 830350 830815 := bstep (se 1 (by rfl) ⟨623111, by rfl⟩ : syracuseStep 830815 = 1246223) B1246223
theorem B830843 : Blo 830350 830843 := bstep (se 1 (by rfl) ⟨623132, by rfl⟩ : syracuseStep 830843 = 1246265) B1246265
theorem B15183247 : Blo 830350 15183247 := bstep (se 1 (by rfl) ⟨11387435, by rfl⟩ : syracuseStep 15183247 = 22774871) B22774871
theorem B830895 : Blo 830350 830895 := bstep (se 1 (by rfl) ⟨623171, by rfl⟩ : syracuseStep 830895 = 1246343) B1246343
theorem B830919 : Blo 830350 830919 := bstep (se 1 (by rfl) ⟨623189, by rfl⟩ : syracuseStep 830919 = 1246379) B1246379
theorem B830939 : Blo 830350 830939 := bstep (se 1 (by rfl) ⟨623204, by rfl⟩ : syracuseStep 830939 = 1246409) B1246409
theorem B831015 : Blo 830350 831015 := bstep (se 1 (by rfl) ⟨623261, by rfl⟩ : syracuseStep 831015 = 1246523) B1246523
theorem B831055 : Blo 830350 831055 := bstep (se 1 (by rfl) ⟨623291, by rfl⟩ : syracuseStep 831055 = 1246583) B1246583
theorem B831071 : Blo 830350 831071 := bstep (se 1 (by rfl) ⟨623303, by rfl⟩ : syracuseStep 831071 = 1246607) B1246607
theorem B831099 : Blo 830350 831099 := bstep (se 1 (by rfl) ⟨623324, by rfl⟩ : syracuseStep 831099 = 1246649) B1246649
theorem B831151 : Blo 830350 831151 := bstep (se 1 (by rfl) ⟨623363, by rfl⟩ : syracuseStep 831151 = 1246727) B1246727
theorem B831175 : Blo 830350 831175 := bstep (se 1 (by rfl) ⟨623381, by rfl⟩ : syracuseStep 831175 = 1246763) B1246763
theorem B831195 : Blo 830350 831195 := bstep (se 1 (by rfl) ⟨623396, by rfl⟩ : syracuseStep 831195 = 1246793) B1246793
theorem B18034397 : Blo 830350 18034397 := bstep (se 3 (by rfl) ⟨3381449, by rfl⟩ : syracuseStep 18034397 = 6762899) B6762899
theorem B4206329 : Blo 830350 4206329 := bstep (se 2 (by rfl) ⟨1577373, by rfl⟩ : syracuseStep 4206329 = 3154747) B3154747
theorem B831271 : Blo 830350 831271 := bstep (se 1 (by rfl) ⟨623453, by rfl⟩ : syracuseStep 831271 = 1246907) B1246907
theorem B831311 : Blo 830350 831311 := bstep (se 1 (by rfl) ⟨623483, by rfl⟩ : syracuseStep 831311 = 1246967) B1246967
theorem B831327 : Blo 830350 831327 := bstep (se 1 (by rfl) ⟨623495, by rfl⟩ : syracuseStep 831327 = 1246991) B1246991
theorem B831355 : Blo 830350 831355 := bstep (se 1 (by rfl) ⟨623516, by rfl⟩ : syracuseStep 831355 = 1247033) B1247033
theorem B831407 : Blo 830350 831407 := bstep (se 1 (by rfl) ⟨623555, by rfl⟩ : syracuseStep 831407 = 1247111) B1247111
theorem B831431 : Blo 830350 831431 := bstep (se 1 (by rfl) ⟨623573, by rfl⟩ : syracuseStep 831431 = 1247147) B1247147
theorem B831451 : Blo 830350 831451 := bstep (se 1 (by rfl) ⟨623588, by rfl⟩ : syracuseStep 831451 = 1247177) B1247177
theorem B831527 : Blo 830350 831527 := bstep (se 1 (by rfl) ⟨623645, by rfl⟩ : syracuseStep 831527 = 1247291) B1247291
theorem B831567 : Blo 830350 831567 := bstep (se 1 (by rfl) ⟨623675, by rfl⟩ : syracuseStep 831567 = 1247351) B1247351
theorem B831583 : Blo 830350 831583 := bstep (se 1 (by rfl) ⟨623687, by rfl⟩ : syracuseStep 831583 = 1247375) B1247375
theorem B831611 : Blo 830350 831611 := bstep (se 1 (by rfl) ⟨623708, by rfl⟩ : syracuseStep 831611 = 1247417) B1247417
theorem B831663 : Blo 830350 831663 := bstep (se 1 (by rfl) ⟨623747, by rfl⟩ : syracuseStep 831663 = 1247495) B1247495
theorem B831687 : Blo 830350 831687 := bstep (se 1 (by rfl) ⟨623765, by rfl⟩ : syracuseStep 831687 = 1247531) B1247531
theorem B831707 : Blo 830350 831707 := bstep (se 1 (by rfl) ⟨623780, by rfl⟩ : syracuseStep 831707 = 1247561) B1247561
theorem B831783 : Blo 830350 831783 := bstep (se 1 (by rfl) ⟨623837, by rfl⟩ : syracuseStep 831783 = 1247675) B1247675
theorem B831823 : Blo 830350 831823 := bstep (se 1 (by rfl) ⟨623867, by rfl⟩ : syracuseStep 831823 = 1247735) B1247735
theorem B831839 : Blo 830350 831839 := bstep (se 1 (by rfl) ⟨623879, by rfl⟩ : syracuseStep 831839 = 1247759) B1247759
theorem B831867 : Blo 830350 831867 := bstep (se 1 (by rfl) ⟨623900, by rfl⟩ : syracuseStep 831867 = 1247801) B1247801
theorem B4206977 : Blo 830350 4206977 := bstep (se 2 (by rfl) ⟨1577616, by rfl⟩ : syracuseStep 4206977 = 3155233) B3155233
theorem B831919 : Blo 830350 831919 := bstep (se 1 (by rfl) ⟨623939, by rfl⟩ : syracuseStep 831919 = 1247879) B1247879
theorem B831943 : Blo 830350 831943 := bstep (se 1 (by rfl) ⟨623957, by rfl⟩ : syracuseStep 831943 = 1247915) B1247915
theorem B1683931 : Blo 830350 1683931 := bstep (se 1 (by rfl) ⟨1262948, by rfl⟩ : syracuseStep 1683931 = 2525897) B2525897
theorem B831963 : Blo 830350 831963 := bstep (se 1 (by rfl) ⟨623972, by rfl⟩ : syracuseStep 831963 = 1247945) B1247945
theorem B832039 : Blo 830350 832039 := bstep (se 1 (by rfl) ⟨624029, by rfl⟩ : syracuseStep 832039 = 1248059) B1248059
theorem B2404903 : Blo 830350 2404903 := bstep (se 1 (by rfl) ⟨1803677, by rfl⟩ : syracuseStep 2404903 = 3607355) B3607355
theorem B832079 : Blo 830350 832079 := bstep (se 1 (by rfl) ⟨624059, by rfl⟩ : syracuseStep 832079 = 1248119) B1248119
theorem B832095 : Blo 830350 832095 := bstep (se 1 (by rfl) ⟨624071, by rfl⟩ : syracuseStep 832095 = 1248143) B1248143
theorem B832123 : Blo 830350 832123 := bstep (se 1 (by rfl) ⟨624092, by rfl⟩ : syracuseStep 832123 = 1248185) B1248185
theorem B2994835 : Blo 830350 2994835 := bstep (se 1 (by rfl) ⟨2246126, by rfl⟩ : syracuseStep 2994835 = 4492253) B4492253
theorem B832175 : Blo 830350 832175 := bstep (se 1 (by rfl) ⟨624131, by rfl⟩ : syracuseStep 832175 = 1248263) B1248263
theorem B53916353 : Blo 830350 53916353 := bstep (se 2 (by rfl) ⟨20218632, by rfl⟩ : syracuseStep 53916353 = 40437265) B40437265
theorem B832199 : Blo 830350 832199 := bstep (se 1 (by rfl) ⟨624149, by rfl⟩ : syracuseStep 832199 = 1248299) B1248299
theorem B2110151 : Blo 830350 2110151 := bstep (se 1 (by rfl) ⟨1582613, by rfl⟩ : syracuseStep 2110151 = 3165227) B3165227
theorem B3846865 : Blo 830350 3846865 := bstep (se 2 (by rfl) ⟨1442574, by rfl⟩ : syracuseStep 3846865 = 2885149) B2885149
theorem B832219 : Blo 830350 832219 := bstep (se 1 (by rfl) ⟨624164, by rfl⟩ : syracuseStep 832219 = 1248329) B1248329
theorem B832295 : Blo 830350 832295 := bstep (se 1 (by rfl) ⟨624221, by rfl⟩ : syracuseStep 832295 = 1248443) B1248443
theorem B23966513 : Blo 830350 23966513 := bstep (se 2 (by rfl) ⟨8987442, by rfl⟩ : syracuseStep 23966513 = 17974885) B17974885
theorem B832335 : Blo 830350 832335 := bstep (se 1 (by rfl) ⟨624251, by rfl⟩ : syracuseStep 832335 = 1248503) B1248503
theorem B1684319 : Blo 830350 1684319 := bstep (se 1 (by rfl) ⟨1263239, by rfl⟩ : syracuseStep 1684319 = 2526479) B2526479
theorem B832351 : Blo 830350 832351 := bstep (se 1 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 832351 = 1248527) B1248527
theorem B832379 : Blo 830350 832379 := bstep (se 1 (by rfl) ⟨624284, by rfl⟩ : syracuseStep 832379 = 1248569) B1248569
theorem B832431 : Blo 830350 832431 := bstep (se 1 (by rfl) ⟨624323, by rfl⟩ : syracuseStep 832431 = 1248647) B1248647
theorem B832455 : Blo 830350 832455 := bstep (se 1 (by rfl) ⟨624341, by rfl⟩ : syracuseStep 832455 = 1248683) B1248683
theorem B832475 : Blo 830350 832475 := bstep (se 1 (by rfl) ⟨624356, by rfl⟩ : syracuseStep 832475 = 1248713) B1248713
theorem B832551 : Blo 830350 832551 := bstep (se 1 (by rfl) ⟨624413, by rfl⟩ : syracuseStep 832551 = 1248827) B1248827
theorem B18035779 : Blo 830350 18035779 := bstep (se 1 (by rfl) ⟨13526834, by rfl⟩ : syracuseStep 18035779 = 27053669) B27053669
theorem B832591 : Blo 830350 832591 := bstep (se 1 (by rfl) ⟨624443, by rfl⟩ : syracuseStep 832591 = 1248887) B1248887
theorem B3159121 : Blo 830350 3159121 := bstep (se 2 (by rfl) ⟨1184670, by rfl⟩ : syracuseStep 3159121 = 2369341) B2369341
theorem B832607 : Blo 830350 832607 := bstep (se 1 (by rfl) ⟨624455, by rfl⟩ : syracuseStep 832607 = 1248911) B1248911
theorem B832635 : Blo 830350 832635 := bstep (se 1 (by rfl) ⟨624476, by rfl⟩ : syracuseStep 832635 = 1248953) B1248953
theorem B4207787 : Blo 830350 4207787 := bstep (se 1 (by rfl) ⟨3155840, by rfl⟩ : syracuseStep 4207787 = 6311681) B6311681
theorem B832687 : Blo 830350 832687 := bstep (se 1 (by rfl) ⟨624515, by rfl⟩ : syracuseStep 832687 = 1249031) B1249031
theorem B832711 : Blo 830350 832711 := bstep (se 1 (by rfl) ⟨624533, by rfl⟩ : syracuseStep 832711 = 1249067) B1249067
theorem B832731 : Blo 830350 832731 := bstep (se 1 (by rfl) ⟨624548, by rfl⟩ : syracuseStep 832731 = 1249097) B1249097
theorem B832807 : Blo 830350 832807 := bstep (se 1 (by rfl) ⟨624605, by rfl⟩ : syracuseStep 832807 = 1249211) B1249211
theorem B832847 : Blo 830350 832847 := bstep (se 1 (by rfl) ⟨624635, by rfl⟩ : syracuseStep 832847 = 1249271) B1249271
theorem B832863 : Blo 830350 832863 := bstep (se 1 (by rfl) ⟨624647, by rfl⟩ : syracuseStep 832863 = 1249295) B1249295
theorem B832891 : Blo 830350 832891 := bstep (se 1 (by rfl) ⟨624668, by rfl⟩ : syracuseStep 832891 = 1249337) B1249337
theorem B3159425 : Blo 830350 3159425 := bstep (se 2 (by rfl) ⟨1184784, by rfl⟩ : syracuseStep 3159425 = 2369569) B2369569
theorem B4732303 : Blo 830350 4732303 := bstep (se 1 (by rfl) ⟨3549227, by rfl⟩ : syracuseStep 4732303 = 7098455) B7098455
theorem B832943 : Blo 830350 832943 := bstep (se 1 (by rfl) ⟨624707, by rfl⟩ : syracuseStep 832943 = 1249415) B1249415
theorem B832967 : Blo 830350 832967 := bstep (se 1 (by rfl) ⟨624725, by rfl⟩ : syracuseStep 832967 = 1249451) B1249451
theorem B832987 : Blo 830350 832987 := bstep (se 1 (by rfl) ⟨624740, by rfl⟩ : syracuseStep 832987 = 1249481) B1249481
theorem B833063 : Blo 830350 833063 := bstep (se 1 (by rfl) ⟨624797, by rfl⟩ : syracuseStep 833063 = 1249595) B1249595
theorem B833103 : Blo 830350 833103 := bstep (se 1 (by rfl) ⟨624827, by rfl⟩ : syracuseStep 833103 = 1249655) B1249655
theorem B833119 : Blo 830350 833119 := bstep (se 1 (by rfl) ⟨624839, by rfl⟩ : syracuseStep 833119 = 1249679) B1249679
theorem B833147 : Blo 830350 833147 := bstep (se 1 (by rfl) ⟨624860, by rfl⟩ : syracuseStep 833147 = 1249721) B1249721
theorem B4208273 : Blo 830350 4208273 := bstep (se 2 (by rfl) ⟨1578102, by rfl⟩ : syracuseStep 4208273 = 3156205) B3156205
theorem B833199 : Blo 830350 833199 := bstep (se 1 (by rfl) ⟨624899, by rfl⟩ : syracuseStep 833199 = 1249799) B1249799
theorem B4503239 : Blo 830350 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B833223 : Blo 830350 833223 := bstep (se 1 (by rfl) ⟨624917, by rfl⟩ : syracuseStep 833223 = 1249835) B1249835
theorem B833243 : Blo 830350 833243 := bstep (se 1 (by rfl) ⟨624932, by rfl⟩ : syracuseStep 833243 = 1249865) B1249865
theorem B833319 : Blo 830350 833319 := bstep (se 1 (by rfl) ⟨624989, by rfl⟩ : syracuseStep 833319 = 1249979) B1249979
theorem B3553091 : Blo 830350 3553091 := bstep (se 1 (by rfl) ⟨2664818, by rfl⟩ : syracuseStep 3553091 = 5329637) B5329637
theorem B3159881 : Blo 830350 3159881 := bstep (se 2 (by rfl) ⟨1184955, by rfl⟩ : syracuseStep 3159881 = 2369911) B2369911
theorem B2111305 : Blo 830350 2111305 := bstep (se 2 (by rfl) ⟨791739, by rfl⟩ : syracuseStep 2111305 = 1583479) B1583479
theorem B833359 : Blo 830350 833359 := bstep (se 1 (by rfl) ⟨625019, by rfl⟩ : syracuseStep 833359 = 1250039) B1250039
theorem B2701151 : Blo 830350 2701151 := bstep (se 1 (by rfl) ⟨2025863, by rfl⟩ : syracuseStep 2701151 = 4051727) B4051727
theorem B833375 : Blo 830350 833375 := bstep (se 1 (by rfl) ⟨625031, by rfl⟩ : syracuseStep 833375 = 1250063) B1250063
theorem B833403 : Blo 830350 833403 := bstep (se 1 (by rfl) ⟨625052, by rfl⟩ : syracuseStep 833403 = 1250105) B1250105
theorem B833455 : Blo 830350 833455 := bstep (se 1 (by rfl) ⟨625091, by rfl⟩ : syracuseStep 833455 = 1250183) B1250183
theorem B833479 : Blo 830350 833479 := bstep (se 1 (by rfl) ⟨625109, by rfl⟩ : syracuseStep 833479 = 1250219) B1250219
theorem B833499 : Blo 830350 833499 := bstep (se 1 (by rfl) ⟨625124, by rfl⟩ : syracuseStep 833499 = 1250249) B1250249
theorem B3160079 : Blo 830350 3160079 := bstep (se 1 (by rfl) ⟨2370059, by rfl⟩ : syracuseStep 3160079 = 4740119) B4740119
theorem B833575 : Blo 830350 833575 := bstep (se 1 (by rfl) ⟨625181, by rfl⟩ : syracuseStep 833575 = 1250363) B1250363
theorem B6305849 : Blo 830350 6305849 := bstep (se 2 (by rfl) ⟨2364693, by rfl⟩ : syracuseStep 6305849 = 4729387) B4729387
theorem B833615 : Blo 830350 833615 := bstep (se 1 (by rfl) ⟨625211, by rfl⟩ : syracuseStep 833615 = 1250423) B1250423
theorem B833631 : Blo 830350 833631 := bstep (se 1 (by rfl) ⟨625223, by rfl⟩ : syracuseStep 833631 = 1250447) B1250447
theorem B833659 : Blo 830350 833659 := bstep (se 1 (by rfl) ⟨625244, by rfl⟩ : syracuseStep 833659 = 1250489) B1250489
theorem B833711 : Blo 830350 833711 := bstep (se 1 (by rfl) ⟨625283, by rfl⟩ : syracuseStep 833711 = 1250567) B1250567
theorem B833735 : Blo 830350 833735 := bstep (se 1 (by rfl) ⟨625301, by rfl⟩ : syracuseStep 833735 = 1250603) B1250603
theorem B833755 : Blo 830350 833755 := bstep (se 1 (by rfl) ⟨625316, by rfl⟩ : syracuseStep 833755 = 1250633) B1250633
theorem B833831 : Blo 830350 833831 := bstep (se 1 (by rfl) ⟨625373, by rfl⟩ : syracuseStep 833831 = 1250747) B1250747
theorem B833871 : Blo 830350 833871 := bstep (se 1 (by rfl) ⟨625403, by rfl⟩ : syracuseStep 833871 = 1250807) B1250807
theorem B534034781 : Blo 830350 534034781 := bstep (se 3 (by rfl) ⟨100131521, by rfl⟩ : syracuseStep 534034781 = 200263043) B200263043
theorem B833887 : Blo 830350 833887 := bstep (se 1 (by rfl) ⟨625415, by rfl⟩ : syracuseStep 833887 = 1250831) B1250831
theorem B833915 : Blo 830350 833915 := bstep (se 1 (by rfl) ⟨625436, by rfl⟩ : syracuseStep 833915 = 1250873) B1250873
theorem B833967 : Blo 830350 833967 := bstep (se 1 (by rfl) ⟨625475, by rfl⟩ : syracuseStep 833967 = 1250951) B1250951
theorem B833991 : Blo 830350 833991 := bstep (se 1 (by rfl) ⟨625493, by rfl⟩ : syracuseStep 833991 = 1250987) B1250987
theorem B834011 : Blo 830350 834011 := bstep (se 1 (by rfl) ⟨625508, by rfl⟩ : syracuseStep 834011 = 1251017) B1251017
theorem B12139037 : Blo 830350 12139037 := bstep (se 3 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 12139037 = 4552139) B4552139
theorem B834087 : Blo 830350 834087 := bstep (se 1 (by rfl) ⟨625565, by rfl⟩ : syracuseStep 834087 = 1251131) B1251131
theorem B834127 : Blo 830350 834127 := bstep (se 1 (by rfl) ⟨625595, by rfl⟩ : syracuseStep 834127 = 1251191) B1251191
theorem B834143 : Blo 830350 834143 := bstep (se 1 (by rfl) ⟨625607, by rfl⟩ : syracuseStep 834143 = 1251215) B1251215
theorem B834171 : Blo 830350 834171 := bstep (se 1 (by rfl) ⟨625628, by rfl⟩ : syracuseStep 834171 = 1251257) B1251257
theorem B834223 : Blo 830350 834223 := bstep (se 1 (by rfl) ⟨625667, by rfl⟩ : syracuseStep 834223 = 1251335) B1251335
theorem B2374343 : Blo 830350 2374343 := bstep (se 1 (by rfl) ⟨1780757, by rfl⟩ : syracuseStep 2374343 = 3561515) B3561515
theorem B834247 : Blo 830350 834247 := bstep (se 1 (by rfl) ⟨625685, by rfl⟩ : syracuseStep 834247 = 1251371) B1251371
theorem B834267 : Blo 830350 834267 := bstep (se 1 (by rfl) ⟨625700, by rfl⟩ : syracuseStep 834267 = 1251401) B1251401
theorem B834343 : Blo 830350 834343 := bstep (se 1 (by rfl) ⟨625757, by rfl⟩ : syracuseStep 834343 = 1251515) B1251515
theorem B2669431 : Blo 830350 2669431 := bstep (se 1 (by rfl) ⟨2002073, by rfl⟩ : syracuseStep 2669431 = 4004147) B4004147
theorem B1424827 : Blo 830350 1424827 := bstep (se 1 (by rfl) ⟨1068620, by rfl⟩ : syracuseStep 1424827 = 2137241) B2137241
theorem B998951 : Blo 830350 998951 := bstep (se 1 (by rfl) ⟨749213, by rfl⟩ : syracuseStep 998951 = 1498427) B1498427
theorem B2702945 : Blo 830350 2702945 := bstep (se 2 (by rfl) ⟨1013604, by rfl⟩ : syracuseStep 2702945 = 2027209) B2027209
theorem B4210541 : Blo 830350 4210541 := bstep (se 3 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 4210541 = 1578953) B1578953
theorem B6307793 : Blo 830350 6307793 := bstep (se 2 (by rfl) ⟨2365422, by rfl⟩ : syracuseStep 6307793 = 4730845) B4730845
theorem B4210703 : Blo 830350 4210703 := bstep (se 1 (by rfl) ⟨3158027, by rfl⟩ : syracuseStep 4210703 = 6316055) B6316055
theorem B1687799 : Blo 830350 1687799 := bstep (se 1 (by rfl) ⟨1265849, by rfl⟩ : syracuseStep 1687799 = 2531699) B2531699
theorem B13517117 : Blo 830350 13517117 := bstep (se 3 (by rfl) ⟨2534459, by rfl⟩ : syracuseStep 13517117 = 5068919) B5068919
theorem B1687969 : Blo 830350 1687969 := bstep (se 2 (by rfl) ⟨632988, by rfl⟩ : syracuseStep 1687969 = 1265977) B1265977
theorem B2802707 : Blo 830350 2802707 := bstep (se 1 (by rfl) ⟨2102030, by rfl⟩ : syracuseStep 2802707 = 4204061) B4204061
theorem B934951 : Blo 830350 934951 := bstep (se 1 (by rfl) ⟨701213, by rfl⟩ : syracuseStep 934951 = 1402427) B1402427
theorem B2803031 : Blo 830350 2803031 := bstep (se 1 (by rfl) ⟨2102273, by rfl⟩ : syracuseStep 2803031 = 4204547) B4204547
theorem B2672327 : Blo 830350 2672327 := bstep (se 1 (by rfl) ⟨2004245, by rfl⟩ : syracuseStep 2672327 = 4008491) B4008491
theorem B8210219 : Blo 830350 8210219 := bstep (se 1 (by rfl) ⟨6157664, by rfl⟩ : syracuseStep 8210219 = 12315329) B12315329
theorem B2804111 : Blo 830350 2804111 := bstep (se 1 (by rfl) ⟨2103083, by rfl⟩ : syracuseStep 2804111 = 4206167) B4206167
theorem B936571 : Blo 830350 936571 := bstep (se 1 (by rfl) ⟨702428, by rfl⟩ : syracuseStep 936571 = 1404857) B1404857
theorem B4213457 : Blo 830350 4213457 := bstep (se 2 (by rfl) ⟨1580046, by rfl⟩ : syracuseStep 4213457 = 3160093) B3160093
theorem B2804435 : Blo 830350 2804435 := bstep (se 1 (by rfl) ⟨2103326, by rfl⟩ : syracuseStep 2804435 = 4206653) B4206653
theorem B1330103 : Blo 830350 1330103 := bstep (se 1 (by rfl) ⟨997577, by rfl⟩ : syracuseStep 1330103 = 1995155) B1995155
theorem B1264567 : Blo 830350 1264567 := bstep (se 1 (by rfl) ⟨948425, by rfl⟩ : syracuseStep 1264567 = 1896851) B1896851
theorem B937039 : Blo 830350 937039 := bstep (se 1 (by rfl) ⟨702779, by rfl⟩ : syracuseStep 937039 = 1405559) B1405559
theorem B1690823 : Blo 830350 1690823 := bstep (se 1 (by rfl) ⟨1268117, by rfl⟩ : syracuseStep 1690823 = 2536235) B2536235
theorem B1330615 : Blo 830350 1330615 := bstep (se 1 (by rfl) ⟨997961, by rfl⟩ : syracuseStep 1330615 = 1995923) B1995923
theorem B937435 : Blo 830350 937435 := bstep (se 1 (by rfl) ⟨703076, by rfl⟩ : syracuseStep 937435 = 1406153) B1406153
theorem B5492423 : Blo 830350 5492423 := bstep (se 1 (by rfl) ⟨4119317, by rfl⟩ : syracuseStep 5492423 = 8238635) B8238635
theorem B3165911 : Blo 830350 3165911 := bstep (se 1 (by rfl) ⟨2374433, by rfl⟩ : syracuseStep 3165911 = 4748867) B4748867
theorem B8015597 : Blo 830350 8015597 := bstep (se 3 (by rfl) ⟨1502924, by rfl⟩ : syracuseStep 8015597 = 3005849) B3005849
theorem B2805623 : Blo 830350 2805623 := bstep (se 1 (by rfl) ⟨2104217, by rfl⟩ : syracuseStep 2805623 = 4208435) B4208435
theorem B3002273 : Blo 830350 3002273 := bstep (se 2 (by rfl) ⟨1125852, by rfl⟩ : syracuseStep 3002273 = 2251705) B2251705
theorem B937903 : Blo 830350 937903 := bstep (se 1 (by rfl) ⟨703427, by rfl⟩ : syracuseStep 937903 = 1406855) B1406855
theorem B2805839 : Blo 830350 2805839 := bstep (se 1 (by rfl) ⟨2104379, by rfl⟩ : syracuseStep 2805839 = 4208759) B4208759
theorem B3002447 : Blo 830350 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B938335 : Blo 830350 938335 := bstep (se 1 (by rfl) ⟨703751, by rfl⟩ : syracuseStep 938335 = 1407503) B1407503
theorem B2806217 : Blo 830350 2806217 := bstep (se 2 (by rfl) ⟨1052331, by rfl⟩ : syracuseStep 2806217 = 2104663) B2104663
theorem B4739593 : Blo 830350 4739593 := bstep (se 2 (by rfl) ⟨1777347, by rfl⟩ : syracuseStep 4739593 = 3554695) B3554695
theorem B2806487 : Blo 830350 2806487 := bstep (se 1 (by rfl) ⟨2104865, by rfl⟩ : syracuseStep 2806487 = 4209731) B4209731
theorem B2741111 : Blo 830350 2741111 := bstep (se 1 (by rfl) ⟨2055833, by rfl⟩ : syracuseStep 2741111 = 4111667) B4111667
theorem B2806703 : Blo 830350 2806703 := bstep (se 1 (by rfl) ⟨2105027, by rfl⟩ : syracuseStep 2806703 = 4210055) B4210055
theorem B4215887 : Blo 830350 4215887 := bstep (se 1 (by rfl) ⟨3161915, by rfl⟩ : syracuseStep 4215887 = 6323831) B6323831
theorem B2249975 : Blo 830350 2249975 := bstep (se 1 (by rfl) ⟨1687481, by rfl⟩ : syracuseStep 2249975 = 3374963) B3374963
theorem B1496495 : Blo 830350 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B4216535 : Blo 830350 4216535 := bstep (se 1 (by rfl) ⟨3162401, by rfl⟩ : syracuseStep 4216535 = 6324803) B6324803
theorem B4741051 : Blo 830350 4741051 := bstep (se 1 (by rfl) ⟨3555788, by rfl⟩ : syracuseStep 4741051 = 7111577) B7111577
theorem B7100369 : Blo 830350 7100369 := bstep (se 2 (by rfl) ⟨2662638, by rfl⟩ : syracuseStep 7100369 = 5325277) B5325277
theorem B9493037 : Blo 830350 9493037 := bstep (se 3 (by rfl) ⟨1779944, by rfl⟩ : syracuseStep 9493037 = 3559889) B3559889
theorem B1333883 : Blo 830350 1333883 := bstep (se 1 (by rfl) ⟨1000412, by rfl⟩ : syracuseStep 1333883 = 2000825) B2000825
theorem B6740813 : Blo 830350 6740813 := bstep (se 3 (by rfl) ⟨1263902, by rfl⟩ : syracuseStep 6740813 = 2527805) B2527805
theorem B1334395 : Blo 830350 1334395 := bstep (se 1 (by rfl) ⟨1000796, by rfl⟩ : syracuseStep 1334395 = 2001593) B2001593
theorem B2809079 : Blo 830350 2809079 := bstep (se 1 (by rfl) ⟨2106809, by rfl⟩ : syracuseStep 2809079 = 4213619) B4213619
theorem B2809403 : Blo 830350 2809403 := bstep (se 1 (by rfl) ⟨2107052, by rfl⟩ : syracuseStep 2809403 = 4214105) B4214105
theorem B2809673 : Blo 830350 2809673 := bstep (se 2 (by rfl) ⟨1053627, by rfl⟩ : syracuseStep 2809673 = 2107255) B2107255
theorem B1335113 : Blo 830350 1335113 := bstep (se 2 (by rfl) ⟨500667, by rfl⟩ : syracuseStep 1335113 = 1001335) B1001335
theorem B1335215 : Blo 830350 1335215 := bstep (se 1 (by rfl) ⟨1001411, by rfl⟩ : syracuseStep 1335215 = 2002823) B2002823
theorem B6741953 : Blo 830350 6741953 := bstep (se 2 (by rfl) ⟨2528232, by rfl⟩ : syracuseStep 6741953 = 5056465) B5056465
theorem B14246117 : Blo 830350 14246117 := bstep (se 4 (by rfl) ⟨1335573, by rfl⟩ : syracuseStep 14246117 = 2671147) B2671147
theorem B1401401 : Blo 830350 1401401 := bstep (se 2 (by rfl) ⟨525525, by rfl⟩ : syracuseStep 1401401 = 1051051) B1051051
theorem B4219451 : Blo 830350 4219451 := bstep (se 1 (by rfl) ⟨3164588, by rfl⟩ : syracuseStep 4219451 = 6329177) B6329177
theorem B3040067 : Blo 830350 3040067 := bstep (se 1 (by rfl) ⟨2280050, by rfl⟩ : syracuseStep 3040067 = 4560101) B4560101
theorem B2810807 : Blo 830350 2810807 := bstep (se 1 (by rfl) ⟨2108105, by rfl⟩ : syracuseStep 2810807 = 4216211) B4216211
theorem B844763 : Blo 830350 844763 := bstep (se 1 (by rfl) ⟨633572, by rfl⟩ : syracuseStep 844763 = 1267145) B1267145
theorem B4220099 : Blo 830350 4220099 := bstep (se 1 (by rfl) ⟨3165074, by rfl⟩ : syracuseStep 4220099 = 6330149) B6330149
theorem B1402103 : Blo 830350 1402103 := bstep (se 1 (by rfl) ⟨1051577, by rfl⟩ : syracuseStep 1402103 = 2103155) B2103155
theorem B6743411 : Blo 830350 6743411 := bstep (se 1 (by rfl) ⟨5057558, by rfl⟩ : syracuseStep 6743411 = 10115117) B10115117
theorem B2254205 : Blo 830350 2254205 := bstep (se 3 (by rfl) ⟨422663, by rfl⟩ : syracuseStep 2254205 = 845327) B845327
theorem B6317513 : Blo 830350 6317513 := bstep (se 2 (by rfl) ⟨2369067, by rfl⟩ : syracuseStep 6317513 = 4738135) B4738135
theorem B2811401 : Blo 830350 2811401 := bstep (se 2 (by rfl) ⟨1054275, by rfl⟩ : syracuseStep 2811401 = 2108551) B2108551
theorem B1402447 : Blo 830350 1402447 := bstep (se 1 (by rfl) ⟨1051835, by rfl⟩ : syracuseStep 1402447 = 2103671) B2103671
theorem B2025083 : Blo 830350 2025083 := bstep (se 1 (by rfl) ⟨1518812, by rfl⟩ : syracuseStep 2025083 = 3037625) B3037625
theorem B16017041 : Blo 830350 16017041 := bstep (se 2 (by rfl) ⟨6006390, by rfl⟩ : syracuseStep 16017041 = 12012781) B12012781
theorem B4744925 : Blo 830350 4744925 := bstep (se 3 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 4744925 = 1779347) B1779347
theorem B1402697 : Blo 830350 1402697 := bstep (se 2 (by rfl) ⟨526011, by rfl⟩ : syracuseStep 1402697 = 1052023) B1052023
theorem B6744221 : Blo 830350 6744221 := bstep (se 3 (by rfl) ⟨1264541, by rfl⟩ : syracuseStep 6744221 = 2529083) B2529083
theorem B1403129 : Blo 830350 1403129 := bstep (se 2 (by rfl) ⟨526173, by rfl⟩ : syracuseStep 1403129 = 1052347) B1052347
theorem B76900661 : Blo 830350 76900661 := bstep (se 5 (by rfl) ⟨3604718, by rfl⟩ : syracuseStep 76900661 = 7209437) B7209437
theorem B26995031 : Blo 830350 26995031 := bstep (se 1 (by rfl) ⟨20246273, by rfl⟩ : syracuseStep 26995031 = 40492547) B40492547
theorem B2812265 : Blo 830350 2812265 := bstep (se 2 (by rfl) ⟨1054599, by rfl⟩ : syracuseStep 2812265 = 2109199) B2109199
theorem B1403311 : Blo 830350 1403311 := bstep (se 1 (by rfl) ⟨1052483, by rfl⟩ : syracuseStep 1403311 = 2104967) B2104967
theorem B1403399 : Blo 830350 1403399 := bstep (se 1 (by rfl) ⟨1052549, by rfl⟩ : syracuseStep 1403399 = 2105099) B2105099
theorem B3795665 : Blo 830350 3795665 := bstep (se 2 (by rfl) ⟨1423374, by rfl⟩ : syracuseStep 3795665 = 2846749) B2846749
theorem B18017099 : Blo 830350 18017099 := bstep (se 1 (by rfl) ⟨13512824, by rfl⟩ : syracuseStep 18017099 = 27025649) B27025649
theorem B1403743 : Blo 830350 1403743 := bstep (se 1 (by rfl) ⟨1052807, by rfl⟩ : syracuseStep 1403743 = 2105615) B2105615
theorem B5335915 : Blo 830350 5335915 := bstep (se 1 (by rfl) ⟨4001936, by rfl⟩ : syracuseStep 5335915 = 8003873) B8003873
theorem B7105427 : Blo 830350 7105427 := bstep (se 1 (by rfl) ⟨5329070, by rfl⟩ : syracuseStep 7105427 = 10658141) B10658141
theorem B1403831 : Blo 830350 1403831 := bstep (se 1 (by rfl) ⟨1052873, by rfl⟩ : syracuseStep 1403831 = 2105747) B2105747
theorem B2812859 : Blo 830350 2812859 := bstep (se 1 (by rfl) ⟨2109644, by rfl⟩ : syracuseStep 2812859 = 4219289) B4219289
theorem B3370099 : Blo 830350 3370099 := bstep (se 1 (by rfl) ⟨2527574, by rfl⟩ : syracuseStep 3370099 = 5055149) B5055149
theorem B13692077 : Blo 830350 13692077 := bstep (se 3 (by rfl) ⟨2567264, by rfl⟩ : syracuseStep 13692077 = 5134529) B5134529
theorem B5074319 : Blo 830350 5074319 := bstep (se 1 (by rfl) ⟨3805739, by rfl⟩ : syracuseStep 5074319 = 7611479) B7611479
theorem B1404425 : Blo 830350 1404425 := bstep (se 2 (by rfl) ⟨526659, by rfl⟩ : syracuseStep 1404425 = 1053319) B1053319
theorem B1404587 : Blo 830350 1404587 := bstep (se 1 (by rfl) ⟨1053440, by rfl⟩ : syracuseStep 1404587 = 2106881) B2106881
theorem B1601543 : Blo 830350 1601543 := bstep (se 1 (by rfl) ⟨1201157, by rfl⟩ : syracuseStep 1601543 = 2402315) B2402315
theorem B1404985 : Blo 830350 1404985 := bstep (se 2 (by rfl) ⟨526869, by rfl⟩ : syracuseStep 1404985 = 1053739) B1053739
theorem B13692989 : Blo 830350 13692989 := bstep (se 3 (by rfl) ⟨2567435, by rfl⟩ : syracuseStep 13692989 = 5134871) B5134871
theorem B1405127 : Blo 830350 1405127 := bstep (se 1 (by rfl) ⟨1053845, by rfl⟩ : syracuseStep 1405127 = 2107691) B2107691
theorem B1503443 : Blo 830350 1503443 := bstep (se 1 (by rfl) ⟨1127582, by rfl⟩ : syracuseStep 1503443 = 2255165) B2255165
theorem B1405289 : Blo 830350 1405289 := bstep (se 2 (by rfl) ⟨526983, by rfl⟩ : syracuseStep 1405289 = 1053967) B1053967
theorem B2814587 : Blo 830350 2814587 := bstep (se 1 (by rfl) ⟨2110940, by rfl⟩ : syracuseStep 2814587 = 4221881) B4221881
theorem B1405687 : Blo 830350 1405687 := bstep (se 1 (by rfl) ⟨1054265, by rfl⟩ : syracuseStep 1405687 = 2108531) B2108531
theorem B2814749 : Blo 830350 2814749 := bstep (se 3 (by rfl) ⟨527765, by rfl⟩ : syracuseStep 2814749 = 1055531) B1055531
theorem B1405883 : Blo 830350 1405883 := bstep (se 1 (by rfl) ⟨1054412, by rfl⟩ : syracuseStep 1405883 = 2108825) B2108825
theorem B1405991 : Blo 830350 1405991 := bstep (se 1 (by rfl) ⟨1054493, by rfl⟩ : syracuseStep 1405991 = 2108987) B2108987
theorem B10679363 : Blo 830350 10679363 := bstep (se 1 (by rfl) ⟨8009522, by rfl⟩ : syracuseStep 10679363 = 16019045) B16019045
theorem B19264715 : Blo 830350 19264715 := bstep (se 1 (by rfl) ⟨14448536, by rfl⟩ : syracuseStep 19264715 = 28897073) B28897073
theorem B1406281 : Blo 830350 1406281 := bstep (se 2 (by rfl) ⟨527355, by rfl⟩ : syracuseStep 1406281 = 1054711) B1054711
theorem B1406315 : Blo 830350 1406315 := bstep (se 1 (by rfl) ⟨1054736, by rfl⟩ : syracuseStep 1406315 = 2109473) B2109473
theorem B24016337 : Blo 830350 24016337 := bstep (se 2 (by rfl) ⟨9006126, by rfl⟩ : syracuseStep 24016337 = 18012253) B18012253
theorem B2815451 : Blo 830350 2815451 := bstep (se 1 (by rfl) ⟨2111588, by rfl⟩ : syracuseStep 2815451 = 4223177) B4223177
theorem B1406713 : Blo 830350 1406713 := bstep (se 2 (by rfl) ⟨527517, by rfl⟩ : syracuseStep 1406713 = 1055035) B1055035
theorem B5994283 : Blo 830350 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B21297005 : Blo 830350 21297005 := bstep (se 3 (by rfl) ⟨3993188, by rfl⟩ : syracuseStep 21297005 = 7986377) B7986377
theorem B1406983 : Blo 830350 1406983 := bstep (se 1 (by rfl) ⟨1055237, by rfl⟩ : syracuseStep 1406983 = 2110475) B2110475
theorem B1407415 : Blo 830350 1407415 := bstep (se 1 (by rfl) ⟨1055561, by rfl⟩ : syracuseStep 1407415 = 2111123) B2111123
theorem B1407611 : Blo 830350 1407611 := bstep (se 1 (by rfl) ⟨1055708, by rfl⟩ : syracuseStep 1407611 = 2111417) B2111417
theorem B9862337 : Blo 830350 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B6749477 : Blo 830350 6749477 := bstep (se 4 (by rfl) ⟨632763, by rfl⟩ : syracuseStep 6749477 = 1265527) B1265527
theorem B4750757 : Blo 830350 4750757 := bstep (se 4 (by rfl) ⟨445383, by rfl⟩ : syracuseStep 4750757 = 890767) B890767
theorem B1080911 : Blo 830350 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B9011411 : Blo 830350 9011411 := bstep (se 1 (by rfl) ⟨6758558, by rfl⟩ : syracuseStep 9011411 = 13517117) B13517117
theorem B1802569 : Blo 830350 1802569 := bstep (se 2 (by rfl) ⟨675963, by rfl⟩ : syracuseStep 1802569 = 1351927) B1351927
theorem B1245551 : Blo 830350 1245551 := bstep (se 1 (by rfl) ⟨934163, by rfl⟩ : syracuseStep 1245551 = 1868327) B1868327
theorem B1245767 : Blo 830350 1245767 := bstep (se 1 (by rfl) ⟨934325, by rfl⟩ : syracuseStep 1245767 = 1868651) B1868651
theorem B1245803 : Blo 830350 1245803 := bstep (se 1 (by rfl) ⟨934352, by rfl⟩ : syracuseStep 1245803 = 1868705) B1868705
theorem B1868471 : Blo 830350 1868471 := bstep (se 1 (by rfl) ⟨1401353, by rfl⟩ : syracuseStep 1868471 = 2802707) B2802707
theorem B1246031 : Blo 830350 1246031 := bstep (se 1 (by rfl) ⟨934523, by rfl⟩ : syracuseStep 1246031 = 1869047) B1869047
theorem B1868687 : Blo 830350 1868687 := bstep (se 1 (by rfl) ⟨1401515, by rfl⟩ : syracuseStep 1868687 = 2803031) B2803031
theorem B3802087 : Blo 830350 3802087 := bstep (se 1 (by rfl) ⟨2851565, by rfl⟩ : syracuseStep 3802087 = 5703131) B5703131
theorem B1246427 : Blo 830350 1246427 := bstep (se 1 (by rfl) ⟨934820, by rfl⟩ : syracuseStep 1246427 = 1869641) B1869641
theorem B5768491 : Blo 830350 5768491 := bstep (se 1 (by rfl) ⟨4326368, by rfl⟩ : syracuseStep 5768491 = 8652737) B8652737
theorem B1246601 : Blo 830350 1246601 := bstep (se 2 (by rfl) ⟨467475, by rfl⟩ : syracuseStep 1246601 = 934951) B934951
theorem B1869407 : Blo 830350 1869407 := bstep (se 1 (by rfl) ⟨1402055, by rfl⟩ : syracuseStep 1869407 = 2804111) B2804111
theorem B10815095 : Blo 830350 10815095 := bstep (se 1 (by rfl) ⟨8111321, by rfl⟩ : syracuseStep 10815095 = 16222643) B16222643
theorem B1246955 : Blo 830350 1246955 := bstep (se 1 (by rfl) ⟨935216, by rfl⟩ : syracuseStep 1246955 = 1870433) B1870433
theorem B1869623 : Blo 830350 1869623 := bstep (se 1 (by rfl) ⟨1402217, by rfl⟩ : syracuseStep 1869623 = 2804435) B2804435
theorem B886735 : Blo 830350 886735 := bstep (se 1 (by rfl) ⟨665051, by rfl⟩ : syracuseStep 886735 = 1330103) B1330103
theorem B1247183 : Blo 830350 1247183 := bstep (se 1 (by rfl) ⟨935387, by rfl⟩ : syracuseStep 1247183 = 1870775) B1870775
theorem B1869929 : Blo 830350 1869929 := bstep (se 2 (by rfl) ⟨701223, by rfl⟩ : syracuseStep 1869929 = 1402447) B1402447
theorem B16255241 : Blo 830350 16255241 := bstep (se 2 (by rfl) ⟨6095715, by rfl⟩ : syracuseStep 16255241 = 12191431) B12191431
theorem B1247579 : Blo 830350 1247579 := bstep (se 1 (by rfl) ⟨935684, by rfl⟩ : syracuseStep 1247579 = 1871369) B1871369
theorem B5343731 : Blo 830350 5343731 := bstep (se 1 (by rfl) ⟨4007798, by rfl⟩ : syracuseStep 5343731 = 8015597) B8015597
theorem B1247807 : Blo 830350 1247807 := bstep (se 1 (by rfl) ⟨935855, by rfl⟩ : syracuseStep 1247807 = 1871711) B1871711
theorem B1870415 : Blo 830350 1870415 := bstep (se 1 (by rfl) ⟨1402811, by rfl⟩ : syracuseStep 1870415 = 2805623) B2805623
theorem B2001515 : Blo 830350 2001515 := bstep (se 1 (by rfl) ⟨1501136, by rfl⟩ : syracuseStep 2001515 = 3002273) B3002273
theorem B1051319 : Blo 830350 1051319 := bstep (se 1 (by rfl) ⟨788489, by rfl⟩ : syracuseStep 1051319 = 1576979) B1576979
theorem B1247927 : Blo 830350 1247927 := bstep (se 1 (by rfl) ⟨935945, by rfl⟩ : syracuseStep 1247927 = 1871891) B1871891
theorem B1870559 : Blo 830350 1870559 := bstep (se 1 (by rfl) ⟨1402919, by rfl⟩ : syracuseStep 1870559 = 2805839) B2805839
theorem B1051471 : Blo 830350 1051471 := bstep (se 1 (by rfl) ⟨788603, by rfl⟩ : syracuseStep 1051471 = 1577207) B1577207
theorem B1248155 : Blo 830350 1248155 := bstep (se 1 (by rfl) ⟨936116, by rfl⟩ : syracuseStep 1248155 = 1872233) B1872233
theorem B1870811 : Blo 830350 1870811 := bstep (se 1 (by rfl) ⟨1403108, by rfl⟩ : syracuseStep 1870811 = 2806217) B2806217
theorem B1870991 : Blo 830350 1870991 := bstep (se 1 (by rfl) ⟨1403243, by rfl⟩ : syracuseStep 1870991 = 2806487) B2806487
theorem B1871081 : Blo 830350 1871081 := bstep (se 2 (by rfl) ⟨701655, by rfl⟩ : syracuseStep 1871081 = 1403311) B1403311
theorem B1871135 : Blo 830350 1871135 := bstep (se 1 (by rfl) ⟨1403351, by rfl⟩ : syracuseStep 1871135 = 2806703) B2806703
theorem B1248551 : Blo 830350 1248551 := bstep (se 1 (by rfl) ⟨936413, by rfl⟩ : syracuseStep 1248551 = 1872827) B1872827
theorem B5999933 : Blo 830350 5999933 := bstep (se 3 (by rfl) ⟨1124987, by rfl⟩ : syracuseStep 5999933 = 2249975) B2249975
theorem B1183099 : Blo 830350 1183099 := bstep (se 1 (by rfl) ⟨887324, by rfl⟩ : syracuseStep 1183099 = 1774649) B1774649
theorem B1248635 : Blo 830350 1248635 := bstep (se 1 (by rfl) ⟨936476, by rfl⟩ : syracuseStep 1248635 = 1872953) B1872953
theorem B1248761 : Blo 830350 1248761 := bstep (se 2 (by rfl) ⟨468285, by rfl⟩ : syracuseStep 1248761 = 936571) B936571
theorem B4001339 : Blo 830350 4001339 := bstep (se 1 (by rfl) ⟨3001004, by rfl⟩ : syracuseStep 4001339 = 6002009) B6002009
theorem B1248863 : Blo 830350 1248863 := bstep (se 1 (by rfl) ⟨936647, by rfl⟩ : syracuseStep 1248863 = 1873295) B1873295
theorem B8982215 : Blo 830350 8982215 := bstep (se 1 (by rfl) ⟨6736661, by rfl⟩ : syracuseStep 8982215 = 13473323) B13473323
theorem B1871657 : Blo 830350 1871657 := bstep (se 2 (by rfl) ⟨701871, by rfl⟩ : syracuseStep 1871657 = 1403743) B1403743
theorem B1576759 : Blo 830350 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B1249079 : Blo 830350 1249079 := bstep (se 1 (by rfl) ⟨936809, by rfl⟩ : syracuseStep 1249079 = 1873619) B1873619
theorem B7114553 : Blo 830350 7114553 := bstep (se 2 (by rfl) ⟨2667957, by rfl⟩ : syracuseStep 7114553 = 5335915) B5335915
theorem B3805193 : Blo 830350 3805193 := bstep (se 2 (by rfl) ⟨1426947, by rfl⟩ : syracuseStep 3805193 = 2853895) B2853895
theorem B1249385 : Blo 830350 1249385 := bstep (se 2 (by rfl) ⟨468519, by rfl⟩ : syracuseStep 1249385 = 937039) B937039
theorem B4493465 : Blo 830350 4493465 := bstep (se 2 (by rfl) ⟨1685049, by rfl⟩ : syracuseStep 4493465 = 3370099) B3370099
theorem B6328691 : Blo 830350 6328691 := bstep (se 1 (by rfl) ⟨4746518, by rfl⟩ : syracuseStep 6328691 = 9493037) B9493037
theorem B1773991 : Blo 830350 1773991 := bstep (se 1 (by rfl) ⟨1330493, by rfl⟩ : syracuseStep 1773991 = 2660987) B2660987
theorem B889255 : Blo 830350 889255 := bstep (se 1 (by rfl) ⟨666941, by rfl⟩ : syracuseStep 889255 = 1333883) B1333883
theorem B1249703 : Blo 830350 1249703 := bstep (se 1 (by rfl) ⟨937277, by rfl⟩ : syracuseStep 1249703 = 1874555) B1874555
theorem B1249787 : Blo 830350 1249787 := bstep (se 1 (by rfl) ⟨937340, by rfl⟩ : syracuseStep 1249787 = 1874681) B1874681
theorem B1446395 : Blo 830350 1446395 := bstep (se 1 (by rfl) ⟨1084796, by rfl⟩ : syracuseStep 1446395 = 2169593) B2169593
theorem B4493875 : Blo 830350 4493875 := bstep (se 1 (by rfl) ⟨3370406, by rfl⟩ : syracuseStep 4493875 = 6740813) B6740813
theorem B1774153 : Blo 830350 1774153 := bstep (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) B1330615
theorem B1249913 : Blo 830350 1249913 := bstep (se 2 (by rfl) ⟨468717, by rfl⟩ : syracuseStep 1249913 = 937435) B937435
theorem B1577647 : Blo 830350 1577647 := bstep (se 1 (by rfl) ⟨1183235, by rfl⟩ : syracuseStep 1577647 = 2366471) B2366471
theorem B1249967 : Blo 830350 1249967 := bstep (se 1 (by rfl) ⟨937475, by rfl⟩ : syracuseStep 1249967 = 1874951) B1874951
theorem B1250015 : Blo 830350 1250015 := bstep (se 1 (by rfl) ⟨937511, by rfl⟩ : syracuseStep 1250015 = 1875023) B1875023
theorem B21893917 : Blo 830350 21893917 := bstep (se 3 (by rfl) ⟨4105109, by rfl⟩ : syracuseStep 21893917 = 8210219) B8210219
theorem B1184591 : Blo 830350 1184591 := bstep (se 1 (by rfl) ⟨888443, by rfl⟩ : syracuseStep 1184591 = 1776887) B1776887
theorem B1872719 : Blo 830350 1872719 := bstep (se 1 (by rfl) ⟨1404539, by rfl⟩ : syracuseStep 1872719 = 2809079) B2809079
theorem B1250279 : Blo 830350 1250279 := bstep (se 1 (by rfl) ⟨937709, by rfl⟩ : syracuseStep 1250279 = 1875419) B1875419
theorem B1872935 : Blo 830350 1872935 := bstep (se 1 (by rfl) ⟨1404701, by rfl⟩ : syracuseStep 1872935 = 2809403) B2809403
theorem B2102395 : Blo 830350 2102395 := bstep (se 1 (by rfl) ⟨1576796, by rfl⟩ : syracuseStep 2102395 = 3153593) B3153593
theorem B1774811 : Blo 830350 1774811 := bstep (se 1 (by rfl) ⟨1331108, by rfl⟩ : syracuseStep 1774811 = 2662217) B2662217
theorem B1873115 : Blo 830350 1873115 := bstep (se 1 (by rfl) ⟨1404836, by rfl⟩ : syracuseStep 1873115 = 2809673) B2809673
theorem B890075 : Blo 830350 890075 := bstep (se 1 (by rfl) ⟨667556, by rfl⟩ : syracuseStep 890075 = 1335113) B1335113
theorem B1578217 : Blo 830350 1578217 := bstep (se 2 (by rfl) ⟨591831, by rfl⟩ : syracuseStep 1578217 = 1183663) B1183663
theorem B1250537 : Blo 830350 1250537 := bstep (se 2 (by rfl) ⟨468951, by rfl⟩ : syracuseStep 1250537 = 937903) B937903
theorem B1250591 : Blo 830350 1250591 := bstep (se 1 (by rfl) ⟨937943, by rfl⟩ : syracuseStep 1250591 = 1875887) B1875887
theorem B4494635 : Blo 830350 4494635 := bstep (se 1 (by rfl) ⟨3370976, by rfl⟩ : syracuseStep 4494635 = 6741953) B6741953
theorem B1054063 : Blo 830350 1054063 := bstep (se 1 (by rfl) ⟨790547, by rfl⟩ : syracuseStep 1054063 = 1581095) B1581095
theorem B1873313 : Blo 830350 1873313 := bstep (se 2 (by rfl) ⟨702492, by rfl⟩ : syracuseStep 1873313 = 1404985) B1404985
theorem B1250759 : Blo 830350 1250759 := bstep (se 1 (by rfl) ⟨938069, by rfl⟩ : syracuseStep 1250759 = 1876139) B1876139
theorem B1251113 : Blo 830350 1251113 := bstep (se 2 (by rfl) ⟨469167, by rfl⟩ : syracuseStep 1251113 = 938335) B938335
theorem B1251119 : Blo 830350 1251119 := bstep (se 1 (by rfl) ⟨938339, by rfl⟩ : syracuseStep 1251119 = 1876679) B1876679
theorem B1873871 : Blo 830350 1873871 := bstep (se 1 (by rfl) ⟨1405403, by rfl⟩ : syracuseStep 1873871 = 2810807) B2810807
theorem B26941571 : Blo 830350 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B1054939 : Blo 830350 1054939 := bstep (se 1 (by rfl) ⟨791204, by rfl⟩ : syracuseStep 1054939 = 1582409) B1582409
theorem B4495607 : Blo 830350 4495607 := bstep (se 1 (by rfl) ⟨3371705, by rfl⟩ : syracuseStep 4495607 = 6743411) B6743411
theorem B1874249 : Blo 830350 1874249 := bstep (se 2 (by rfl) ⟨702843, by rfl⟩ : syracuseStep 1874249 = 1405687) B1405687
theorem B1874267 : Blo 830350 1874267 := bstep (se 1 (by rfl) ⟨1405700, by rfl⟩ : syracuseStep 1874267 = 2811401) B2811401
theorem B1350055 : Blo 830350 1350055 := bstep (se 1 (by rfl) ⟨1012541, by rfl⟩ : syracuseStep 1350055 = 2025083) B2025083
theorem B2103803 : Blo 830350 2103803 := bstep (se 1 (by rfl) ⟨1577852, by rfl⟩ : syracuseStep 2103803 = 3155705) B3155705
theorem B1579591 : Blo 830350 1579591 := bstep (se 1 (by rfl) ⟨1184693, by rfl⟩ : syracuseStep 1579591 = 2369387) B2369387
theorem B4496147 : Blo 830350 4496147 := bstep (se 1 (by rfl) ⟨3372110, by rfl⟩ : syracuseStep 4496147 = 6744221) B6744221
theorem B36936485 : Blo 830350 36936485 := bstep (se 4 (by rfl) ⟨3462795, by rfl⟩ : syracuseStep 36936485 = 6925591) B6925591
theorem B17996687 : Blo 830350 17996687 := bstep (se 1 (by rfl) ⟨13497515, by rfl⟩ : syracuseStep 17996687 = 26995031) B26995031
theorem B3087247 : Blo 830350 3087247 := bstep (se 1 (by rfl) ⟨2315435, by rfl⟩ : syracuseStep 3087247 = 4630871) B4630871
theorem B1874843 : Blo 830350 1874843 := bstep (se 1 (by rfl) ⟨1406132, by rfl⟩ : syracuseStep 1874843 = 2812265) B2812265
theorem B1875041 : Blo 830350 1875041 := bstep (se 2 (by rfl) ⟨703140, by rfl⟩ : syracuseStep 1875041 = 1406281) B1406281
theorem B2366653 : Blo 830350 2366653 := bstep (se 3 (by rfl) ⟨443747, by rfl⟩ : syracuseStep 2366653 = 887495) B887495
theorem B1875239 : Blo 830350 1875239 := bstep (se 1 (by rfl) ⟨1406429, by rfl⟩ : syracuseStep 1875239 = 2812859) B2812859
theorem B1580411 : Blo 830350 1580411 := bstep (se 1 (by rfl) ⟨1185308, by rfl⟩ : syracuseStep 1580411 = 2370617) B2370617
theorem B3153289 : Blo 830350 3153289 := bstep (se 2 (by rfl) ⟨1182483, by rfl⟩ : syracuseStep 3153289 = 2364967) B2364967
theorem B2104775 : Blo 830350 2104775 := bstep (se 1 (by rfl) ⟨1578581, by rfl⟩ : syracuseStep 2104775 = 3157163) B3157163
theorem B2104825 : Blo 830350 2104825 := bstep (se 2 (by rfl) ⟨789309, by rfl⟩ : syracuseStep 2104825 = 1578619) B1578619
theorem B3382879 : Blo 830350 3382879 := bstep (se 1 (by rfl) ⟨2537159, by rfl⟩ : syracuseStep 3382879 = 5074319) B5074319
theorem B1875617 : Blo 830350 1875617 := bstep (se 2 (by rfl) ⟨703356, by rfl⟩ : syracuseStep 1875617 = 1406713) B1406713
theorem B2105129 : Blo 830350 2105129 := bstep (se 2 (by rfl) ⟨789423, by rfl⟩ : syracuseStep 2105129 = 1578847) B1578847
theorem B1875977 : Blo 830350 1875977 := bstep (se 2 (by rfl) ⟨703491, by rfl⟩ : syracuseStep 1875977 = 1406983) B1406983
theorem B2105473 : Blo 830350 2105473 := bstep (se 2 (by rfl) ⟨789552, by rfl⟩ : syracuseStep 2105473 = 1579105) B1579105
theorem B1876391 : Blo 830350 1876391 := bstep (se 1 (by rfl) ⟨1407293, by rfl⟩ : syracuseStep 1876391 = 2814587) B2814587
theorem B1876499 : Blo 830350 1876499 := bstep (se 1 (by rfl) ⟨1407374, by rfl⟩ : syracuseStep 1876499 = 2814749) B2814749
theorem B1876553 : Blo 830350 1876553 := bstep (se 2 (by rfl) ⟨703707, by rfl⟩ : syracuseStep 1876553 = 1407415) B1407415
theorem B7119575 : Blo 830350 7119575 := bstep (se 1 (by rfl) ⟨5339681, by rfl⟩ : syracuseStep 7119575 = 10679363) B10679363
theorem B2106283 : Blo 830350 2106283 := bstep (se 1 (by rfl) ⟨1579712, by rfl⟩ : syracuseStep 2106283 = 3159425) B3159425
theorem B1876967 : Blo 830350 1876967 := bstep (se 1 (by rfl) ⟨1407725, by rfl⟩ : syracuseStep 1876967 = 2815451) B2815451
theorem B17966069 : Blo 830350 17966069 := bstep (se 5 (by rfl) ⟨842159, by rfl⟩ : syracuseStep 17966069 = 1684319) B1684319
theorem B2368727 : Blo 830350 2368727 := bstep (se 1 (by rfl) ⟨1776545, by rfl⟩ : syracuseStep 2368727 = 3553091) B3553091
theorem B2106587 : Blo 830350 2106587 := bstep (se 1 (by rfl) ⟨1579940, by rfl⟩ : syracuseStep 2106587 = 3159881) B3159881
theorem B3548393 : Blo 830350 3548393 := bstep (se 2 (by rfl) ⟨1330647, by rfl⟩ : syracuseStep 3548393 = 2661295) B2661295
theorem B14198003 : Blo 830350 14198003 := bstep (se 1 (by rfl) ⟨10648502, by rfl⟩ : syracuseStep 14198003 = 21297005) B21297005
theorem B2106719 : Blo 830350 2106719 := bstep (se 1 (by rfl) ⟨1580039, by rfl⟩ : syracuseStep 2106719 = 3160079) B3160079
theorem B4203899 : Blo 830350 4203899 := bstep (se 1 (by rfl) ⟨3152924, by rfl⟩ : syracuseStep 4203899 = 6305849) B6305849
theorem B2663869 : Blo 830350 2663869 := bstep (se 3 (by rfl) ⟨499475, by rfl⟩ : syracuseStep 2663869 = 998951) B998951
theorem B1779193 : Blo 830350 1779193 := bstep (se 2 (by rfl) ⟨667197, by rfl⟩ : syracuseStep 1779193 = 1334395) B1334395
theorem B1582895 : Blo 830350 1582895 := bstep (se 1 (by rfl) ⟨1187171, by rfl⟩ : syracuseStep 1582895 = 2374343) B2374343
theorem B2107417 : Blo 830350 2107417 := bstep (se 2 (by rfl) ⟨790281, by rfl⟩ : syracuseStep 2107417 = 1580563) B1580563
theorem B4499651 : Blo 830350 4499651 := bstep (se 1 (by rfl) ⟨3374738, by rfl⟩ : syracuseStep 4499651 = 6749477) B6749477
theorem B7219493 : Blo 830350 7219493 := bstep (se 4 (by rfl) ⟨676827, by rfl⟩ : syracuseStep 7219493 = 1353655) B1353655
theorem B2107721 : Blo 830350 2107721 := bstep (se 2 (by rfl) ⟨790395, by rfl⟩ : syracuseStep 2107721 = 1580791) B1580791
theorem B4205195 : Blo 830350 4205195 := bstep (se 1 (by rfl) ⟨3153896, by rfl⟩ : syracuseStep 4205195 = 6307793) B6307793
theorem B4270781 : Blo 830350 4270781 := bstep (se 3 (by rfl) ⟨800771, by rfl⟩ : syracuseStep 4270781 = 1601543) B1601543
theorem B1125199 : Blo 830350 1125199 := bstep (se 1 (by rfl) ⟨843899, by rfl⟩ : syracuseStep 1125199 = 1687799) B1687799
theorem B8006525 : Blo 830350 8006525 := bstep (se 3 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 8006525 = 3002447) B3002447
theorem B830363 : Blo 830350 830363 := bstep (se 1 (by rfl) ⟨622772, by rfl⟩ : syracuseStep 830363 = 1245545) B1245545
theorem B830415 : Blo 830350 830415 := bstep (se 1 (by rfl) ⟨622811, by rfl⟩ : syracuseStep 830415 = 1245623) B1245623
theorem B830439 : Blo 830350 830439 := bstep (se 1 (by rfl) ⟨622829, by rfl⟩ : syracuseStep 830439 = 1245659) B1245659
theorem B4009181 : Blo 830350 4009181 := bstep (se 3 (by rfl) ⟨751721, by rfl⟩ : syracuseStep 4009181 = 1503443) B1503443
theorem B830751 : Blo 830350 830751 := bstep (se 1 (by rfl) ⟨623063, by rfl⟩ : syracuseStep 830751 = 1246127) B1246127
theorem B830811 : Blo 830350 830811 := bstep (se 1 (by rfl) ⟨623108, by rfl⟩ : syracuseStep 830811 = 1246217) B1246217
theorem B830831 : Blo 830350 830831 := bstep (se 1 (by rfl) ⟨623123, by rfl⟩ : syracuseStep 830831 = 1246247) B1246247
theorem B830887 : Blo 830350 830887 := bstep (se 1 (by rfl) ⟨623165, by rfl⟩ : syracuseStep 830887 = 1246331) B1246331
theorem B830971 : Blo 830350 830971 := bstep (se 1 (by rfl) ⟨623228, by rfl⟩ : syracuseStep 830971 = 1246457) B1246457
theorem B831039 : Blo 830350 831039 := bstep (se 1 (by rfl) ⟨623279, by rfl⟩ : syracuseStep 831039 = 1246559) B1246559
theorem B831047 : Blo 830350 831047 := bstep (se 1 (by rfl) ⟨623285, by rfl⟩ : syracuseStep 831047 = 1246571) B1246571
theorem B2403935 : Blo 830350 2403935 := bstep (se 1 (by rfl) ⟨1802951, by rfl⟩ : syracuseStep 2403935 = 3605903) B3605903
theorem B831199 : Blo 830350 831199 := bstep (se 1 (by rfl) ⟨623399, by rfl⟩ : syracuseStep 831199 = 1246799) B1246799
theorem B2371369 : Blo 830350 2371369 := bstep (se 2 (by rfl) ⟨889263, by rfl⟩ : syracuseStep 2371369 = 1778527) B1778527
theorem B831279 : Blo 830350 831279 := bstep (se 1 (by rfl) ⟨623459, by rfl⟩ : syracuseStep 831279 = 1246919) B1246919
theorem B1781551 : Blo 830350 1781551 := bstep (se 1 (by rfl) ⟨1336163, by rfl⟩ : syracuseStep 1781551 = 2672327) B2672327
theorem B831387 : Blo 830350 831387 := bstep (se 1 (by rfl) ⟨623540, by rfl⟩ : syracuseStep 831387 = 1247081) B1247081
theorem B831439 : Blo 830350 831439 := bstep (se 1 (by rfl) ⟨623579, by rfl⟩ : syracuseStep 831439 = 1247159) B1247159
theorem B831463 : Blo 830350 831463 := bstep (se 1 (by rfl) ⟨623597, by rfl⟩ : syracuseStep 831463 = 1247195) B1247195
theorem B831775 : Blo 830350 831775 := bstep (se 1 (by rfl) ⟨623831, by rfl⟩ : syracuseStep 831775 = 1247663) B1247663
theorem B831835 : Blo 830350 831835 := bstep (se 1 (by rfl) ⟨623876, by rfl⟩ : syracuseStep 831835 = 1247753) B1247753
theorem B831855 : Blo 830350 831855 := bstep (se 1 (by rfl) ⟨623891, by rfl⟩ : syracuseStep 831855 = 1247783) B1247783
theorem B831911 : Blo 830350 831911 := bstep (se 1 (by rfl) ⟨623933, by rfl⟩ : syracuseStep 831911 = 1247867) B1247867
theorem B831995 : Blo 830350 831995 := bstep (se 1 (by rfl) ⟨623996, by rfl⟩ : syracuseStep 831995 = 1247993) B1247993
theorem B832063 : Blo 830350 832063 := bstep (se 1 (by rfl) ⟨624047, by rfl⟩ : syracuseStep 832063 = 1248095) B1248095
theorem B832071 : Blo 830350 832071 := bstep (se 1 (by rfl) ⟨624053, by rfl⟩ : syracuseStep 832071 = 1248107) B1248107
theorem B832223 : Blo 830350 832223 := bstep (se 1 (by rfl) ⟨624167, by rfl⟩ : syracuseStep 832223 = 1248335) B1248335
theorem B832303 : Blo 830350 832303 := bstep (se 1 (by rfl) ⟨624227, by rfl⟩ : syracuseStep 832303 = 1248455) B1248455
theorem B1127215 : Blo 830350 1127215 := bstep (se 1 (by rfl) ⟨845411, by rfl⟩ : syracuseStep 1127215 = 1690823) B1690823
theorem B2667343 : Blo 830350 2667343 := bstep (se 1 (by rfl) ⟨2000507, by rfl⟩ : syracuseStep 2667343 = 4001015) B4001015
theorem B832411 : Blo 830350 832411 := bstep (se 1 (by rfl) ⟨624308, by rfl⟩ : syracuseStep 832411 = 1248617) B1248617
theorem B832463 : Blo 830350 832463 := bstep (se 1 (by rfl) ⟨624347, by rfl⟩ : syracuseStep 832463 = 1248695) B1248695
theorem B832487 : Blo 830350 832487 := bstep (se 1 (by rfl) ⟨624365, by rfl⟩ : syracuseStep 832487 = 1248731) B1248731
theorem B11973689 : Blo 830350 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B2110607 : Blo 830350 2110607 := bstep (se 1 (by rfl) ⟨1582955, by rfl⟩ : syracuseStep 2110607 = 3165911) B3165911
theorem B832799 : Blo 830350 832799 := bstep (se 1 (by rfl) ⟨624599, by rfl⟩ : syracuseStep 832799 = 1249199) B1249199
theorem B832859 : Blo 830350 832859 := bstep (se 1 (by rfl) ⟨624644, by rfl⟩ : syracuseStep 832859 = 1249289) B1249289
theorem B832879 : Blo 830350 832879 := bstep (se 1 (by rfl) ⟨624659, by rfl⟩ : syracuseStep 832879 = 1249319) B1249319
theorem B832935 : Blo 830350 832935 := bstep (se 1 (by rfl) ⟨624701, by rfl⟩ : syracuseStep 832935 = 1249403) B1249403
theorem B833019 : Blo 830350 833019 := bstep (se 1 (by rfl) ⟨624764, by rfl⟩ : syracuseStep 833019 = 1249529) B1249529
theorem B833087 : Blo 830350 833087 := bstep (se 1 (by rfl) ⟨624815, by rfl⟩ : syracuseStep 833087 = 1249631) B1249631
theorem B833095 : Blo 830350 833095 := bstep (se 1 (by rfl) ⟨624821, by rfl⟩ : syracuseStep 833095 = 1249643) B1249643
theorem B2537147 : Blo 830350 2537147 := bstep (se 1 (by rfl) ⟨1902860, by rfl⟩ : syracuseStep 2537147 = 3805721) B3805721
theorem B833247 : Blo 830350 833247 := bstep (se 1 (by rfl) ⟨624935, by rfl⟩ : syracuseStep 833247 = 1249871) B1249871
theorem B833327 : Blo 830350 833327 := bstep (se 1 (by rfl) ⟨624995, by rfl⟩ : syracuseStep 833327 = 1249991) B1249991
theorem B11974493 : Blo 830350 11974493 := bstep (se 3 (by rfl) ⟨2245217, by rfl⟩ : syracuseStep 11974493 = 4490435) B4490435
theorem B833435 : Blo 830350 833435 := bstep (se 1 (by rfl) ⟨625076, by rfl⟩ : syracuseStep 833435 = 1250153) B1250153
theorem B833487 : Blo 830350 833487 := bstep (se 1 (by rfl) ⟨625115, by rfl⟩ : syracuseStep 833487 = 1250231) B1250231
theorem B833511 : Blo 830350 833511 := bstep (se 1 (by rfl) ⟨625133, by rfl⟩ : syracuseStep 833511 = 1250267) B1250267
theorem B2373761 : Blo 830350 2373761 := bstep (se 2 (by rfl) ⟨890160, by rfl⟩ : syracuseStep 2373761 = 1780321) B1780321
theorem B3553465 : Blo 830350 3553465 := bstep (se 2 (by rfl) ⟨1332549, by rfl⟩ : syracuseStep 3553465 = 2665099) B2665099
theorem B4208921 : Blo 830350 4208921 := bstep (se 2 (by rfl) ⟨1578345, by rfl⟩ : syracuseStep 4208921 = 3156691) B3156691
theorem B833823 : Blo 830350 833823 := bstep (se 1 (by rfl) ⟨625367, by rfl⟩ : syracuseStep 833823 = 1250735) B1250735
theorem B833883 : Blo 830350 833883 := bstep (se 1 (by rfl) ⟨625412, by rfl⟩ : syracuseStep 833883 = 1250825) B1250825
theorem B833903 : Blo 830350 833903 := bstep (se 1 (by rfl) ⟨625427, by rfl⟩ : syracuseStep 833903 = 1250855) B1250855
theorem B833959 : Blo 830350 833959 := bstep (se 1 (by rfl) ⟨625469, by rfl⟩ : syracuseStep 833959 = 1250939) B1250939
theorem B834043 : Blo 830350 834043 := bstep (se 1 (by rfl) ⟨625532, by rfl⟩ : syracuseStep 834043 = 1251065) B1251065
theorem B834111 : Blo 830350 834111 := bstep (se 1 (by rfl) ⟨625583, by rfl⟩ : syracuseStep 834111 = 1251167) B1251167
theorem B834119 : Blo 830350 834119 := bstep (se 1 (by rfl) ⟨625589, by rfl⟩ : syracuseStep 834119 = 1251179) B1251179
theorem B1686089 : Blo 830350 1686089 := bstep (se 2 (by rfl) ⟨632283, by rfl⟩ : syracuseStep 1686089 = 1264567) B1264567
theorem B2374217 : Blo 830350 2374217 := bstep (se 2 (by rfl) ⟨890331, by rfl⟩ : syracuseStep 2374217 = 1780663) B1780663
theorem B4733579 : Blo 830350 4733579 := bstep (se 1 (by rfl) ⟨3550184, by rfl⟩ : syracuseStep 4733579 = 7100369) B7100369
theorem B834271 : Blo 830350 834271 := bstep (se 1 (by rfl) ⟨625703, by rfl⟩ : syracuseStep 834271 = 1251407) B1251407
theorem B1686671 : Blo 830350 1686671 := bstep (se 1 (by rfl) ⟨1265003, by rfl⟩ : syracuseStep 1686671 = 2530007) B2530007
theorem B7126339 : Blo 830350 7126339 := bstep (se 1 (by rfl) ⟨5344754, by rfl⟩ : syracuseStep 7126339 = 10689509) B10689509
theorem B28884599 : Blo 830350 28884599 := bstep (se 1 (by rfl) ⟨21663449, by rfl⟩ : syracuseStep 28884599 = 43326899) B43326899
theorem B934267 : Blo 830350 934267 := bstep (se 1 (by rfl) ⟨700700, by rfl⟩ : syracuseStep 934267 = 1401401) B1401401
theorem B2245241 : Blo 830350 2245241 := bstep (se 2 (by rfl) ⟨841965, by rfl⟩ : syracuseStep 2245241 = 1683931) B1683931
theorem B934735 : Blo 830350 934735 := bstep (se 1 (by rfl) ⟨701051, by rfl⟩ : syracuseStep 934735 = 1402103) B1402103
theorem B5129153 : Blo 830350 5129153 := bstep (se 2 (by rfl) ⟨1923432, by rfl⟩ : syracuseStep 5129153 = 3846865) B3846865
theorem B4211675 : Blo 830350 4211675 := bstep (se 1 (by rfl) ⟨3158756, by rfl⟩ : syracuseStep 4211675 = 6317513) B6317513
theorem B4211837 : Blo 830350 4211837 := bstep (se 3 (by rfl) ⟨789719, by rfl⟩ : syracuseStep 4211837 = 1579439) B1579439
theorem B3163283 : Blo 830350 3163283 := bstep (se 1 (by rfl) ⟨2372462, by rfl⟩ : syracuseStep 3163283 = 4744925) B4744925
theorem B935131 : Blo 830350 935131 := bstep (se 1 (by rfl) ⟨701348, by rfl⟩ : syracuseStep 935131 = 1402697) B1402697
theorem B4212161 : Blo 830350 4212161 := bstep (se 2 (by rfl) ⟨1579560, by rfl⟩ : syracuseStep 4212161 = 3159121) B3159121
theorem B935419 : Blo 830350 935419 := bstep (se 1 (by rfl) ⟨701564, by rfl⟩ : syracuseStep 935419 = 1403129) B1403129
theorem B51267107 : Blo 830350 51267107 := bstep (se 1 (by rfl) ⟨38450330, by rfl⟩ : syracuseStep 51267107 = 76900661) B76900661
theorem B935599 : Blo 830350 935599 := bstep (se 1 (by rfl) ⟨701699, by rfl⟩ : syracuseStep 935599 = 1403399) B1403399
theorem B6309737 : Blo 830350 6309737 := bstep (se 2 (by rfl) ⟨2366151, by rfl⟩ : syracuseStep 6309737 = 4732303) B4732303
theorem B12011399 : Blo 830350 12011399 := bstep (se 1 (by rfl) ⟨9008549, by rfl⟩ : syracuseStep 12011399 = 18017099) B18017099
theorem B4736951 : Blo 830350 4736951 := bstep (se 1 (by rfl) ⟨3552713, by rfl⟩ : syracuseStep 4736951 = 7105427) B7105427
theorem B935887 : Blo 830350 935887 := bstep (se 1 (by rfl) ⟨701915, by rfl⟩ : syracuseStep 935887 = 1403831) B1403831
theorem B6408143 : Blo 830350 6408143 := bstep (se 1 (by rfl) ⟨4806107, by rfl⟩ : syracuseStep 6408143 = 9612215) B9612215
theorem B9128051 : Blo 830350 9128051 := bstep (se 1 (by rfl) ⟨6846038, by rfl⟩ : syracuseStep 9128051 = 13692077) B13692077
theorem B2803841 : Blo 830350 2803841 := bstep (se 2 (by rfl) ⟨1051440, by rfl⟩ : syracuseStep 2803841 = 2102881) B2102881
theorem B936283 : Blo 830350 936283 := bstep (se 1 (by rfl) ⟨702212, by rfl⟩ : syracuseStep 936283 = 1404425) B1404425
theorem B936391 : Blo 830350 936391 := bstep (se 1 (by rfl) ⟨702293, by rfl⟩ : syracuseStep 936391 = 1404587) B1404587
theorem B2804219 : Blo 830350 2804219 := bstep (se 1 (by rfl) ⟨2103164, by rfl⟩ : syracuseStep 2804219 = 4206329) B4206329
theorem B9128659 : Blo 830350 9128659 := bstep (se 1 (by rfl) ⟨6846494, by rfl⟩ : syracuseStep 9128659 = 13692989) B13692989
theorem B936751 : Blo 830350 936751 := bstep (se 1 (by rfl) ⟨702563, by rfl⟩ : syracuseStep 936751 = 1405127) B1405127
theorem B936859 : Blo 830350 936859 := bstep (se 1 (by rfl) ⟨702644, by rfl⟩ : syracuseStep 936859 = 1405289) B1405289
theorem B2804651 : Blo 830350 2804651 := bstep (se 1 (by rfl) ⟨2103488, by rfl⟩ : syracuseStep 2804651 = 4206977) B4206977
theorem B15977675 : Blo 830350 15977675 := bstep (se 1 (by rfl) ⟨11983256, by rfl⟩ : syracuseStep 15977675 = 23966513) B23966513
theorem B937255 : Blo 830350 937255 := bstep (se 1 (by rfl) ⟨702941, by rfl⟩ : syracuseStep 937255 = 1405883) B1405883
theorem B937327 : Blo 830350 937327 := bstep (se 1 (by rfl) ⟨702995, by rfl⟩ : syracuseStep 937327 = 1405991) B1405991
theorem B2805191 : Blo 830350 2805191 := bstep (se 1 (by rfl) ⟨2103893, by rfl⟩ : syracuseStep 2805191 = 4207787) B4207787
theorem B937543 : Blo 830350 937543 := bstep (se 1 (by rfl) ⟨703157, by rfl⟩ : syracuseStep 937543 = 1406315) B1406315
theorem B16010891 : Blo 830350 16010891 := bstep (se 1 (by rfl) ⟨12008168, by rfl⟩ : syracuseStep 16010891 = 24016337) B24016337
theorem B2805515 : Blo 830350 2805515 := bstep (se 1 (by rfl) ⟨2104136, by rfl⟩ : syracuseStep 2805515 = 4208273) B4208273
theorem B3002159 : Blo 830350 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B3559241 : Blo 830350 3559241 := bstep (se 2 (by rfl) ⟨1334715, by rfl⟩ : syracuseStep 3559241 = 2669431) B2669431
theorem B2805785 : Blo 830350 2805785 := bstep (se 2 (by rfl) ⟨1052169, by rfl⟩ : syracuseStep 2805785 = 2104339) B2104339
theorem B938407 : Blo 830350 938407 := bstep (se 1 (by rfl) ⟨703805, by rfl⟩ : syracuseStep 938407 = 1407611) B1407611
theorem B6574891 : Blo 830350 6574891 := bstep (se 1 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 6574891 = 9862337) B9862337
theorem B3167171 : Blo 830350 3167171 := bstep (se 1 (by rfl) ⟨2375378, by rfl⟩ : syracuseStep 3167171 = 4750757) B4750757
theorem B3560573 : Blo 830350 3560573 := bstep (se 3 (by rfl) ⟨667607, by rfl⟩ : syracuseStep 3560573 = 1335215) B1335215
theorem B2807027 : Blo 830350 2807027 := bstep (se 1 (by rfl) ⟨2105270, by rfl⟩ : syracuseStep 2807027 = 4210541) B4210541
theorem B2807135 : Blo 830350 2807135 := bstep (se 1 (by rfl) ⟨2105351, by rfl⟩ : syracuseStep 2807135 = 4210703) B4210703
theorem B1922617 : Blo 830350 1922617 := bstep (se 2 (by rfl) ⟨720981, by rfl⟩ : syracuseStep 1922617 = 1441963) B1441963
theorem B2709179 : Blo 830350 2709179 := bstep (se 1 (by rfl) ⟨2031884, by rfl⟩ : syracuseStep 2709179 = 4063769) B4063769
theorem B2250625 : Blo 830350 2250625 := bstep (se 2 (by rfl) ⟨843984, by rfl⟩ : syracuseStep 2250625 = 1687969) B1687969
theorem B3561839 : Blo 830350 3561839 := bstep (se 1 (by rfl) ⟨2671379, by rfl⟩ : syracuseStep 3561839 = 5342759) B5342759
theorem B1333831 : Blo 830350 1333831 := bstep (se 1 (by rfl) ⟨1000373, by rfl⟩ : syracuseStep 1333831 = 2000747) B2000747
theorem B2808701 : Blo 830350 2808701 := bstep (se 3 (by rfl) ⟨526631, by rfl⟩ : syracuseStep 2808701 = 1053263) B1053263
theorem B2808971 : Blo 830350 2808971 := bstep (se 1 (by rfl) ⟨2106728, by rfl⟩ : syracuseStep 2808971 = 4213457) B4213457
theorem B1334651 : Blo 830350 1334651 := bstep (se 1 (by rfl) ⟨1000988, by rfl⟩ : syracuseStep 1334651 = 2001977) B2001977
theorem B9625337 : Blo 830350 9625337 := bstep (se 2 (by rfl) ⟨3609501, by rfl⟩ : syracuseStep 9625337 = 7219003) B7219003
theorem B3661615 : Blo 830350 3661615 := bstep (se 1 (by rfl) ⟨2746211, by rfl⟩ : syracuseStep 3661615 = 5492423) B5492423
theorem B5693257 : Blo 830350 5693257 := bstep (se 2 (by rfl) ⟨2134971, by rfl⟩ : syracuseStep 5693257 = 4269943) B4269943
theorem B2252701 : Blo 830350 2252701 := bstep (se 3 (by rfl) ⟨422381, by rfl⟩ : syracuseStep 2252701 = 844763) B844763
theorem B5988401 : Blo 830350 5988401 := bstep (se 2 (by rfl) ⟨2245650, by rfl⟩ : syracuseStep 5988401 = 4491301) B4491301
theorem B2253167 : Blo 830350 2253167 := bstep (se 1 (by rfl) ⟨1689875, by rfl⟩ : syracuseStep 2253167 = 3379751) B3379751
theorem B1827407 : Blo 830350 1827407 := bstep (se 1 (by rfl) ⟨1370555, by rfl⟩ : syracuseStep 1827407 = 2741111) B2741111
theorem B1270379 : Blo 830350 1270379 := bstep (se 1 (by rfl) ⟨952784, by rfl⟩ : syracuseStep 1270379 = 1905569) B1905569
theorem B9101969 : Blo 830350 9101969 := bstep (se 2 (by rfl) ⟨3413238, by rfl⟩ : syracuseStep 9101969 = 6826477) B6826477
theorem B9462419 : Blo 830350 9462419 := bstep (se 1 (by rfl) ⟨7096814, by rfl⟩ : syracuseStep 9462419 = 14193629) B14193629
theorem B2810591 : Blo 830350 2810591 := bstep (se 1 (by rfl) ⟨2107943, by rfl⟩ : syracuseStep 2810591 = 4215887) B4215887
theorem B3990653 : Blo 830350 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B2811023 : Blo 830350 2811023 := bstep (se 1 (by rfl) ⟨2108267, by rfl⟩ : syracuseStep 2811023 = 4216535) B4216535
theorem B4220423 : Blo 830350 4220423 := bstep (se 1 (by rfl) ⟨3165317, by rfl⟩ : syracuseStep 4220423 = 6330635) B6330635
theorem B1402555 : Blo 830350 1402555 := bstep (se 1 (by rfl) ⟨1051916, by rfl⟩ : syracuseStep 1402555 = 2103833) B2103833
theorem B20244329 : Blo 830350 20244329 := bstep (se 2 (by rfl) ⟨7591623, by rfl⟩ : syracuseStep 20244329 = 15183247) B15183247
theorem B4220909 : Blo 830350 4220909 := bstep (se 3 (by rfl) ⟨791420, by rfl⟩ : syracuseStep 4220909 = 1582841) B1582841
theorem B16017587 : Blo 830350 16017587 := bstep (se 1 (by rfl) ⟨12013190, by rfl⟩ : syracuseStep 16017587 = 24026381) B24026381
theorem B2812157 : Blo 830350 2812157 := bstep (se 3 (by rfl) ⟨527279, by rfl⟩ : syracuseStep 2812157 = 1054559) B1054559
theorem B4221395 : Blo 830350 4221395 := bstep (se 1 (by rfl) ⟨3166046, by rfl⟩ : syracuseStep 4221395 = 6332093) B6332093
theorem B1403615 : Blo 830350 1403615 := bstep (se 1 (by rfl) ⟨1052711, by rfl⟩ : syracuseStep 1403615 = 2105423) B2105423
theorem B12151565 : Blo 830350 12151565 := bstep (se 3 (by rfl) ⟨2278418, by rfl⟩ : syracuseStep 12151565 = 4556837) B4556837
theorem B4221719 : Blo 830350 4221719 := bstep (se 1 (by rfl) ⟨3166289, by rfl⟩ : syracuseStep 4221719 = 6332579) B6332579
theorem B9497411 : Blo 830350 9497411 := bstep (se 1 (by rfl) ⟨7123058, by rfl⟩ : syracuseStep 9497411 = 14246117) B14246117
theorem B2812967 : Blo 830350 2812967 := bstep (se 1 (by rfl) ⟨2109725, by rfl⟩ : syracuseStep 2812967 = 4219451) B4219451
theorem B1404047 : Blo 830350 1404047 := bstep (se 1 (by rfl) ⟨1053035, by rfl⟩ : syracuseStep 1404047 = 2106071) B2106071
theorem B2026711 : Blo 830350 2026711 := bstep (se 1 (by rfl) ⟨1520033, by rfl⟩ : syracuseStep 2026711 = 3040067) B3040067
theorem B6319457 : Blo 830350 6319457 := bstep (se 2 (by rfl) ⟨2369796, by rfl⟩ : syracuseStep 6319457 = 4739593) B4739593
theorem B1404283 : Blo 830350 1404283 := bstep (se 1 (by rfl) ⟨1053212, by rfl⟩ : syracuseStep 1404283 = 2106425) B2106425
theorem B3206537 : Blo 830350 3206537 := bstep (se 2 (by rfl) ⟨1202451, by rfl⟩ : syracuseStep 3206537 = 2404903) B2404903
theorem B2813399 : Blo 830350 2813399 := bstep (se 1 (by rfl) ⟨2110049, by rfl⟩ : syracuseStep 2813399 = 4220099) B4220099
theorem B3993113 : Blo 830350 3993113 := bstep (se 2 (by rfl) ⟨1497417, by rfl⟩ : syracuseStep 3993113 = 2994835) B2994835
theorem B1502803 : Blo 830350 1502803 := bstep (se 1 (by rfl) ⟨1127102, by rfl⟩ : syracuseStep 1502803 = 2254205) B2254205
theorem B1011295 : Blo 830350 1011295 := bstep (se 1 (by rfl) ⟨758471, by rfl⟩ : syracuseStep 1011295 = 1516943) B1516943
theorem B10678027 : Blo 830350 10678027 := bstep (se 1 (by rfl) ⟨8008520, by rfl⟩ : syracuseStep 10678027 = 16017041) B16017041
theorem B24047705 : Blo 830350 24047705 := bstep (se 2 (by rfl) ⟨9017889, by rfl⟩ : syracuseStep 24047705 = 18035779) B18035779
theorem B4223339 : Blo 830350 4223339 := bstep (se 1 (by rfl) ⟨3167504, by rfl⟩ : syracuseStep 4223339 = 6335009) B6335009
theorem B10121773 : Blo 830350 10121773 := bstep (se 3 (by rfl) ⟨1897832, by rfl⟩ : syracuseStep 10121773 = 3795665) B3795665
theorem B1405775 : Blo 830350 1405775 := bstep (se 1 (by rfl) ⟨1054331, by rfl⟩ : syracuseStep 1405775 = 2108663) B2108663
theorem B7992377 : Blo 830350 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B2815073 : Blo 830350 2815073 := bstep (se 2 (by rfl) ⟨1055652, by rfl⟩ : syracuseStep 2815073 = 2111305) B2111305
theorem B12022931 : Blo 830350 12022931 := bstep (se 1 (by rfl) ⟨9017198, by rfl⟩ : syracuseStep 12022931 = 18034397) B18034397
theorem B6321401 : Blo 830350 6321401 := bstep (se 2 (by rfl) ⟨2370525, by rfl⟩ : syracuseStep 6321401 = 4741051) B4741051
theorem B35944235 : Blo 830350 35944235 := bstep (se 1 (by rfl) ⟨26958176, by rfl⟩ : syracuseStep 35944235 = 53916353) B53916353
theorem B1406767 : Blo 830350 1406767 := bstep (se 1 (by rfl) ⟨1055075, by rfl⟩ : syracuseStep 1406767 = 2110151) B2110151
theorem B12843143 : Blo 830350 12843143 := bstep (se 1 (by rfl) ⟨9632357, by rfl⟩ : syracuseStep 12843143 = 19264715) B19264715
theorem B1800767 : Blo 830350 1800767 := bstep (se 1 (by rfl) ⟨1350575, by rfl⟩ : syracuseStep 1800767 = 2701151) B2701151
theorem B2882429 : Blo 830350 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B356023187 : Blo 830350 356023187 := bstep (se 1 (by rfl) ⟨267017390, by rfl⟩ : syracuseStep 356023187 = 534034781) B534034781
theorem B8092691 : Blo 830350 8092691 := bstep (se 1 (by rfl) ⟨6069518, by rfl⟩ : syracuseStep 8092691 = 12139037) B12139037
theorem B1899769 : Blo 830350 1899769 := bstep (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) B1424827
theorem B1801963 : Blo 830350 1801963 := bstep (se 1 (by rfl) ⟨1351472, by rfl⟩ : syracuseStep 1801963 = 2702945) B2702945
theorem B1245647 : Blo 830350 1245647 := bstep (se 1 (by rfl) ⟨934235, by rfl⟩ : syracuseStep 1245647 = 1868471) B1868471
theorem B1245689 : Blo 830350 1245689 := bstep (se 2 (by rfl) ⟨467133, by rfl⟩ : syracuseStep 1245689 = 934267) B934267
theorem B1245791 : Blo 830350 1245791 := bstep (se 1 (by rfl) ⟨934343, by rfl⟩ : syracuseStep 1245791 = 1868687) B1868687
theorem B34178071 : Blo 830350 34178071 := bstep (se 1 (by rfl) ⟨25633553, by rfl⟩ : syracuseStep 34178071 = 51267107) B51267107
theorem B1246271 : Blo 830350 1246271 := bstep (se 1 (by rfl) ⟨934703, by rfl⟩ : syracuseStep 1246271 = 1869407) B1869407
theorem B7210063 : Blo 830350 7210063 := bstep (se 1 (by rfl) ⟨5407547, by rfl⟩ : syracuseStep 7210063 = 10815095) B10815095
theorem B1246313 : Blo 830350 1246313 := bstep (se 2 (by rfl) ⟨467367, by rfl⟩ : syracuseStep 1246313 = 934735) B934735
theorem B1246415 : Blo 830350 1246415 := bstep (se 1 (by rfl) ⟨934811, by rfl⟩ : syracuseStep 1246415 = 1869623) B1869623
theorem B1246619 : Blo 830350 1246619 := bstep (se 1 (by rfl) ⟨934964, by rfl⟩ : syracuseStep 1246619 = 1869929) B1869929
theorem B1869227 : Blo 830350 1869227 := bstep (se 1 (by rfl) ⟨1401920, by rfl⟩ : syracuseStep 1869227 = 2803841) B2803841
theorem B1246841 : Blo 830350 1246841 := bstep (se 2 (by rfl) ⟨467565, by rfl⟩ : syracuseStep 1246841 = 935131) B935131
theorem B1869479 : Blo 830350 1869479 := bstep (se 1 (by rfl) ⟨1402109, by rfl⟩ : syracuseStep 1869479 = 2804219) B2804219
theorem B1246943 : Blo 830350 1246943 := bstep (se 1 (by rfl) ⟨935207, by rfl⟩ : syracuseStep 1246943 = 1870415) B1870415
theorem B1247039 : Blo 830350 1247039 := bstep (se 1 (by rfl) ⟨935279, by rfl⟩ : syracuseStep 1247039 = 1870559) B1870559
theorem B1869767 : Blo 830350 1869767 := bstep (se 1 (by rfl) ⟨1402325, by rfl⟩ : syracuseStep 1869767 = 2804651) B2804651
theorem B1247207 : Blo 830350 1247207 := bstep (se 1 (by rfl) ⟨935405, by rfl⟩ : syracuseStep 1247207 = 1870811) B1870811
theorem B1247225 : Blo 830350 1247225 := bstep (se 2 (by rfl) ⟨467709, by rfl⟩ : syracuseStep 1247225 = 935419) B935419
theorem B1247327 : Blo 830350 1247327 := bstep (se 1 (by rfl) ⟨935495, by rfl⟩ : syracuseStep 1247327 = 1870991) B1870991
theorem B10651783 : Blo 830350 10651783 := bstep (se 1 (by rfl) ⟨7988837, by rfl⟩ : syracuseStep 10651783 = 15977675) B15977675
theorem B1247387 : Blo 830350 1247387 := bstep (se 1 (by rfl) ⟨935540, by rfl⟩ : syracuseStep 1247387 = 1871081) B1871081
theorem B1247423 : Blo 830350 1247423 := bstep (se 1 (by rfl) ⟨935567, by rfl⟩ : syracuseStep 1247423 = 1871135) B1871135
theorem B3999955 : Blo 830350 3999955 := bstep (se 1 (by rfl) ⟨2999966, by rfl⟩ : syracuseStep 3999955 = 5999933) B5999933
theorem B1247465 : Blo 830350 1247465 := bstep (se 2 (by rfl) ⟨467799, by rfl⟩ : syracuseStep 1247465 = 935599) B935599
theorem B1870073 : Blo 830350 1870073 := bstep (se 2 (by rfl) ⟨701277, by rfl⟩ : syracuseStep 1870073 = 1402555) B1402555
theorem B1870127 : Blo 830350 1870127 := bstep (se 1 (by rfl) ⟨1402595, by rfl⟩ : syracuseStep 1870127 = 2805191) B2805191
theorem B1870343 : Blo 830350 1870343 := bstep (se 1 (by rfl) ⟨1402757, by rfl⟩ : syracuseStep 1870343 = 2805515) B2805515
theorem B1247771 : Blo 830350 1247771 := bstep (se 1 (by rfl) ⟨935828, by rfl⟩ : syracuseStep 1247771 = 1871657) B1871657
theorem B2001439 : Blo 830350 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B1182313 : Blo 830350 1182313 := bstep (se 2 (by rfl) ⟨443367, by rfl⟩ : syracuseStep 1182313 = 886735) B886735
theorem B1247849 : Blo 830350 1247849 := bstep (se 2 (by rfl) ⟨467943, by rfl⟩ : syracuseStep 1247849 = 935887) B935887
theorem B1870523 : Blo 830350 1870523 := bstep (se 1 (by rfl) ⟨1402892, by rfl⟩ : syracuseStep 1870523 = 2805785) B2805785
theorem B1248377 : Blo 830350 1248377 := bstep (se 2 (by rfl) ⟨468141, by rfl⟩ : syracuseStep 1248377 = 936283) B936283
theorem B1248479 : Blo 830350 1248479 := bstep (se 1 (by rfl) ⟨936359, by rfl⟩ : syracuseStep 1248479 = 1872719) B1872719
theorem B1248521 : Blo 830350 1248521 := bstep (se 2 (by rfl) ⟨468195, by rfl⟩ : syracuseStep 1248521 = 936391) B936391
theorem B1248623 : Blo 830350 1248623 := bstep (se 1 (by rfl) ⟨936467, by rfl⟩ : syracuseStep 1248623 = 1872935) B1872935
theorem B1248743 : Blo 830350 1248743 := bstep (se 1 (by rfl) ⟨936557, by rfl⟩ : syracuseStep 1248743 = 1873115) B1873115
theorem B1871351 : Blo 830350 1871351 := bstep (se 1 (by rfl) ⟨1403513, by rfl⟩ : syracuseStep 1871351 = 2807027) B2807027
theorem B1871423 : Blo 830350 1871423 := bstep (se 1 (by rfl) ⟨1403567, by rfl⟩ : syracuseStep 1871423 = 2807135) B2807135
theorem B1248875 : Blo 830350 1248875 := bstep (se 1 (by rfl) ⟨936656, by rfl⟩ : syracuseStep 1248875 = 1873313) B1873313
theorem B1249001 : Blo 830350 1249001 := bstep (se 2 (by rfl) ⟨468375, by rfl⟩ : syracuseStep 1249001 = 936751) B936751
theorem B1806119 : Blo 830350 1806119 := bstep (se 1 (by rfl) ⟨1354589, by rfl⟩ : syracuseStep 1806119 = 2709179) B2709179
theorem B1249145 : Blo 830350 1249145 := bstep (se 2 (by rfl) ⟨468429, by rfl⟩ : syracuseStep 1249145 = 936859) B936859
theorem B1249247 : Blo 830350 1249247 := bstep (se 1 (by rfl) ⟨936935, by rfl⟩ : syracuseStep 1249247 = 1873871) B1873871
theorem B17961047 : Blo 830350 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B1249499 : Blo 830350 1249499 := bstep (se 1 (by rfl) ⟨937124, by rfl⟩ : syracuseStep 1249499 = 1874249) B1874249
theorem B1249511 : Blo 830350 1249511 := bstep (se 1 (by rfl) ⟨937133, by rfl⟩ : syracuseStep 1249511 = 1874267) B1874267
theorem B1249673 : Blo 830350 1249673 := bstep (se 2 (by rfl) ⟨468627, by rfl⟩ : syracuseStep 1249673 = 937255) B937255
theorem B1249769 : Blo 830350 1249769 := bstep (se 2 (by rfl) ⟨468663, by rfl⟩ : syracuseStep 1249769 = 937327) B937327
theorem B1577465 : Blo 830350 1577465 := bstep (se 2 (by rfl) ⟨591549, by rfl⟩ : syracuseStep 1577465 = 1183099) B1183099
theorem B1872377 : Blo 830350 1872377 := bstep (se 2 (by rfl) ⟨702141, by rfl⟩ : syracuseStep 1872377 = 1404283) B1404283
theorem B1872467 : Blo 830350 1872467 := bstep (se 1 (by rfl) ⟨1404350, by rfl⟩ : syracuseStep 1872467 = 2808701) B2808701
theorem B11997791 : Blo 830350 11997791 := bstep (se 1 (by rfl) ⟨8998343, by rfl⟩ : syracuseStep 11997791 = 17996687) B17996687
theorem B1249895 : Blo 830350 1249895 := bstep (se 1 (by rfl) ⟨937421, by rfl⟩ : syracuseStep 1249895 = 1874843) B1874843
theorem B1250027 : Blo 830350 1250027 := bstep (se 1 (by rfl) ⟨937520, by rfl⟩ : syracuseStep 1250027 = 1875041) B1875041
theorem B1872647 : Blo 830350 1872647 := bstep (se 1 (by rfl) ⟨1404485, by rfl⟩ : syracuseStep 1872647 = 2808971) B2808971
theorem B1250057 : Blo 830350 1250057 := bstep (se 2 (by rfl) ⟨468771, by rfl⟩ : syracuseStep 1250057 = 937543) B937543
theorem B2003737 : Blo 830350 2003737 := bstep (se 2 (by rfl) ⟨751401, by rfl⟩ : syracuseStep 2003737 = 1502803) B1502803
theorem B1348393 : Blo 830350 1348393 := bstep (se 2 (by rfl) ⟨505647, by rfl⟩ : syracuseStep 1348393 = 1011295) B1011295
theorem B1250159 : Blo 830350 1250159 := bstep (se 1 (by rfl) ⟨937619, by rfl⟩ : syracuseStep 1250159 = 1875239) B1875239
theorem B2102345 : Blo 830350 2102345 := bstep (se 2 (by rfl) ⟨788379, by rfl⟩ : syracuseStep 2102345 = 1576759) B1576759
theorem B1250411 : Blo 830350 1250411 := bstep (se 1 (by rfl) ⟨937808, by rfl⟩ : syracuseStep 1250411 = 1875617) B1875617
theorem B1250651 : Blo 830350 1250651 := bstep (se 1 (by rfl) ⟨937988, by rfl⟩ : syracuseStep 1250651 = 1875977) B1875977
theorem B1250927 : Blo 830350 1250927 := bstep (se 1 (by rfl) ⟨938195, by rfl⟩ : syracuseStep 1250927 = 1876391) B1876391
theorem B1250999 : Blo 830350 1250999 := bstep (se 1 (by rfl) ⟨938249, by rfl⟩ : syracuseStep 1250999 = 1876499) B1876499
theorem B1251035 : Blo 830350 1251035 := bstep (se 1 (by rfl) ⟨938276, by rfl⟩ : syracuseStep 1251035 = 1876553) B1876553
theorem B6067979 : Blo 830350 6067979 := bstep (se 1 (by rfl) ⟨4550984, by rfl⟩ : syracuseStep 6067979 = 9101969) B9101969
theorem B1873727 : Blo 830350 1873727 := bstep (se 1 (by rfl) ⟨1405295, by rfl⟩ : syracuseStep 1873727 = 2810591) B2810591
theorem B2365321 : Blo 830350 2365321 := bstep (se 2 (by rfl) ⟨886995, by rfl⟩ : syracuseStep 2365321 = 1773991) B1773991
theorem B1185673 : Blo 830350 1185673 := bstep (se 2 (by rfl) ⟨444627, by rfl⟩ : syracuseStep 1185673 = 889255) B889255
theorem B1251209 : Blo 830350 1251209 := bstep (se 2 (by rfl) ⟨469203, by rfl⟩ : syracuseStep 1251209 = 938407) B938407
theorem B1251311 : Blo 830350 1251311 := bstep (se 1 (by rfl) ⟨938483, by rfl⟩ : syracuseStep 1251311 = 1876967) B1876967
theorem B2660435 : Blo 830350 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B1874015 : Blo 830350 1874015 := bstep (se 1 (by rfl) ⟨1405511, by rfl⟩ : syracuseStep 1874015 = 2811023) B2811023
theorem B2365537 : Blo 830350 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B1579151 : Blo 830350 1579151 := bstep (se 1 (by rfl) ⟨1184363, by rfl⟩ : syracuseStep 1579151 = 2368727) B2368727
theorem B2365595 : Blo 830350 2365595 := bstep (se 1 (by rfl) ⟨1774196, by rfl⟩ : syracuseStep 2365595 = 3548393) B3548393
theorem B2103529 : Blo 830350 2103529 := bstep (se 2 (by rfl) ⟨788823, by rfl⟩ : syracuseStep 2103529 = 1577647) B1577647
theorem B1055263 : Blo 830350 1055263 := bstep (se 1 (by rfl) ⟨791447, by rfl⟩ : syracuseStep 1055263 = 1582895) B1582895
theorem B1874771 : Blo 830350 1874771 := bstep (se 1 (by rfl) ⟨1406078, by rfl⟩ : syracuseStep 1874771 = 2812157) B2812157
theorem B2104289 : Blo 830350 2104289 := bstep (se 2 (by rfl) ⟨789108, by rfl⟩ : syracuseStep 2104289 = 1578217) B1578217
theorem B8101043 : Blo 830350 8101043 := bstep (se 1 (by rfl) ⟨6075782, by rfl⟩ : syracuseStep 8101043 = 12151565) B12151565
theorem B6331607 : Blo 830350 6331607 := bstep (se 1 (by rfl) ⟨4748705, by rfl⟩ : syracuseStep 6331607 = 9497411) B9497411
theorem B1875311 : Blo 830350 1875311 := bstep (se 1 (by rfl) ⟨1406483, by rfl⟩ : syracuseStep 1875311 = 2812967) B2812967
theorem B2563489 : Blo 830350 2563489 := bstep (se 2 (by rfl) ⟨961308, by rfl⟩ : syracuseStep 2563489 = 1922617) B1922617
theorem B2137691 : Blo 830350 2137691 := bstep (se 1 (by rfl) ⟨1603268, by rfl⟩ : syracuseStep 2137691 = 3206537) B3206537
theorem B1875599 : Blo 830350 1875599 := bstep (se 1 (by rfl) ⟨1406699, by rfl⟩ : syracuseStep 1875599 = 2813399) B2813399
theorem B2662075 : Blo 830350 2662075 := bstep (se 1 (by rfl) ⟨1996556, by rfl⟩ : syracuseStep 2662075 = 3993113) B3993113
theorem B1875689 : Blo 830350 1875689 := bstep (se 2 (by rfl) ⟨703383, by rfl⟩ : syracuseStep 1875689 = 1406767) B1406767
theorem B16031803 : Blo 830350 16031803 := bstep (se 1 (by rfl) ⟨12023852, by rfl⟩ : syracuseStep 16031803 = 24047705) B24047705
theorem B10691149 : Blo 830350 10691149 := bstep (se 3 (by rfl) ⟨2004590, by rfl⟩ : syracuseStep 10691149 = 4009181) B4009181
theorem B1876715 : Blo 830350 1876715 := bstep (se 1 (by rfl) ⟨1407536, by rfl⟩ : syracuseStep 1876715 = 2815073) B2815073
theorem B2106121 : Blo 830350 2106121 := bstep (se 2 (by rfl) ⟨789795, by rfl⟩ : syracuseStep 2106121 = 1579591) B1579591
theorem B1778441 : Blo 830350 1778441 := bstep (se 2 (by rfl) ⟨666915, by rfl⟩ : syracuseStep 1778441 = 1333831) B1333831
theorem B23962823 : Blo 830350 23962823 := bstep (se 1 (by rfl) ⟨17972117, by rfl⟩ : syracuseStep 23962823 = 35944235) B35944235
theorem B1582507 : Blo 830350 1582507 := bstep (se 1 (by rfl) ⟨1186880, by rfl⟩ : syracuseStep 1582507 = 2373761) B2373761
theorem B8562095 : Blo 830350 8562095 := bstep (se 1 (by rfl) ⟨6421571, by rfl⟩ : syracuseStep 8562095 = 12843143) B12843143
theorem B3155537 : Blo 830350 3155537 := bstep (se 2 (by rfl) ⟨1183326, by rfl⟩ : syracuseStep 3155537 = 2366653) B2366653
theorem B2533025 : Blo 830350 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B1124059 : Blo 830350 1124059 := bstep (se 1 (by rfl) ⟨843044, by rfl⟩ : syracuseStep 1124059 = 1686089) B1686089
theorem B1582811 : Blo 830350 1582811 := bstep (se 1 (by rfl) ⟨1187108, by rfl⟩ : syracuseStep 1582811 = 2374217) B2374217
theorem B3155719 : Blo 830350 3155719 := bstep (se 1 (by rfl) ⟨2366789, by rfl⟩ : syracuseStep 3155719 = 4733579) B4733579
theorem B4204385 : Blo 830350 4204385 := bstep (se 2 (by rfl) ⟨1576644, by rfl⟩ : syracuseStep 4204385 = 3153289) B3153289
theorem B237348791 : Blo 830350 237348791 := bstep (se 1 (by rfl) ⟨178011593, by rfl⟩ : syracuseStep 237348791 = 356023187) B356023187
theorem B1124447 : Blo 830350 1124447 := bstep (se 1 (by rfl) ⟨843335, by rfl⟩ : syracuseStep 1124447 = 1686671) B1686671
theorem B2402617 : Blo 830350 2402617 := bstep (se 2 (by rfl) ⟨900981, by rfl⟩ : syracuseStep 2402617 = 1801963) B1801963
theorem B6007607 : Blo 830350 6007607 := bstep (se 1 (by rfl) ⟨4505705, by rfl⟩ : syracuseStep 6007607 = 9011411) B9011411
theorem B830367 : Blo 830350 830367 := bstep (se 1 (by rfl) ⟨622775, by rfl⟩ : syracuseStep 830367 = 1245551) B1245551
theorem B830511 : Blo 830350 830511 := bstep (se 1 (by rfl) ⟨622883, by rfl⟩ : syracuseStep 830511 = 1245767) B1245767
theorem B830535 : Blo 830350 830535 := bstep (se 1 (by rfl) ⟨622901, by rfl⟩ : syracuseStep 830535 = 1245803) B1245803
theorem B2403425 : Blo 830350 2403425 := bstep (se 2 (by rfl) ⟨901284, by rfl⟩ : syracuseStep 2403425 = 1802569) B1802569
theorem B830687 : Blo 830350 830687 := bstep (se 1 (by rfl) ⟨623015, by rfl⟩ : syracuseStep 830687 = 1246031) B1246031
theorem B3419435 : Blo 830350 3419435 := bstep (se 1 (by rfl) ⟨2564576, by rfl⟩ : syracuseStep 3419435 = 5129153) B5129153
theorem B2108855 : Blo 830350 2108855 := bstep (se 1 (by rfl) ⟨1581641, by rfl⟩ : syracuseStep 2108855 = 3163283) B3163283
theorem B830951 : Blo 830350 830951 := bstep (se 1 (by rfl) ⟨623213, by rfl⟩ : syracuseStep 830951 = 1246427) B1246427
theorem B831067 : Blo 830350 831067 := bstep (se 1 (by rfl) ⟨623300, by rfl⟩ : syracuseStep 831067 = 1246601) B1246601
theorem B831303 : Blo 830350 831303 := bstep (se 1 (by rfl) ⟨623477, by rfl⟩ : syracuseStep 831303 = 1246955) B1246955
theorem B4206491 : Blo 830350 4206491 := bstep (se 1 (by rfl) ⟨3154868, by rfl⟩ : syracuseStep 4206491 = 6309737) B6309737
theorem B8007599 : Blo 830350 8007599 := bstep (se 1 (by rfl) ⟨6005699, by rfl⟩ : syracuseStep 8007599 = 12011399) B12011399
theorem B3157967 : Blo 830350 3157967 := bstep (se 1 (by rfl) ⟨2368475, by rfl⟩ : syracuseStep 3157967 = 4736951) B4736951
theorem B831455 : Blo 830350 831455 := bstep (se 1 (by rfl) ⟨623591, by rfl⟩ : syracuseStep 831455 = 1247183) B1247183
theorem B4272095 : Blo 830350 4272095 := bstep (se 1 (by rfl) ⟨3204071, by rfl⟩ : syracuseStep 4272095 = 6408143) B6408143
theorem B831719 : Blo 830350 831719 := bstep (se 1 (by rfl) ⟨623789, by rfl⟩ : syracuseStep 831719 = 1247579) B1247579
theorem B831871 : Blo 830350 831871 := bstep (se 1 (by rfl) ⟨623903, by rfl⟩ : syracuseStep 831871 = 1247807) B1247807
theorem B831951 : Blo 830350 831951 := bstep (se 1 (by rfl) ⟨623963, by rfl⟩ : syracuseStep 831951 = 1247927) B1247927
theorem B3551825 : Blo 830350 3551825 := bstep (se 2 (by rfl) ⟨1331934, by rfl⟩ : syracuseStep 3551825 = 2663869) B2663869
theorem B832103 : Blo 830350 832103 := bstep (se 1 (by rfl) ⟨624077, by rfl⟩ : syracuseStep 832103 = 1248155) B1248155
theorem B2372257 : Blo 830350 2372257 := bstep (se 2 (by rfl) ⟨889596, by rfl⟩ : syracuseStep 2372257 = 1779193) B1779193
theorem B832367 : Blo 830350 832367 := bstep (se 1 (by rfl) ⟨624275, by rfl⟩ : syracuseStep 832367 = 1248551) B1248551
theorem B3158909 : Blo 830350 3158909 := bstep (se 3 (by rfl) ⟨592295, by rfl⟩ : syracuseStep 3158909 = 1184591) B1184591
theorem B832423 : Blo 830350 832423 := bstep (se 1 (by rfl) ⟨624317, by rfl⟩ : syracuseStep 832423 = 1248635) B1248635
theorem B832507 : Blo 830350 832507 := bstep (se 1 (by rfl) ⟨624380, by rfl⟩ : syracuseStep 832507 = 1248761) B1248761
theorem B832575 : Blo 830350 832575 := bstep (se 1 (by rfl) ⟨624431, by rfl⟩ : syracuseStep 832575 = 1248863) B1248863
theorem B832719 : Blo 830350 832719 := bstep (se 1 (by rfl) ⟨624539, by rfl⟩ : syracuseStep 832719 = 1249079) B1249079
theorem B2372827 : Blo 830350 2372827 := bstep (se 1 (by rfl) ⟨1779620, by rfl⟩ : syracuseStep 2372827 = 3559241) B3559241
theorem B2536795 : Blo 830350 2536795 := bstep (se 1 (by rfl) ⟨1902596, by rfl⟩ : syracuseStep 2536795 = 3805193) B3805193
theorem B832923 : Blo 830350 832923 := bstep (se 1 (by rfl) ⟨624692, by rfl⟩ : syracuseStep 832923 = 1249385) B1249385
theorem B2995643 : Blo 830350 2995643 := bstep (se 1 (by rfl) ⟨2246732, by rfl⟩ : syracuseStep 2995643 = 4493465) B4493465
theorem B833135 : Blo 830350 833135 := bstep (se 1 (by rfl) ⟨624851, by rfl⟩ : syracuseStep 833135 = 1249703) B1249703
theorem B833191 : Blo 830350 833191 := bstep (se 1 (by rfl) ⟨624893, by rfl⟩ : syracuseStep 833191 = 1249787) B1249787
theorem B833275 : Blo 830350 833275 := bstep (se 1 (by rfl) ⟨624956, by rfl⟩ : syracuseStep 833275 = 1249913) B1249913
theorem B833311 : Blo 830350 833311 := bstep (se 1 (by rfl) ⟨624983, by rfl⟩ : syracuseStep 833311 = 1249967) B1249967
theorem B833343 : Blo 830350 833343 := bstep (se 1 (by rfl) ⟨625007, by rfl⟩ : syracuseStep 833343 = 1250015) B1250015
theorem B4732829 : Blo 830350 4732829 := bstep (se 3 (by rfl) ⟨887405, by rfl⟩ : syracuseStep 4732829 = 1774811) B1774811
theorem B2373533 : Blo 830350 2373533 := bstep (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) B890075
theorem B2111447 : Blo 830350 2111447 := bstep (se 1 (by rfl) ⟨1583585, by rfl⟩ : syracuseStep 2111447 = 3167171) B3167171
theorem B833519 : Blo 830350 833519 := bstep (se 1 (by rfl) ⟨625139, by rfl⟩ : syracuseStep 833519 = 1250279) B1250279
theorem B2373715 : Blo 830350 2373715 := bstep (se 1 (by rfl) ⟨1780286, by rfl⟩ : syracuseStep 2373715 = 3560573) B3560573
theorem B833691 : Blo 830350 833691 := bstep (se 1 (by rfl) ⟨625268, by rfl⟩ : syracuseStep 833691 = 1250537) B1250537
theorem B833727 : Blo 830350 833727 := bstep (se 1 (by rfl) ⟨625295, by rfl⟩ : syracuseStep 833727 = 1250591) B1250591
theorem B2996423 : Blo 830350 2996423 := bstep (se 1 (by rfl) ⟨2247317, by rfl⟩ : syracuseStep 2996423 = 4494635) B4494635
theorem B12171545 : Blo 830350 12171545 := bstep (se 2 (by rfl) ⟨4564329, by rfl⟩ : syracuseStep 12171545 = 9128659) B9128659
theorem B833839 : Blo 830350 833839 := bstep (se 1 (by rfl) ⟨625379, by rfl⟩ : syracuseStep 833839 = 1250759) B1250759
theorem B834075 : Blo 830350 834075 := bstep (se 1 (by rfl) ⟨625556, by rfl⟩ : syracuseStep 834075 = 1251113) B1251113
theorem B834079 : Blo 830350 834079 := bstep (se 1 (by rfl) ⟨625559, by rfl⟩ : syracuseStep 834079 = 1251119) B1251119
theorem B2997071 : Blo 830350 2997071 := bstep (se 1 (by rfl) ⟨2247803, by rfl⟩ : syracuseStep 2997071 = 4495607) B4495607
theorem B2374559 : Blo 830350 2374559 := bstep (se 1 (by rfl) ⟨1780919, by rfl⟩ : syracuseStep 2374559 = 3561839) B3561839
theorem B6011813 : Blo 830350 6011813 := bstep (se 4 (by rfl) ⟨563607, by rfl⟩ : syracuseStep 6011813 = 1127215) B1127215
theorem B2702281 : Blo 830350 2702281 := bstep (se 2 (by rfl) ⟨1013355, by rfl⟩ : syracuseStep 2702281 = 2026711) B2026711
theorem B2997431 : Blo 830350 2997431 := bstep (se 1 (by rfl) ⟨2248073, by rfl⟩ : syracuseStep 2997431 = 4496147) B4496147
theorem B24624323 : Blo 830350 24624323 := bstep (se 1 (by rfl) ⟨18468242, by rfl⟩ : syracuseStep 24624323 = 36936485) B36936485
theorem B14237369 : Blo 830350 14237369 := bstep (se 2 (by rfl) ⟨5339013, by rfl⟩ : syracuseStep 14237369 = 10678027) B10678027
theorem B3161825 : Blo 830350 3161825 := bstep (se 2 (by rfl) ⟨1185684, by rfl⟩ : syracuseStep 3161825 = 2371369) B2371369
theorem B2375401 : Blo 830350 2375401 := bstep (se 2 (by rfl) ⟨890775, by rfl⟩ : syracuseStep 2375401 = 1781551) B1781551
theorem B6308279 : Blo 830350 6308279 := bstep (se 1 (by rfl) ⟨4731209, by rfl⟩ : syracuseStep 6308279 = 9462419) B9462419
theorem B11977379 : Blo 830350 11977379 := bstep (se 1 (by rfl) ⟨8983034, by rfl⟩ : syracuseStep 11977379 = 17966069) B17966069
theorem B2802599 : Blo 830350 2802599 := bstep (se 1 (by rfl) ⟨2101949, by rfl⟩ : syracuseStep 2802599 = 4203899) B4203899
theorem B8766521 : Blo 830350 8766521 := bstep (se 2 (by rfl) ⟨3287445, by rfl⟩ : syracuseStep 8766521 = 6574891) B6574891
theorem B3556457 : Blo 830350 3556457 := bstep (se 2 (by rfl) ⟨1333671, by rfl⟩ : syracuseStep 3556457 = 2667343) B2667343
theorem B21349493 : Blo 830350 21349493 := bstep (se 5 (by rfl) ⟨1000757, by rfl⟩ : syracuseStep 21349493 = 2001515) B2001515
theorem B2999767 : Blo 830350 2999767 := bstep (se 1 (by rfl) ⟨2249825, by rfl⟩ : syracuseStep 2999767 = 4499651) B4499651
theorem B2803193 : Blo 830350 2803193 := bstep (se 2 (by rfl) ⟨1051197, by rfl⟩ : syracuseStep 2803193 = 2102395) B2102395
theorem B2803463 : Blo 830350 2803463 := bstep (se 1 (by rfl) ⟨2102597, by rfl⟩ : syracuseStep 2803463 = 4205195) B4205195
theorem B2803517 : Blo 830350 2803517 := bstep (se 3 (by rfl) ⟨525659, by rfl⟩ : syracuseStep 2803517 = 1051319) B1051319
theorem B935743 : Blo 830350 935743 := bstep (se 1 (by rfl) ⟨701807, by rfl⟩ : syracuseStep 935743 = 1403615) B1403615
theorem B936031 : Blo 830350 936031 := bstep (se 1 (by rfl) ⟨702023, by rfl⟩ : syracuseStep 936031 = 1404047) B1404047
theorem B4212971 : Blo 830350 4212971 := bstep (se 1 (by rfl) ⟨3159728, by rfl⟩ : syracuseStep 4212971 = 6319457) B6319457
theorem B3000833 : Blo 830350 3000833 := bstep (se 2 (by rfl) ⟨1125312, by rfl⟩ : syracuseStep 3000833 = 2250625) B2250625
theorem B4737953 : Blo 830350 4737953 := bstep (se 2 (by rfl) ⟨1776732, by rfl⟩ : syracuseStep 4737953 = 3553465) B3553465
theorem B937183 : Blo 830350 937183 := bstep (se 1 (by rfl) ⟨702887, by rfl⟩ : syracuseStep 937183 = 1405775) B1405775
theorem B7982459 : Blo 830350 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B5328251 : Blo 830350 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B8015287 : Blo 830350 8015287 := bstep (se 1 (by rfl) ⟨6011465, by rfl⟩ : syracuseStep 8015287 = 12022931) B12022931
theorem B4214267 : Blo 830350 4214267 := bstep (se 1 (by rfl) ⟨3160700, by rfl⟩ : syracuseStep 4214267 = 6321401) B6321401
theorem B4214429 : Blo 830350 4214429 := bstep (se 3 (by rfl) ⟨790205, by rfl⟩ : syracuseStep 4214429 = 1580411) B1580411
theorem B3559069 : Blo 830350 3559069 := bstep (se 3 (by rfl) ⟨667325, by rfl⟩ : syracuseStep 3559069 = 1334651) B1334651
theorem B1691431 : Blo 830350 1691431 := bstep (se 1 (by rfl) ⟨1268573, by rfl⟩ : syracuseStep 1691431 = 2537147) B2537147
theorem B4116329 : Blo 830350 4116329 := bstep (se 2 (by rfl) ⟨1543623, by rfl⟩ : syracuseStep 4116329 = 3087247) B3087247
theorem B7982995 : Blo 830350 7982995 := bstep (se 1 (by rfl) ⟨5987246, by rfl⟩ : syracuseStep 7982995 = 11974493) B11974493
theorem B10670237 : Blo 830350 10670237 := bstep (se 3 (by rfl) ⟨2000669, by rfl⟩ : syracuseStep 10670237 = 4001339) B4001339
theorem B2805947 : Blo 830350 2805947 := bstep (se 1 (by rfl) ⟨2104460, by rfl⟩ : syracuseStep 2805947 = 4208921) B4208921
theorem B1200511 : Blo 830350 1200511 := bstep (se 1 (by rfl) ⟨900383, by rfl⟩ : syracuseStep 1200511 = 1800767) B1800767
theorem B1921619 : Blo 830350 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B2806433 : Blo 830350 2806433 := bstep (se 2 (by rfl) ⟨1052412, by rfl⟩ : syracuseStep 2806433 = 2104825) B2104825
theorem B5395127 : Blo 830350 5395127 := bstep (se 1 (by rfl) ⟨4046345, by rfl⟩ : syracuseStep 5395127 = 8092691) B8092691
theorem B4510505 : Blo 830350 4510505 := bstep (se 2 (by rfl) ⟨1691439, by rfl⟩ : syracuseStep 4510505 = 3382879) B3382879
theorem B19256399 : Blo 830350 19256399 := bstep (se 1 (by rfl) ⟨14442299, by rfl⟩ : syracuseStep 19256399 = 28884599) B28884599
theorem B7591009 : Blo 830350 7591009 := bstep (se 2 (by rfl) ⟨2846628, by rfl⟩ : syracuseStep 7591009 = 5693257) B5693257
theorem B3003601 : Blo 830350 3003601 := bstep (se 2 (by rfl) ⟨1126350, by rfl⟩ : syracuseStep 3003601 = 2252701) B2252701
theorem B2807297 : Blo 830350 2807297 := bstep (se 2 (by rfl) ⟨1052736, by rfl⟩ : syracuseStep 2807297 = 2105473) B2105473
theorem B1496827 : Blo 830350 1496827 := bstep (se 1 (by rfl) ⟨1122620, by rfl⟩ : syracuseStep 1496827 = 2245241) B2245241
theorem B2807783 : Blo 830350 2807783 := bstep (se 1 (by rfl) ⟨2105837, by rfl⟩ : syracuseStep 2807783 = 4211675) B4211675
theorem B2807891 : Blo 830350 2807891 := bstep (se 1 (by rfl) ⟨2105918, by rfl⟩ : syracuseStep 2807891 = 4211837) B4211837
theorem B2808107 : Blo 830350 2808107 := bstep (se 1 (by rfl) ⟨2106080, by rfl⟩ : syracuseStep 2808107 = 4212161) B4212161
theorem B2808377 : Blo 830350 2808377 := bstep (se 2 (by rfl) ⟨1053141, by rfl⟩ : syracuseStep 2808377 = 2106283) B2106283
theorem B5069449 : Blo 830350 5069449 := bstep (se 2 (by rfl) ⟨1901043, by rfl⟩ : syracuseStep 5069449 = 3802087) B3802087
theorem B3857053 : Blo 830350 3857053 := bstep (se 3 (by rfl) ⟨723197, by rfl⟩ : syracuseStep 3857053 = 1446395) B1446395
theorem B6085367 : Blo 830350 6085367 := bstep (se 1 (by rfl) ⟨4564025, by rfl⟩ : syracuseStep 6085367 = 9128051) B9128051
theorem B10836827 : Blo 830350 10836827 := bstep (se 1 (by rfl) ⟨8127620, by rfl⟩ : syracuseStep 10836827 = 16255241) B16255241
theorem B4873085 : Blo 830350 4873085 := bstep (se 3 (by rfl) ⟨913703, by rfl⟩ : syracuseStep 4873085 = 1827407) B1827407
theorem B3562487 : Blo 830350 3562487 := bstep (se 1 (by rfl) ⟨2671865, by rfl⟩ : syracuseStep 3562487 = 5343731) B5343731
theorem B7691321 : Blo 830350 7691321 := bstep (se 2 (by rfl) ⟨2884245, by rfl⟩ : syracuseStep 7691321 = 5768491) B5768491
theorem B10673927 : Blo 830350 10673927 := bstep (se 1 (by rfl) ⟨8005445, by rfl⟩ : syracuseStep 10673927 = 16010891) B16010891
theorem B5988143 : Blo 830350 5988143 := bstep (se 1 (by rfl) ⟨4491107, by rfl⟩ : syracuseStep 5988143 = 8982215) B8982215
theorem B4743035 : Blo 830350 4743035 := bstep (se 1 (by rfl) ⟨3557276, by rfl⟩ : syracuseStep 4743035 = 7114553) B7114553
theorem B2809889 : Blo 830350 2809889 := bstep (se 2 (by rfl) ⟨1053708, by rfl⟩ : syracuseStep 2809889 = 2107417) B2107417
theorem B4219127 : Blo 830350 4219127 := bstep (se 1 (by rfl) ⟨3164345, by rfl⟩ : syracuseStep 4219127 = 6328691) B6328691
theorem B1401961 : Blo 830350 1401961 := bstep (se 2 (by rfl) ⟨525735, by rfl⟩ : syracuseStep 1401961 = 1051471) B1051471
theorem B1500265 : Blo 830350 1500265 := bstep (se 2 (by rfl) ⟨562599, by rfl⟩ : syracuseStep 1500265 = 1125199) B1125199
theorem B1402535 : Blo 830350 1402535 := bstep (se 1 (by rfl) ⟨1051901, by rfl⟩ : syracuseStep 1402535 = 2103803) B2103803
theorem B1403183 : Blo 830350 1403183 := bstep (se 1 (by rfl) ⟨1052387, by rfl⟩ : syracuseStep 1403183 = 2104775) B2104775
theorem B6416891 : Blo 830350 6416891 := bstep (se 1 (by rfl) ⟨4812668, by rfl⟩ : syracuseStep 6416891 = 9625337) B9625337
theorem B1403419 : Blo 830350 1403419 := bstep (se 1 (by rfl) ⟨1052564, by rfl⟩ : syracuseStep 1403419 = 2105129) B2105129
theorem B3992267 : Blo 830350 3992267 := bstep (se 1 (by rfl) ⟨2994200, by rfl⟩ : syracuseStep 3992267 = 5988401) B5988401
theorem B1502111 : Blo 830350 1502111 := bstep (se 1 (by rfl) ⟨1126583, by rfl⟩ : syracuseStep 1502111 = 2253167) B2253167
theorem B846919 : Blo 830350 846919 := bstep (se 1 (by rfl) ⟨635189, by rfl⟩ : syracuseStep 846919 = 1270379) B1270379
theorem B4746383 : Blo 830350 4746383 := bstep (se 1 (by rfl) ⟨3559787, by rfl⟩ : syracuseStep 4746383 = 7119575) B7119575
theorem B13495697 : Blo 830350 13495697 := bstep (se 2 (by rfl) ⟨5060886, by rfl⟩ : syracuseStep 13495697 = 10121773) B10121773
theorem B5991833 : Blo 830350 5991833 := bstep (se 2 (by rfl) ⟨2246937, by rfl⟩ : syracuseStep 5991833 = 4493875) B4493875
theorem B1404391 : Blo 830350 1404391 := bstep (se 1 (by rfl) ⟨1053293, by rfl⟩ : syracuseStep 1404391 = 2106587) B2106587
theorem B9465335 : Blo 830350 9465335 := bstep (se 1 (by rfl) ⟨7099001, by rfl⟩ : syracuseStep 9465335 = 14198003) B14198003
theorem B1404479 : Blo 830350 1404479 := bstep (se 1 (by rfl) ⟨1053359, by rfl⟩ : syracuseStep 1404479 = 2106719) B2106719
theorem B2813615 : Blo 830350 2813615 := bstep (se 1 (by rfl) ⟨2110211, by rfl⟩ : syracuseStep 2813615 = 4220423) B4220423
theorem B29191889 : Blo 830350 29191889 := bstep (se 2 (by rfl) ⟨10946958, by rfl⟩ : syracuseStep 29191889 = 21893917) B21893917
theorem B13496219 : Blo 830350 13496219 := bstep (se 1 (by rfl) ⟨10122164, by rfl⟩ : syracuseStep 13496219 = 20244329) B20244329
theorem B2813939 : Blo 830350 2813939 := bstep (se 1 (by rfl) ⟨2110454, by rfl⟩ : syracuseStep 2813939 = 4220909) B4220909
theorem B10678391 : Blo 830350 10678391 := bstep (se 1 (by rfl) ⟨8008793, by rfl⟩ : syracuseStep 10678391 = 16017587) B16017587
theorem B4812995 : Blo 830350 4812995 := bstep (se 1 (by rfl) ⟨3609746, by rfl⟩ : syracuseStep 4812995 = 7219493) B7219493
theorem B1405147 : Blo 830350 1405147 := bstep (se 1 (by rfl) ⟨1053860, by rfl⟩ : syracuseStep 1405147 = 2107721) B2107721
theorem B2814263 : Blo 830350 2814263 := bstep (se 1 (by rfl) ⟨2110697, by rfl⟩ : syracuseStep 2814263 = 4221395) B4221395
theorem B2847187 : Blo 830350 2847187 := bstep (se 1 (by rfl) ⟨2135390, by rfl⟩ : syracuseStep 2847187 = 4270781) B4270781
theorem B1405417 : Blo 830350 1405417 := bstep (se 2 (by rfl) ⟨527031, by rfl⟩ : syracuseStep 1405417 = 1054063) B1054063
theorem B2814479 : Blo 830350 2814479 := bstep (se 1 (by rfl) ⟨2110859, by rfl⟩ : syracuseStep 2814479 = 4221719) B4221719
theorem B5337683 : Blo 830350 5337683 := bstep (se 1 (by rfl) ⟨4003262, by rfl⟩ : syracuseStep 5337683 = 8006525) B8006525
theorem B1602623 : Blo 830350 1602623 := bstep (se 1 (by rfl) ⟨1201967, by rfl⟩ : syracuseStep 1602623 = 2403935) B2403935
theorem B2815559 : Blo 830350 2815559 := bstep (se 1 (by rfl) ⟨2111669, by rfl⟩ : syracuseStep 2815559 = 4223339) B4223339
theorem B1406585 : Blo 830350 1406585 := bstep (se 2 (by rfl) ⟨527469, by rfl⟩ : syracuseStep 1406585 = 1054939) B1054939
theorem B1800073 : Blo 830350 1800073 := bstep (se 2 (by rfl) ⟨675027, by rfl⟩ : syracuseStep 1800073 = 1350055) B1350055
theorem B1407071 : Blo 830350 1407071 := bstep (se 1 (by rfl) ⟨1055303, by rfl⟩ : syracuseStep 1407071 = 2110607) B2110607
theorem B19528613 : Blo 830350 19528613 := bstep (se 4 (by rfl) ⟨1830807, by rfl⟩ : syracuseStep 19528613 = 3661615) B3661615
theorem B9501785 : Blo 830350 9501785 := bstep (se 2 (by rfl) ⟨3563169, by rfl⟩ : syracuseStep 9501785 = 7126339) B7126339
theorem B1868399 : Blo 830350 1868399 := bstep (se 1 (by rfl) ⟨1401299, by rfl⟩ : syracuseStep 1868399 = 2802599) B2802599
theorem B14254865 : Blo 830350 14254865 := bstep (se 2 (by rfl) ⟨5345574, by rfl⟩ : syracuseStep 14254865 = 10691149) B10691149
theorem B1246151 : Blo 830350 1246151 := bstep (se 1 (by rfl) ⟨934613, by rfl⟩ : syracuseStep 1246151 = 1869227) B1869227
theorem B11994101 : Blo 830350 11994101 := bstep (se 5 (by rfl) ⟨562223, by rfl⟩ : syracuseStep 11994101 = 1124447) B1124447
theorem B1868795 : Blo 830350 1868795 := bstep (se 1 (by rfl) ⟨1401596, by rfl⟩ : syracuseStep 1868795 = 2803193) B2803193
theorem B1246319 : Blo 830350 1246319 := bstep (se 1 (by rfl) ⟨934739, by rfl⟩ : syracuseStep 1246319 = 1869479) B1869479
theorem B1868975 : Blo 830350 1868975 := bstep (se 1 (by rfl) ⟨1401731, by rfl⟩ : syracuseStep 1868975 = 2803463) B2803463
theorem B1869011 : Blo 830350 1869011 := bstep (se 1 (by rfl) ⟨1401758, by rfl⟩ : syracuseStep 1869011 = 2803517) B2803517
theorem B1246511 : Blo 830350 1246511 := bstep (se 1 (by rfl) ⟨934883, by rfl⟩ : syracuseStep 1246511 = 1869767) B1869767
theorem B1869281 : Blo 830350 1869281 := bstep (se 2 (by rfl) ⟨700980, by rfl⟩ : syracuseStep 1869281 = 1401961) B1401961
theorem B1246715 : Blo 830350 1246715 := bstep (se 1 (by rfl) ⟨935036, by rfl⟩ : syracuseStep 1246715 = 1870073) B1870073
theorem B1246751 : Blo 830350 1246751 := bstep (se 1 (by rfl) ⟨935063, by rfl⟩ : syracuseStep 1246751 = 1870127) B1870127
theorem B2000555 : Blo 830350 2000555 := bstep (se 1 (by rfl) ⟨1500416, by rfl⟩ : syracuseStep 2000555 = 3000833) B3000833
theorem B1246895 : Blo 830350 1246895 := bstep (se 1 (by rfl) ⟨935171, by rfl⟩ : syracuseStep 1246895 = 1870343) B1870343
theorem B1247015 : Blo 830350 1247015 := bstep (se 1 (by rfl) ⟨935261, by rfl⟩ : syracuseStep 1247015 = 1870523) B1870523
theorem B14387005 : Blo 830350 14387005 := bstep (se 3 (by rfl) ⟨2697563, by rfl⟩ : syracuseStep 14387005 = 5395127) B5395127
theorem B3999689 : Blo 830350 3999689 := bstep (se 2 (by rfl) ⟨1499883, by rfl⟩ : syracuseStep 3999689 = 2999767) B2999767
theorem B1247567 : Blo 830350 1247567 := bstep (se 1 (by rfl) ⟨935675, by rfl⟩ : syracuseStep 1247567 = 1871351) B1871351
theorem B1247615 : Blo 830350 1247615 := bstep (se 1 (by rfl) ⟨935711, by rfl⟩ : syracuseStep 1247615 = 1871423) B1871423
theorem B1247657 : Blo 830350 1247657 := bstep (se 2 (by rfl) ⟨467871, by rfl⟩ : syracuseStep 1247657 = 935743) B935743
theorem B7113491 : Blo 830350 7113491 := bstep (se 1 (by rfl) ⟨5335118, by rfl⟩ : syracuseStep 7113491 = 10670237) B10670237
theorem B1870631 : Blo 830350 1870631 := bstep (se 1 (by rfl) ⟨1402973, by rfl⟩ : syracuseStep 1870631 = 2805947) B2805947
theorem B1248041 : Blo 830350 1248041 := bstep (se 2 (by rfl) ⟨468015, by rfl⟩ : syracuseStep 1248041 = 936031) B936031
theorem B1051643 : Blo 830350 1051643 := bstep (se 1 (by rfl) ⟨788732, by rfl⟩ : syracuseStep 1051643 = 1577465) B1577465
theorem B1248251 : Blo 830350 1248251 := bstep (se 1 (by rfl) ⟨936188, by rfl⟩ : syracuseStep 1248251 = 1872377) B1872377
theorem B1281079 : Blo 830350 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B1248311 : Blo 830350 1248311 := bstep (se 1 (by rfl) ⟨936233, by rfl⟩ : syracuseStep 1248311 = 1872467) B1872467
theorem B7998527 : Blo 830350 7998527 := bstep (se 1 (by rfl) ⟨5998895, by rfl⟩ : syracuseStep 7998527 = 11997791) B11997791
theorem B1870955 : Blo 830350 1870955 := bstep (se 1 (by rfl) ⟨1403216, by rfl⟩ : syracuseStep 1870955 = 2806433) B2806433
theorem B1248431 : Blo 830350 1248431 := bstep (se 1 (by rfl) ⟨936323, by rfl⟩ : syracuseStep 1248431 = 1872647) B1872647
theorem B1871225 : Blo 830350 1871225 := bstep (se 2 (by rfl) ⟨701709, by rfl⟩ : syracuseStep 1871225 = 1403419) B1403419
theorem B27037061 : Blo 830350 27037061 := bstep (se 4 (by rfl) ⟨2534724, by rfl⟩ : syracuseStep 27037061 = 5069449) B5069449
theorem B1576417 : Blo 830350 1576417 := bstep (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) B1182313
theorem B1871531 : Blo 830350 1871531 := bstep (se 1 (by rfl) ⟨1403648, by rfl⟩ : syracuseStep 1871531 = 2807297) B2807297
theorem B1249151 : Blo 830350 1249151 := bstep (se 1 (by rfl) ⟨936863, by rfl⟩ : syracuseStep 1249151 = 1873727) B1873727
theorem B1871855 : Blo 830350 1871855 := bstep (se 1 (by rfl) ⟨1403891, by rfl⟩ : syracuseStep 1871855 = 2807783) B2807783
theorem B1773623 : Blo 830350 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B1871927 : Blo 830350 1871927 := bstep (se 1 (by rfl) ⟨1403945, by rfl⟩ : syracuseStep 1871927 = 2807891) B2807891
theorem B1249343 : Blo 830350 1249343 := bstep (se 1 (by rfl) ⟨937007, by rfl⟩ : syracuseStep 1249343 = 1874015) B1874015
theorem B1052767 : Blo 830350 1052767 := bstep (se 1 (by rfl) ⟨789575, by rfl⟩ : syracuseStep 1052767 = 1579151) B1579151
theorem B1577063 : Blo 830350 1577063 := bstep (se 1 (by rfl) ⟨1182797, by rfl⟩ : syracuseStep 1577063 = 2365595) B2365595
theorem B1872071 : Blo 830350 1872071 := bstep (se 1 (by rfl) ⟨1404053, by rfl⟩ : syracuseStep 1872071 = 2808107) B2808107
theorem B1249577 : Blo 830350 1249577 := bstep (se 2 (by rfl) ⟨468591, by rfl⟩ : syracuseStep 1249577 = 937183) B937183
theorem B1872251 : Blo 830350 1872251 := bstep (se 1 (by rfl) ⟨1404188, by rfl⟩ : syracuseStep 1872251 = 2808377) B2808377
theorem B1249847 : Blo 830350 1249847 := bstep (se 1 (by rfl) ⟨937385, by rfl⟩ : syracuseStep 1249847 = 1874771) B1874771
theorem B10687049 : Blo 830350 10687049 := bstep (se 2 (by rfl) ⟨4007643, by rfl⟩ : syracuseStep 10687049 = 8015287) B8015287
theorem B3248723 : Blo 830350 3248723 := bstep (se 1 (by rfl) ⟨2436542, by rfl⟩ : syracuseStep 3248723 = 4873085) B4873085
theorem B1872521 : Blo 830350 1872521 := bstep (se 2 (by rfl) ⟨702195, by rfl⟩ : syracuseStep 1872521 = 1404391) B1404391
theorem B1250207 : Blo 830350 1250207 := bstep (se 1 (by rfl) ⟨937655, by rfl⟩ : syracuseStep 1250207 = 1875311) B1875311
theorem B1250399 : Blo 830350 1250399 := bstep (se 1 (by rfl) ⟨937799, by rfl⟩ : syracuseStep 1250399 = 1875599) B1875599
theorem B1250459 : Blo 830350 1250459 := bstep (se 1 (by rfl) ⟨937844, by rfl⟩ : syracuseStep 1250459 = 1875689) B1875689
theorem B7115951 : Blo 830350 7115951 := bstep (se 1 (by rfl) ⟨5336963, by rfl⟩ : syracuseStep 7115951 = 10673927) B10673927
theorem B1873259 : Blo 830350 1873259 := bstep (se 1 (by rfl) ⟨1404944, by rfl⟩ : syracuseStep 1873259 = 2809889) B2809889
theorem B1873529 : Blo 830350 1873529 := bstep (se 2 (by rfl) ⟨702573, by rfl⟩ : syracuseStep 1873529 = 1405147) B1405147
theorem B1251143 : Blo 830350 1251143 := bstep (se 1 (by rfl) ⟨938357, by rfl⟩ : syracuseStep 1251143 = 1876715) B1876715
theorem B8001413 : Blo 830350 8001413 := bstep (se 4 (by rfl) ⟨750132, by rfl⟩ : syracuseStep 8001413 = 1500265) B1500265
theorem B1873889 : Blo 830350 1873889 := bstep (se 2 (by rfl) ⟨702708, by rfl⟩ : syracuseStep 1873889 = 1405417) B1405417
theorem B5708063 : Blo 830350 5708063 := bstep (se 1 (by rfl) ⟨4281047, by rfl⟩ : syracuseStep 5708063 = 8562095) B8562095
theorem B2103691 : Blo 830350 2103691 := bstep (se 1 (by rfl) ⟨1577768, by rfl⟩ : syracuseStep 2103691 = 3155537) B3155537
theorem B1055207 : Blo 830350 1055207 := bstep (se 1 (by rfl) ⟨791405, by rfl⟩ : syracuseStep 1055207 = 1582811) B1582811
theorem B4004801 : Blo 830350 4004801 := bstep (se 2 (by rfl) ⟨1501800, by rfl⟩ : syracuseStep 4004801 = 3003601) B3003601
theorem B3382393 : Blo 830350 3382393 := bstep (se 2 (by rfl) ⟨1268397, by rfl⟩ : syracuseStep 3382393 = 2536795) B2536795
theorem B2661511 : Blo 830350 2661511 := bstep (se 1 (by rfl) ⟨1996133, by rfl⟩ : syracuseStep 2661511 = 3992267) B3992267
theorem B4005071 : Blo 830350 4005071 := bstep (se 1 (by rfl) ⟨3003803, by rfl⟩ : syracuseStep 4005071 = 6007607) B6007607
theorem B1875743 : Blo 830350 1875743 := bstep (se 1 (by rfl) ⟨1406807, by rfl⟩ : syracuseStep 1875743 = 2813615) B2813615
theorem B3153761 : Blo 830350 3153761 := bstep (se 2 (by rfl) ⟨1182660, by rfl⟩ : syracuseStep 3153761 = 2365321) B2365321
theorem B1580897 : Blo 830350 1580897 := bstep (se 2 (by rfl) ⟨592836, by rfl⟩ : syracuseStep 1580897 = 1185673) B1185673
theorem B2105311 : Blo 830350 2105311 := bstep (se 1 (by rfl) ⟨1578983, by rfl⟩ : syracuseStep 2105311 = 3157967) B3157967
theorem B1875959 : Blo 830350 1875959 := bstep (se 1 (by rfl) ⟨1406969, by rfl⟩ : syracuseStep 1875959 = 2813939) B2813939
theorem B7118927 : Blo 830350 7118927 := bstep (se 1 (by rfl) ⟨5339195, by rfl⟩ : syracuseStep 7118927 = 10678391) B10678391
theorem B3154049 : Blo 830350 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B1876175 : Blo 830350 1876175 := bstep (se 1 (by rfl) ⟨1407131, by rfl⟩ : syracuseStep 1876175 = 2814263) B2814263
theorem B1876319 : Blo 830350 1876319 := bstep (se 1 (by rfl) ⟨1407239, by rfl⟩ : syracuseStep 1876319 = 2814479) B2814479
theorem B2367883 : Blo 830350 2367883 := bstep (se 1 (by rfl) ⟨1775912, by rfl⟩ : syracuseStep 2367883 = 3551825) B3551825
theorem B2105939 : Blo 830350 2105939 := bstep (se 1 (by rfl) ⟨1579454, by rfl⟩ : syracuseStep 2105939 = 3158909) B3158909
theorem B9118493 : Blo 830350 9118493 := bstep (se 3 (by rfl) ⟨1709717, by rfl⟩ : syracuseStep 9118493 = 3419435) B3419435
theorem B1877039 : Blo 830350 1877039 := bstep (se 1 (by rfl) ⟨1407779, by rfl⟩ : syracuseStep 1877039 = 2815559) B2815559
theorem B3155219 : Blo 830350 3155219 := bstep (se 1 (by rfl) ⟨2366414, by rfl⟩ : syracuseStep 3155219 = 4732829) B4732829
theorem B1582355 : Blo 830350 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B9020965 : Blo 830350 9020965 := bstep (se 4 (by rfl) ⟨845715, by rfl⟩ : syracuseStep 9020965 = 1691431) B1691431
theorem B3417985 : Blo 830350 3417985 := bstep (se 2 (by rfl) ⟨1281744, by rfl⟩ : syracuseStep 3417985 = 2563489) B2563489
theorem B1583039 : Blo 830350 1583039 := bstep (se 1 (by rfl) ⟨1187279, by rfl⟩ : syracuseStep 1583039 = 2374559) B2374559
theorem B4007875 : Blo 830350 4007875 := bstep (se 1 (by rfl) ⟨3005906, by rfl⟩ : syracuseStep 4007875 = 6011813) B6011813
theorem B13019075 : Blo 830350 13019075 := bstep (se 1 (by rfl) ⟨9764306, by rfl⟩ : syracuseStep 13019075 = 19528613) B19528613
theorem B6334523 : Blo 830350 6334523 := bstep (se 1 (by rfl) ⟨4750892, by rfl⟩ : syracuseStep 6334523 = 9501785) B9501785
theorem B3549433 : Blo 830350 3549433 := bstep (se 2 (by rfl) ⟨1331037, by rfl⟩ : syracuseStep 3549433 = 2662075) B2662075
theorem B2107883 : Blo 830350 2107883 := bstep (se 1 (by rfl) ⟨1580912, by rfl⟩ : syracuseStep 2107883 = 3161825) B3161825
theorem B21375737 : Blo 830350 21375737 := bstep (se 2 (by rfl) ⟨8015901, by rfl⟩ : syracuseStep 21375737 = 16031803) B16031803
theorem B4205519 : Blo 830350 4205519 := bstep (se 1 (by rfl) ⟨3154139, by rfl⟩ : syracuseStep 4205519 = 6308279) B6308279
theorem B830431 : Blo 830350 830431 := bstep (se 1 (by rfl) ⟨622823, by rfl⟩ : syracuseStep 830431 = 1245647) B1245647
theorem B830459 : Blo 830350 830459 := bstep (se 1 (by rfl) ⟨622844, by rfl⟩ : syracuseStep 830459 = 1245689) B1245689
theorem B830527 : Blo 830350 830527 := bstep (se 1 (by rfl) ⟨622895, by rfl⟩ : syracuseStep 830527 = 1245791) B1245791
theorem B5844347 : Blo 830350 5844347 := bstep (se 1 (by rfl) ⟨4383260, by rfl⟩ : syracuseStep 5844347 = 8766521) B8766521
theorem B830847 : Blo 830350 830847 := bstep (se 1 (by rfl) ⟨623135, by rfl⟩ : syracuseStep 830847 = 1246271) B1246271
theorem B830875 : Blo 830350 830875 := bstep (se 1 (by rfl) ⟨623156, by rfl⟩ : syracuseStep 830875 = 1246313) B1246313
theorem B2370971 : Blo 830350 2370971 := bstep (se 1 (by rfl) ⟨1778228, by rfl⟩ : syracuseStep 2370971 = 3556457) B3556457
theorem B14232995 : Blo 830350 14232995 := bstep (se 1 (by rfl) ⟨10674746, by rfl⟩ : syracuseStep 14232995 = 21349493) B21349493
theorem B830943 : Blo 830350 830943 := bstep (se 1 (by rfl) ⟨623207, by rfl⟩ : syracuseStep 830943 = 1246415) B1246415
theorem B831079 : Blo 830350 831079 := bstep (se 1 (by rfl) ⟨623309, by rfl⟩ : syracuseStep 831079 = 1246619) B1246619
theorem B831227 : Blo 830350 831227 := bstep (se 1 (by rfl) ⟨623420, by rfl⟩ : syracuseStep 831227 = 1246841) B1246841
theorem B831295 : Blo 830350 831295 := bstep (se 1 (by rfl) ⟨623471, by rfl⟩ : syracuseStep 831295 = 1246943) B1246943
theorem B831359 : Blo 830350 831359 := bstep (se 1 (by rfl) ⟨623519, by rfl⟩ : syracuseStep 831359 = 1247039) B1247039
theorem B831471 : Blo 830350 831471 := bstep (se 1 (by rfl) ⟨623603, by rfl⟩ : syracuseStep 831471 = 1247207) B1247207
theorem B831483 : Blo 830350 831483 := bstep (se 1 (by rfl) ⟨623612, by rfl⟩ : syracuseStep 831483 = 1247225) B1247225
theorem B831551 : Blo 830350 831551 := bstep (se 1 (by rfl) ⟨623663, by rfl⟩ : syracuseStep 831551 = 1247327) B1247327
theorem B831591 : Blo 830350 831591 := bstep (se 1 (by rfl) ⟨623693, by rfl⟩ : syracuseStep 831591 = 1247387) B1247387
theorem B9613417 : Blo 830350 9613417 := bstep (se 2 (by rfl) ⟨3605031, by rfl⟩ : syracuseStep 9613417 = 7210063) B7210063
theorem B831615 : Blo 830350 831615 := bstep (se 1 (by rfl) ⟨623711, by rfl⟩ : syracuseStep 831615 = 1247423) B1247423
theorem B831643 : Blo 830350 831643 := bstep (se 1 (by rfl) ⟨623732, by rfl⟩ : syracuseStep 831643 = 1247465) B1247465
theorem B831847 : Blo 830350 831847 := bstep (se 1 (by rfl) ⟨623885, by rfl⟩ : syracuseStep 831847 = 1247771) B1247771
theorem B831899 : Blo 830350 831899 := bstep (se 1 (by rfl) ⟨623924, by rfl⟩ : syracuseStep 831899 = 1247849) B1247849
theorem B2110009 : Blo 830350 2110009 := bstep (se 2 (by rfl) ⟨791253, by rfl⟩ : syracuseStep 2110009 = 1582507) B1582507
theorem B3158635 : Blo 830350 3158635 := bstep (se 1 (by rfl) ⟨2368976, by rfl⟩ : syracuseStep 3158635 = 4737953) B4737953
theorem B6402725 : Blo 830350 6402725 := bstep (se 4 (by rfl) ⟨600255, by rfl⟩ : syracuseStep 6402725 = 1200511) B1200511
theorem B832251 : Blo 830350 832251 := bstep (se 1 (by rfl) ⟨624188, by rfl⟩ : syracuseStep 832251 = 1248377) B1248377
theorem B832319 : Blo 830350 832319 := bstep (se 1 (by rfl) ⟨624239, by rfl⟩ : syracuseStep 832319 = 1248479) B1248479
theorem B832347 : Blo 830350 832347 := bstep (se 1 (by rfl) ⟨624260, by rfl⟩ : syracuseStep 832347 = 1248521) B1248521
theorem B832415 : Blo 830350 832415 := bstep (se 1 (by rfl) ⟨624311, by rfl⟩ : syracuseStep 832415 = 1248623) B1248623
theorem B5321639 : Blo 830350 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B3552167 : Blo 830350 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B832495 : Blo 830350 832495 := bstep (se 1 (by rfl) ⟨624371, by rfl⟩ : syracuseStep 832495 = 1248743) B1248743
theorem B4207625 : Blo 830350 4207625 := bstep (se 2 (by rfl) ⟨1577859, by rfl⟩ : syracuseStep 4207625 = 3155719) B3155719
theorem B832583 : Blo 830350 832583 := bstep (se 1 (by rfl) ⟨624437, by rfl⟩ : syracuseStep 832583 = 1248875) B1248875
theorem B832667 : Blo 830350 832667 := bstep (se 1 (by rfl) ⟨624500, by rfl⟩ : syracuseStep 832667 = 1249001) B1249001
theorem B832763 : Blo 830350 832763 := bstep (se 1 (by rfl) ⟨624572, by rfl⟩ : syracuseStep 832763 = 1249145) B1249145
theorem B832831 : Blo 830350 832831 := bstep (se 1 (by rfl) ⟨624623, by rfl⟩ : syracuseStep 832831 = 1249247) B1249247
theorem B11974031 : Blo 830350 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B832999 : Blo 830350 832999 := bstep (se 1 (by rfl) ⟨624749, by rfl⟩ : syracuseStep 832999 = 1249499) B1249499
theorem B833007 : Blo 830350 833007 := bstep (se 1 (by rfl) ⟨624755, by rfl⟩ : syracuseStep 833007 = 1249511) B1249511
theorem B4273661 : Blo 830350 4273661 := bstep (se 3 (by rfl) ⟨801311, by rfl⟩ : syracuseStep 4273661 = 1602623) B1602623
theorem B14202377 : Blo 830350 14202377 := bstep (se 2 (by rfl) ⟨5325891, by rfl⟩ : syracuseStep 14202377 = 10651783) B10651783
theorem B833115 : Blo 830350 833115 := bstep (se 1 (by rfl) ⟨624836, by rfl⟩ : syracuseStep 833115 = 1249673) B1249673
theorem B833179 : Blo 830350 833179 := bstep (se 1 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 833179 = 1249769) B1249769
theorem B833263 : Blo 830350 833263 := bstep (se 1 (by rfl) ⟨624947, by rfl⟩ : syracuseStep 833263 = 1249895) B1249895
theorem B833351 : Blo 830350 833351 := bstep (se 1 (by rfl) ⟨625013, by rfl⟩ : syracuseStep 833351 = 1250027) B1250027
theorem B833371 : Blo 830350 833371 := bstep (se 1 (by rfl) ⟨625028, by rfl⟩ : syracuseStep 833371 = 1250057) B1250057
theorem B833439 : Blo 830350 833439 := bstep (se 1 (by rfl) ⟨625079, by rfl⟩ : syracuseStep 833439 = 1250159) B1250159
theorem B2668585 : Blo 830350 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B833607 : Blo 830350 833607 := bstep (se 1 (by rfl) ⟨625205, by rfl⟩ : syracuseStep 833607 = 1250411) B1250411
theorem B833767 : Blo 830350 833767 := bstep (se 1 (by rfl) ⟨625325, by rfl⟩ : syracuseStep 833767 = 1250651) B1250651
theorem B833951 : Blo 830350 833951 := bstep (se 1 (by rfl) ⟨625463, by rfl⟩ : syracuseStep 833951 = 1250927) B1250927
theorem B833999 : Blo 830350 833999 := bstep (se 1 (by rfl) ⟨625499, by rfl⟩ : syracuseStep 833999 = 1250999) B1250999
theorem B834023 : Blo 830350 834023 := bstep (se 1 (by rfl) ⟨625517, by rfl⟩ : syracuseStep 834023 = 1251035) B1251035
theorem B4045319 : Blo 830350 4045319 := bstep (se 1 (by rfl) ⟨3033989, by rfl⟩ : syracuseStep 4045319 = 6067979) B6067979
theorem B834139 : Blo 830350 834139 := bstep (se 1 (by rfl) ⟨625604, by rfl⟩ : syracuseStep 834139 = 1251209) B1251209
theorem B834207 : Blo 830350 834207 := bstep (se 1 (by rfl) ⟨625655, by rfl⟩ : syracuseStep 834207 = 1251311) B1251311
theorem B7224551 : Blo 830350 7224551 := bstep (se 1 (by rfl) ⟨5418413, by rfl⟩ : syracuseStep 7224551 = 10836827) B10836827
theorem B2374991 : Blo 830350 2374991 := bstep (se 1 (by rfl) ⟨1781243, by rfl⟩ : syracuseStep 2374991 = 3562487) B3562487
theorem B5127547 : Blo 830350 5127547 := bstep (se 1 (by rfl) ⟨3845660, by rfl⟩ : syracuseStep 5127547 = 7691321) B7691321
theorem B1425127 : Blo 830350 1425127 := bstep (se 1 (by rfl) ⟨1068845, by rfl⟩ : syracuseStep 1425127 = 2137691) B2137691
theorem B3162023 : Blo 830350 3162023 := bstep (se 1 (by rfl) ⟨2371517, by rfl⟩ : syracuseStep 3162023 = 4743035) B4743035
theorem B15975215 : Blo 830350 15975215 := bstep (se 1 (by rfl) ⟨11981411, by rfl⟩ : syracuseStep 15975215 = 23962823) B23962823
theorem B3163009 : Blo 830350 3163009 := bstep (se 2 (by rfl) ⟨1186128, by rfl⟩ : syracuseStep 3163009 = 2372257) B2372257
theorem B2671649 : Blo 830350 2671649 := bstep (se 2 (by rfl) ⟨1001868, by rfl⟩ : syracuseStep 2671649 = 2003737) B2003737
theorem B1688683 : Blo 830350 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B935023 : Blo 830350 935023 := bstep (se 1 (by rfl) ⟨701267, by rfl⟩ : syracuseStep 935023 = 1402535) B1402535
theorem B2802923 : Blo 830350 2802923 := bstep (se 1 (by rfl) ⟨2102192, by rfl⟩ : syracuseStep 2802923 = 4204385) B4204385
theorem B935455 : Blo 830350 935455 := bstep (se 1 (by rfl) ⟨701591, by rfl⟩ : syracuseStep 935455 = 1403183) B1403183
theorem B3163769 : Blo 830350 3163769 := bstep (se 2 (by rfl) ⟨1186413, by rfl⟩ : syracuseStep 3163769 = 2372827) B2372827
theorem B4277927 : Blo 830350 4277927 := bstep (se 1 (by rfl) ⟨3208445, by rfl⟩ : syracuseStep 4277927 = 6416891) B6416891
theorem B1001407 : Blo 830350 1001407 := bstep (se 1 (by rfl) ⟨751055, by rfl⟩ : syracuseStep 1001407 = 1502111) B1502111
theorem B3164255 : Blo 830350 3164255 := bstep (se 1 (by rfl) ⟨2373191, by rfl⟩ : syracuseStep 3164255 = 4746383) B4746383
theorem B8997131 : Blo 830350 8997131 := bstep (se 1 (by rfl) ⟨6747848, by rfl⟩ : syracuseStep 8997131 = 13495697) B13495697
theorem B6310223 : Blo 830350 6310223 := bstep (se 1 (by rfl) ⟨4732667, by rfl⟩ : syracuseStep 6310223 = 9465335) B9465335
theorem B936319 : Blo 830350 936319 := bstep (se 1 (by rfl) ⟨702239, by rfl⟩ : syracuseStep 936319 = 1404479) B1404479
theorem B2804327 : Blo 830350 2804327 := bstep (se 1 (by rfl) ⟨2103245, by rfl⟩ : syracuseStep 2804327 = 4206491) B4206491
theorem B8997479 : Blo 830350 8997479 := bstep (se 1 (by rfl) ⟨6748109, by rfl⟩ : syracuseStep 8997479 = 13496219) B13496219
theorem B3164953 : Blo 830350 3164953 := bstep (se 2 (by rfl) ⟨1186857, by rfl⟩ : syracuseStep 3164953 = 2373715) B2373715
theorem B2804705 : Blo 830350 2804705 := bstep (se 2 (by rfl) ⟨1051764, by rfl⟩ : syracuseStep 2804705 = 2103529) B2103529
theorem B3558455 : Blo 830350 3558455 := bstep (se 1 (by rfl) ⟨2668841, by rfl⟩ : syracuseStep 3558455 = 5337683) B5337683
theorem B15978221 : Blo 830350 15978221 := bstep (se 3 (by rfl) ⟨2995916, by rfl⟩ : syracuseStep 15978221 = 5991833) B5991833
theorem B937723 : Blo 830350 937723 := bstep (se 1 (by rfl) ⟨703292, by rfl⟩ : syracuseStep 937723 = 1406585) B1406585
theorem B938047 : Blo 830350 938047 := bstep (se 1 (by rfl) ⟨703535, by rfl⟩ : syracuseStep 938047 = 1407071) B1407071
theorem B8114363 : Blo 830350 8114363 := bstep (se 1 (by rfl) ⟨6085772, by rfl⟩ : syracuseStep 8114363 = 12171545) B12171545
theorem B3167201 : Blo 830350 3167201 := bstep (se 2 (by rfl) ⟨1187700, by rfl⟩ : syracuseStep 3167201 = 2375401) B2375401
theorem B9491579 : Blo 830350 9491579 := bstep (se 1 (by rfl) ⟨7118684, by rfl⟩ : syracuseStep 9491579 = 14237369) B14237369
theorem B7984919 : Blo 830350 7984919 := bstep (se 1 (by rfl) ⟨5988689, by rfl⟩ : syracuseStep 7984919 = 11977379) B11977379
theorem B2808161 : Blo 830350 2808161 := bstep (se 2 (by rfl) ⟨1053060, by rfl⟩ : syracuseStep 2808161 = 2106121) B2106121
theorem B45570761 : Blo 830350 45570761 := bstep (se 2 (by rfl) ⟨17089035, by rfl⟩ : syracuseStep 45570761 = 34178071) B34178071
theorem B2808647 : Blo 830350 2808647 := bstep (se 1 (by rfl) ⟨2106485, by rfl⟩ : syracuseStep 2808647 = 4212971) B4212971
theorem B4742509 : Blo 830350 4742509 := bstep (se 3 (by rfl) ⟨889220, by rfl⟩ : syracuseStep 4742509 = 1778441) B1778441
theorem B1498745 : Blo 830350 1498745 := bstep (se 2 (by rfl) ⟨562029, by rfl⟩ : syracuseStep 1498745 = 1124059) B1124059
theorem B2809511 : Blo 830350 2809511 := bstep (se 1 (by rfl) ⟨2107133, by rfl⟩ : syracuseStep 2809511 = 4214267) B4214267
theorem B2809619 : Blo 830350 2809619 := bstep (se 1 (by rfl) ⟨2107214, by rfl⟩ : syracuseStep 2809619 = 4214429) B4214429
theorem B1204079 : Blo 830350 1204079 := bstep (se 1 (by rfl) ⟨903059, by rfl⟩ : syracuseStep 1204079 = 1806119) B1806119
theorem B2744219 : Blo 830350 2744219 := bstep (se 1 (by rfl) ⟨2058164, by rfl⟩ : syracuseStep 2744219 = 4116329) B4116329
theorem B5333273 : Blo 830350 5333273 := bstep (se 2 (by rfl) ⟨1999977, by rfl⟩ : syracuseStep 5333273 = 3999955) B3999955
theorem B3203489 : Blo 830350 3203489 := bstep (se 2 (by rfl) ⟨1201308, by rfl⟩ : syracuseStep 3203489 = 2402617) B2402617
theorem B3007003 : Blo 830350 3007003 := bstep (se 1 (by rfl) ⟨2255252, by rfl⟩ : syracuseStep 3007003 = 4510505) B4510505
theorem B1401563 : Blo 830350 1401563 := bstep (se 1 (by rfl) ⟨1051172, by rfl⟩ : syracuseStep 1401563 = 2102345) B2102345
theorem B12837599 : Blo 830350 12837599 := bstep (se 1 (by rfl) ⟨9628199, by rfl⟩ : syracuseStep 12837599 = 19256399) B19256399
theorem B7988381 : Blo 830350 7988381 := bstep (se 3 (by rfl) ⟨1497821, by rfl⟩ : syracuseStep 7988381 = 2995643) B2995643
theorem B4056911 : Blo 830350 4056911 := bstep (se 1 (by rfl) ⟨3042683, by rfl⟩ : syracuseStep 4056911 = 6085367) B6085367
theorem B1402859 : Blo 830350 1402859 := bstep (se 1 (by rfl) ⟨1052144, by rfl⟩ : syracuseStep 1402859 = 2104289) B2104289
theorem B5400695 : Blo 830350 5400695 := bstep (se 1 (by rfl) ⟨4050521, by rfl⟩ : syracuseStep 5400695 = 8101043) B8101043
theorem B4221071 : Blo 830350 4221071 := bstep (se 1 (by rfl) ⟨3165803, by rfl⟩ : syracuseStep 4221071 = 6331607) B6331607
theorem B4745425 : Blo 830350 4745425 := bstep (se 2 (by rfl) ⟨1779534, by rfl⟩ : syracuseStep 4745425 = 3559069) B3559069
theorem B10643993 : Blo 830350 10643993 := bstep (se 2 (by rfl) ⟨3991497, by rfl⟩ : syracuseStep 10643993 = 7982995) B7982995
theorem B3992095 : Blo 830350 3992095 := bstep (se 1 (by rfl) ⟨2994071, by rfl⟩ : syracuseStep 3992095 = 5988143) B5988143
theorem B2812751 : Blo 830350 2812751 := bstep (se 1 (by rfl) ⟨2109563, by rfl⟩ : syracuseStep 2812751 = 4219127) B4219127
theorem B4516901 : Blo 830350 4516901 := bstep (se 4 (by rfl) ⟨423459, by rfl⟩ : syracuseStep 4516901 = 846919) B846919
theorem B3796249 : Blo 830350 3796249 := bstep (se 2 (by rfl) ⟨1423593, by rfl⟩ : syracuseStep 3796249 = 2847187) B2847187
theorem B1797857 : Blo 830350 1797857 := bstep (se 2 (by rfl) ⟨674196, by rfl⟩ : syracuseStep 1797857 = 1348393) B1348393
theorem B158232527 : Blo 830350 158232527 := bstep (se 1 (by rfl) ⟨118674395, by rfl⟩ : syracuseStep 158232527 = 237348791) B237348791
theorem B10121345 : Blo 830350 10121345 := bstep (se 2 (by rfl) ⟨3795504, by rfl⟩ : syracuseStep 10121345 = 7591009) B7591009
theorem B1602283 : Blo 830350 1602283 := bstep (se 1 (by rfl) ⟨1201712, by rfl⟩ : syracuseStep 1602283 = 2403425) B2403425
theorem B1405903 : Blo 830350 1405903 := bstep (se 1 (by rfl) ⟨1054427, by rfl⟩ : syracuseStep 1405903 = 2108855) B2108855
theorem B1995769 : Blo 830350 1995769 := bstep (se 2 (by rfl) ⟨748413, by rfl⟩ : syracuseStep 1995769 = 1496827) B1496827
theorem B19461259 : Blo 830350 19461259 := bstep (se 1 (by rfl) ⟨14595944, by rfl⟩ : syracuseStep 19461259 = 29191889) B29191889
theorem B5338399 : Blo 830350 5338399 := bstep (se 1 (by rfl) ⟨4003799, by rfl⟩ : syracuseStep 5338399 = 8007599) B8007599
theorem B2848063 : Blo 830350 2848063 := bstep (se 1 (by rfl) ⟨2136047, by rfl⟩ : syracuseStep 2848063 = 4272095) B4272095
theorem B3208663 : Blo 830350 3208663 := bstep (se 1 (by rfl) ⟨2406497, by rfl⟩ : syracuseStep 3208663 = 4812995) B4812995
theorem B1407017 : Blo 830350 1407017 := bstep (se 2 (by rfl) ⟨527631, by rfl⟩ : syracuseStep 1407017 = 1055263) B1055263
theorem B5142737 : Blo 830350 5142737 := bstep (se 2 (by rfl) ⟨1928526, by rfl⟩ : syracuseStep 5142737 = 3857053) B3857053
theorem B3603041 : Blo 830350 3603041 := bstep (se 2 (by rfl) ⟨1351140, by rfl⟩ : syracuseStep 3603041 = 2702281) B2702281
theorem B1407631 : Blo 830350 1407631 := bstep (se 1 (by rfl) ⟨1055723, by rfl⟩ : syracuseStep 1407631 = 2111447) B2111447
theorem B1997615 : Blo 830350 1997615 := bstep (se 1 (by rfl) ⟨1498211, by rfl⟩ : syracuseStep 1997615 = 2996423) B2996423
theorem B1998047 : Blo 830350 1998047 := bstep (se 1 (by rfl) ⟨1498535, by rfl⟩ : syracuseStep 1998047 = 2997071) B2997071
theorem B9600389 : Blo 830350 9600389 := bstep (se 4 (by rfl) ⟨900036, by rfl⟩ : syracuseStep 9600389 = 1800073) B1800073
theorem B1998287 : Blo 830350 1998287 := bstep (se 1 (by rfl) ⟨1498715, by rfl⟩ : syracuseStep 1998287 = 2997431) B2997431
theorem B16416215 : Blo 830350 16416215 := bstep (se 1 (by rfl) ⟨12312161, by rfl⟩ : syracuseStep 16416215 = 24624323) B24624323
theorem B1245599 : Blo 830350 1245599 := bstep (se 1 (by rfl) ⟨934199, by rfl⟩ : syracuseStep 1245599 = 1868399) B1868399
theorem B9503243 : Blo 830350 9503243 := bstep (se 1 (by rfl) ⟨7127432, by rfl⟩ : syracuseStep 9503243 = 14254865) B14254865
theorem B10650143 : Blo 830350 10650143 := bstep (se 1 (by rfl) ⟨7987607, by rfl⟩ : syracuseStep 10650143 = 15975215) B15975215
theorem B7996067 : Blo 830350 7996067 := bstep (se 1 (by rfl) ⟨5997050, by rfl⟩ : syracuseStep 7996067 = 11994101) B11994101
theorem B1245863 : Blo 830350 1245863 := bstep (se 1 (by rfl) ⟨934397, by rfl⟩ : syracuseStep 1245863 = 1868795) B1868795
theorem B1245983 : Blo 830350 1245983 := bstep (se 1 (by rfl) ⟨934487, by rfl⟩ : syracuseStep 1245983 = 1868975) B1868975
theorem B1246007 : Blo 830350 1246007 := bstep (se 1 (by rfl) ⟨934505, by rfl⟩ : syracuseStep 1246007 = 1869011) B1869011
theorem B1868615 : Blo 830350 1868615 := bstep (se 1 (by rfl) ⟨1401461, by rfl⟩ : syracuseStep 1868615 = 2802923) B2802923
theorem B1246187 : Blo 830350 1246187 := bstep (se 1 (by rfl) ⟨934640, by rfl⟩ : syracuseStep 1246187 = 1869281) B1869281
theorem B2851951 : Blo 830350 2851951 := bstep (se 1 (by rfl) ⟨2138963, by rfl⟩ : syracuseStep 2851951 = 4277927) B4277927
theorem B1246697 : Blo 830350 1246697 := bstep (se 2 (by rfl) ⟨467511, by rfl⟩ : syracuseStep 1246697 = 935023) B935023
theorem B5998087 : Blo 830350 5998087 := bstep (se 1 (by rfl) ⟨4498565, by rfl⟩ : syracuseStep 5998087 = 8997131) B8997131
theorem B1869551 : Blo 830350 1869551 := bstep (se 1 (by rfl) ⟨1402163, by rfl⟩ : syracuseStep 1869551 = 2804327) B2804327
theorem B5998319 : Blo 830350 5998319 := bstep (se 1 (by rfl) ⟨4498739, by rfl⟩ : syracuseStep 5998319 = 8997479) B8997479
theorem B1247087 : Blo 830350 1247087 := bstep (se 1 (by rfl) ⟨935315, by rfl⟩ : syracuseStep 1247087 = 1870631) B1870631
theorem B1869803 : Blo 830350 1869803 := bstep (se 1 (by rfl) ⟨1402352, by rfl⟩ : syracuseStep 1869803 = 2804705) B2804705
theorem B1247273 : Blo 830350 1247273 := bstep (se 2 (by rfl) ⟨467727, by rfl⟩ : syracuseStep 1247273 = 935455) B935455
theorem B12027953 : Blo 830350 12027953 := bstep (se 2 (by rfl) ⟨4510482, by rfl⟩ : syracuseStep 12027953 = 9020965) B9020965
theorem B1247303 : Blo 830350 1247303 := bstep (se 1 (by rfl) ⟨935477, by rfl⟩ : syracuseStep 1247303 = 1870955) B1870955
theorem B1247483 : Blo 830350 1247483 := bstep (se 1 (by rfl) ⟨935612, by rfl⟩ : syracuseStep 1247483 = 1871225) B1871225
theorem B18024707 : Blo 830350 18024707 := bstep (se 1 (by rfl) ⟨13518530, by rfl⟩ : syracuseStep 18024707 = 27037061) B27037061
theorem B1247687 : Blo 830350 1247687 := bstep (se 1 (by rfl) ⟨935765, by rfl⟩ : syracuseStep 1247687 = 1871531) B1871531
theorem B10652147 : Blo 830350 10652147 := bstep (se 1 (by rfl) ⟨7989110, by rfl⟩ : syracuseStep 10652147 = 15978221) B15978221
theorem B4557313 : Blo 830350 4557313 := bstep (se 2 (by rfl) ⟨1708992, by rfl⟩ : syracuseStep 4557313 = 3417985) B3417985
theorem B5343833 : Blo 830350 5343833 := bstep (se 2 (by rfl) ⟨2003937, by rfl⟩ : syracuseStep 5343833 = 4007875) B4007875
theorem B1247903 : Blo 830350 1247903 := bstep (se 1 (by rfl) ⟨935927, by rfl⟩ : syracuseStep 1247903 = 1871855) B1871855
theorem B1247951 : Blo 830350 1247951 := bstep (se 1 (by rfl) ⟨935963, by rfl⟩ : syracuseStep 1247951 = 1871927) B1871927
theorem B1051375 : Blo 830350 1051375 := bstep (se 1 (by rfl) ⟨788531, by rfl⟩ : syracuseStep 1051375 = 1577063) B1577063
theorem B5409575 : Blo 830350 5409575 := bstep (se 1 (by rfl) ⟨4057181, by rfl⟩ : syracuseStep 5409575 = 8114363) B8114363
theorem B1248047 : Blo 830350 1248047 := bstep (se 1 (by rfl) ⟨936035, by rfl⟩ : syracuseStep 1248047 = 1872071) B1872071
theorem B1248167 : Blo 830350 1248167 := bstep (se 1 (by rfl) ⟨936125, by rfl⟩ : syracuseStep 1248167 = 1872251) B1872251
theorem B6327233 : Blo 830350 6327233 := bstep (se 2 (by rfl) ⟨2372712, by rfl⟩ : syracuseStep 6327233 = 4745425) B4745425
theorem B2165815 : Blo 830350 2165815 := bstep (se 1 (by rfl) ⟨1624361, by rfl⟩ : syracuseStep 2165815 = 3248723) B3248723
theorem B1248347 : Blo 830350 1248347 := bstep (se 1 (by rfl) ⟨936260, by rfl⟩ : syracuseStep 1248347 = 1872521) B1872521
theorem B1248425 : Blo 830350 1248425 := bstep (se 2 (by rfl) ⟨468159, by rfl⟩ : syracuseStep 1248425 = 936319) B936319
theorem B6327719 : Blo 830350 6327719 := bstep (se 1 (by rfl) ⟨4745789, by rfl⟩ : syracuseStep 6327719 = 9491579) B9491579
theorem B1248839 : Blo 830350 1248839 := bstep (se 1 (by rfl) ⟨936629, by rfl⟩ : syracuseStep 1248839 = 1873259) B1873259
theorem B1249019 : Blo 830350 1249019 := bstep (se 1 (by rfl) ⟨936764, by rfl⟩ : syracuseStep 1249019 = 1873529) B1873529
theorem B1249259 : Blo 830350 1249259 := bstep (se 1 (by rfl) ⟨936944, by rfl⟩ : syracuseStep 1249259 = 1873889) B1873889
theorem B3805375 : Blo 830350 3805375 := bstep (se 1 (by rfl) ⟨2854031, by rfl⟩ : syracuseStep 3805375 = 5708063) B5708063
theorem B1872107 : Blo 830350 1872107 := bstep (se 1 (by rfl) ⟨1404080, by rfl⟩ : syracuseStep 1872107 = 2808161) B2808161
theorem B30380507 : Blo 830350 30380507 := bstep (se 1 (by rfl) ⟨22785380, by rfl⟩ : syracuseStep 30380507 = 45570761) B45570761
theorem B1872431 : Blo 830350 1872431 := bstep (se 1 (by rfl) ⟨1404323, by rfl⟩ : syracuseStep 1872431 = 2808647) B2808647
theorem B2101889 : Blo 830350 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B1250297 : Blo 830350 1250297 := bstep (se 2 (by rfl) ⟨468861, by rfl⟩ : syracuseStep 1250297 = 937723) B937723
theorem B1873007 : Blo 830350 1873007 := bstep (se 1 (by rfl) ⟨1404755, by rfl⟩ : syracuseStep 1873007 = 2809511) B2809511
theorem B1873079 : Blo 830350 1873079 := bstep (se 1 (by rfl) ⟨1404809, by rfl⟩ : syracuseStep 1873079 = 2809619) B2809619
theorem B1250495 : Blo 830350 1250495 := bstep (se 1 (by rfl) ⟨937871, by rfl⟩ : syracuseStep 1250495 = 1875743) B1875743
theorem B2102507 : Blo 830350 2102507 := bstep (se 1 (by rfl) ⟨1576880, by rfl⟩ : syracuseStep 2102507 = 3153761) B3153761
theorem B1250639 : Blo 830350 1250639 := bstep (se 1 (by rfl) ⟨937979, by rfl⟩ : syracuseStep 1250639 = 1875959) B1875959
theorem B1250729 : Blo 830350 1250729 := bstep (se 2 (by rfl) ⟨469023, by rfl⟩ : syracuseStep 1250729 = 938047) B938047
theorem B2102699 : Blo 830350 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B1250783 : Blo 830350 1250783 := bstep (se 1 (by rfl) ⟨938087, by rfl⟩ : syracuseStep 1250783 = 1876175) B1876175
theorem B12817889 : Blo 830350 12817889 := bstep (se 2 (by rfl) ⟨4806708, by rfl⟩ : syracuseStep 12817889 = 9613417) B9613417
theorem B1250879 : Blo 830350 1250879 := bstep (se 1 (by rfl) ⟨938159, by rfl⟩ : syracuseStep 1250879 = 1876319) B1876319
theorem B2135659 : Blo 830350 2135659 := bstep (se 1 (by rfl) ⟨1601744, by rfl⟩ : syracuseStep 2135659 = 3203489) B3203489
theorem B8558399 : Blo 830350 8558399 := bstep (se 1 (by rfl) ⟨6418799, by rfl⟩ : syracuseStep 8558399 = 12837599) B12837599
theorem B1251359 : Blo 830350 1251359 := bstep (se 1 (by rfl) ⟨938519, by rfl⟩ : syracuseStep 1251359 = 1877039) B1877039
theorem B2103479 : Blo 830350 2103479 := bstep (se 1 (by rfl) ⟨1577609, by rfl⟩ : syracuseStep 2103479 = 3155219) B3155219
theorem B2136377 : Blo 830350 2136377 := bstep (se 2 (by rfl) ⟨801141, by rfl⟩ : syracuseStep 2136377 = 1602283) B1602283
theorem B1874537 : Blo 830350 1874537 := bstep (se 2 (by rfl) ⟨702951, by rfl⟩ : syracuseStep 1874537 = 1405903) B1405903
theorem B1055359 : Blo 830350 1055359 := bstep (se 1 (by rfl) ⟨791519, by rfl⟩ : syracuseStep 1055359 = 1583039) B1583039
theorem B2661025 : Blo 830350 2661025 := bstep (se 2 (by rfl) ⟨997884, by rfl⟩ : syracuseStep 2661025 = 1995769) B1995769
theorem B7117865 : Blo 830350 7117865 := bstep (se 2 (by rfl) ⟨2669199, by rfl⟩ : syracuseStep 7117865 = 5338399) B5338399
theorem B1875167 : Blo 830350 1875167 := bstep (se 1 (by rfl) ⟨1406375, by rfl⟩ : syracuseStep 1875167 = 2812751) B2812751
theorem B1580647 : Blo 830350 1580647 := bstep (se 1 (by rfl) ⟨1185485, by rfl⟩ : syracuseStep 1580647 = 2370971) B2370971
theorem B105488351 : Blo 830350 105488351 := bstep (se 1 (by rfl) ⟨79116263, by rfl⟩ : syracuseStep 105488351 = 158232527) B158232527
theorem B4268483 : Blo 830350 4268483 := bstep (se 1 (by rfl) ⟨3201362, by rfl⟩ : syracuseStep 4268483 = 6402725) B6402725
theorem B3547759 : Blo 830350 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B2368111 : Blo 830350 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B1876841 : Blo 830350 1876841 := bstep (se 2 (by rfl) ⟨703815, by rfl⟩ : syracuseStep 1876841 = 1407631) B1407631
theorem B3548681 : Blo 830350 3548681 := bstep (se 2 (by rfl) ⟨1330755, by rfl⟩ : syracuseStep 3548681 = 2661511) B2661511
theorem B2696879 : Blo 830350 2696879 := bstep (se 1 (by rfl) ⟨2022659, by rfl⟩ : syracuseStep 2696879 = 4045319) B4045319
theorem B2402027 : Blo 830350 2402027 := bstep (se 1 (by rfl) ⟨1801520, by rfl⟩ : syracuseStep 2402027 = 3603041) B3603041
theorem B1583327 : Blo 830350 1583327 := bstep (se 1 (by rfl) ⟨1187495, by rfl⟩ : syracuseStep 1583327 = 2374991) B2374991
theorem B6400259 : Blo 830350 6400259 := bstep (se 1 (by rfl) ⟨4800194, by rfl⟩ : syracuseStep 6400259 = 9600389) B9600389
theorem B2108015 : Blo 830350 2108015 := bstep (se 1 (by rfl) ⟨1581011, by rfl⟩ : syracuseStep 2108015 = 3162023) B3162023
theorem B4729661 : Blo 830350 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B3157177 : Blo 830350 3157177 := bstep (se 2 (by rfl) ⟨1183941, by rfl⟩ : syracuseStep 3157177 = 2367883) B2367883
theorem B830767 : Blo 830350 830767 := bstep (se 1 (by rfl) ⟨623075, by rfl⟩ : syracuseStep 830767 = 1246151) B1246151
theorem B1781099 : Blo 830350 1781099 := bstep (se 1 (by rfl) ⟨1335824, by rfl⟩ : syracuseStep 1781099 = 2671649) B2671649
theorem B4009337 : Blo 830350 4009337 := bstep (se 2 (by rfl) ⟨1503501, by rfl⟩ : syracuseStep 4009337 = 3007003) B3007003
theorem B830879 : Blo 830350 830879 := bstep (se 1 (by rfl) ⟨623159, by rfl⟩ : syracuseStep 830879 = 1246319) B1246319
theorem B831007 : Blo 830350 831007 := bstep (se 1 (by rfl) ⟨623255, by rfl⟩ : syracuseStep 831007 = 1246511) B1246511
theorem B831143 : Blo 830350 831143 := bstep (se 1 (by rfl) ⟨623357, by rfl⟩ : syracuseStep 831143 = 1246715) B1246715
theorem B831167 : Blo 830350 831167 := bstep (se 1 (by rfl) ⟨623375, by rfl⟩ : syracuseStep 831167 = 1246751) B1246751
theorem B2109179 : Blo 830350 2109179 := bstep (se 1 (by rfl) ⟨1581884, by rfl⟩ : syracuseStep 2109179 = 3163769) B3163769
theorem B831263 : Blo 830350 831263 := bstep (se 1 (by rfl) ⟨623447, by rfl⟩ : syracuseStep 831263 = 1246895) B1246895
theorem B831343 : Blo 830350 831343 := bstep (se 1 (by rfl) ⟨623507, by rfl⟩ : syracuseStep 831343 = 1247015) B1247015
theorem B2666459 : Blo 830350 2666459 := bstep (se 1 (by rfl) ⟨1999844, by rfl⟩ : syracuseStep 2666459 = 3999689) B3999689
theorem B2109503 : Blo 830350 2109503 := bstep (se 1 (by rfl) ⟨1582127, by rfl⟩ : syracuseStep 2109503 = 3164255) B3164255
theorem B4206815 : Blo 830350 4206815 := bstep (se 1 (by rfl) ⟨3155111, by rfl⟩ : syracuseStep 4206815 = 6310223) B6310223
theorem B831711 : Blo 830350 831711 := bstep (se 1 (by rfl) ⟨623783, by rfl⟩ : syracuseStep 831711 = 1247567) B1247567
theorem B831743 : Blo 830350 831743 := bstep (se 1 (by rfl) ⟨623807, by rfl⟩ : syracuseStep 831743 = 1247615) B1247615
theorem B831771 : Blo 830350 831771 := bstep (se 1 (by rfl) ⟨623828, by rfl⟩ : syracuseStep 831771 = 1247657) B1247657
theorem B832027 : Blo 830350 832027 := bstep (se 1 (by rfl) ⟨624020, by rfl⟩ : syracuseStep 832027 = 1248041) B1248041
theorem B832167 : Blo 830350 832167 := bstep (se 1 (by rfl) ⟨624125, by rfl⟩ : syracuseStep 832167 = 1248251) B1248251
theorem B832207 : Blo 830350 832207 := bstep (se 1 (by rfl) ⟨624155, by rfl⟩ : syracuseStep 832207 = 1248311) B1248311
theorem B2372303 : Blo 830350 2372303 := bstep (se 1 (by rfl) ⟨1779227, by rfl⟩ : syracuseStep 2372303 = 3558455) B3558455
theorem B832287 : Blo 830350 832287 := bstep (se 1 (by rfl) ⟨624215, by rfl⟩ : syracuseStep 832287 = 1248431) B1248431
theorem B19182673 : Blo 830350 19182673 := bstep (se 2 (by rfl) ⟨7193502, by rfl⟩ : syracuseStep 19182673 = 14387005) B14387005
theorem B832767 : Blo 830350 832767 := bstep (se 1 (by rfl) ⟨624575, by rfl⟩ : syracuseStep 832767 = 1249151) B1249151
theorem B832895 : Blo 830350 832895 := bstep (se 1 (by rfl) ⟨624671, by rfl⟩ : syracuseStep 832895 = 1249343) B1249343
theorem B833051 : Blo 830350 833051 := bstep (se 1 (by rfl) ⟨624788, by rfl⟩ : syracuseStep 833051 = 1249577) B1249577
theorem B4732577 : Blo 830350 4732577 := bstep (se 2 (by rfl) ⟨1774716, by rfl⟩ : syracuseStep 4732577 = 3549433) B3549433
theorem B833231 : Blo 830350 833231 := bstep (se 1 (by rfl) ⟨624923, by rfl⟩ : syracuseStep 833231 = 1249847) B1249847
theorem B7124699 : Blo 830350 7124699 := bstep (se 1 (by rfl) ⟨5343524, by rfl⟩ : syracuseStep 7124699 = 10687049) B10687049
theorem B833471 : Blo 830350 833471 := bstep (se 1 (by rfl) ⟨625103, by rfl⟩ : syracuseStep 833471 = 1250207) B1250207
theorem B2111467 : Blo 830350 2111467 := bstep (se 1 (by rfl) ⟨1583600, by rfl⟩ : syracuseStep 2111467 = 3167201) B3167201
theorem B5322793 : Blo 830350 5322793 := bstep (se 2 (by rfl) ⟨1996047, by rfl⟩ : syracuseStep 5322793 = 3992095) B3992095
theorem B833599 : Blo 830350 833599 := bstep (se 1 (by rfl) ⟨625199, by rfl⟩ : syracuseStep 833599 = 1250399) B1250399
theorem B833639 : Blo 830350 833639 := bstep (se 1 (by rfl) ⟨625229, by rfl⟩ : syracuseStep 833639 = 1250459) B1250459
theorem B5323279 : Blo 830350 5323279 := bstep (se 1 (by rfl) ⟨3992459, by rfl⟩ : syracuseStep 5323279 = 7984919) B7984919
theorem B834095 : Blo 830350 834095 := bstep (se 1 (by rfl) ⟨625571, by rfl⟩ : syracuseStep 834095 = 1251143) B1251143
theorem B62339701 : Blo 830350 62339701 := bstep (se 5 (by rfl) ⟨2922173, by rfl⟩ : syracuseStep 62339701 = 5844347) B5844347
theorem B5061665 : Blo 830350 5061665 := bstep (se 2 (by rfl) ⟨1898124, by rfl⟩ : syracuseStep 5061665 = 3796249) B3796249
theorem B2669867 : Blo 830350 2669867 := bstep (se 1 (by rfl) ⟨2002400, by rfl⟩ : syracuseStep 2669867 = 4004801) B4004801
theorem B2670047 : Blo 830350 2670047 := bstep (se 1 (by rfl) ⟨2002535, by rfl⟩ : syracuseStep 2670047 = 4005071) B4005071
theorem B999163 : Blo 830350 999163 := bstep (se 1 (by rfl) ⟨749372, by rfl⟩ : syracuseStep 999163 = 1498745) B1498745
theorem B3555515 : Blo 830350 3555515 := bstep (se 1 (by rfl) ⟨2666636, by rfl⟩ : syracuseStep 3555515 = 5333273) B5333273
theorem B6832421 : Blo 830350 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B934375 : Blo 830350 934375 := bstep (se 1 (by rfl) ⟨700781, by rfl⟩ : syracuseStep 934375 = 1401563) B1401563
theorem B6078995 : Blo 830350 6078995 := bstep (se 1 (by rfl) ⟨4559246, by rfl⟩ : syracuseStep 6078995 = 9118493) B9118493
theorem B5325587 : Blo 830350 5325587 := bstep (se 1 (by rfl) ⟨3994190, by rfl⟩ : syracuseStep 5325587 = 7988381) B7988381
theorem B4211513 : Blo 830350 4211513 := bstep (se 2 (by rfl) ⟨1579317, by rfl⟩ : syracuseStep 4211513 = 3158635) B3158635
theorem B2704607 : Blo 830350 2704607 := bstep (se 1 (by rfl) ⟨2028455, by rfl⟩ : syracuseStep 2704607 = 4056911) B4056911
theorem B935239 : Blo 830350 935239 := bstep (se 1 (by rfl) ⟨701429, by rfl⟩ : syracuseStep 935239 = 1402859) B1402859
theorem B7095995 : Blo 830350 7095995 := bstep (se 1 (by rfl) ⟨5321996, by rfl⟩ : syracuseStep 7095995 = 10643993) B10643993
theorem B4278217 : Blo 830350 4278217 := bstep (se 2 (by rfl) ⟨1604331, by rfl⟩ : syracuseStep 4278217 = 3208663) B3208663
theorem B2803679 : Blo 830350 2803679 := bstep (se 1 (by rfl) ⟨2102759, by rfl⟩ : syracuseStep 2803679 = 4205519) B4205519
theorem B9488663 : Blo 830350 9488663 := bstep (se 1 (by rfl) ⟨7116497, by rfl⟩ : syracuseStep 9488663 = 14232995) B14232995
theorem B1198571 : Blo 830350 1198571 := bstep (se 1 (by rfl) ⟨898928, by rfl⟩ : syracuseStep 1198571 = 1797857) B1797857
theorem B2804381 : Blo 830350 2804381 := bstep (se 3 (by rfl) ⟨525821, by rfl⟩ : syracuseStep 2804381 = 1051643) B1051643
theorem B3558113 : Blo 830350 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B2804921 : Blo 830350 2804921 := bstep (se 2 (by rfl) ⟨1051845, by rfl⟩ : syracuseStep 2804921 = 2103691) B2103691
theorem B5328125 : Blo 830350 5328125 := bstep (se 3 (by rfl) ⟨999023, by rfl⟩ : syracuseStep 5328125 = 1998047) B1998047
theorem B2805083 : Blo 830350 2805083 := bstep (se 1 (by rfl) ⟨2103812, by rfl⟩ : syracuseStep 2805083 = 4207625) B4207625
theorem B7982687 : Blo 830350 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B938011 : Blo 830350 938011 := bstep (se 1 (by rfl) ⟨703508, by rfl⟩ : syracuseStep 938011 = 1407017) B1407017
theorem B3428491 : Blo 830350 3428491 := bstep (se 1 (by rfl) ⟨2571368, by rfl⟩ : syracuseStep 3428491 = 5142737) B5142737
theorem B4509857 : Blo 830350 4509857 := bstep (se 2 (by rfl) ⟨1691196, by rfl⟩ : syracuseStep 4509857 = 3382393) B3382393
theorem B6836729 : Blo 830350 6836729 := bstep (se 2 (by rfl) ⟨2563773, by rfl⟩ : syracuseStep 6836729 = 5127547) B5127547
theorem B1331743 : Blo 830350 1331743 := bstep (se 1 (by rfl) ⟨998807, by rfl⟩ : syracuseStep 1331743 = 1997615) B1997615
theorem B4215725 : Blo 830350 4215725 := bstep (se 3 (by rfl) ⟨790448, by rfl⟩ : syracuseStep 4215725 = 1580897) B1580897
theorem B1332191 : Blo 830350 1332191 := bstep (se 1 (by rfl) ⟨999143, by rfl⟩ : syracuseStep 1332191 = 1998287) B1998287
theorem B2807081 : Blo 830350 2807081 := bstep (se 2 (by rfl) ⟨1052655, by rfl⟩ : syracuseStep 2807081 = 2105311) B2105311
theorem B1333703 : Blo 830350 1333703 := bstep (se 1 (by rfl) ⟨1000277, by rfl⟩ : syracuseStep 1333703 = 2000555) B2000555
theorem B4217345 : Blo 830350 4217345 := bstep (se 2 (by rfl) ⟨1581504, by rfl⟩ : syracuseStep 4217345 = 3163009) B3163009
theorem B2251577 : Blo 830350 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B4742327 : Blo 830350 4742327 := bstep (se 1 (by rfl) ⟨3556745, by rfl⟩ : syracuseStep 4742327 = 7113491) B7113491
theorem B5332351 : Blo 830350 5332351 := bstep (se 1 (by rfl) ⟨3999263, by rfl⟩ : syracuseStep 5332351 = 7998527) B7998527
theorem B1335209 : Blo 830350 1335209 := bstep (se 2 (by rfl) ⟨500703, by rfl⟩ : syracuseStep 1335209 = 1001407) B1001407
theorem B4219613 : Blo 830350 4219613 := bstep (se 3 (by rfl) ⟨791177, by rfl⟩ : syracuseStep 4219613 = 1582355) B1582355
theorem B4743967 : Blo 830350 4743967 := bstep (se 1 (by rfl) ⟨3557975, by rfl⟩ : syracuseStep 4743967 = 7115951) B7115951
theorem B4219937 : Blo 830350 4219937 := bstep (se 2 (by rfl) ⟨1582476, by rfl⟩ : syracuseStep 4219937 = 3164953) B3164953
theorem B5334275 : Blo 830350 5334275 := bstep (se 1 (by rfl) ⟨4000706, by rfl⟩ : syracuseStep 5334275 = 8001413) B8001413
theorem B1829479 : Blo 830350 1829479 := bstep (se 1 (by rfl) ⟨1372109, by rfl⟩ : syracuseStep 1829479 = 2744219) B2744219
theorem B4745951 : Blo 830350 4745951 := bstep (se 1 (by rfl) ⟨3559463, by rfl⟩ : syracuseStep 4745951 = 7118927) B7118927
theorem B1403689 : Blo 830350 1403689 := bstep (se 2 (by rfl) ⟨526383, by rfl⟩ : syracuseStep 1403689 = 1052767) B1052767
theorem B1403959 : Blo 830350 1403959 := bstep (se 1 (by rfl) ⟨1052969, by rfl⟩ : syracuseStep 1403959 = 2105939) B2105939
theorem B2813345 : Blo 830350 2813345 := bstep (se 2 (by rfl) ⟨1055004, by rfl⟩ : syracuseStep 2813345 = 2110009) B2110009
theorem B2813885 : Blo 830350 2813885 := bstep (se 3 (by rfl) ⟨527603, by rfl⟩ : syracuseStep 2813885 = 1055207) B1055207
theorem B8679383 : Blo 830350 8679383 := bstep (se 1 (by rfl) ⟨6509537, by rfl⟩ : syracuseStep 8679383 = 13019075) B13019075
theorem B4223015 : Blo 830350 4223015 := bstep (se 1 (by rfl) ⟨3167261, by rfl⟩ : syracuseStep 4223015 = 6334523) B6334523
theorem B3600463 : Blo 830350 3600463 := bstep (se 1 (by rfl) ⟨2700347, by rfl⟩ : syracuseStep 3600463 = 5400695) B5400695
theorem B2814047 : Blo 830350 2814047 := bstep (se 1 (by rfl) ⟨2110535, by rfl⟩ : syracuseStep 2814047 = 4221071) B4221071
theorem B25948345 : Blo 830350 25948345 := bstep (se 2 (by rfl) ⟨9730629, by rfl⟩ : syracuseStep 25948345 = 19461259) B19461259
theorem B1405255 : Blo 830350 1405255 := bstep (se 1 (by rfl) ⟨1053941, by rfl⟩ : syracuseStep 1405255 = 2107883) B2107883
theorem B3797417 : Blo 830350 3797417 := bstep (se 2 (by rfl) ⟨1424031, by rfl⟩ : syracuseStep 3797417 = 2848063) B2848063
theorem B14250491 : Blo 830350 14250491 := bstep (se 1 (by rfl) ⟨10687868, by rfl⟩ : syracuseStep 14250491 = 21375737) B21375737
theorem B3011267 : Blo 830350 3011267 := bstep (se 1 (by rfl) ⟨2258450, by rfl⟩ : syracuseStep 3011267 = 4516901) B4516901
theorem B6747563 : Blo 830350 6747563 := bstep (se 1 (by rfl) ⟨5060672, by rfl⟩ : syracuseStep 6747563 = 10121345) B10121345
theorem B2849107 : Blo 830350 2849107 := bstep (se 1 (by rfl) ⟨2136830, by rfl⟩ : syracuseStep 2849107 = 4273661) B4273661
theorem B9468251 : Blo 830350 9468251 := bstep (se 1 (by rfl) ⟨7101188, by rfl⟩ : syracuseStep 9468251 = 14202377) B14202377
theorem B6323345 : Blo 830350 6323345 := bstep (se 2 (by rfl) ⟨2371254, by rfl⟩ : syracuseStep 6323345 = 4742509) B4742509
theorem B4816367 : Blo 830350 4816367 := bstep (se 1 (by rfl) ⟨3612275, by rfl⟩ : syracuseStep 4816367 = 7224551) B7224551
theorem B3210877 : Blo 830350 3210877 := bstep (se 3 (by rfl) ⟨602039, by rfl⟩ : syracuseStep 3210877 = 1204079) B1204079
theorem B1900169 : Blo 830350 1900169 := bstep (se 2 (by rfl) ⟨712563, by rfl⟩ : syracuseStep 1900169 = 1425127) B1425127
theorem B10944143 : Blo 830350 10944143 := bstep (se 1 (by rfl) ⟨8208107, by rfl⟩ : syracuseStep 10944143 = 16416215) B16416215
theorem B4554947 : Blo 830350 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B1245743 : Blo 830350 1245743 := bstep (se 1 (by rfl) ⟨934307, by rfl⟩ : syracuseStep 1245743 = 1868615) B1868615
theorem B1245833 : Blo 830350 1245833 := bstep (se 2 (by rfl) ⟨467187, by rfl⟩ : syracuseStep 1245833 = 934375) B934375
theorem B1803071 : Blo 830350 1803071 := bstep (se 1 (by rfl) ⟨1352303, by rfl⟩ : syracuseStep 1803071 = 2704607) B2704607
theorem B6325289 : Blo 830350 6325289 := bstep (se 2 (by rfl) ⟨2371983, by rfl⟩ : syracuseStep 6325289 = 4743967) B4743967
theorem B1246367 : Blo 830350 1246367 := bstep (se 1 (by rfl) ⟨934775, by rfl⟩ : syracuseStep 1246367 = 1869551) B1869551
theorem B3998879 : Blo 830350 3998879 := bstep (se 1 (by rfl) ⟨2999159, by rfl⟩ : syracuseStep 3998879 = 5998319) B5998319
theorem B1869119 : Blo 830350 1869119 := bstep (se 1 (by rfl) ⟨1401839, by rfl⟩ : syracuseStep 1869119 = 2803679) B2803679
theorem B1246535 : Blo 830350 1246535 := bstep (se 1 (by rfl) ⟨934901, by rfl⟩ : syracuseStep 1246535 = 1869803) B1869803
theorem B3802601 : Blo 830350 3802601 := bstep (se 2 (by rfl) ⟨1425975, by rfl⟩ : syracuseStep 3802601 = 2851951) B2851951
theorem B6325775 : Blo 830350 6325775 := bstep (se 1 (by rfl) ⟨4744331, by rfl⟩ : syracuseStep 6325775 = 9488663) B9488663
theorem B1246985 : Blo 830350 1246985 := bstep (se 2 (by rfl) ⟨467619, by rfl⟩ : syracuseStep 1246985 = 935239) B935239
theorem B1869587 : Blo 830350 1869587 := bstep (se 1 (by rfl) ⟨1402190, by rfl⟩ : syracuseStep 1869587 = 2804381) B2804381
theorem B8030045 : Blo 830350 8030045 := bstep (se 3 (by rfl) ⟨1505633, by rfl⟩ : syracuseStep 8030045 = 3011267) B3011267
theorem B3606383 : Blo 830350 3606383 := bstep (se 1 (by rfl) ⟨2704787, by rfl⟩ : syracuseStep 3606383 = 5409575) B5409575
theorem B7997449 : Blo 830350 7997449 := bstep (se 2 (by rfl) ⟨2999043, by rfl⟩ : syracuseStep 7997449 = 5998087) B5998087
theorem B1869947 : Blo 830350 1869947 := bstep (se 1 (by rfl) ⟨1402460, by rfl⟩ : syracuseStep 1869947 = 2804921) B2804921
theorem B1870055 : Blo 830350 1870055 := bstep (se 1 (by rfl) ⟨1402541, by rfl⟩ : syracuseStep 1870055 = 2805083) B2805083
theorem B5704289 : Blo 830350 5704289 := bstep (se 2 (by rfl) ⟨2139108, by rfl⟩ : syracuseStep 5704289 = 4278217) B4278217
theorem B1248071 : Blo 830350 1248071 := bstep (se 1 (by rfl) ⟨936053, by rfl⟩ : syracuseStep 1248071 = 1872107) B1872107
theorem B20253671 : Blo 830350 20253671 := bstep (se 1 (by rfl) ⟨15190253, by rfl⟩ : syracuseStep 20253671 = 30380507) B30380507
theorem B1248287 : Blo 830350 1248287 := bstep (se 1 (by rfl) ⟨936215, by rfl⟩ : syracuseStep 1248287 = 1872431) B1872431
theorem B888127 : Blo 830350 888127 := bstep (se 1 (by rfl) ⟨666095, by rfl⟩ : syracuseStep 888127 = 1332191) B1332191
theorem B1248671 : Blo 830350 1248671 := bstep (se 1 (by rfl) ⟨936503, by rfl⟩ : syracuseStep 1248671 = 1873007) B1873007
theorem B1248719 : Blo 830350 1248719 := bstep (se 1 (by rfl) ⟨936539, by rfl⟩ : syracuseStep 1248719 = 1873079) B1873079
theorem B1871387 : Blo 830350 1871387 := bstep (se 1 (by rfl) ⟨1403540, by rfl⟩ : syracuseStep 1871387 = 2807081) B2807081
theorem B1871585 : Blo 830350 1871585 := bstep (se 2 (by rfl) ⟨701844, by rfl⟩ : syracuseStep 1871585 = 1403689) B1403689
theorem B5705599 : Blo 830350 5705599 := bstep (se 1 (by rfl) ⟨4279199, by rfl⟩ : syracuseStep 5705599 = 8558399) B8558399
theorem B1871945 : Blo 830350 1871945 := bstep (se 2 (by rfl) ⟨701979, by rfl⟩ : syracuseStep 1871945 = 1403959) B1403959
theorem B2887753 : Blo 830350 2887753 := bstep (se 2 (by rfl) ⟨1082907, by rfl⟩ : syracuseStep 2887753 = 2165815) B2165815
theorem B1249691 : Blo 830350 1249691 := bstep (se 1 (by rfl) ⟨937268, by rfl⟩ : syracuseStep 1249691 = 1874537) B1874537
theorem B1250111 : Blo 830350 1250111 := bstep (se 1 (by rfl) ⟨937583, by rfl⟩ : syracuseStep 1250111 = 1875167) B1875167
theorem B70325567 : Blo 830350 70325567 := bstep (se 1 (by rfl) ⟨52744175, by rfl⟩ : syracuseStep 70325567 = 105488351) B105488351
theorem B1250681 : Blo 830350 1250681 := bstep (se 2 (by rfl) ⟨469005, by rfl⟩ : syracuseStep 1250681 = 938011) B938011
theorem B1873673 : Blo 830350 1873673 := bstep (se 2 (by rfl) ⟨702627, by rfl⟩ : syracuseStep 1873673 = 1405255) B1405255
theorem B1251227 : Blo 830350 1251227 := bstep (se 1 (by rfl) ⟨938420, by rfl⟩ : syracuseStep 1251227 = 1876841) B1876841
theorem B1775657 : Blo 830350 1775657 := bstep (se 2 (by rfl) ⟨665871, by rfl⟩ : syracuseStep 1775657 = 1331743) B1331743
theorem B2365787 : Blo 830350 2365787 := bstep (se 1 (by rfl) ⟨1774340, by rfl⟩ : syracuseStep 2365787 = 3548681) B3548681
theorem B4266839 : Blo 830350 4266839 := bstep (se 1 (by rfl) ⟨3200129, by rfl⟩ : syracuseStep 4266839 = 6400259) B6400259
theorem B3153107 : Blo 830350 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B6004205 : Blo 830350 6004205 := bstep (se 3 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 6004205 = 2251577) B2251577
theorem B1187399 : Blo 830350 1187399 := bstep (se 1 (by rfl) ⟨890549, by rfl⟩ : syracuseStep 1187399 = 1781099) B1781099
theorem B1875563 : Blo 830350 1875563 := bstep (se 1 (by rfl) ⟨1406672, by rfl⟩ : syracuseStep 1875563 = 2813345) B2813345
theorem B1875923 : Blo 830350 1875923 := bstep (se 1 (by rfl) ⟨1406942, by rfl⟩ : syracuseStep 1875923 = 2813885) B2813885
theorem B1777639 : Blo 830350 1777639 := bstep (se 1 (by rfl) ⟨1333229, by rfl⟩ : syracuseStep 1777639 = 2666459) B2666459
theorem B1876031 : Blo 830350 1876031 := bstep (se 1 (by rfl) ⟨1407023, by rfl⟩ : syracuseStep 1876031 = 2814047) B2814047
theorem B2531611 : Blo 830350 2531611 := bstep (se 1 (by rfl) ⟨1898708, by rfl⟩ : syracuseStep 2531611 = 3797417) B3797417
theorem B1581535 : Blo 830350 1581535 := bstep (se 1 (by rfl) ⟨1186151, by rfl⟩ : syracuseStep 1581535 = 2372303) B2372303
theorem B3548033 : Blo 830350 3548033 := bstep (se 2 (by rfl) ⟨1330512, by rfl⟩ : syracuseStep 3548033 = 2661025) B2661025
theorem B4498375 : Blo 830350 4498375 := bstep (se 1 (by rfl) ⟨3373781, by rfl⟩ : syracuseStep 4498375 = 6747563) B6747563
theorem B3155051 : Blo 830350 3155051 := bstep (se 1 (by rfl) ⟨2366288, by rfl⟩ : syracuseStep 3155051 = 4732577) B4732577
theorem B2107529 : Blo 830350 2107529 := bstep (se 2 (by rfl) ⟨790323, by rfl⟩ : syracuseStep 2107529 = 1580647) B1580647
theorem B1779911 : Blo 830350 1779911 := bstep (se 1 (by rfl) ⟨1334933, by rfl⟩ : syracuseStep 1779911 = 2669867) B2669867
theorem B1780031 : Blo 830350 1780031 := bstep (se 1 (by rfl) ⟨1335023, by rfl⟩ : syracuseStep 1780031 = 2670047) B2670047
theorem B830399 : Blo 830350 830399 := bstep (se 1 (by rfl) ⟨622799, by rfl⟩ : syracuseStep 830399 = 1245599) B1245599
theorem B6335495 : Blo 830350 6335495 := bstep (se 1 (by rfl) ⟨4751621, by rfl⟩ : syracuseStep 6335495 = 9503243) B9503243
theorem B830575 : Blo 830350 830575 := bstep (se 1 (by rfl) ⟨622931, by rfl⟩ : syracuseStep 830575 = 1245863) B1245863
theorem B9481373 : Blo 830350 9481373 := bstep (se 3 (by rfl) ⟨1777757, by rfl⟩ : syracuseStep 9481373 = 3555515) B3555515
theorem B3550391 : Blo 830350 3550391 := bstep (se 1 (by rfl) ⟨2662793, by rfl⟩ : syracuseStep 3550391 = 5325587) B5325587
theorem B830655 : Blo 830350 830655 := bstep (se 1 (by rfl) ⟨622991, by rfl⟩ : syracuseStep 830655 = 1245983) B1245983
theorem B830671 : Blo 830350 830671 := bstep (se 1 (by rfl) ⟨623003, by rfl⟩ : syracuseStep 830671 = 1246007) B1246007
theorem B830791 : Blo 830350 830791 := bstep (se 1 (by rfl) ⟨623093, by rfl⟩ : syracuseStep 830791 = 1246187) B1246187
theorem B4730345 : Blo 830350 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B3157481 : Blo 830350 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B831131 : Blo 830350 831131 := bstep (se 1 (by rfl) ⟨623348, by rfl⟩ : syracuseStep 831131 = 1246697) B1246697
theorem B4730663 : Blo 830350 4730663 := bstep (se 1 (by rfl) ⟨3547997, by rfl⟩ : syracuseStep 4730663 = 7095995) B7095995
theorem B831391 : Blo 830350 831391 := bstep (se 1 (by rfl) ⟨623543, by rfl⟩ : syracuseStep 831391 = 1247087) B1247087
theorem B18231277 : Blo 830350 18231277 := bstep (se 3 (by rfl) ⟨3418364, by rfl⟩ : syracuseStep 18231277 = 6836729) B6836729
theorem B831515 : Blo 830350 831515 := bstep (se 1 (by rfl) ⟨623636, by rfl⟩ : syracuseStep 831515 = 1247273) B1247273
theorem B831535 : Blo 830350 831535 := bstep (se 1 (by rfl) ⟨623651, by rfl⟩ : syracuseStep 831535 = 1247303) B1247303
theorem B831655 : Blo 830350 831655 := bstep (se 1 (by rfl) ⟨623741, by rfl⟩ : syracuseStep 831655 = 1247483) B1247483
theorem B831791 : Blo 830350 831791 := bstep (se 1 (by rfl) ⟨623843, by rfl⟩ : syracuseStep 831791 = 1247687) B1247687
theorem B831935 : Blo 830350 831935 := bstep (se 1 (by rfl) ⟨623951, by rfl⟩ : syracuseStep 831935 = 1247903) B1247903
theorem B831967 : Blo 830350 831967 := bstep (se 1 (by rfl) ⟨623975, by rfl⟩ : syracuseStep 831967 = 1247951) B1247951
theorem B2372075 : Blo 830350 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B832031 : Blo 830350 832031 := bstep (se 1 (by rfl) ⟨624023, by rfl⟩ : syracuseStep 832031 = 1248047) B1248047
theorem B832111 : Blo 830350 832111 := bstep (se 1 (by rfl) ⟨624083, by rfl⟩ : syracuseStep 832111 = 1248167) B1248167
theorem B832231 : Blo 830350 832231 := bstep (se 1 (by rfl) ⟨624173, by rfl⟩ : syracuseStep 832231 = 1248347) B1248347
theorem B832283 : Blo 830350 832283 := bstep (se 1 (by rfl) ⟨624212, by rfl⟩ : syracuseStep 832283 = 1248425) B1248425
theorem B3552083 : Blo 830350 3552083 := bstep (se 1 (by rfl) ⟨2664062, by rfl⟩ : syracuseStep 3552083 = 5328125) B5328125
theorem B832559 : Blo 830350 832559 := bstep (se 1 (by rfl) ⟨624419, by rfl⟩ : syracuseStep 832559 = 1248839) B1248839
theorem B5321791 : Blo 830350 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B832679 : Blo 830350 832679 := bstep (se 1 (by rfl) ⟨624509, by rfl⟩ : syracuseStep 832679 = 1249019) B1249019
theorem B832839 : Blo 830350 832839 := bstep (se 1 (by rfl) ⟨624629, by rfl⟩ : syracuseStep 832839 = 1249259) B1249259
theorem B833531 : Blo 830350 833531 := bstep (se 1 (by rfl) ⟨625148, by rfl⟩ : syracuseStep 833531 = 1250297) B1250297
theorem B6076417 : Blo 830350 6076417 := bstep (se 2 (by rfl) ⟨2278656, by rfl⟩ : syracuseStep 6076417 = 4557313) B4557313
theorem B833663 : Blo 830350 833663 := bstep (se 1 (by rfl) ⟨625247, by rfl⟩ : syracuseStep 833663 = 1250495) B1250495
theorem B2439305 : Blo 830350 2439305 := bstep (se 2 (by rfl) ⟨914739, by rfl⟩ : syracuseStep 2439305 = 1829479) B1829479
theorem B833759 : Blo 830350 833759 := bstep (se 1 (by rfl) ⟨625319, by rfl⟩ : syracuseStep 833759 = 1250639) B1250639
theorem B833819 : Blo 830350 833819 := bstep (se 1 (by rfl) ⟨625364, by rfl⟩ : syracuseStep 833819 = 1250729) B1250729
theorem B833855 : Blo 830350 833855 := bstep (se 1 (by rfl) ⟨625391, by rfl⟩ : syracuseStep 833855 = 1250783) B1250783
theorem B833919 : Blo 830350 833919 := bstep (se 1 (by rfl) ⟨625439, by rfl⟩ : syracuseStep 833919 = 1250879) B1250879
theorem B834239 : Blo 830350 834239 := bstep (se 1 (by rfl) ⟨625679, by rfl⟩ : syracuseStep 834239 = 1251359) B1251359
theorem B1424251 : Blo 830350 1424251 := bstep (se 1 (by rfl) ⟨1068188, by rfl⟩ : syracuseStep 1424251 = 2136377) B2136377
theorem B4209569 : Blo 830350 4209569 := bstep (se 2 (by rfl) ⟨1578588, by rfl⟩ : syracuseStep 4209569 = 3157177) B3157177
theorem B3161551 : Blo 830350 3161551 := bstep (se 1 (by rfl) ⟨2371163, by rfl⟩ : syracuseStep 3161551 = 4742327) B4742327
theorem B4800617 : Blo 830350 4800617 := bstep (se 2 (by rfl) ⟨1800231, by rfl⟩ : syracuseStep 4800617 = 3600463) B3600463
theorem B4571321 : Blo 830350 4571321 := bstep (se 2 (by rfl) ⟨1714245, by rfl⟩ : syracuseStep 4571321 = 3428491) B3428491
theorem B3556183 : Blo 830350 3556183 := bstep (se 1 (by rfl) ⟨2667137, by rfl⟩ : syracuseStep 3556183 = 5334275) B5334275
theorem B3556541 : Blo 830350 3556541 := bstep (se 3 (by rfl) ⟨666851, by rfl⟩ : syracuseStep 3556541 = 1333703) B1333703
theorem B3196189 : Blo 830350 3196189 := bstep (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) B1198571
theorem B25576897 : Blo 830350 25576897 := bstep (se 2 (by rfl) ⟨9591336, by rfl⟩ : syracuseStep 25576897 = 19182673) B19182673
theorem B3163967 : Blo 830350 3163967 := bstep (se 1 (by rfl) ⟨2372975, by rfl⟩ : syracuseStep 3163967 = 4745951) B4745951
theorem B2672891 : Blo 830350 2672891 := bstep (se 1 (by rfl) ⟨2004668, by rfl⟩ : syracuseStep 2672891 = 4009337) B4009337
theorem B5786255 : Blo 830350 5786255 := bstep (se 1 (by rfl) ⟨4339691, by rfl⟩ : syracuseStep 5786255 = 8679383) B8679383
theorem B7097057 : Blo 830350 7097057 := bstep (se 2 (by rfl) ⟨2661396, by rfl⟩ : syracuseStep 7097057 = 5322793) B5322793
theorem B2804543 : Blo 830350 2804543 := bstep (se 1 (by rfl) ⟨2103407, by rfl⟩ : syracuseStep 2804543 = 4206815) B4206815
theorem B7097705 : Blo 830350 7097705 := bstep (se 2 (by rfl) ⟨2661639, by rfl⟩ : syracuseStep 7097705 = 5323279) B5323279
theorem B83119601 : Blo 830350 83119601 := bstep (se 2 (by rfl) ⟨31169850, by rfl⟩ : syracuseStep 83119601 = 62339701) B62339701
theorem B6312167 : Blo 830350 6312167 := bstep (se 1 (by rfl) ⟨4734125, by rfl⟩ : syracuseStep 6312167 = 9468251) B9468251
theorem B4215563 : Blo 830350 4215563 := bstep (se 1 (by rfl) ⟨3161672, by rfl⟩ : syracuseStep 4215563 = 6323345) B6323345
theorem B4281169 : Blo 830350 4281169 := bstep (se 2 (by rfl) ⟨1605438, by rfl⟩ : syracuseStep 4281169 = 3210877) B3210877
theorem B1332217 : Blo 830350 1332217 := bstep (se 2 (by rfl) ⟨499581, by rfl⟩ : syracuseStep 1332217 = 999163) B999163
theorem B1266779 : Blo 830350 1266779 := bstep (se 1 (by rfl) ⟨950084, by rfl⟩ : syracuseStep 1266779 = 1900169) B1900169
theorem B7296095 : Blo 830350 7296095 := bstep (se 1 (by rfl) ⟨5472071, by rfl⟩ : syracuseStep 7296095 = 10944143) B10944143
theorem B3560557 : Blo 830350 3560557 := bstep (se 3 (by rfl) ⟨667604, by rfl⟩ : syracuseStep 3560557 = 1335209) B1335209
theorem B4052663 : Blo 830350 4052663 := bstep (se 1 (by rfl) ⟨3039497, by rfl⟩ : syracuseStep 4052663 = 6078995) B6078995
theorem B7100095 : Blo 830350 7100095 := bstep (se 1 (by rfl) ⟨5325071, by rfl⟩ : syracuseStep 7100095 = 10650143) B10650143
theorem B5330711 : Blo 830350 5330711 := bstep (se 1 (by rfl) ⟨3998033, by rfl⟩ : syracuseStep 5330711 = 7996067) B7996067
theorem B2807675 : Blo 830350 2807675 := bstep (se 1 (by rfl) ⟨2105756, by rfl⟩ : syracuseStep 2807675 = 4211513) B4211513
theorem B8018635 : Blo 830350 8018635 := bstep (se 1 (by rfl) ⟨6013976, by rfl⟩ : syracuseStep 8018635 = 12027953) B12027953
theorem B7101431 : Blo 830350 7101431 := bstep (se 1 (by rfl) ⟨5326073, by rfl⟩ : syracuseStep 7101431 = 10652147) B10652147
theorem B3562555 : Blo 830350 3562555 := bstep (se 1 (by rfl) ⟨2671916, by rfl⟩ : syracuseStep 3562555 = 5343833) B5343833
theorem B4218155 : Blo 830350 4218155 := bstep (se 1 (by rfl) ⟨3163616, by rfl⟩ : syracuseStep 4218155 = 6327233) B6327233
theorem B4218479 : Blo 830350 4218479 := bstep (se 1 (by rfl) ⟨3163859, by rfl⟩ : syracuseStep 4218479 = 6327719) B6327719
theorem B3006571 : Blo 830350 3006571 := bstep (se 1 (by rfl) ⟨2254928, by rfl⟩ : syracuseStep 3006571 = 4509857) B4509857
theorem B1401259 : Blo 830350 1401259 := bstep (se 1 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 1401259 = 2101889) B2101889
theorem B2810483 : Blo 830350 2810483 := bstep (se 1 (by rfl) ⟨2107862, by rfl⟩ : syracuseStep 2810483 = 4215725) B4215725
theorem B1401671 : Blo 830350 1401671 := bstep (se 1 (by rfl) ⟨1051253, by rfl⟩ : syracuseStep 1401671 = 2102507) B2102507
theorem B1401799 : Blo 830350 1401799 := bstep (se 1 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 1401799 = 2102699) B2102699
theorem B1401833 : Blo 830350 1401833 := bstep (se 2 (by rfl) ⟨525687, by rfl⟩ : syracuseStep 1401833 = 1051375) B1051375
theorem B8545259 : Blo 830350 8545259 := bstep (se 1 (by rfl) ⟨6408944, by rfl⟩ : syracuseStep 8545259 = 12817889) B12817889
theorem B1402319 : Blo 830350 1402319 := bstep (se 1 (by rfl) ⟨1051739, by rfl⟩ : syracuseStep 1402319 = 2103479) B2103479
theorem B2811563 : Blo 830350 2811563 := bstep (se 1 (by rfl) ⟨2108672, by rfl⟩ : syracuseStep 2811563 = 4217345) B4217345
theorem B4745243 : Blo 830350 4745243 := bstep (se 1 (by rfl) ⟨3558932, by rfl⟩ : syracuseStep 4745243 = 7117865) B7117865
theorem B34597793 : Blo 830350 34597793 := bstep (se 2 (by rfl) ⟨12974172, by rfl⟩ : syracuseStep 34597793 = 25948345) B25948345
theorem B5073833 : Blo 830350 5073833 := bstep (se 2 (by rfl) ⟨1902687, by rfl⟩ : syracuseStep 5073833 = 3805375) B3805375
theorem B2845655 : Blo 830350 2845655 := bstep (se 1 (by rfl) ⟨2134241, by rfl⟩ : syracuseStep 2845655 = 4268483) B4268483
theorem B2813075 : Blo 830350 2813075 := bstep (se 1 (by rfl) ⟨2109806, by rfl⟩ : syracuseStep 2813075 = 4219613) B4219613
theorem B4222205 : Blo 830350 4222205 := bstep (se 3 (by rfl) ⟨791663, by rfl⟩ : syracuseStep 4222205 = 1583327) B1583327
theorem B48065885 : Blo 830350 48065885 := bstep (se 3 (by rfl) ⟨9012353, by rfl⟩ : syracuseStep 48065885 = 18024707) B18024707
theorem B2813291 : Blo 830350 2813291 := bstep (se 1 (by rfl) ⟨2109968, by rfl⟩ : syracuseStep 2813291 = 4219937) B4219937
theorem B1797919 : Blo 830350 1797919 := bstep (se 1 (by rfl) ⟨1348439, by rfl⟩ : syracuseStep 1797919 = 2696879) B2696879
theorem B1601351 : Blo 830350 1601351 := bstep (se 1 (by rfl) ⟨1201013, by rfl⟩ : syracuseStep 1601351 = 2402027) B2402027
theorem B1405343 : Blo 830350 1405343 := bstep (se 1 (by rfl) ⟨1054007, by rfl⟩ : syracuseStep 1405343 = 2108015) B2108015
theorem B2847545 : Blo 830350 2847545 := bstep (se 2 (by rfl) ⟨1067829, by rfl⟩ : syracuseStep 2847545 = 2135659) B2135659
theorem B1406119 : Blo 830350 1406119 := bstep (se 1 (by rfl) ⟨1054589, by rfl⟩ : syracuseStep 1406119 = 2109179) B2109179
theorem B2815289 : Blo 830350 2815289 := bstep (se 2 (by rfl) ⟨1055733, by rfl⟩ : syracuseStep 2815289 = 2111467) B2111467
theorem B2815343 : Blo 830350 2815343 := bstep (se 1 (by rfl) ⟨2111507, by rfl⟩ : syracuseStep 2815343 = 4223015) B4223015
theorem B1406335 : Blo 830350 1406335 := bstep (se 1 (by rfl) ⟨1054751, by rfl⟩ : syracuseStep 1406335 = 2109503) B2109503
theorem B9500327 : Blo 830350 9500327 := bstep (se 1 (by rfl) ⟨7125245, by rfl⟩ : syracuseStep 9500327 = 14250491) B14250491
theorem B3798809 : Blo 830350 3798809 := bstep (se 2 (by rfl) ⟨1424553, by rfl⟩ : syracuseStep 3798809 = 2849107) B2849107
theorem B1407145 : Blo 830350 1407145 := bstep (se 2 (by rfl) ⟨527679, by rfl⟩ : syracuseStep 1407145 = 1055359) B1055359
theorem B4749799 : Blo 830350 4749799 := bstep (se 1 (by rfl) ⟨3562349, by rfl⟩ : syracuseStep 4749799 = 7124699) B7124699
theorem B7109801 : Blo 830350 7109801 := bstep (se 2 (by rfl) ⟨2666175, by rfl⟩ : syracuseStep 7109801 = 5332351) B5332351
theorem B3374443 : Blo 830350 3374443 := bstep (se 1 (by rfl) ⟨2530832, by rfl⟩ : syracuseStep 3374443 = 5061665) B5061665
theorem B3210911 : Blo 830350 3210911 := bstep (se 1 (by rfl) ⟨2408183, by rfl⟩ : syracuseStep 3210911 = 4816367) B4816367
theorem B3375481 : Blo 830350 3375481 := bstep (se 2 (by rfl) ⟨1265805, by rfl⟩ : syracuseStep 3375481 = 2531611) B2531611
theorem B12190189 : Blo 830350 12190189 := bstep (se 3 (by rfl) ⟨2285660, by rfl⟩ : syracuseStep 12190189 = 4571321) B4571321
theorem B1868345 : Blo 830350 1868345 := bstep (se 2 (by rfl) ⟨700629, by rfl⟩ : syracuseStep 1868345 = 1401259) B1401259
theorem B1246079 : Blo 830350 1246079 := bstep (se 1 (by rfl) ⟨934559, by rfl⟩ : syracuseStep 1246079 = 1869119) B1869119
theorem B1246391 : Blo 830350 1246391 := bstep (se 1 (by rfl) ⟨934793, by rfl⟩ : syracuseStep 1246391 = 1869587) B1869587
theorem B1869065 : Blo 830350 1869065 := bstep (se 2 (by rfl) ⟨700899, by rfl⟩ : syracuseStep 1869065 = 1401799) B1401799
theorem B5997833 : Blo 830350 5997833 := bstep (se 2 (by rfl) ⟨2249187, by rfl⟩ : syracuseStep 5997833 = 4498375) B4498375
theorem B1246631 : Blo 830350 1246631 := bstep (se 1 (by rfl) ⟨934973, by rfl⟩ : syracuseStep 1246631 = 1869947) B1869947
theorem B1246703 : Blo 830350 1246703 := bstep (se 1 (by rfl) ⟨935027, by rfl⟩ : syracuseStep 1246703 = 1870055) B1870055
theorem B4261585 : Blo 830350 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B3802859 : Blo 830350 3802859 := bstep (se 1 (by rfl) ⟨2852144, by rfl⟩ : syracuseStep 3802859 = 5704289) B5704289
theorem B1869695 : Blo 830350 1869695 := bstep (se 1 (by rfl) ⟨1402271, by rfl⟩ : syracuseStep 1869695 = 2804543) B2804543
theorem B13502447 : Blo 830350 13502447 := bstep (se 1 (by rfl) ⟨10126835, by rfl⟩ : syracuseStep 13502447 = 20253671) B20253671
theorem B55413067 : Blo 830350 55413067 := bstep (se 1 (by rfl) ⟨41559800, by rfl⟩ : syracuseStep 55413067 = 83119601) B83119601
theorem B1247591 : Blo 830350 1247591 := bstep (se 1 (by rfl) ⟨935693, by rfl⟩ : syracuseStep 1247591 = 1871387) B1871387
theorem B1247723 : Blo 830350 1247723 := bstep (se 1 (by rfl) ⟨935792, by rfl⟩ : syracuseStep 1247723 = 1871585) B1871585
theorem B1247963 : Blo 830350 1247963 := bstep (se 1 (by rfl) ⟨935972, by rfl⟩ : syracuseStep 1247963 = 1871945) B1871945
theorem B3378077 : Blo 830350 3378077 := bstep (se 3 (by rfl) ⟨633389, by rfl⟩ : syracuseStep 3378077 = 1266779) B1266779
theorem B68324309 : Blo 830350 68324309 := bstep (se 7 (by rfl) ⟨800675, by rfl⟩ : syracuseStep 68324309 = 1601351) B1601351
theorem B1249115 : Blo 830350 1249115 := bstep (se 1 (by rfl) ⟨936836, by rfl⟩ : syracuseStep 1249115 = 1873673) B1873673
theorem B1871783 : Blo 830350 1871783 := bstep (se 1 (by rfl) ⟨1403837, by rfl⟩ : syracuseStep 1871783 = 2807675) B2807675
theorem B1183771 : Blo 830350 1183771 := bstep (se 1 (by rfl) ⟨887828, by rfl⟩ : syracuseStep 1183771 = 1775657) B1775657
theorem B2102071 : Blo 830350 2102071 := bstep (se 1 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 2102071 = 3153107) B3153107
theorem B4002803 : Blo 830350 4002803 := bstep (se 1 (by rfl) ⟨3002102, by rfl⟩ : syracuseStep 4002803 = 6004205) B6004205
theorem B1250375 : Blo 830350 1250375 := bstep (se 1 (by rfl) ⟨937781, by rfl⟩ : syracuseStep 1250375 = 1875563) B1875563
theorem B7607465 : Blo 830350 7607465 := bstep (se 2 (by rfl) ⟨2852799, by rfl⟩ : syracuseStep 7607465 = 5705599) B5705599
theorem B1250615 : Blo 830350 1250615 := bstep (se 1 (by rfl) ⟨937961, by rfl⟩ : syracuseStep 1250615 = 1875923) B1875923
theorem B1250687 : Blo 830350 1250687 := bstep (se 1 (by rfl) ⟨938015, by rfl⟩ : syracuseStep 1250687 = 1876031) B1876031
theorem B1873655 : Blo 830350 1873655 := bstep (se 1 (by rfl) ⟨1405241, by rfl⟩ : syracuseStep 1873655 = 2810483) B2810483
theorem B2365355 : Blo 830350 2365355 := bstep (se 1 (by rfl) ⟨1774016, by rfl⟩ : syracuseStep 2365355 = 3548033) B3548033
theorem B2103367 : Blo 830350 2103367 := bstep (se 1 (by rfl) ⟨1577525, by rfl⟩ : syracuseStep 2103367 = 3155051) B3155051
theorem B5708225 : Blo 830350 5708225 := bstep (se 2 (by rfl) ⟨2140584, by rfl⟩ : syracuseStep 5708225 = 4281169) B4281169
theorem B1874375 : Blo 830350 1874375 := bstep (se 1 (by rfl) ⟨1405781, by rfl⟩ : syracuseStep 1874375 = 2811563) B2811563
theorem B1776289 : Blo 830350 1776289 := bstep (se 2 (by rfl) ⟨666108, by rfl⟩ : syracuseStep 1776289 = 1332217) B1332217
theorem B1186607 : Blo 830350 1186607 := bstep (se 1 (by rfl) ⟨889955, by rfl⟩ : syracuseStep 1186607 = 1779911) B1779911
theorem B1186687 : Blo 830350 1186687 := bstep (se 1 (by rfl) ⟨890015, by rfl⟩ : syracuseStep 1186687 = 1780031) B1780031
theorem B1874825 : Blo 830350 1874825 := bstep (se 2 (by rfl) ⟨703059, by rfl⟩ : syracuseStep 1874825 = 1406119) B1406119
theorem B1875113 : Blo 830350 1875113 := bstep (se 2 (by rfl) ⟨703167, by rfl⟩ : syracuseStep 1875113 = 1406335) B1406335
theorem B17997029 : Blo 830350 17997029 := bstep (se 4 (by rfl) ⟨1687221, by rfl⟩ : syracuseStep 17997029 = 3374443) B3374443
theorem B3382555 : Blo 830350 3382555 := bstep (se 1 (by rfl) ⟨2536916, by rfl⟩ : syracuseStep 3382555 = 5073833) B5073833
theorem B1875383 : Blo 830350 1875383 := bstep (se 1 (by rfl) ⟨1406537, by rfl⟩ : syracuseStep 1875383 = 2813075) B2813075
theorem B2366927 : Blo 830350 2366927 := bstep (se 1 (by rfl) ⟨1775195, by rfl⟩ : syracuseStep 2366927 = 3550391) B3550391
theorem B1875527 : Blo 830350 1875527 := bstep (se 1 (by rfl) ⟨1406645, by rfl⟩ : syracuseStep 1875527 = 2813291) B2813291
theorem B3153563 : Blo 830350 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B2104987 : Blo 830350 2104987 := bstep (se 1 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 2104987 = 3157481) B3157481
theorem B3153775 : Blo 830350 3153775 := bstep (se 1 (by rfl) ⟨2365331, by rfl⟩ : syracuseStep 3153775 = 4730663) B4730663
theorem B8101889 : Blo 830350 8101889 := bstep (se 2 (by rfl) ⟨3038208, by rfl⟩ : syracuseStep 8101889 = 6076417) B6076417
theorem B1876193 : Blo 830350 1876193 := bstep (se 2 (by rfl) ⟨703572, by rfl⟩ : syracuseStep 1876193 = 1407145) B1407145
theorem B1581383 : Blo 830350 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B2368055 : Blo 830350 2368055 := bstep (se 1 (by rfl) ⟨1776041, by rfl⟩ : syracuseStep 2368055 = 3552083) B3552083
theorem B6333065 : Blo 830350 6333065 := bstep (se 2 (by rfl) ⟨2374899, by rfl⟩ : syracuseStep 6333065 = 4749799) B4749799
theorem B1876859 : Blo 830350 1876859 := bstep (se 1 (by rfl) ⟨1407644, by rfl⟩ : syracuseStep 1876859 = 2815289) B2815289
theorem B1876895 : Blo 830350 1876895 := bstep (se 1 (by rfl) ⟨1407671, by rfl⟩ : syracuseStep 1876895 = 2815343) B2815343
theorem B10691513 : Blo 830350 10691513 := bstep (se 2 (by rfl) ⟨4009317, by rfl⟩ : syracuseStep 10691513 = 8018635) B8018635
theorem B6333551 : Blo 830350 6333551 := bstep (se 1 (by rfl) ⟨4750163, by rfl⟩ : syracuseStep 6333551 = 9500327) B9500327
theorem B2532539 : Blo 830350 2532539 := bstep (se 1 (by rfl) ⟨1899404, by rfl⟩ : syracuseStep 2532539 = 3798809) B3798809
theorem B2140607 : Blo 830350 2140607 := bstep (se 1 (by rfl) ⟨1605455, by rfl⟩ : syracuseStep 2140607 = 3210911) B3210911
theorem B2370185 : Blo 830350 2370185 := bstep (se 2 (by rfl) ⟨888819, by rfl⟩ : syracuseStep 2370185 = 1777639) B1777639
theorem B4008761 : Blo 830350 4008761 := bstep (se 2 (by rfl) ⟨1503285, by rfl⟩ : syracuseStep 4008761 = 3006571) B3006571
theorem B830495 : Blo 830350 830495 := bstep (se 1 (by rfl) ⟨622871, by rfl⟩ : syracuseStep 830495 = 1245743) B1245743
theorem B830555 : Blo 830350 830555 := bstep (se 1 (by rfl) ⟨622916, by rfl⟩ : syracuseStep 830555 = 1245833) B1245833
theorem B2108713 : Blo 830350 2108713 := bstep (se 2 (by rfl) ⟨790767, by rfl⟩ : syracuseStep 2108713 = 1581535) B1581535
theorem B830911 : Blo 830350 830911 := bstep (se 1 (by rfl) ⟨623183, by rfl⟩ : syracuseStep 830911 = 1246367) B1246367
theorem B2665919 : Blo 830350 2665919 := bstep (se 1 (by rfl) ⟨1999439, by rfl⟩ : syracuseStep 2665919 = 3998879) B3998879
theorem B2371027 : Blo 830350 2371027 := bstep (se 1 (by rfl) ⟨1778270, by rfl⟩ : syracuseStep 2371027 = 3556541) B3556541
theorem B831023 : Blo 830350 831023 := bstep (se 1 (by rfl) ⟨623267, by rfl⟩ : syracuseStep 831023 = 1246535) B1246535
theorem B2535067 : Blo 830350 2535067 := bstep (se 1 (by rfl) ⟨1901300, by rfl⟩ : syracuseStep 2535067 = 3802601) B3802601
theorem B831323 : Blo 830350 831323 := bstep (se 1 (by rfl) ⟨623492, by rfl⟩ : syracuseStep 831323 = 1246985) B1246985
theorem B2109311 : Blo 830350 2109311 := bstep (se 1 (by rfl) ⟨1581983, by rfl⟩ : syracuseStep 2109311 = 3163967) B3163967
theorem B5353363 : Blo 830350 5353363 := bstep (se 1 (by rfl) ⟨4015022, by rfl⟩ : syracuseStep 5353363 = 8030045) B8030045
theorem B2404255 : Blo 830350 2404255 := bstep (se 1 (by rfl) ⟨1803191, by rfl⟩ : syracuseStep 2404255 = 3606383) B3606383
theorem B1781927 : Blo 830350 1781927 := bstep (se 1 (by rfl) ⟨1336445, by rfl⟩ : syracuseStep 1781927 = 2672891) B2672891
theorem B4731371 : Blo 830350 4731371 := bstep (se 1 (by rfl) ⟨3548528, by rfl⟩ : syracuseStep 4731371 = 7097057) B7097057
theorem B832047 : Blo 830350 832047 := bstep (se 1 (by rfl) ⟨624035, by rfl⟩ : syracuseStep 832047 = 1248071) B1248071
theorem B832191 : Blo 830350 832191 := bstep (se 1 (by rfl) ⟨624143, by rfl⟩ : syracuseStep 832191 = 1248287) B1248287
theorem B4731803 : Blo 830350 4731803 := bstep (se 1 (by rfl) ⟨3548852, by rfl⟩ : syracuseStep 4731803 = 7097705) B7097705
theorem B832447 : Blo 830350 832447 := bstep (se 1 (by rfl) ⟨624335, by rfl⟩ : syracuseStep 832447 = 1248671) B1248671
theorem B832479 : Blo 830350 832479 := bstep (se 1 (by rfl) ⟨624359, by rfl⟩ : syracuseStep 832479 = 1248719) B1248719
theorem B10663265 : Blo 830350 10663265 := bstep (se 2 (by rfl) ⟨3998724, by rfl⟩ : syracuseStep 10663265 = 7997449) B7997449
theorem B4208111 : Blo 830350 4208111 := bstep (se 1 (by rfl) ⟨3156083, by rfl⟩ : syracuseStep 4208111 = 6312167) B6312167
theorem B833127 : Blo 830350 833127 := bstep (se 1 (by rfl) ⟨624845, by rfl⟩ : syracuseStep 833127 = 1249691) B1249691
theorem B833407 : Blo 830350 833407 := bstep (se 1 (by rfl) ⟨625055, by rfl⟩ : syracuseStep 833407 = 1250111) B1250111
theorem B4864063 : Blo 830350 4864063 := bstep (se 1 (by rfl) ⟨3648047, by rfl⟩ : syracuseStep 4864063 = 7296095) B7296095
theorem B833787 : Blo 830350 833787 := bstep (se 1 (by rfl) ⟨625340, by rfl⟩ : syracuseStep 833787 = 1250681) B1250681
theorem B2701775 : Blo 830350 2701775 := bstep (se 1 (by rfl) ⟨2026331, by rfl⟩ : syracuseStep 2701775 = 4052663) B4052663
theorem B3553807 : Blo 830350 3553807 := bstep (se 1 (by rfl) ⟨2665355, by rfl⟩ : syracuseStep 3553807 = 5330711) B5330711
theorem B834151 : Blo 830350 834151 := bstep (se 1 (by rfl) ⟨625613, by rfl⟩ : syracuseStep 834151 = 1251227) B1251227
theorem B4734287 : Blo 830350 4734287 := bstep (se 1 (by rfl) ⟨3550715, by rfl⟩ : syracuseStep 4734287 = 7101431) B7101431
theorem B3850337 : Blo 830350 3850337 := bstep (se 2 (by rfl) ⟨1443876, by rfl⟩ : syracuseStep 3850337 = 2887753) B2887753
theorem B934447 : Blo 830350 934447 := bstep (se 1 (by rfl) ⟨700835, by rfl⟩ : syracuseStep 934447 = 1401671) B1401671
theorem B934555 : Blo 830350 934555 := bstep (se 1 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 934555 = 1401833) B1401833
theorem B6308765 : Blo 830350 6308765 := bstep (se 3 (by rfl) ⟨1182893, by rfl⟩ : syracuseStep 6308765 = 2365787) B2365787
theorem B934879 : Blo 830350 934879 := bstep (se 1 (by rfl) ⟨701159, by rfl⟩ : syracuseStep 934879 = 1402319) B1402319
theorem B3163495 : Blo 830350 3163495 := bstep (se 1 (by rfl) ⟨2372621, by rfl⟩ : syracuseStep 3163495 = 4745243) B4745243
theorem B7095721 : Blo 830350 7095721 := bstep (se 2 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 7095721 = 5321791) B5321791
theorem B4736677 : Blo 830350 4736677 := bstep (se 4 (by rfl) ⟨444063, by rfl⟩ : syracuseStep 4736677 = 888127) B888127
theorem B936895 : Blo 830350 936895 := bstep (se 1 (by rfl) ⟨702671, by rfl⟩ : syracuseStep 936895 = 1405343) B1405343
theorem B1626203 : Blo 830350 1626203 := bstep (se 1 (by rfl) ⟨1219652, by rfl⟩ : syracuseStep 1626203 = 2439305) B2439305
theorem B9588901 : Blo 830350 9588901 := bstep (se 4 (by rfl) ⟨898959, by rfl⟩ : syracuseStep 9588901 = 1797919) B1797919
theorem B3166397 : Blo 830350 3166397 := bstep (se 3 (by rfl) ⟨593699, by rfl⟩ : syracuseStep 3166397 = 1187399) B1187399
theorem B4215401 : Blo 830350 4215401 := bstep (se 2 (by rfl) ⟨1580775, by rfl⟩ : syracuseStep 4215401 = 3161551) B3161551
theorem B2806379 : Blo 830350 2806379 := bstep (se 1 (by rfl) ⟨2104784, by rfl⟩ : syracuseStep 2806379 = 4209569) B4209569
theorem B4739867 : Blo 830350 4739867 := bstep (se 1 (by rfl) ⟨3554900, by rfl⟩ : syracuseStep 4739867 = 7109801) B7109801
theorem B3200411 : Blo 830350 3200411 := bstep (se 1 (by rfl) ⟨2400308, by rfl⟩ : syracuseStep 3200411 = 4800617) B4800617
theorem B3036631 : Blo 830350 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B1202047 : Blo 830350 1202047 := bstep (se 1 (by rfl) ⟨901535, by rfl⟩ : syracuseStep 1202047 = 1803071) B1803071
theorem B4216859 : Blo 830350 4216859 := bstep (se 1 (by rfl) ⟨3162644, by rfl⟩ : syracuseStep 4216859 = 6325289) B6325289
theorem B4217183 : Blo 830350 4217183 := bstep (se 1 (by rfl) ⟨3162887, by rfl⟩ : syracuseStep 4217183 = 6325775) B6325775
theorem B4741577 : Blo 830350 4741577 := bstep (se 2 (by rfl) ⟨1778091, by rfl⟩ : syracuseStep 4741577 = 3556183) B3556183
theorem B3857503 : Blo 830350 3857503 := bstep (se 1 (by rfl) ⟨2893127, by rfl⟩ : syracuseStep 3857503 = 5786255) B5786255
theorem B34102529 : Blo 830350 34102529 := bstep (se 2 (by rfl) ⟨12788448, by rfl⟩ : syracuseStep 34102529 = 25576897) B25576897
theorem B2810375 : Blo 830350 2810375 := bstep (se 1 (by rfl) ⟨2107781, by rfl⟩ : syracuseStep 2810375 = 4215563) B4215563
theorem B46883711 : Blo 830350 46883711 := bstep (se 1 (by rfl) ⟨35162783, by rfl⟩ : syracuseStep 46883711 = 70325567) B70325567
theorem B2844559 : Blo 830350 2844559 := bstep (se 1 (by rfl) ⟨2133419, by rfl⟩ : syracuseStep 2844559 = 4266839) B4266839
theorem B2812103 : Blo 830350 2812103 := bstep (se 1 (by rfl) ⟨2109077, by rfl⟩ : syracuseStep 2812103 = 4218155) B4218155
theorem B2812319 : Blo 830350 2812319 := bstep (se 1 (by rfl) ⟨2109239, by rfl⟩ : syracuseStep 2812319 = 4218479) B4218479
theorem B24308369 : Blo 830350 24308369 := bstep (se 2 (by rfl) ⟨9115638, by rfl⟩ : syracuseStep 24308369 = 18231277) B18231277
theorem B5696839 : Blo 830350 5696839 := bstep (se 1 (by rfl) ⟨4272629, by rfl⟩ : syracuseStep 5696839 = 8545259) B8545259
theorem B1405019 : Blo 830350 1405019 := bstep (se 1 (by rfl) ⟨1053764, by rfl⟩ : syracuseStep 1405019 = 2107529) B2107529
theorem B4747409 : Blo 830350 4747409 := bstep (se 2 (by rfl) ⟨1780278, by rfl⟩ : syracuseStep 4747409 = 3560557) B3560557
theorem B23065195 : Blo 830350 23065195 := bstep (se 1 (by rfl) ⟨17298896, by rfl⟩ : syracuseStep 23065195 = 34597793) B34597793
theorem B1897103 : Blo 830350 1897103 := bstep (se 1 (by rfl) ⟨1422827, by rfl⟩ : syracuseStep 1897103 = 2845655) B2845655
theorem B4223663 : Blo 830350 4223663 := bstep (se 1 (by rfl) ⟨3167747, by rfl⟩ : syracuseStep 4223663 = 6335495) B6335495
theorem B6320915 : Blo 830350 6320915 := bstep (se 1 (by rfl) ⟨4740686, by rfl⟩ : syracuseStep 6320915 = 9481373) B9481373
theorem B2814803 : Blo 830350 2814803 := bstep (se 1 (by rfl) ⟨2111102, by rfl⟩ : syracuseStep 2814803 = 4222205) B4222205
theorem B32043923 : Blo 830350 32043923 := bstep (se 1 (by rfl) ⟨24032942, by rfl⟩ : syracuseStep 32043923 = 48065885) B48065885
theorem B9466793 : Blo 830350 9466793 := bstep (se 2 (by rfl) ⟨3550047, by rfl⟩ : syracuseStep 9466793 = 7100095) B7100095
theorem B1898363 : Blo 830350 1898363 := bstep (se 1 (by rfl) ⟨1423772, by rfl⟩ : syracuseStep 1898363 = 2847545) B2847545
theorem B1899001 : Blo 830350 1899001 := bstep (se 2 (by rfl) ⟨712125, by rfl⟩ : syracuseStep 1899001 = 1424251) B1424251
theorem B4750073 : Blo 830350 4750073 := bstep (se 2 (by rfl) ⟨1781277, by rfl⟩ : syracuseStep 4750073 = 3562555) B3562555
theorem B1245563 : Blo 830350 1245563 := bstep (se 1 (by rfl) ⟨934172, by rfl⟩ : syracuseStep 1245563 = 1868345) B1868345
theorem B16253585 : Blo 830350 16253585 := bstep (se 2 (by rfl) ⟨6095094, by rfl⟩ : syracuseStep 16253585 = 12190189) B12190189
theorem B1245929 : Blo 830350 1245929 := bstep (se 2 (by rfl) ⟨467223, by rfl⟩ : syracuseStep 1245929 = 934447) B934447
theorem B1246043 : Blo 830350 1246043 := bstep (se 1 (by rfl) ⟨934532, by rfl⟩ : syracuseStep 1246043 = 1869065) B1869065
theorem B3998555 : Blo 830350 3998555 := bstep (se 1 (by rfl) ⟨2998916, by rfl⟩ : syracuseStep 3998555 = 5997833) B5997833
theorem B1246073 : Blo 830350 1246073 := bstep (se 2 (by rfl) ⟨467277, by rfl⟩ : syracuseStep 1246073 = 934555) B934555
theorem B1246463 : Blo 830350 1246463 := bstep (se 1 (by rfl) ⟨934847, by rfl⟩ : syracuseStep 1246463 = 1869695) B1869695
theorem B1246505 : Blo 830350 1246505 := bstep (se 2 (by rfl) ⟨467439, by rfl⟩ : syracuseStep 1246505 = 934879) B934879
theorem B45549539 : Blo 830350 45549539 := bstep (se 1 (by rfl) ⟨34162154, by rfl⟩ : syracuseStep 45549539 = 68324309) B68324309
theorem B1247855 : Blo 830350 1247855 := bstep (se 1 (by rfl) ⟨935891, by rfl⟩ : syracuseStep 1247855 = 1871783) B1871783
theorem B1870919 : Blo 830350 1870919 := bstep (se 1 (by rfl) ⟨1403189, by rfl⟩ : syracuseStep 1870919 = 2806379) B2806379
theorem B2133607 : Blo 830350 2133607 := bstep (se 1 (by rfl) ⟨1600205, by rfl⟩ : syracuseStep 2133607 = 3200411) B3200411
theorem B1249103 : Blo 830350 1249103 := bstep (se 1 (by rfl) ⟨936827, by rfl⟩ : syracuseStep 1249103 = 1873655) B1873655
theorem B1249193 : Blo 830350 1249193 := bstep (se 2 (by rfl) ⟨468447, by rfl⟩ : syracuseStep 1249193 = 936895) B936895
theorem B1576903 : Blo 830350 1576903 := bstep (se 1 (by rfl) ⟨1182677, by rfl⟩ : syracuseStep 1576903 = 2365355) B2365355
theorem B3805483 : Blo 830350 3805483 := bstep (se 1 (by rfl) ⟨2854112, by rfl⟩ : syracuseStep 3805483 = 5708225) B5708225
theorem B1249583 : Blo 830350 1249583 := bstep (se 1 (by rfl) ⟨937187, by rfl⟩ : syracuseStep 1249583 = 1874375) B1874375
theorem B1249883 : Blo 830350 1249883 := bstep (se 1 (by rfl) ⟨937412, by rfl⟩ : syracuseStep 1249883 = 1874825) B1874825
theorem B1250075 : Blo 830350 1250075 := bstep (se 1 (by rfl) ⟨937556, by rfl⟩ : syracuseStep 1250075 = 1875113) B1875113
theorem B11998019 : Blo 830350 11998019 := bstep (se 1 (by rfl) ⟨8998514, by rfl⟩ : syracuseStep 11998019 = 17997029) B17997029
theorem B3380089 : Blo 830350 3380089 := bstep (se 2 (by rfl) ⟨1267533, by rfl⟩ : syracuseStep 3380089 = 2535067) B2535067
theorem B1250255 : Blo 830350 1250255 := bstep (se 1 (by rfl) ⟨937691, by rfl⟩ : syracuseStep 1250255 = 1875383) B1875383
theorem B1577951 : Blo 830350 1577951 := bstep (se 1 (by rfl) ⟨1183463, by rfl⟩ : syracuseStep 1577951 = 2366927) B2366927
theorem B1250351 : Blo 830350 1250351 := bstep (se 1 (by rfl) ⟨937763, by rfl⟩ : syracuseStep 1250351 = 1875527) B1875527
theorem B2102375 : Blo 830350 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B1578361 : Blo 830350 1578361 := bstep (se 2 (by rfl) ⟨591885, by rfl⟩ : syracuseStep 1578361 = 1183771) B1183771
theorem B1250795 : Blo 830350 1250795 := bstep (se 1 (by rfl) ⟨938096, by rfl⟩ : syracuseStep 1250795 = 1876193) B1876193
theorem B12785201 : Blo 830350 12785201 := bstep (se 2 (by rfl) ⟨4794450, by rfl⟩ : syracuseStep 12785201 = 9588901) B9588901
theorem B1873583 : Blo 830350 1873583 := bstep (se 1 (by rfl) ⟨1405187, by rfl⟩ : syracuseStep 1873583 = 2810375) B2810375
theorem B1578703 : Blo 830350 1578703 := bstep (se 1 (by rfl) ⟨1184027, by rfl⟩ : syracuseStep 1578703 = 2368055) B2368055
theorem B1251239 : Blo 830350 1251239 := bstep (se 1 (by rfl) ⟨938429, by rfl⟩ : syracuseStep 1251239 = 1876859) B1876859
theorem B1251263 : Blo 830350 1251263 := bstep (se 1 (by rfl) ⟨938447, by rfl⟩ : syracuseStep 1251263 = 1876895) B1876895
theorem B1874735 : Blo 830350 1874735 := bstep (se 1 (by rfl) ⟨1406051, by rfl⟩ : syracuseStep 1874735 = 2812103) B2812103
theorem B1874879 : Blo 830350 1874879 := bstep (se 1 (by rfl) ⟨1406159, by rfl⟩ : syracuseStep 1874879 = 2812319) B2812319
theorem B1580123 : Blo 830350 1580123 := bstep (se 1 (by rfl) ⟨1185092, by rfl⟩ : syracuseStep 1580123 = 2370185) B2370185
theorem B1187951 : Blo 830350 1187951 := bstep (se 1 (by rfl) ⟨890963, by rfl⟩ : syracuseStep 1187951 = 1781927) B1781927
theorem B3154247 : Blo 830350 3154247 := bstep (se 1 (by rfl) ⟨2365685, by rfl⟩ : syracuseStep 3154247 = 4731371) B4731371
theorem B1876535 : Blo 830350 1876535 := bstep (se 1 (by rfl) ⟨1407401, by rfl⟩ : syracuseStep 1876535 = 2814803) B2814803
theorem B3154535 : Blo 830350 3154535 := bstep (se 1 (by rfl) ⟨2365901, by rfl⟩ : syracuseStep 3154535 = 4731803) B4731803
theorem B2532001 : Blo 830350 2532001 := bstep (se 2 (by rfl) ⟨949500, by rfl⟩ : syracuseStep 2532001 = 1899001) B1899001
theorem B2368385 : Blo 830350 2368385 := bstep (se 2 (by rfl) ⟨888144, by rfl⟩ : syracuseStep 2368385 = 1776289) B1776289
theorem B1582249 : Blo 830350 1582249 := bstep (se 2 (by rfl) ⟨593343, by rfl⟩ : syracuseStep 1582249 = 1186687) B1186687
theorem B3156191 : Blo 830350 3156191 := bstep (se 1 (by rfl) ⟨2367143, by rfl⟩ : syracuseStep 3156191 = 4734287) B4734287
theorem B4205033 : Blo 830350 4205033 := bstep (se 2 (by rfl) ⟨1576887, by rfl⟩ : syracuseStep 4205033 = 3153775) B3153775
theorem B2566891 : Blo 830350 2566891 := bstep (se 1 (by rfl) ⟨1925168, by rfl⟩ : syracuseStep 2566891 = 3850337) B3850337
theorem B4336541 : Blo 830350 4336541 := bstep (se 3 (by rfl) ⟨813101, by rfl⟩ : syracuseStep 4336541 = 1626203) B1626203
theorem B4500641 : Blo 830350 4500641 := bstep (se 2 (by rfl) ⟨1687740, by rfl⟩ : syracuseStep 4500641 = 3375481) B3375481
theorem B830719 : Blo 830350 830719 := bstep (se 1 (by rfl) ⟨623039, by rfl⟩ : syracuseStep 830719 = 1246079) B1246079
theorem B4205843 : Blo 830350 4205843 := bstep (se 1 (by rfl) ⟨3154382, by rfl⟩ : syracuseStep 4205843 = 6308765) B6308765
theorem B830927 : Blo 830350 830927 := bstep (se 1 (by rfl) ⟨623195, by rfl⟩ : syracuseStep 830927 = 1246391) B1246391
theorem B831087 : Blo 830350 831087 := bstep (se 1 (by rfl) ⟨623315, by rfl⟩ : syracuseStep 831087 = 1246631) B1246631
theorem B831135 : Blo 830350 831135 := bstep (se 1 (by rfl) ⟨623351, by rfl⟩ : syracuseStep 831135 = 1246703) B1246703
theorem B2535239 : Blo 830350 2535239 := bstep (se 1 (by rfl) ⟨1901429, by rfl⟩ : syracuseStep 2535239 = 3802859) B3802859
theorem B831727 : Blo 830350 831727 := bstep (se 1 (by rfl) ⟨623795, by rfl⟩ : syracuseStep 831727 = 1247591) B1247591
theorem B831815 : Blo 830350 831815 := bstep (se 1 (by rfl) ⟨623861, by rfl⟩ : syracuseStep 831815 = 1247723) B1247723
theorem B5058941 : Blo 830350 5058941 := bstep (se 3 (by rfl) ⟨948551, by rfl⟩ : syracuseStep 5058941 = 1897103) B1897103
theorem B831975 : Blo 830350 831975 := bstep (se 1 (by rfl) ⟨623981, by rfl⟩ : syracuseStep 831975 = 1247963) B1247963
theorem B5682113 : Blo 830350 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B832743 : Blo 830350 832743 := bstep (se 1 (by rfl) ⟨624557, by rfl⟩ : syracuseStep 832743 = 1249115) B1249115
theorem B2110931 : Blo 830350 2110931 := bstep (se 1 (by rfl) ⟨1583198, by rfl⟩ : syracuseStep 2110931 = 3166397) B3166397
theorem B3159911 : Blo 830350 3159911 := bstep (se 1 (by rfl) ⟨2369933, by rfl⟩ : syracuseStep 3159911 = 4739867) B4739867
theorem B2668535 : Blo 830350 2668535 := bstep (se 1 (by rfl) ⟨2001401, by rfl⟩ : syracuseStep 2668535 = 4002803) B4002803
theorem B833583 : Blo 830350 833583 := bstep (se 1 (by rfl) ⟨625187, by rfl⟩ : syracuseStep 833583 = 1250375) B1250375
theorem B833743 : Blo 830350 833743 := bstep (se 1 (by rfl) ⟨625307, by rfl⟩ : syracuseStep 833743 = 1250615) B1250615
theorem B833791 : Blo 830350 833791 := bstep (se 1 (by rfl) ⟨625343, by rfl⟩ : syracuseStep 833791 = 1250687) B1250687
theorem B3161051 : Blo 830350 3161051 := bstep (se 1 (by rfl) ⟨2370788, by rfl⟩ : syracuseStep 3161051 = 4741577) B4741577
theorem B3161369 : Blo 830350 3161369 := bstep (se 2 (by rfl) ⟨1185513, by rfl⟩ : syracuseStep 3161369 = 2371027) B2371027
theorem B7127675 : Blo 830350 7127675 := bstep (se 1 (by rfl) ⟨5345756, by rfl⟩ : syracuseStep 7127675 = 10691513) B10691513
theorem B1688359 : Blo 830350 1688359 := bstep (se 1 (by rfl) ⟨1266269, by rfl⟩ : syracuseStep 1688359 = 2532539) B2532539
theorem B30753593 : Blo 830350 30753593 := bstep (se 2 (by rfl) ⟨11532597, by rfl⟩ : syracuseStep 30753593 = 23065195) B23065195
theorem B2802761 : Blo 830350 2802761 := bstep (se 2 (by rfl) ⟨1051035, by rfl⟩ : syracuseStep 2802761 = 2102071) B2102071
theorem B1427071 : Blo 830350 1427071 := bstep (se 1 (by rfl) ⟨1070303, by rfl⟩ : syracuseStep 1427071 = 2140607) B2140607
theorem B16205579 : Blo 830350 16205579 := bstep (se 1 (by rfl) ⟨12154184, by rfl⟩ : syracuseStep 16205579 = 24308369) B24308369
theorem B2672507 : Blo 830350 2672507 := bstep (se 1 (by rfl) ⟨2004380, by rfl⟩ : syracuseStep 2672507 = 4008761) B4008761
theorem B4048841 : Blo 830350 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B3164285 : Blo 830350 3164285 := bstep (se 3 (by rfl) ⟨593303, by rfl⟩ : syracuseStep 3164285 = 1186607) B1186607
theorem B936679 : Blo 830350 936679 := bstep (se 1 (by rfl) ⟨702509, by rfl⟩ : syracuseStep 936679 = 1405019) B1405019
theorem B2804489 : Blo 830350 2804489 := bstep (se 2 (by rfl) ⟨1051683, by rfl⟩ : syracuseStep 2804489 = 2103367) B2103367
theorem B3164939 : Blo 830350 3164939 := bstep (se 1 (by rfl) ⟨2373704, by rfl⟩ : syracuseStep 3164939 = 4747409) B4747409
theorem B4213943 : Blo 830350 4213943 := bstep (se 1 (by rfl) ⟨3160457, by rfl⟩ : syracuseStep 4213943 = 6320915) B6320915
theorem B6311195 : Blo 830350 6311195 := bstep (se 1 (by rfl) ⟨4733396, by rfl⟩ : syracuseStep 6311195 = 9466793) B9466793
theorem B4738409 : Blo 830350 4738409 := bstep (se 2 (by rfl) ⟨1776903, by rfl⟩ : syracuseStep 4738409 = 3553807) B3553807
theorem B2805407 : Blo 830350 2805407 := bstep (se 1 (by rfl) ⟨2104055, by rfl⟩ : syracuseStep 2805407 = 4208111) B4208111
theorem B1265575 : Blo 830350 1265575 := bstep (se 1 (by rfl) ⟨949181, by rfl⟩ : syracuseStep 1265575 = 1898363) B1898363
theorem B4510073 : Blo 830350 4510073 := bstep (se 2 (by rfl) ⟨1691277, by rfl⟩ : syracuseStep 4510073 = 3382555) B3382555
theorem B3166715 : Blo 830350 3166715 := bstep (se 1 (by rfl) ⟨2375036, by rfl⟩ : syracuseStep 3166715 = 4750073) B4750073
theorem B6410917 : Blo 830350 6410917 := bstep (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) B1202047
theorem B2806649 : Blo 830350 2806649 := bstep (se 2 (by rfl) ⟨1052493, by rfl⟩ : syracuseStep 2806649 = 2104987) B2104987
theorem B4217021 : Blo 830350 4217021 := bstep (se 3 (by rfl) ⟨790691, by rfl⟩ : syracuseStep 4217021 = 1581383) B1581383
theorem B9001631 : Blo 830350 9001631 := bstep (se 1 (by rfl) ⟨6751223, by rfl⟩ : syracuseStep 9001631 = 13502447) B13502447
theorem B4217993 : Blo 830350 4217993 := bstep (se 2 (by rfl) ⟨1581747, by rfl⟩ : syracuseStep 4217993 = 3163495) B3163495
theorem B9460961 : Blo 830350 9460961 := bstep (se 2 (by rfl) ⟨3547860, by rfl⟩ : syracuseStep 9460961 = 7095721) B7095721
theorem B2252051 : Blo 830350 2252051 := bstep (se 1 (by rfl) ⟨1689038, by rfl⟩ : syracuseStep 2252051 = 3378077) B3378077
theorem B6315569 : Blo 830350 6315569 := bstep (se 2 (by rfl) ⟨2368338, by rfl⟩ : syracuseStep 6315569 = 4736677) B4736677
theorem B3792745 : Blo 830350 3792745 := bstep (se 2 (by rfl) ⟨1422279, by rfl⟩ : syracuseStep 3792745 = 2844559) B2844559
theorem B2810267 : Blo 830350 2810267 := bstep (se 1 (by rfl) ⟨2107700, by rfl⟩ : syracuseStep 2810267 = 4215401) B4215401
theorem B73884089 : Blo 830350 73884089 := bstep (se 2 (by rfl) ⟨27706533, by rfl⟩ : syracuseStep 73884089 = 55413067) B55413067
theorem B5071643 : Blo 830350 5071643 := bstep (se 1 (by rfl) ⟨3803732, by rfl⟩ : syracuseStep 5071643 = 7607465) B7607465
theorem B2811239 : Blo 830350 2811239 := bstep (se 1 (by rfl) ⟨2108429, by rfl⟩ : syracuseStep 2811239 = 4216859) B4216859
theorem B2811455 : Blo 830350 2811455 := bstep (se 1 (by rfl) ⟨2108591, by rfl⟩ : syracuseStep 2811455 = 4217183) B4217183
theorem B2811617 : Blo 830350 2811617 := bstep (se 2 (by rfl) ⟨1054356, by rfl⟩ : syracuseStep 2811617 = 2108713) B2108713
theorem B7595785 : Blo 830350 7595785 := bstep (se 2 (by rfl) ⟨2848419, by rfl⟩ : syracuseStep 7595785 = 5696839) B5696839
theorem B22735019 : Blo 830350 22735019 := bstep (se 1 (by rfl) ⟨17051264, by rfl⟩ : syracuseStep 22735019 = 34102529) B34102529
theorem B7137817 : Blo 830350 7137817 := bstep (se 2 (by rfl) ⟨2676681, by rfl⟩ : syracuseStep 7137817 = 5353363) B5353363
theorem B3205673 : Blo 830350 3205673 := bstep (se 2 (by rfl) ⟨1202127, by rfl⟩ : syracuseStep 3205673 = 2404255) B2404255
theorem B5401259 : Blo 830350 5401259 := bstep (se 1 (by rfl) ⟨4050944, by rfl⟩ : syracuseStep 5401259 = 8101889) B8101889
theorem B4222043 : Blo 830350 4222043 := bstep (se 1 (by rfl) ⟨3166532, by rfl⟩ : syracuseStep 4222043 = 6333065) B6333065
theorem B31255807 : Blo 830350 31255807 := bstep (se 1 (by rfl) ⟨23441855, by rfl⟩ : syracuseStep 31255807 = 46883711) B46883711
theorem B4222367 : Blo 830350 4222367 := bstep (se 1 (by rfl) ⟨3166775, by rfl⟩ : syracuseStep 4222367 = 6333551) B6333551
theorem B1406207 : Blo 830350 1406207 := bstep (se 1 (by rfl) ⟨1054655, by rfl⟩ : syracuseStep 1406207 = 2109311) B2109311
theorem B6485417 : Blo 830350 6485417 := bstep (se 2 (by rfl) ⟨2432031, by rfl⟩ : syracuseStep 6485417 = 4864063) B4864063
theorem B2815775 : Blo 830350 2815775 := bstep (se 1 (by rfl) ⟨2111831, by rfl⟩ : syracuseStep 2815775 = 4223663) B4223663
theorem B21362615 : Blo 830350 21362615 := bstep (se 1 (by rfl) ⟨16021961, by rfl⟩ : syracuseStep 21362615 = 32043923) B32043923
theorem B7108843 : Blo 830350 7108843 := bstep (se 1 (by rfl) ⟨5331632, by rfl⟩ : syracuseStep 7108843 = 10663265) B10663265
theorem B7109117 : Blo 830350 7109117 := bstep (se 3 (by rfl) ⟨1332959, by rfl⟩ : syracuseStep 7109117 = 2665919) B2665919
theorem B5143337 : Blo 830350 5143337 := bstep (se 2 (by rfl) ⟨1928751, by rfl⟩ : syracuseStep 5143337 = 3857503) B3857503
theorem B1801183 : Blo 830350 1801183 := bstep (se 1 (by rfl) ⟨1350887, by rfl⟩ : syracuseStep 1801183 = 2701775) B2701775
theorem B4751783 : Blo 830350 4751783 := bstep (se 1 (by rfl) ⟨3563837, by rfl⟩ : syracuseStep 4751783 = 7127675) B7127675
theorem B152273429 : Blo 830350 152273429 := bstep (se 6 (by rfl) ⟨3568908, by rfl⟩ : syracuseStep 152273429 = 7137817) B7137817
theorem B1868507 : Blo 830350 1868507 := bstep (se 1 (by rfl) ⟨1401380, by rfl⟩ : syracuseStep 1868507 = 2802761) B2802761
theorem B3376001 : Blo 830350 3376001 := bstep (se 2 (by rfl) ⟨1266000, by rfl⟩ : syracuseStep 3376001 = 2532001) B2532001
theorem B1869659 : Blo 830350 1869659 := bstep (se 1 (by rfl) ⟨1402244, by rfl⟩ : syracuseStep 1869659 = 2804489) B2804489
theorem B1247279 : Blo 830350 1247279 := bstep (se 1 (by rfl) ⟨935459, by rfl⟩ : syracuseStep 1247279 = 1870919) B1870919
theorem B1902761 : Blo 830350 1902761 := bstep (se 2 (by rfl) ⟨713535, by rfl⟩ : syracuseStep 1902761 = 1427071) B1427071
theorem B10127713 : Blo 830350 10127713 := bstep (se 2 (by rfl) ⟨3797892, by rfl⟩ : syracuseStep 10127713 = 7595785) B7595785
theorem B1870271 : Blo 830350 1870271 := bstep (se 1 (by rfl) ⟨1402703, by rfl⟩ : syracuseStep 1870271 = 2805407) B2805407
theorem B7998679 : Blo 830350 7998679 := bstep (se 1 (by rfl) ⟨5999009, by rfl⟩ : syracuseStep 7998679 = 11998019) B11998019
theorem B1871099 : Blo 830350 1871099 := bstep (se 1 (by rfl) ⟨1403324, by rfl⟩ : syracuseStep 1871099 = 2806649) B2806649
theorem B1051967 : Blo 830350 1051967 := bstep (se 1 (by rfl) ⟨788975, by rfl⟩ : syracuseStep 1051967 = 1577951) B1577951
theorem B1248905 : Blo 830350 1248905 := bstep (se 2 (by rfl) ⟨468339, by rfl⟩ : syracuseStep 1248905 = 936679) B936679
theorem B8523467 : Blo 830350 8523467 := bstep (se 1 (by rfl) ⟨6392600, by rfl⟩ : syracuseStep 8523467 = 12785201) B12785201
theorem B1249055 : Blo 830350 1249055 := bstep (se 1 (by rfl) ⟨936791, by rfl⟩ : syracuseStep 1249055 = 1873583) B1873583
theorem B6001087 : Blo 830350 6001087 := bstep (se 1 (by rfl) ⟨4500815, by rfl⟩ : syracuseStep 6001087 = 9001631) B9001631
theorem B1249823 : Blo 830350 1249823 := bstep (se 1 (by rfl) ⟨937367, by rfl⟩ : syracuseStep 1249823 = 1874735) B1874735
theorem B1249919 : Blo 830350 1249919 := bstep (se 1 (by rfl) ⟨937439, by rfl⟩ : syracuseStep 1249919 = 1874879) B1874879
theorem B1053415 : Blo 830350 1053415 := bstep (se 1 (by rfl) ⟨790061, by rfl⟩ : syracuseStep 1053415 = 1580123) B1580123
theorem B2102537 : Blo 830350 2102537 := bstep (se 2 (by rfl) ⟨788451, by rfl⟩ : syracuseStep 2102537 = 1576903) B1576903
theorem B2102831 : Blo 830350 2102831 := bstep (se 1 (by rfl) ⟨1577123, by rfl⟩ : syracuseStep 2102831 = 3154247) B3154247
theorem B1873511 : Blo 830350 1873511 := bstep (se 1 (by rfl) ⟨1405133, by rfl⟩ : syracuseStep 1873511 = 2810267) B2810267
theorem B49256059 : Blo 830350 49256059 := bstep (se 1 (by rfl) ⟨36942044, by rfl⟩ : syracuseStep 49256059 = 73884089) B73884089
theorem B1251023 : Blo 830350 1251023 := bstep (se 1 (by rfl) ⟨938267, by rfl⟩ : syracuseStep 1251023 = 1876535) B1876535
theorem B2103023 : Blo 830350 2103023 := bstep (se 1 (by rfl) ⟨1577267, by rfl⟩ : syracuseStep 2103023 = 3154535) B3154535
theorem B60626717 : Blo 830350 60626717 := bstep (se 3 (by rfl) ⟨11367509, by rfl⟩ : syracuseStep 60626717 = 22735019) B22735019
theorem B3381095 : Blo 830350 3381095 := bstep (se 1 (by rfl) ⟨2535821, by rfl⟩ : syracuseStep 3381095 = 5071643) B5071643
theorem B1578923 : Blo 830350 1578923 := bstep (se 1 (by rfl) ⟨1184192, by rfl⟩ : syracuseStep 1578923 = 2368385) B2368385
theorem B1874159 : Blo 830350 1874159 := bstep (se 1 (by rfl) ⟨1405619, by rfl⟩ : syracuseStep 1874159 = 2811239) B2811239
theorem B1874303 : Blo 830350 1874303 := bstep (se 1 (by rfl) ⟨1405727, by rfl⟩ : syracuseStep 1874303 = 2811455) B2811455
theorem B1874411 : Blo 830350 1874411 := bstep (se 1 (by rfl) ⟨1405808, by rfl⟩ : syracuseStep 1874411 = 2811617) B2811617
theorem B2104127 : Blo 830350 2104127 := bstep (se 1 (by rfl) ⟨1578095, by rfl⟩ : syracuseStep 2104127 = 3156191) B3156191
theorem B2137115 : Blo 830350 2137115 := bstep (se 1 (by rfl) ⟨1602836, by rfl⟩ : syracuseStep 2137115 = 3205673) B3205673
theorem B2104481 : Blo 830350 2104481 := bstep (se 2 (by rfl) ⟨789180, by rfl⟩ : syracuseStep 2104481 = 1578361) B1578361
theorem B2891027 : Blo 830350 2891027 := bstep (se 1 (by rfl) ⟨2168270, by rfl⟩ : syracuseStep 2891027 = 4336541) B4336541
theorem B2104937 : Blo 830350 2104937 := bstep (se 2 (by rfl) ⟨789351, by rfl⟩ : syracuseStep 2104937 = 1578703) B1578703
theorem B9478457 : Blo 830350 9478457 := bstep (se 2 (by rfl) ⟨3554421, by rfl⟩ : syracuseStep 9478457 = 7108843) B7108843
theorem B12001709 : Blo 830350 12001709 := bstep (se 3 (by rfl) ⟨2250320, by rfl⟩ : syracuseStep 12001709 = 4500641) B4500641
theorem B1877183 : Blo 830350 1877183 := bstep (se 1 (by rfl) ⟨1407887, by rfl⟩ : syracuseStep 1877183 = 2815775) B2815775
theorem B2106607 : Blo 830350 2106607 := bstep (se 1 (by rfl) ⟨1579955, by rfl⟩ : syracuseStep 2106607 = 3159911) B3159911
theorem B2401577 : Blo 830350 2401577 := bstep (se 2 (by rfl) ⟨900591, by rfl⟩ : syracuseStep 2401577 = 1801183) B1801183
theorem B1779023 : Blo 830350 1779023 := bstep (se 1 (by rfl) ⟨1334267, by rfl⟩ : syracuseStep 1779023 = 2668535) B2668535
theorem B20227973 : Blo 830350 20227973 := bstep (se 4 (by rfl) ⟨1896372, by rfl⟩ : syracuseStep 20227973 = 3792745) B3792745
theorem B2107367 : Blo 830350 2107367 := bstep (se 1 (by rfl) ⟨1580525, by rfl⟩ : syracuseStep 2107367 = 3161051) B3161051
theorem B2107579 : Blo 830350 2107579 := bstep (se 1 (by rfl) ⟨1580684, by rfl⟩ : syracuseStep 2107579 = 3161369) B3161369
theorem B830375 : Blo 830350 830375 := bstep (se 1 (by rfl) ⟨622781, by rfl⟩ : syracuseStep 830375 = 1245563) B1245563
theorem B830619 : Blo 830350 830619 := bstep (se 1 (by rfl) ⟨622964, by rfl⟩ : syracuseStep 830619 = 1245929) B1245929
theorem B830695 : Blo 830350 830695 := bstep (se 1 (by rfl) ⟨623021, by rfl⟩ : syracuseStep 830695 = 1246043) B1246043
theorem B2665703 : Blo 830350 2665703 := bstep (se 1 (by rfl) ⟨1999277, by rfl⟩ : syracuseStep 2665703 = 3998555) B3998555
theorem B830715 : Blo 830350 830715 := bstep (se 1 (by rfl) ⟨623036, by rfl⟩ : syracuseStep 830715 = 1246073) B1246073
theorem B830975 : Blo 830350 830975 := bstep (se 1 (by rfl) ⟨623231, by rfl⟩ : syracuseStep 830975 = 1246463) B1246463
theorem B831003 : Blo 830350 831003 := bstep (se 1 (by rfl) ⟨623252, by rfl⟩ : syracuseStep 831003 = 1246505) B1246505
theorem B1781671 : Blo 830350 1781671 := bstep (se 1 (by rfl) ⟨1336253, by rfl⟩ : syracuseStep 1781671 = 2672507) B2672507
theorem B2699227 : Blo 830350 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B2109523 : Blo 830350 2109523 := bstep (se 1 (by rfl) ⟨1582142, by rfl⟩ : syracuseStep 2109523 = 3164285) B3164285
theorem B2109665 : Blo 830350 2109665 := bstep (se 2 (by rfl) ⟨791124, by rfl⟩ : syracuseStep 2109665 = 1582249) B1582249
theorem B831903 : Blo 830350 831903 := bstep (se 1 (by rfl) ⟨623927, by rfl⟩ : syracuseStep 831903 = 1247855) B1247855
theorem B2109959 : Blo 830350 2109959 := bstep (se 1 (by rfl) ⟨1582469, by rfl⟩ : syracuseStep 2109959 = 3164939) B3164939
theorem B4207463 : Blo 830350 4207463 := bstep (se 1 (by rfl) ⟨3155597, by rfl⟩ : syracuseStep 4207463 = 6311195) B6311195
theorem B3158939 : Blo 830350 3158939 := bstep (se 1 (by rfl) ⟨2369204, by rfl⟩ : syracuseStep 3158939 = 4738409) B4738409
theorem B832735 : Blo 830350 832735 := bstep (se 1 (by rfl) ⟨624551, by rfl⟩ : syracuseStep 832735 = 1249103) B1249103
theorem B832795 : Blo 830350 832795 := bstep (se 1 (by rfl) ⟨624596, by rfl⟩ : syracuseStep 832795 = 1249193) B1249193
theorem B833055 : Blo 830350 833055 := bstep (se 1 (by rfl) ⟨624791, by rfl⟩ : syracuseStep 833055 = 1249583) B1249583
theorem B2111143 : Blo 830350 2111143 := bstep (se 1 (by rfl) ⟨1583357, by rfl⟩ : syracuseStep 2111143 = 3166715) B3166715
theorem B833255 : Blo 830350 833255 := bstep (se 1 (by rfl) ⟨624941, by rfl⟩ : syracuseStep 833255 = 1249883) B1249883
theorem B833383 : Blo 830350 833383 := bstep (se 1 (by rfl) ⟨625037, by rfl⟩ : syracuseStep 833383 = 1250075) B1250075
theorem B833503 : Blo 830350 833503 := bstep (se 1 (by rfl) ⟨625127, by rfl⟩ : syracuseStep 833503 = 1250255) B1250255
theorem B833567 : Blo 830350 833567 := bstep (se 1 (by rfl) ⟨625175, by rfl⟩ : syracuseStep 833567 = 1250351) B1250351
theorem B3422521 : Blo 830350 3422521 := bstep (se 2 (by rfl) ⟨1283445, by rfl⟩ : syracuseStep 3422521 = 2566891) B2566891
theorem B833863 : Blo 830350 833863 := bstep (se 1 (by rfl) ⟨625397, by rfl⟩ : syracuseStep 833863 = 1250795) B1250795
theorem B834159 : Blo 830350 834159 := bstep (se 1 (by rfl) ⟨625619, by rfl⟩ : syracuseStep 834159 = 1251239) B1251239
theorem B834175 : Blo 830350 834175 := bstep (se 1 (by rfl) ⟨625631, by rfl⟩ : syracuseStep 834175 = 1251263) B1251263
theorem B6307307 : Blo 830350 6307307 := bstep (se 1 (by rfl) ⟨4730480, by rfl⟩ : syracuseStep 6307307 = 9460961) B9460961
theorem B4210379 : Blo 830350 4210379 := bstep (se 1 (by rfl) ⟨3157784, by rfl⟩ : syracuseStep 4210379 = 6315569) B6315569
theorem B1687433 : Blo 830350 1687433 := bstep (se 2 (by rfl) ⟨632787, by rfl⟩ : syracuseStep 1687433 = 1265575) B1265575
theorem B4506785 : Blo 830350 4506785 := bstep (se 2 (by rfl) ⟨1690044, by rfl⟩ : syracuseStep 4506785 = 3380089) B3380089
theorem B2803355 : Blo 830350 2803355 := bstep (se 1 (by rfl) ⟨2102516, by rfl⟩ : syracuseStep 2803355 = 4205033) B4205033
theorem B2803895 : Blo 830350 2803895 := bstep (se 1 (by rfl) ⟨2102921, by rfl⟩ : syracuseStep 2803895 = 4205843) B4205843
theorem B1690159 : Blo 830350 1690159 := bstep (se 1 (by rfl) ⟨1267619, by rfl⟩ : syracuseStep 1690159 = 2535239) B2535239
theorem B3788075 : Blo 830350 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B937471 : Blo 830350 937471 := bstep (se 1 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 937471 = 1406207) B1406207
theorem B14241743 : Blo 830350 14241743 := bstep (se 1 (by rfl) ⟨10681307, by rfl⟩ : syracuseStep 14241743 = 21362615) B21362615
theorem B4739411 : Blo 830350 4739411 := bstep (se 1 (by rfl) ⟨3554558, by rfl⟩ : syracuseStep 4739411 = 7109117) B7109117
theorem B3428891 : Blo 830350 3428891 := bstep (se 1 (by rfl) ⟨2571668, by rfl⟩ : syracuseStep 3428891 = 5143337) B5143337
theorem B3167869 : Blo 830350 3167869 := bstep (se 3 (by rfl) ⟨593975, by rfl⟩ : syracuseStep 3167869 = 1187951) B1187951
theorem B10835723 : Blo 830350 10835723 := bstep (se 1 (by rfl) ⟨8126792, by rfl⟩ : syracuseStep 10835723 = 16253585) B16253585
theorem B20502395 : Blo 830350 20502395 := bstep (se 1 (by rfl) ⟨15376796, by rfl⟩ : syracuseStep 20502395 = 30753593) B30753593
theorem B13490509 : Blo 830350 13490509 := bstep (se 3 (by rfl) ⟨2529470, by rfl⟩ : syracuseStep 13490509 = 5058941) B5058941
theorem B2251145 : Blo 830350 2251145 := bstep (se 2 (by rfl) ⟨844179, by rfl⟩ : syracuseStep 2251145 = 1688359) B1688359
theorem B10803719 : Blo 830350 10803719 := bstep (se 1 (by rfl) ⟨8102789, by rfl⟩ : syracuseStep 10803719 = 16205579) B16205579
theorem B30366359 : Blo 830350 30366359 := bstep (se 1 (by rfl) ⟨22774769, by rfl⟩ : syracuseStep 30366359 = 45549539) B45549539
theorem B2809295 : Blo 830350 2809295 := bstep (se 1 (by rfl) ⟨2106971, by rfl⟩ : syracuseStep 2809295 = 4213943) B4213943
theorem B3006715 : Blo 830350 3006715 := bstep (se 1 (by rfl) ⟨2255036, by rfl⟩ : syracuseStep 3006715 = 4510073) B4510073
theorem B1401583 : Blo 830350 1401583 := bstep (se 1 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 1401583 = 2102375) B2102375
theorem B2811347 : Blo 830350 2811347 := bstep (se 1 (by rfl) ⟨2108510, by rfl⟩ : syracuseStep 2811347 = 4217021) B4217021
theorem B41674409 : Blo 830350 41674409 := bstep (se 2 (by rfl) ⟨15627903, by rfl⟩ : syracuseStep 41674409 = 31255807) B31255807
theorem B2811995 : Blo 830350 2811995 := bstep (se 1 (by rfl) ⟨2108996, by rfl⟩ : syracuseStep 2811995 = 4217993) B4217993
theorem B2844809 : Blo 830350 2844809 := bstep (se 2 (by rfl) ⟨1066803, by rfl⟩ : syracuseStep 2844809 = 2133607) B2133607
theorem B1501367 : Blo 830350 1501367 := bstep (se 1 (by rfl) ⟨1126025, by rfl⟩ : syracuseStep 1501367 = 2252051) B2252051
theorem B5073977 : Blo 830350 5073977 := bstep (se 2 (by rfl) ⟨1902741, by rfl⟩ : syracuseStep 5073977 = 3805483) B3805483
theorem B8547889 : Blo 830350 8547889 := bstep (se 2 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 8547889 = 6410917) B6410917
theorem B3600839 : Blo 830350 3600839 := bstep (se 1 (by rfl) ⟨2700629, by rfl⟩ : syracuseStep 3600839 = 5401259) B5401259
theorem B2814695 : Blo 830350 2814695 := bstep (se 1 (by rfl) ⟨2111021, by rfl⟩ : syracuseStep 2814695 = 4222043) B4222043
theorem B2814911 : Blo 830350 2814911 := bstep (se 1 (by rfl) ⟨2111183, by rfl⟩ : syracuseStep 2814911 = 4222367) B4222367
theorem B4323611 : Blo 830350 4323611 := bstep (se 1 (by rfl) ⟨3242708, by rfl⟩ : syracuseStep 4323611 = 6485417) B6485417
theorem B1407287 : Blo 830350 1407287 := bstep (se 1 (by rfl) ⟨1055465, by rfl⟩ : syracuseStep 1407287 = 2110931) B2110931
theorem B101515619 : Blo 830350 101515619 := bstep (se 1 (by rfl) ⟨76136714, by rfl⟩ : syracuseStep 101515619 = 152273429) B152273429
theorem B1245671 : Blo 830350 1245671 := bstep (se 1 (by rfl) ⟨934253, by rfl⟩ : syracuseStep 1245671 = 1868507) B1868507
theorem B1868777 : Blo 830350 1868777 := bstep (se 2 (by rfl) ⟨700791, by rfl⟩ : syracuseStep 1868777 = 1401583) B1401583
theorem B1868903 : Blo 830350 1868903 := bstep (se 1 (by rfl) ⟨1401677, by rfl⟩ : syracuseStep 1868903 = 2803355) B2803355
theorem B1246439 : Blo 830350 1246439 := bstep (se 1 (by rfl) ⟨934829, by rfl⟩ : syracuseStep 1246439 = 1869659) B1869659
theorem B1869263 : Blo 830350 1869263 := bstep (se 1 (by rfl) ⟨1401947, by rfl⟩ : syracuseStep 1869263 = 2803895) B2803895
theorem B1246847 : Blo 830350 1246847 := bstep (se 1 (by rfl) ⟨935135, by rfl⟩ : syracuseStep 1246847 = 1870271) B1870271
theorem B1247399 : Blo 830350 1247399 := bstep (se 1 (by rfl) ⟨935549, by rfl⟩ : syracuseStep 1247399 = 1871099) B1871099
theorem B2525383 : Blo 830350 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B13503617 : Blo 830350 13503617 := bstep (se 2 (by rfl) ⟨5063856, by rfl⟩ : syracuseStep 13503617 = 10127713) B10127713
theorem B1249007 : Blo 830350 1249007 := bstep (se 1 (by rfl) ⟨936755, by rfl⟩ : syracuseStep 1249007 = 1873511) B1873511
theorem B13668263 : Blo 830350 13668263 := bstep (se 1 (by rfl) ⟨10251197, by rfl⟩ : syracuseStep 13668263 = 20502395) B20502395
theorem B1052615 : Blo 830350 1052615 := bstep (se 1 (by rfl) ⟨789461, by rfl⟩ : syracuseStep 1052615 = 1578923) B1578923
theorem B1249439 : Blo 830350 1249439 := bstep (se 1 (by rfl) ⟨937079, by rfl⟩ : syracuseStep 1249439 = 1874159) B1874159
theorem B1249535 : Blo 830350 1249535 := bstep (se 1 (by rfl) ⟨937151, by rfl⟩ : syracuseStep 1249535 = 1874303) B1874303
theorem B1249607 : Blo 830350 1249607 := bstep (se 1 (by rfl) ⟨937205, by rfl⟩ : syracuseStep 1249607 = 1874411) B1874411
theorem B1249961 : Blo 830350 1249961 := bstep (se 2 (by rfl) ⟨468735, by rfl⟩ : syracuseStep 1249961 = 937471) B937471
theorem B1872863 : Blo 830350 1872863 := bstep (se 1 (by rfl) ⟨1404647, by rfl⟩ : syracuseStep 1872863 = 2809295) B2809295
theorem B53941261 : Blo 830350 53941261 := bstep (se 3 (by rfl) ⟨10113986, by rfl⟩ : syracuseStep 53941261 = 20227973) B20227973
theorem B8001449 : Blo 830350 8001449 := bstep (se 2 (by rfl) ⟨3000543, by rfl⟩ : syracuseStep 8001449 = 6001087) B6001087
theorem B1251455 : Blo 830350 1251455 := bstep (se 1 (by rfl) ⟨938591, by rfl⟩ : syracuseStep 1251455 = 1877183) B1877183
theorem B1186015 : Blo 830350 1186015 := bstep (se 1 (by rfl) ⟨889511, by rfl⟩ : syracuseStep 1186015 = 1779023) B1779023
theorem B1874231 : Blo 830350 1874231 := bstep (se 1 (by rfl) ⟨1405673, by rfl⟩ : syracuseStep 1874231 = 2811347) B2811347
theorem B28809917 : Blo 830350 28809917 := bstep (se 3 (by rfl) ⟨5401859, by rfl⟩ : syracuseStep 28809917 = 10803719) B10803719
theorem B1874663 : Blo 830350 1874663 := bstep (se 1 (by rfl) ⟨1405997, by rfl⟩ : syracuseStep 1874663 = 2811995) B2811995
theorem B3382651 : Blo 830350 3382651 := bstep (se 1 (by rfl) ⟨2536988, by rfl⟩ : syracuseStep 3382651 = 5073977) B5073977
theorem B1777135 : Blo 830350 1777135 := bstep (se 1 (by rfl) ⟨1332851, by rfl⟩ : syracuseStep 1777135 = 2665703) B2665703
theorem B65674745 : Blo 830350 65674745 := bstep (se 2 (by rfl) ⟨24628029, by rfl⟩ : syracuseStep 65674745 = 49256059) B49256059
theorem B2400559 : Blo 830350 2400559 := bstep (se 1 (by rfl) ⟨1800419, by rfl⟩ : syracuseStep 2400559 = 3600839) B3600839
theorem B4563361 : Blo 830350 4563361 := bstep (se 2 (by rfl) ⟨1711260, by rfl⟩ : syracuseStep 4563361 = 3422521) B3422521
theorem B1876463 : Blo 830350 1876463 := bstep (se 1 (by rfl) ⟨1407347, by rfl⟩ : syracuseStep 1876463 = 2814695) B2814695
theorem B2105959 : Blo 830350 2105959 := bstep (se 1 (by rfl) ⟨1579469, by rfl⟩ : syracuseStep 2105959 = 3158939) B3158939
theorem B1876607 : Blo 830350 1876607 := bstep (se 1 (by rfl) ⟨1407455, by rfl⟩ : syracuseStep 1876607 = 2814911) B2814911
theorem B4204871 : Blo 830350 4204871 := bstep (se 1 (by rfl) ⟨3153653, by rfl⟩ : syracuseStep 4204871 = 6307307) B6307307
theorem B4499821 : Blo 830350 4499821 := bstep (se 3 (by rfl) ⟨843716, by rfl⟩ : syracuseStep 4499821 = 1687433) B1687433
theorem B14395877 : Blo 830350 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B4008953 : Blo 830350 4008953 := bstep (se 2 (by rfl) ⟨1503357, by rfl⟩ : syracuseStep 4008953 = 3006715) B3006715
theorem B831519 : Blo 830350 831519 := bstep (se 1 (by rfl) ⟨623639, by rfl⟩ : syracuseStep 831519 = 1247279) B1247279
theorem B832603 : Blo 830350 832603 := bstep (se 1 (by rfl) ⟨624452, by rfl⟩ : syracuseStep 832603 = 1248905) B1248905
theorem B5682311 : Blo 830350 5682311 := bstep (se 1 (by rfl) ⟨4261733, by rfl⟩ : syracuseStep 5682311 = 8523467) B8523467
theorem B832703 : Blo 830350 832703 := bstep (se 1 (by rfl) ⟨624527, by rfl⟩ : syracuseStep 832703 = 1249055) B1249055
theorem B3159607 : Blo 830350 3159607 := bstep (se 1 (by rfl) ⟨2369705, by rfl⟩ : syracuseStep 3159607 = 4739411) B4739411
theorem B833215 : Blo 830350 833215 := bstep (se 1 (by rfl) ⟨624911, by rfl⟩ : syracuseStep 833215 = 1249823) B1249823
theorem B833279 : Blo 830350 833279 := bstep (se 1 (by rfl) ⟨624959, by rfl⟩ : syracuseStep 833279 = 1249919) B1249919
theorem B834015 : Blo 830350 834015 := bstep (se 1 (by rfl) ⟨625511, by rfl⟩ : syracuseStep 834015 = 1251023) B1251023
theorem B7223815 : Blo 830350 7223815 := bstep (se 1 (by rfl) ⟨5417861, by rfl⟩ : syracuseStep 7223815 = 10835723) B10835723
theorem B40417811 : Blo 830350 40417811 := bstep (se 1 (by rfl) ⟨30313358, by rfl⟩ : syracuseStep 40417811 = 60626717) B60626717
theorem B10664905 : Blo 830350 10664905 := bstep (se 2 (by rfl) ⟨3999339, by rfl⟩ : syracuseStep 10664905 = 7998679) B7998679
theorem B2375561 : Blo 830350 2375561 := bstep (se 2 (by rfl) ⟨890835, by rfl⟩ : syracuseStep 2375561 = 1781671) B1781671
theorem B2804975 : Blo 830350 2804975 := bstep (se 1 (by rfl) ⟨2103731, by rfl⟩ : syracuseStep 2804975 = 4207463) B4207463
theorem B2805245 : Blo 830350 2805245 := bstep (se 3 (by rfl) ⟨525983, by rfl⟩ : syracuseStep 2805245 = 1051967) B1051967
theorem B938191 : Blo 830350 938191 := bstep (se 1 (by rfl) ⟨703643, by rfl⟩ : syracuseStep 938191 = 1407287) B1407287
theorem B2806919 : Blo 830350 2806919 := bstep (se 1 (by rfl) ⟨2105189, by rfl⟩ : syracuseStep 2806919 = 4210379) B4210379
theorem B3167855 : Blo 830350 3167855 := bstep (se 1 (by rfl) ⟨2375891, by rfl⟩ : syracuseStep 3167855 = 4751783) B4751783
theorem B2250667 : Blo 830350 2250667 := bstep (se 1 (by rfl) ⟨1688000, by rfl⟩ : syracuseStep 2250667 = 3376001) B3376001
theorem B3004523 : Blo 830350 3004523 := bstep (se 1 (by rfl) ⟨2253392, by rfl⟩ : syracuseStep 3004523 = 4506785) B4506785
theorem B32004557 : Blo 830350 32004557 := bstep (se 3 (by rfl) ⟨6000854, by rfl⟩ : syracuseStep 32004557 = 12001709) B12001709
theorem B1268507 : Blo 830350 1268507 := bstep (se 1 (by rfl) ⟨951380, by rfl⟩ : syracuseStep 1268507 = 1902761) B1902761
theorem B2808809 : Blo 830350 2808809 := bstep (se 2 (by rfl) ⟨1053303, by rfl⟩ : syracuseStep 2808809 = 2106607) B2106607
theorem B16014581 : Blo 830350 16014581 := bstep (se 5 (by rfl) ⟨750683, by rfl⟩ : syracuseStep 16014581 = 1501367) B1501367
theorem B9494495 : Blo 830350 9494495 := bstep (se 1 (by rfl) ⟨7120871, by rfl⟩ : syracuseStep 9494495 = 14241743) B14241743
theorem B2810105 : Blo 830350 2810105 := bstep (se 2 (by rfl) ⟨1053789, by rfl⟩ : syracuseStep 2810105 = 2107579) B2107579
theorem B2285927 : Blo 830350 2285927 := bstep (se 1 (by rfl) ⟨1714445, by rfl⟩ : syracuseStep 2285927 = 3428891) B3428891
theorem B2253545 : Blo 830350 2253545 := bstep (se 2 (by rfl) ⟨845079, by rfl⟩ : syracuseStep 2253545 = 1690159) B1690159
theorem B1401691 : Blo 830350 1401691 := bstep (se 1 (by rfl) ⟨1051268, by rfl⟩ : syracuseStep 1401691 = 2102537) B2102537
theorem B1401887 : Blo 830350 1401887 := bstep (se 1 (by rfl) ⟨1051415, by rfl⟩ : syracuseStep 1401887 = 2102831) B2102831
theorem B1402015 : Blo 830350 1402015 := bstep (se 1 (by rfl) ⟨1051511, by rfl⟩ : syracuseStep 1402015 = 2103023) B2103023
theorem B2254063 : Blo 830350 2254063 := bstep (se 1 (by rfl) ⟨1690547, by rfl⟩ : syracuseStep 2254063 = 3381095) B3381095
theorem B1500763 : Blo 830350 1500763 := bstep (se 1 (by rfl) ⟨1125572, by rfl⟩ : syracuseStep 1500763 = 2251145) B2251145
theorem B20244239 : Blo 830350 20244239 := bstep (se 1 (by rfl) ⟨15183179, by rfl⟩ : syracuseStep 20244239 = 30366359) B30366359
theorem B1402751 : Blo 830350 1402751 := bstep (se 1 (by rfl) ⟨1052063, by rfl⟩ : syracuseStep 1402751 = 2104127) B2104127
theorem B11397185 : Blo 830350 11397185 := bstep (se 2 (by rfl) ⟨4273944, by rfl⟩ : syracuseStep 11397185 = 8547889) B8547889
theorem B1402987 : Blo 830350 1402987 := bstep (se 1 (by rfl) ⟨1052240, by rfl⟩ : syracuseStep 1402987 = 2104481) B2104481
theorem B1927351 : Blo 830350 1927351 := bstep (se 1 (by rfl) ⟨1445513, by rfl⟩ : syracuseStep 1927351 = 2891027) B2891027
theorem B1403291 : Blo 830350 1403291 := bstep (se 1 (by rfl) ⟨1052468, by rfl⟩ : syracuseStep 1403291 = 2104937) B2104937
theorem B2812697 : Blo 830350 2812697 := bstep (se 2 (by rfl) ⟨1054761, by rfl⟩ : syracuseStep 2812697 = 2109523) B2109523
theorem B6318971 : Blo 830350 6318971 := bstep (se 1 (by rfl) ⟨4739228, by rfl⟩ : syracuseStep 6318971 = 9478457) B9478457
theorem B1601051 : Blo 830350 1601051 := bstep (se 1 (by rfl) ⟨1200788, by rfl⟩ : syracuseStep 1601051 = 2401577) B2401577
theorem B1404553 : Blo 830350 1404553 := bstep (se 2 (by rfl) ⟨526707, by rfl⟩ : syracuseStep 1404553 = 1053415) B1053415
theorem B27782939 : Blo 830350 27782939 := bstep (se 1 (by rfl) ⟨20837204, by rfl⟩ : syracuseStep 27782939 = 41674409) B41674409
theorem B1404911 : Blo 830350 1404911 := bstep (se 1 (by rfl) ⟨1053683, by rfl⟩ : syracuseStep 1404911 = 2107367) B2107367
theorem B1896539 : Blo 830350 1896539 := bstep (se 1 (by rfl) ⟨1422404, by rfl⟩ : syracuseStep 1896539 = 2844809) B2844809
theorem B4223825 : Blo 830350 4223825 := bstep (se 2 (by rfl) ⟨1583934, by rfl⟩ : syracuseStep 4223825 = 3167869) B3167869
theorem B2814857 : Blo 830350 2814857 := bstep (se 2 (by rfl) ⟨1055571, by rfl⟩ : syracuseStep 2814857 = 2111143) B2111143
theorem B5698973 : Blo 830350 5698973 := bstep (se 3 (by rfl) ⟨1068557, by rfl⟩ : syracuseStep 5698973 = 2137115) B2137115
theorem B1406443 : Blo 830350 1406443 := bstep (se 1 (by rfl) ⟨1054832, by rfl⟩ : syracuseStep 1406443 = 2109665) B2109665
theorem B1406639 : Blo 830350 1406639 := bstep (se 1 (by rfl) ⟨1054979, by rfl⟩ : syracuseStep 1406639 = 2109959) B2109959
theorem B17987345 : Blo 830350 17987345 := bstep (se 2 (by rfl) ⟨6745254, by rfl⟩ : syracuseStep 17987345 = 13490509) B13490509
theorem B2882407 : Blo 830350 2882407 := bstep (se 1 (by rfl) ⟨2161805, by rfl⟩ : syracuseStep 2882407 = 4323611) B4323611
theorem B1245851 : Blo 830350 1245851 := bstep (se 1 (by rfl) ⟨934388, by rfl⟩ : syracuseStep 1245851 = 1868777) B1868777
theorem B1245935 : Blo 830350 1245935 := bstep (se 1 (by rfl) ⟨934451, by rfl⟩ : syracuseStep 1245935 = 1868903) B1868903
theorem B1246175 : Blo 830350 1246175 := bstep (se 1 (by rfl) ⟨934631, by rfl⟩ : syracuseStep 1246175 = 1869263) B1869263
theorem B1868921 : Blo 830350 1868921 := bstep (se 2 (by rfl) ⟨700845, by rfl⟩ : syracuseStep 1868921 = 1401691) B1401691
theorem B1869353 : Blo 830350 1869353 := bstep (se 2 (by rfl) ⟨701007, by rfl⟩ : syracuseStep 1869353 = 1402015) B1402015
theorem B2001017 : Blo 830350 2001017 := bstep (se 2 (by rfl) ⟨750381, by rfl⟩ : syracuseStep 2001017 = 1500763) B1500763
theorem B1869983 : Blo 830350 1869983 := bstep (se 1 (by rfl) ⟨1402487, by rfl⟩ : syracuseStep 1869983 = 2804975) B2804975
theorem B1870163 : Blo 830350 1870163 := bstep (se 1 (by rfl) ⟨1402622, by rfl⟩ : syracuseStep 1870163 = 2805245) B2805245
theorem B9112175 : Blo 830350 9112175 := bstep (se 1 (by rfl) ⟨6834131, by rfl⟩ : syracuseStep 9112175 = 13668263) B13668263
theorem B1870649 : Blo 830350 1870649 := bstep (se 2 (by rfl) ⟨701493, by rfl⟩ : syracuseStep 1870649 = 1402987) B1402987
theorem B5999761 : Blo 830350 5999761 := bstep (se 2 (by rfl) ⟨2249910, by rfl⟩ : syracuseStep 5999761 = 4499821) B4499821
theorem B1248575 : Blo 830350 1248575 := bstep (se 1 (by rfl) ⟨936431, by rfl⟩ : syracuseStep 1248575 = 1872863) B1872863
theorem B1871279 : Blo 830350 1871279 := bstep (se 1 (by rfl) ⟨1403459, by rfl⟩ : syracuseStep 1871279 = 2806919) B2806919
theorem B2003015 : Blo 830350 2003015 := bstep (se 1 (by rfl) ⟨1502261, by rfl⟩ : syracuseStep 2003015 = 3004523) B3004523
theorem B1249487 : Blo 830350 1249487 := bstep (se 1 (by rfl) ⟨937115, by rfl⟩ : syracuseStep 1249487 = 1874231) B1874231
theorem B21336371 : Blo 830350 21336371 := bstep (se 1 (by rfl) ⟨16002278, by rfl⟩ : syracuseStep 21336371 = 32004557) B32004557
theorem B19206611 : Blo 830350 19206611 := bstep (se 1 (by rfl) ⟨14404958, by rfl⟩ : syracuseStep 19206611 = 28809917) B28809917
theorem B1249775 : Blo 830350 1249775 := bstep (se 1 (by rfl) ⟨937331, by rfl⟩ : syracuseStep 1249775 = 1874663) B1874663
theorem B1872539 : Blo 830350 1872539 := bstep (se 1 (by rfl) ⟨1404404, by rfl⟩ : syracuseStep 1872539 = 2808809) B2808809
theorem B1872737 : Blo 830350 1872737 := bstep (se 2 (by rfl) ⟨702276, by rfl⟩ : syracuseStep 1872737 = 1404553) B1404553
theorem B43783163 : Blo 830350 43783163 := bstep (se 1 (by rfl) ⟨32837372, by rfl⟩ : syracuseStep 43783163 = 65674745) B65674745
theorem B6329663 : Blo 830350 6329663 := bstep (se 1 (by rfl) ⟨4747247, by rfl⟩ : syracuseStep 6329663 = 9494495) B9494495
theorem B1873403 : Blo 830350 1873403 := bstep (se 1 (by rfl) ⟨1405052, by rfl⟩ : syracuseStep 1873403 = 2810105) B2810105
theorem B1250921 : Blo 830350 1250921 := bstep (se 2 (by rfl) ⟨469095, by rfl⟩ : syracuseStep 1250921 = 938191) B938191
theorem B1250975 : Blo 830350 1250975 := bstep (se 1 (by rfl) ⟨938231, by rfl⟩ : syracuseStep 1250975 = 1876463) B1876463
theorem B1251071 : Blo 830350 1251071 := bstep (se 1 (by rfl) ⟨938303, by rfl⟩ : syracuseStep 1251071 = 1876607) B1876607
theorem B1875131 : Blo 830350 1875131 := bstep (se 1 (by rfl) ⟨1406348, by rfl⟩ : syracuseStep 1875131 = 2812697) B2812697
theorem B1875257 : Blo 830350 1875257 := bstep (se 2 (by rfl) ⟨703221, by rfl⟩ : syracuseStep 1875257 = 1406443) B1406443
theorem B18521959 : Blo 830350 18521959 := bstep (se 1 (by rfl) ⟨13891469, by rfl⟩ : syracuseStep 18521959 = 27782939) B27782939
theorem B1581353 : Blo 830350 1581353 := bstep (se 2 (by rfl) ⟨593007, by rfl⟩ : syracuseStep 1581353 = 1186015) B1186015
theorem B1876571 : Blo 830350 1876571 := bstep (se 1 (by rfl) ⟨1407428, by rfl⟩ : syracuseStep 1876571 = 2814857) B2814857
theorem B3843209 : Blo 830350 3843209 := bstep (se 2 (by rfl) ⟨1441203, by rfl⟩ : syracuseStep 3843209 = 2882407) B2882407
theorem B4269469 : Blo 830350 4269469 := bstep (se 3 (by rfl) ⟨800525, by rfl⟩ : syracuseStep 4269469 = 1601051) B1601051
theorem B26945207 : Blo 830350 26945207 := bstep (se 1 (by rfl) ⟨20208905, by rfl⟩ : syracuseStep 26945207 = 40417811) B40417811
theorem B2369513 : Blo 830350 2369513 := bstep (se 2 (by rfl) ⟨888567, by rfl⟩ : syracuseStep 2369513 = 1777135) B1777135
theorem B1583707 : Blo 830350 1583707 := bstep (se 1 (by rfl) ⟨1187780, by rfl⟩ : syracuseStep 1583707 = 2375561) B2375561
theorem B67677079 : Blo 830350 67677079 := bstep (se 1 (by rfl) ⟨50757809, by rfl⟩ : syracuseStep 67677079 = 101515619) B101515619
theorem B830447 : Blo 830350 830447 := bstep (se 1 (by rfl) ⟨622835, by rfl⟩ : syracuseStep 830447 = 1245671) B1245671
theorem B830959 : Blo 830350 830959 := bstep (se 1 (by rfl) ⟨623219, by rfl⟩ : syracuseStep 830959 = 1246439) B1246439
theorem B20229749 : Blo 830350 20229749 := bstep (se 5 (by rfl) ⟨948269, by rfl⟩ : syracuseStep 20229749 = 1896539) B1896539
theorem B831231 : Blo 830350 831231 := bstep (se 1 (by rfl) ⟨623423, by rfl⟩ : syracuseStep 831231 = 1246847) B1246847
theorem B831599 : Blo 830350 831599 := bstep (se 1 (by rfl) ⟨623699, by rfl⟩ : syracuseStep 831599 = 1247399) B1247399
theorem B832671 : Blo 830350 832671 := bstep (se 1 (by rfl) ⟨624503, by rfl⟩ : syracuseStep 832671 = 1249007) B1249007
theorem B832959 : Blo 830350 832959 := bstep (se 1 (by rfl) ⟨624719, by rfl⟩ : syracuseStep 832959 = 1249439) B1249439
theorem B833023 : Blo 830350 833023 := bstep (se 1 (by rfl) ⟨624767, by rfl⟩ : syracuseStep 833023 = 1249535) B1249535
theorem B833071 : Blo 830350 833071 := bstep (se 1 (by rfl) ⟨624803, by rfl⟩ : syracuseStep 833071 = 1249607) B1249607
theorem B2569801 : Blo 830350 2569801 := bstep (se 2 (by rfl) ⟨963675, by rfl⟩ : syracuseStep 2569801 = 1927351) B1927351
theorem B833307 : Blo 830350 833307 := bstep (se 1 (by rfl) ⟨624980, by rfl⟩ : syracuseStep 833307 = 1249961) B1249961
theorem B2111903 : Blo 830350 2111903 := bstep (se 1 (by rfl) ⟨1583927, by rfl⟩ : syracuseStep 2111903 = 3167855) B3167855
theorem B834303 : Blo 830350 834303 := bstep (se 1 (by rfl) ⟨625727, by rfl⟩ : syracuseStep 834303 = 1251455) B1251455
theorem B1523951 : Blo 830350 1523951 := bstep (se 1 (by rfl) ⟨1142963, by rfl⟩ : syracuseStep 1523951 = 2285927) B2285927
theorem B934591 : Blo 830350 934591 := bstep (se 1 (by rfl) ⟨700943, by rfl⟩ : syracuseStep 934591 = 1401887) B1401887
theorem B935167 : Blo 830350 935167 := bstep (se 1 (by rfl) ⟨701375, by rfl⟩ : syracuseStep 935167 = 1402751) B1402751
theorem B2803247 : Blo 830350 2803247 := bstep (se 1 (by rfl) ⟨2102435, by rfl⟩ : syracuseStep 2803247 = 4204871) B4204871
theorem B935527 : Blo 830350 935527 := bstep (se 1 (by rfl) ⟨701645, by rfl⟩ : syracuseStep 935527 = 1403291) B1403291
theorem B4212647 : Blo 830350 4212647 := bstep (se 1 (by rfl) ⟨3159485, by rfl⟩ : syracuseStep 4212647 = 6318971) B6318971
theorem B18040805 : Blo 830350 18040805 := bstep (se 4 (by rfl) ⟨1691325, by rfl⟩ : syracuseStep 18040805 = 3382651) B3382651
theorem B2672635 : Blo 830350 2672635 := bstep (se 1 (by rfl) ⟨2004476, by rfl⟩ : syracuseStep 2672635 = 4008953) B4008953
theorem B4212809 : Blo 830350 4212809 := bstep (se 2 (by rfl) ⟨1579803, by rfl⟩ : syracuseStep 4212809 = 3159607) B3159607
theorem B3000889 : Blo 830350 3000889 := bstep (se 2 (by rfl) ⟨1125333, by rfl⟩ : syracuseStep 3000889 = 2250667) B2250667
theorem B936607 : Blo 830350 936607 := bstep (se 1 (by rfl) ⟨702455, by rfl⟩ : syracuseStep 936607 = 1404911) B1404911
theorem B3788207 : Blo 830350 3788207 := bstep (se 1 (by rfl) ⟨2841155, by rfl⟩ : syracuseStep 3788207 = 5682311) B5682311
theorem B937759 : Blo 830350 937759 := bstep (se 1 (by rfl) ⟨703319, by rfl⟩ : syracuseStep 937759 = 1406639) B1406639
theorem B2806973 : Blo 830350 2806973 := bstep (se 3 (by rfl) ⟨526307, by rfl⟩ : syracuseStep 2806973 = 1052615) B1052615
theorem B2807945 : Blo 830350 2807945 := bstep (se 2 (by rfl) ⟨1052979, by rfl⟩ : syracuseStep 2807945 = 2105959) B2105959
theorem B12802981 : Blo 830350 12802981 := bstep (se 4 (by rfl) ⟨1200279, by rfl⟩ : syracuseStep 12802981 = 2400559) B2400559
theorem B3005417 : Blo 830350 3005417 := bstep (se 2 (by rfl) ⟨1127031, by rfl⟩ : syracuseStep 3005417 = 2254063) B2254063
theorem B9002411 : Blo 830350 9002411 := bstep (se 1 (by rfl) ⟨6751808, by rfl⟩ : syracuseStep 9002411 = 13503617) B13503617
theorem B24337925 : Blo 830350 24337925 := bstep (se 4 (by rfl) ⟨2281680, by rfl⟩ : syracuseStep 24337925 = 4563361) B4563361
theorem B3367177 : Blo 830350 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B5334299 : Blo 830350 5334299 := bstep (se 1 (by rfl) ⟨4000724, by rfl⟩ : syracuseStep 5334299 = 8001449) B8001449
theorem B845671 : Blo 830350 845671 := bstep (se 1 (by rfl) ⟨634253, by rfl⟩ : syracuseStep 845671 = 1268507) B1268507
theorem B10676387 : Blo 830350 10676387 := bstep (se 1 (by rfl) ⟨8007290, by rfl⟩ : syracuseStep 10676387 = 16014581) B16014581
theorem B1502363 : Blo 830350 1502363 := bstep (se 1 (by rfl) ⟨1126772, by rfl⟩ : syracuseStep 1502363 = 2253545) B2253545
theorem B13496159 : Blo 830350 13496159 := bstep (se 1 (by rfl) ⟨10122119, by rfl⟩ : syracuseStep 13496159 = 20244239) B20244239
theorem B71921681 : Blo 830350 71921681 := bstep (se 2 (by rfl) ⟨26970630, by rfl⟩ : syracuseStep 71921681 = 53941261) B53941261
theorem B7598123 : Blo 830350 7598123 := bstep (se 1 (by rfl) ⟨5698592, by rfl⟩ : syracuseStep 7598123 = 11397185) B11397185
theorem B9597251 : Blo 830350 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B2815883 : Blo 830350 2815883 := bstep (se 1 (by rfl) ⟨2111912, by rfl⟩ : syracuseStep 2815883 = 4223825) B4223825
theorem B9631753 : Blo 830350 9631753 := bstep (se 2 (by rfl) ⟨3611907, by rfl⟩ : syracuseStep 9631753 = 7223815) B7223815
theorem B3799315 : Blo 830350 3799315 := bstep (se 1 (by rfl) ⟨2849486, by rfl⟩ : syracuseStep 3799315 = 5698973) B5698973
theorem B11991563 : Blo 830350 11991563 := bstep (se 1 (by rfl) ⟨8993672, by rfl⟩ : syracuseStep 11991563 = 17987345) B17987345
theorem B14219873 : Blo 830350 14219873 := bstep (se 2 (by rfl) ⟨5332452, by rfl⟩ : syracuseStep 14219873 = 10664905) B10664905
theorem B1015967 : Blo 830350 1015967 := bstep (se 1 (by rfl) ⟨761975, by rfl⟩ : syracuseStep 1015967 = 1523951) B1523951
theorem B5341373 : Blo 830350 5341373 := bstep (se 3 (by rfl) ⟨1001507, by rfl⟩ : syracuseStep 5341373 = 2003015) B2003015
theorem B1245947 : Blo 830350 1245947 := bstep (se 1 (by rfl) ⟨934460, by rfl⟩ : syracuseStep 1245947 = 1868921) B1868921
theorem B25592669 : Blo 830350 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B1246121 : Blo 830350 1246121 := bstep (se 2 (by rfl) ⟨467295, by rfl⟩ : syracuseStep 1246121 = 934591) B934591
theorem B1246235 : Blo 830350 1246235 := bstep (se 1 (by rfl) ⟨934676, by rfl⟩ : syracuseStep 1246235 = 1869353) B1869353
theorem B1868831 : Blo 830350 1868831 := bstep (se 1 (by rfl) ⟨1401623, by rfl⟩ : syracuseStep 1868831 = 2803247) B2803247
theorem B12027203 : Blo 830350 12027203 := bstep (se 1 (by rfl) ⟨9020402, by rfl⟩ : syracuseStep 12027203 = 18040805) B18040805
theorem B17958277 : Blo 830350 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B1246655 : Blo 830350 1246655 := bstep (se 1 (by rfl) ⟨934991, by rfl⟩ : syracuseStep 1246655 = 1869983) B1869983
theorem B1246775 : Blo 830350 1246775 := bstep (se 1 (by rfl) ⟨935081, by rfl⟩ : syracuseStep 1246775 = 1870163) B1870163
theorem B1246889 : Blo 830350 1246889 := bstep (se 2 (by rfl) ⟨467583, by rfl⟩ : syracuseStep 1246889 = 935167) B935167
theorem B1247099 : Blo 830350 1247099 := bstep (se 1 (by rfl) ⟨935324, by rfl⟩ : syracuseStep 1247099 = 1870649) B1870649
theorem B1247369 : Blo 830350 1247369 := bstep (se 2 (by rfl) ⟨467763, by rfl⟩ : syracuseStep 1247369 = 935527) B935527
theorem B2525471 : Blo 830350 2525471 := bstep (se 1 (by rfl) ⟨1894103, by rfl⟩ : syracuseStep 2525471 = 3788207) B3788207
theorem B1247519 : Blo 830350 1247519 := bstep (se 1 (by rfl) ⟨935639, by rfl⟩ : syracuseStep 1247519 = 1871279) B1871279
theorem B14224247 : Blo 830350 14224247 := bstep (se 1 (by rfl) ⟨10668185, by rfl⟩ : syracuseStep 14224247 = 21336371) B21336371
theorem B1248359 : Blo 830350 1248359 := bstep (se 1 (by rfl) ⟨936269, by rfl⟩ : syracuseStep 1248359 = 1872539) B1872539
theorem B1248491 : Blo 830350 1248491 := bstep (se 1 (by rfl) ⟨936368, by rfl⟩ : syracuseStep 1248491 = 1872737) B1872737
theorem B4001185 : Blo 830350 4001185 := bstep (se 2 (by rfl) ⟨1500444, by rfl⟩ : syracuseStep 4001185 = 3000889) B3000889
theorem B1871315 : Blo 830350 1871315 := bstep (se 1 (by rfl) ⟨1403486, by rfl⟩ : syracuseStep 1871315 = 2806973) B2806973
theorem B1248809 : Blo 830350 1248809 := bstep (se 2 (by rfl) ⟨468303, by rfl⟩ : syracuseStep 1248809 = 936607) B936607
theorem B1248935 : Blo 830350 1248935 := bstep (se 1 (by rfl) ⟨936701, by rfl⟩ : syracuseStep 1248935 = 1873403) B1873403
theorem B1871963 : Blo 830350 1871963 := bstep (se 1 (by rfl) ⟨1403972, by rfl⟩ : syracuseStep 1871963 = 2807945) B2807945
theorem B7999681 : Blo 830350 7999681 := bstep (se 2 (by rfl) ⟨2999880, by rfl⟩ : syracuseStep 7999681 = 5999761) B5999761
theorem B2003611 : Blo 830350 2003611 := bstep (se 1 (by rfl) ⟨1502708, by rfl⟩ : syracuseStep 2003611 = 3005417) B3005417
theorem B1250087 : Blo 830350 1250087 := bstep (se 1 (by rfl) ⟨937565, by rfl⟩ : syracuseStep 1250087 = 1875131) B1875131
theorem B1250171 : Blo 830350 1250171 := bstep (se 1 (by rfl) ⟨937628, by rfl⟩ : syracuseStep 1250171 = 1875257) B1875257
theorem B6001607 : Blo 830350 6001607 := bstep (se 1 (by rfl) ⟨4501205, by rfl⟩ : syracuseStep 6001607 = 9002411) B9002411
theorem B16225283 : Blo 830350 16225283 := bstep (se 1 (by rfl) ⟨12168962, by rfl⟩ : syracuseStep 16225283 = 24337925) B24337925
theorem B1250345 : Blo 830350 1250345 := bstep (se 2 (by rfl) ⟨468879, by rfl⟩ : syracuseStep 1250345 = 937759) B937759
theorem B1054235 : Blo 830350 1054235 := bstep (se 1 (by rfl) ⟨790676, by rfl⟩ : syracuseStep 1054235 = 1581353) B1581353
theorem B1251047 : Blo 830350 1251047 := bstep (se 1 (by rfl) ⟨938285, by rfl⟩ : syracuseStep 1251047 = 1876571) B1876571
theorem B2562139 : Blo 830350 2562139 := bstep (se 1 (by rfl) ⟨1921604, by rfl⟩ : syracuseStep 2562139 = 3843209) B3843209
theorem B17963471 : Blo 830350 17963471 := bstep (se 1 (by rfl) ⟨13472603, by rfl⟩ : syracuseStep 17963471 = 26945207) B26945207
theorem B1579675 : Blo 830350 1579675 := bstep (se 1 (by rfl) ⟨1184756, by rfl⟩ : syracuseStep 1579675 = 2369513) B2369513
theorem B7117591 : Blo 830350 7117591 := bstep (se 1 (by rfl) ⟨5338193, by rfl⟩ : syracuseStep 7117591 = 10676387) B10676387
theorem B47947787 : Blo 830350 47947787 := bstep (se 1 (by rfl) ⟨35960840, by rfl⟩ : syracuseStep 47947787 = 71921681) B71921681
theorem B1877255 : Blo 830350 1877255 := bstep (se 1 (by rfl) ⟨1407941, by rfl⟩ : syracuseStep 1877255 = 2815883) B2815883
theorem B9479915 : Blo 830350 9479915 := bstep (se 1 (by rfl) ⟨7109936, by rfl⟩ : syracuseStep 9479915 = 14219873) B14219873
theorem B830567 : Blo 830350 830567 := bstep (se 1 (by rfl) ⟨622925, by rfl⟩ : syracuseStep 830567 = 1245851) B1245851
theorem B830623 : Blo 830350 830623 := bstep (se 1 (by rfl) ⟨622967, by rfl⟩ : syracuseStep 830623 = 1245935) B1245935
theorem B830783 : Blo 830350 830783 := bstep (se 1 (by rfl) ⟨623087, by rfl⟩ : syracuseStep 830783 = 1246175) B1246175
theorem B6074783 : Blo 830350 6074783 := bstep (se 1 (by rfl) ⟨4556087, by rfl⟩ : syracuseStep 6074783 = 9112175) B9112175
theorem B832383 : Blo 830350 832383 := bstep (se 1 (by rfl) ⟨624287, by rfl⟩ : syracuseStep 832383 = 1248575) B1248575
theorem B1127561 : Blo 830350 1127561 := bstep (se 2 (by rfl) ⟨422835, by rfl⟩ : syracuseStep 1127561 = 845671) B845671
theorem B832991 : Blo 830350 832991 := bstep (se 1 (by rfl) ⟨624743, by rfl⟩ : syracuseStep 832991 = 1249487) B1249487
theorem B833183 : Blo 830350 833183 := bstep (se 1 (by rfl) ⟨624887, by rfl⟩ : syracuseStep 833183 = 1249775) B1249775
theorem B2111609 : Blo 830350 2111609 := bstep (se 2 (by rfl) ⟨791853, by rfl⟩ : syracuseStep 2111609 = 1583707) B1583707
theorem B833947 : Blo 830350 833947 := bstep (se 1 (by rfl) ⟨625460, by rfl⟩ : syracuseStep 833947 = 1250921) B1250921
theorem B833983 : Blo 830350 833983 := bstep (se 1 (by rfl) ⟨625487, by rfl⟩ : syracuseStep 833983 = 1250975) B1250975
theorem B834047 : Blo 830350 834047 := bstep (se 1 (by rfl) ⟨625535, by rfl⟩ : syracuseStep 834047 = 1251071) B1251071
theorem B3556199 : Blo 830350 3556199 := bstep (se 1 (by rfl) ⟨2667149, by rfl⟩ : syracuseStep 3556199 = 5334299) B5334299
theorem B3426401 : Blo 830350 3426401 := bstep (se 2 (by rfl) ⟨1284900, by rfl⟩ : syracuseStep 3426401 = 2569801) B2569801
theorem B1001575 : Blo 830350 1001575 := bstep (se 1 (by rfl) ⟨751181, by rfl⟩ : syracuseStep 1001575 = 1502363) B1502363
theorem B13486499 : Blo 830350 13486499 := bstep (se 1 (by rfl) ⟨10114874, by rfl⟩ : syracuseStep 13486499 = 20229749) B20229749
theorem B8997439 : Blo 830350 8997439 := bstep (se 1 (by rfl) ⟨6748079, by rfl⟩ : syracuseStep 8997439 = 13496159) B13496159
theorem B5065415 : Blo 830350 5065415 := bstep (se 1 (by rfl) ⟨3799061, by rfl⟩ : syracuseStep 5065415 = 7598123) B7598123
theorem B5065753 : Blo 830350 5065753 := bstep (se 2 (by rfl) ⟨1899657, by rfl⟩ : syracuseStep 5065753 = 3799315) B3799315
theorem B24695945 : Blo 830350 24695945 := bstep (se 2 (by rfl) ⟨9260979, by rfl⟩ : syracuseStep 24695945 = 18521959) B18521959
theorem B51369349 : Blo 830350 51369349 := bstep (se 4 (by rfl) ⟨4815876, by rfl⟩ : syracuseStep 51369349 = 9631753) B9631753
theorem B2808431 : Blo 830350 2808431 := bstep (se 1 (by rfl) ⟨2106323, by rfl⟩ : syracuseStep 2808431 = 4212647) B4212647
theorem B2808539 : Blo 830350 2808539 := bstep (se 1 (by rfl) ⟨2106404, by rfl⟩ : syracuseStep 2808539 = 4212809) B4212809
theorem B1334011 : Blo 830350 1334011 := bstep (se 1 (by rfl) ⟨1000508, by rfl⟩ : syracuseStep 1334011 = 2001017) B2001017
theorem B5692625 : Blo 830350 5692625 := bstep (se 2 (by rfl) ⟨2134734, by rfl⟩ : syracuseStep 5692625 = 4269469) B4269469
theorem B3563513 : Blo 830350 3563513 := bstep (se 2 (by rfl) ⟨1336317, by rfl⟩ : syracuseStep 3563513 = 2672635) B2672635
theorem B12804407 : Blo 830350 12804407 := bstep (se 1 (by rfl) ⟨9603305, by rfl⟩ : syracuseStep 12804407 = 19206611) B19206611
theorem B29188775 : Blo 830350 29188775 := bstep (se 1 (by rfl) ⟨21891581, by rfl⟩ : syracuseStep 29188775 = 43783163) B43783163
theorem B4219775 : Blo 830350 4219775 := bstep (se 1 (by rfl) ⟨3164831, by rfl⟩ : syracuseStep 4219775 = 6329663) B6329663
theorem B90236105 : Blo 830350 90236105 := bstep (se 2 (by rfl) ⟨33838539, by rfl⟩ : syracuseStep 90236105 = 67677079) B67677079
theorem B17070641 : Blo 830350 17070641 := bstep (se 2 (by rfl) ⟨6401490, by rfl⟩ : syracuseStep 17070641 = 12802981) B12802981
theorem B1407935 : Blo 830350 1407935 := bstep (se 1 (by rfl) ⟨1055951, by rfl⟩ : syracuseStep 1407935 = 2111903) B2111903
theorem B7994375 : Blo 830350 7994375 := bstep (se 1 (by rfl) ⟨5995781, by rfl⟩ : syracuseStep 7994375 = 11991563) B11991563
theorem B5341733 : Blo 830350 5341733 := bstep (se 4 (by rfl) ⟨500787, by rfl⟩ : syracuseStep 5341733 = 1001575) B1001575
theorem B1245887 : Blo 830350 1245887 := bstep (se 1 (by rfl) ⟨934415, by rfl⟩ : syracuseStep 1245887 = 1868831) B1868831
theorem B3376943 : Blo 830350 3376943 := bstep (se 1 (by rfl) ⟨2532707, by rfl⟩ : syracuseStep 3376943 = 5065415) B5065415
theorem B1247543 : Blo 830350 1247543 := bstep (se 1 (by rfl) ⟨935657, by rfl⟩ : syracuseStep 1247543 = 1871315) B1871315
theorem B1247975 : Blo 830350 1247975 := bstep (se 1 (by rfl) ⟨935981, by rfl⟩ : syracuseStep 1247975 = 1871963) B1871963
theorem B4001071 : Blo 830350 4001071 := bstep (se 1 (by rfl) ⟨3000803, by rfl⟩ : syracuseStep 4001071 = 6001607) B6001607
theorem B11996585 : Blo 830350 11996585 := bstep (se 2 (by rfl) ⟨4498719, by rfl⟩ : syracuseStep 11996585 = 8997439) B8997439
theorem B6754337 : Blo 830350 6754337 := bstep (se 2 (by rfl) ⟨2532876, by rfl⟩ : syracuseStep 6754337 = 5065753) B5065753
theorem B1872287 : Blo 830350 1872287 := bstep (se 1 (by rfl) ⟨1404215, by rfl⟩ : syracuseStep 1872287 = 2808431) B2808431
theorem B1872359 : Blo 830350 1872359 := bstep (se 1 (by rfl) ⟨1404269, by rfl⟩ : syracuseStep 1872359 = 2808539) B2808539
theorem B1251503 : Blo 830350 1251503 := bstep (se 1 (by rfl) ⟨938627, by rfl⟩ : syracuseStep 1251503 = 1877255) B1877255
theorem B68492465 : Blo 830350 68492465 := bstep (se 2 (by rfl) ⟨25684674, by rfl⟩ : syracuseStep 68492465 = 51369349) B51369349
theorem B3416185 : Blo 830350 3416185 := bstep (se 2 (by rfl) ⟨1281069, by rfl⟩ : syracuseStep 3416185 = 2562139) B2562139
theorem B2106233 : Blo 830350 2106233 := bstep (se 2 (by rfl) ⟨789837, by rfl⟩ : syracuseStep 2106233 = 1579675) B1579675
theorem B1778681 : Blo 830350 1778681 := bstep (se 2 (by rfl) ⟨667005, by rfl⟩ : syracuseStep 1778681 = 1334011) B1334011
theorem B11380427 : Blo 830350 11380427 := bstep (se 1 (by rfl) ⟨8535320, by rfl⟩ : syracuseStep 11380427 = 17070641) B17070641
theorem B830631 : Blo 830350 830631 := bstep (se 1 (by rfl) ⟨622973, by rfl⟩ : syracuseStep 830631 = 1245947) B1245947
theorem B2370799 : Blo 830350 2370799 := bstep (se 1 (by rfl) ⟨1778099, by rfl⟩ : syracuseStep 2370799 = 3556199) B3556199
theorem B830747 : Blo 830350 830747 := bstep (se 1 (by rfl) ⟨623060, by rfl⟩ : syracuseStep 830747 = 1246121) B1246121
theorem B830823 : Blo 830350 830823 := bstep (se 1 (by rfl) ⟨623117, by rfl⟩ : syracuseStep 830823 = 1246235) B1246235
theorem B831103 : Blo 830350 831103 := bstep (se 1 (by rfl) ⟨623327, by rfl⟩ : syracuseStep 831103 = 1246655) B1246655
theorem B831183 : Blo 830350 831183 := bstep (se 1 (by rfl) ⟨623387, by rfl⟩ : syracuseStep 831183 = 1246775) B1246775
theorem B831259 : Blo 830350 831259 := bstep (se 1 (by rfl) ⟨623444, by rfl⟩ : syracuseStep 831259 = 1246889) B1246889
theorem B831399 : Blo 830350 831399 := bstep (se 1 (by rfl) ⟨623549, by rfl⟩ : syracuseStep 831399 = 1247099) B1247099
theorem B831579 : Blo 830350 831579 := bstep (se 1 (by rfl) ⟨623684, by rfl⟩ : syracuseStep 831579 = 1247369) B1247369
theorem B1683647 : Blo 830350 1683647 := bstep (se 1 (by rfl) ⟨1262735, by rfl⟩ : syracuseStep 1683647 = 2525471) B2525471
theorem B831679 : Blo 830350 831679 := bstep (se 1 (by rfl) ⟨623759, by rfl⟩ : syracuseStep 831679 = 1247519) B1247519
theorem B8990999 : Blo 830350 8990999 := bstep (se 1 (by rfl) ⟨6743249, by rfl⟩ : syracuseStep 8990999 = 13486499) B13486499
theorem B9482831 : Blo 830350 9482831 := bstep (se 1 (by rfl) ⟨7112123, by rfl⟩ : syracuseStep 9482831 = 14224247) B14224247
theorem B832239 : Blo 830350 832239 := bstep (se 1 (by rfl) ⟨624179, by rfl⟩ : syracuseStep 832239 = 1248359) B1248359
theorem B832327 : Blo 830350 832327 := bstep (se 1 (by rfl) ⟨624245, by rfl⟩ : syracuseStep 832327 = 1248491) B1248491
theorem B832539 : Blo 830350 832539 := bstep (se 1 (by rfl) ⟨624404, by rfl⟩ : syracuseStep 832539 = 1248809) B1248809
theorem B832623 : Blo 830350 832623 := bstep (se 1 (by rfl) ⟨624467, by rfl⟩ : syracuseStep 832623 = 1248935) B1248935
theorem B43267421 : Blo 830350 43267421 := bstep (se 3 (by rfl) ⟨8112641, by rfl⟩ : syracuseStep 43267421 = 16225283) B16225283
theorem B833391 : Blo 830350 833391 := bstep (se 1 (by rfl) ⟨625043, by rfl⟩ : syracuseStep 833391 = 1250087) B1250087
theorem B833447 : Blo 830350 833447 := bstep (se 1 (by rfl) ⟨625085, by rfl⟩ : syracuseStep 833447 = 1250171) B1250171
theorem B833563 : Blo 830350 833563 := bstep (se 1 (by rfl) ⟨625172, by rfl⟩ : syracuseStep 833563 = 1250345) B1250345
theorem B16463963 : Blo 830350 16463963 := bstep (se 1 (by rfl) ⟨12347972, by rfl⟩ : syracuseStep 16463963 = 24695945) B24695945
theorem B834031 : Blo 830350 834031 := bstep (se 1 (by rfl) ⟨625523, by rfl⟩ : syracuseStep 834031 = 1251047) B1251047
theorem B11975647 : Blo 830350 11975647 := bstep (se 1 (by rfl) ⟨8981735, by rfl⟩ : syracuseStep 11975647 = 17963471) B17963471
theorem B2375675 : Blo 830350 2375675 := bstep (se 1 (by rfl) ⟨1781756, by rfl⟩ : syracuseStep 2375675 = 3563513) B3563513
theorem B31965191 : Blo 830350 31965191 := bstep (se 1 (by rfl) ⟨23973893, by rfl⟩ : syracuseStep 31965191 = 47947787) B47947787
theorem B8536271 : Blo 830350 8536271 := bstep (se 1 (by rfl) ⟨6402203, by rfl⟩ : syracuseStep 8536271 = 12804407) B12804407
theorem B10666241 : Blo 830350 10666241 := bstep (se 2 (by rfl) ⟨3999840, by rfl⟩ : syracuseStep 10666241 = 7999681) B7999681
theorem B2671481 : Blo 830350 2671481 := bstep (se 2 (by rfl) ⟨1001805, by rfl⟩ : syracuseStep 2671481 = 2003611) B2003611
theorem B4049855 : Blo 830350 4049855 := bstep (se 1 (by rfl) ⟨3037391, by rfl⟩ : syracuseStep 4049855 = 6074783) B6074783
theorem B9490121 : Blo 830350 9490121 := bstep (se 2 (by rfl) ⟨3558795, by rfl⟩ : syracuseStep 9490121 = 7117591) B7117591
theorem B938623 : Blo 830350 938623 := bstep (se 1 (by rfl) ⟨703967, by rfl⟩ : syracuseStep 938623 = 1407935) B1407935
theorem B5329583 : Blo 830350 5329583 := bstep (se 1 (by rfl) ⟨3997187, by rfl⟩ : syracuseStep 5329583 = 7994375) B7994375
theorem B3560915 : Blo 830350 3560915 := bstep (se 1 (by rfl) ⟨2670686, by rfl⟩ : syracuseStep 3560915 = 5341373) B5341373
theorem B2709245 : Blo 830350 2709245 := bstep (se 3 (by rfl) ⟨507983, by rfl⟩ : syracuseStep 2709245 = 1015967) B1015967
theorem B17061779 : Blo 830350 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B8018135 : Blo 830350 8018135 := bstep (se 1 (by rfl) ⟨6013601, by rfl⟩ : syracuseStep 8018135 = 12027203) B12027203
theorem B23944369 : Blo 830350 23944369 := bstep (se 2 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 23944369 = 17958277) B17958277
theorem B3006829 : Blo 830350 3006829 := bstep (se 3 (by rfl) ⟨563780, by rfl⟩ : syracuseStep 3006829 = 1127561) B1127561
theorem B2811293 : Blo 830350 2811293 := bstep (se 3 (by rfl) ⟨527117, by rfl⟩ : syracuseStep 2811293 = 1054235) B1054235
theorem B5334913 : Blo 830350 5334913 := bstep (se 2 (by rfl) ⟨2000592, by rfl⟩ : syracuseStep 5334913 = 4001185) B4001185
theorem B3795083 : Blo 830350 3795083 := bstep (se 1 (by rfl) ⟨2846312, by rfl⟩ : syracuseStep 3795083 = 5692625) B5692625
theorem B9137069 : Blo 830350 9137069 := bstep (se 3 (by rfl) ⟨1713200, by rfl⟩ : syracuseStep 9137069 = 3426401) B3426401
theorem B19459183 : Blo 830350 19459183 := bstep (se 1 (by rfl) ⟨14594387, by rfl⟩ : syracuseStep 19459183 = 29188775) B29188775
theorem B2813183 : Blo 830350 2813183 := bstep (se 1 (by rfl) ⟨2109887, by rfl⟩ : syracuseStep 2813183 = 4219775) B4219775
theorem B60157403 : Blo 830350 60157403 := bstep (se 1 (by rfl) ⟨45118052, by rfl⟩ : syracuseStep 60157403 = 90236105) B90236105
theorem B6319943 : Blo 830350 6319943 := bstep (se 1 (by rfl) ⟨4739957, by rfl⟩ : syracuseStep 6319943 = 9479915) B9479915
theorem B1407739 : Blo 830350 1407739 := bstep (se 1 (by rfl) ⟨1055804, by rfl⟩ : syracuseStep 1407739 = 2111609) B2111609
theorem B4554913 : Blo 830350 4554913 := bstep (se 2 (by rfl) ⟨1708092, by rfl⟩ : syracuseStep 4554913 = 3416185) B3416185
theorem B7110827 : Blo 830350 7110827 := bstep (se 1 (by rfl) ⟨5333120, by rfl⟩ : syracuseStep 7110827 = 10666241) B10666241
theorem B7997723 : Blo 830350 7997723 := bstep (se 1 (by rfl) ⟨5998292, by rfl⟩ : syracuseStep 7997723 = 11996585) B11996585
theorem B6326747 : Blo 830350 6326747 := bstep (se 1 (by rfl) ⟨4745060, by rfl⟩ : syracuseStep 6326747 = 9490121) B9490121
theorem B7113217 : Blo 830350 7113217 := bstep (se 2 (by rfl) ⟨2667456, by rfl⟩ : syracuseStep 7113217 = 5334913) B5334913
theorem B1248191 : Blo 830350 1248191 := bstep (se 1 (by rfl) ⟨936143, by rfl⟩ : syracuseStep 1248191 = 1872287) B1872287
theorem B1248239 : Blo 830350 1248239 := bstep (se 1 (by rfl) ⟨936179, by rfl⟩ : syracuseStep 1248239 = 1872359) B1872359
theorem B11374519 : Blo 830350 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B5345423 : Blo 830350 5345423 := bstep (se 1 (by rfl) ⟨4009067, by rfl⟩ : syracuseStep 5345423 = 8018135) B8018135
theorem B1185787 : Blo 830350 1185787 := bstep (se 1 (by rfl) ⟨889340, by rfl⟩ : syracuseStep 1185787 = 1778681) B1778681
theorem B1251497 : Blo 830350 1251497 := bstep (se 2 (by rfl) ⟨469311, by rfl⟩ : syracuseStep 1251497 = 938623) B938623
theorem B1874195 : Blo 830350 1874195 := bstep (se 1 (by rfl) ⟨1405646, by rfl⟩ : syracuseStep 1874195 = 2811293) B2811293
theorem B2530055 : Blo 830350 2530055 := bstep (se 1 (by rfl) ⟨1897541, by rfl⟩ : syracuseStep 2530055 = 3795083) B3795083
theorem B1875455 : Blo 830350 1875455 := bstep (se 1 (by rfl) ⟨1406591, by rfl⟩ : syracuseStep 1875455 = 2813183) B2813183
theorem B1122431 : Blo 830350 1122431 := bstep (se 1 (by rfl) ⟨841823, by rfl⟩ : syracuseStep 1122431 = 1683647) B1683647
theorem B28844947 : Blo 830350 28844947 := bstep (se 1 (by rfl) ⟨21633710, by rfl⟩ : syracuseStep 28844947 = 43267421) B43267421
theorem B1876985 : Blo 830350 1876985 := bstep (se 2 (by rfl) ⟨703869, by rfl⟩ : syracuseStep 1876985 = 1407739) B1407739
theorem B15967529 : Blo 830350 15967529 := bstep (se 2 (by rfl) ⟨5987823, by rfl⟩ : syracuseStep 15967529 = 11975647) B11975647
theorem B31925825 : Blo 830350 31925825 := bstep (se 2 (by rfl) ⟨11972184, by rfl⟩ : syracuseStep 31925825 = 23944369) B23944369
theorem B1583783 : Blo 830350 1583783 := bstep (se 1 (by rfl) ⟨1187837, by rfl⟩ : syracuseStep 1583783 = 2375675) B2375675
theorem B21310127 : Blo 830350 21310127 := bstep (se 1 (by rfl) ⟨15982595, by rfl⟩ : syracuseStep 21310127 = 31965191) B31965191
theorem B830591 : Blo 830350 830591 := bstep (se 1 (by rfl) ⟨622943, by rfl⟩ : syracuseStep 830591 = 1245887) B1245887
theorem B4009105 : Blo 830350 4009105 := bstep (se 2 (by rfl) ⟨1503414, by rfl⟩ : syracuseStep 4009105 = 3006829) B3006829
theorem B831695 : Blo 830350 831695 := bstep (se 1 (by rfl) ⟨623771, by rfl⟩ : syracuseStep 831695 = 1247543) B1247543
theorem B831983 : Blo 830350 831983 := bstep (se 1 (by rfl) ⟨623987, by rfl⟩ : syracuseStep 831983 = 1247975) B1247975
theorem B2699903 : Blo 830350 2699903 := bstep (se 1 (by rfl) ⟨2024927, by rfl⟩ : syracuseStep 2699903 = 4049855) B4049855
theorem B7123949 : Blo 830350 7123949 := bstep (se 3 (by rfl) ⟨1335740, by rfl⟩ : syracuseStep 7123949 = 2671481) B2671481
theorem B4502891 : Blo 830350 4502891 := bstep (se 1 (by rfl) ⟨3377168, by rfl⟩ : syracuseStep 4502891 = 6754337) B6754337
theorem B3553055 : Blo 830350 3553055 := bstep (se 1 (by rfl) ⟨2664791, by rfl⟩ : syracuseStep 3553055 = 5329583) B5329583
theorem B2373943 : Blo 830350 2373943 := bstep (se 1 (by rfl) ⟨1780457, by rfl⟩ : syracuseStep 2373943 = 3560915) B3560915
theorem B834335 : Blo 830350 834335 := bstep (se 1 (by rfl) ⟨625751, by rfl⟩ : syracuseStep 834335 = 1251503) B1251503
theorem B3161065 : Blo 830350 3161065 := bstep (se 2 (by rfl) ⟨1185399, by rfl⟩ : syracuseStep 3161065 = 2370799) B2370799
theorem B7224653 : Blo 830350 7224653 := bstep (se 3 (by rfl) ⟨1354622, by rfl⟩ : syracuseStep 7224653 = 2709245) B2709245
theorem B45661643 : Blo 830350 45661643 := bstep (se 1 (by rfl) ⟨34246232, by rfl⟩ : syracuseStep 45661643 = 68492465) B68492465
theorem B7586951 : Blo 830350 7586951 := bstep (se 1 (by rfl) ⟨5690213, by rfl⟩ : syracuseStep 7586951 = 11380427) B11380427
theorem B4213295 : Blo 830350 4213295 := bstep (se 1 (by rfl) ⟨3159971, by rfl⟩ : syracuseStep 4213295 = 6319943) B6319943
theorem B3561155 : Blo 830350 3561155 := bstep (se 1 (by rfl) ⟨2670866, by rfl⟩ : syracuseStep 3561155 = 5341733) B5341733
theorem B2251295 : Blo 830350 2251295 := bstep (se 1 (by rfl) ⟨1688471, by rfl⟩ : syracuseStep 2251295 = 3376943) B3376943
theorem B91053557 : Blo 830350 91053557 := bstep (se 5 (by rfl) ⟨4268135, by rfl⟩ : syracuseStep 91053557 = 8536271) B8536271
theorem B25945577 : Blo 830350 25945577 := bstep (se 2 (by rfl) ⟨9729591, by rfl⟩ : syracuseStep 25945577 = 19459183) B19459183
theorem B5334761 : Blo 830350 5334761 := bstep (se 2 (by rfl) ⟨2000535, by rfl⟩ : syracuseStep 5334761 = 4001071) B4001071
theorem B1404155 : Blo 830350 1404155 := bstep (se 1 (by rfl) ⟨1053116, by rfl⟩ : syracuseStep 1404155 = 2106233) B2106233
theorem B6091379 : Blo 830350 6091379 := bstep (se 1 (by rfl) ⟨4568534, by rfl⟩ : syracuseStep 6091379 = 9137069) B9137069
theorem B40104935 : Blo 830350 40104935 := bstep (se 1 (by rfl) ⟨30078701, by rfl⟩ : syracuseStep 40104935 = 60157403) B60157403
theorem B5993999 : Blo 830350 5993999 := bstep (se 1 (by rfl) ⟨4495499, by rfl⟩ : syracuseStep 5993999 = 8990999) B8990999
theorem B6321887 : Blo 830350 6321887 := bstep (se 1 (by rfl) ⟨4741415, by rfl⟩ : syracuseStep 6321887 = 9482831) B9482831
theorem B10975975 : Blo 830350 10975975 := bstep (se 1 (by rfl) ⟨8231981, by rfl⟩ : syracuseStep 10975975 = 16463963) B16463963
theorem B1249463 : Blo 830350 1249463 := bstep (se 1 (by rfl) ⟨937097, by rfl⟩ : syracuseStep 1249463 = 1874195) B1874195
theorem B5345473 : Blo 830350 5345473 := bstep (se 2 (by rfl) ⟨2004552, by rfl⟩ : syracuseStep 5345473 = 4009105) B4009105
theorem B1250303 : Blo 830350 1250303 := bstep (se 1 (by rfl) ⟨937727, by rfl⟩ : syracuseStep 1250303 = 1875455) B1875455
theorem B1251323 : Blo 830350 1251323 := bstep (se 1 (by rfl) ⟨938492, by rfl⟩ : syracuseStep 1251323 = 1876985) B1876985
theorem B1055855 : Blo 830350 1055855 := bstep (se 1 (by rfl) ⟨791891, by rfl⟩ : syracuseStep 1055855 = 1583783) B1583783
theorem B1581049 : Blo 830350 1581049 := bstep (se 2 (by rfl) ⟨592893, by rfl⟩ : syracuseStep 1581049 = 1185787) B1185787
theorem B2368703 : Blo 830350 2368703 := bstep (se 1 (by rfl) ⟨1776527, by rfl⟩ : syracuseStep 2368703 = 3553055) B3553055
theorem B6073217 : Blo 830350 6073217 := bstep (se 2 (by rfl) ⟨2277456, by rfl⟩ : syracuseStep 6073217 = 4554913) B4554913
theorem B2993149 : Blo 830350 2993149 := bstep (se 3 (by rfl) ⟨561215, by rfl⟩ : syracuseStep 2993149 = 1122431) B1122431
theorem B832127 : Blo 830350 832127 := bstep (se 1 (by rfl) ⟨624095, by rfl⟩ : syracuseStep 832127 = 1248191) B1248191
theorem B832159 : Blo 830350 832159 := bstep (se 1 (by rfl) ⟨624119, by rfl⟩ : syracuseStep 832159 = 1248239) B1248239
theorem B20231869 : Blo 830350 20231869 := bstep (se 3 (by rfl) ⟨3793475, by rfl⟩ : syracuseStep 20231869 = 7586951) B7586951
theorem B9484289 : Blo 830350 9484289 := bstep (se 2 (by rfl) ⟨3556608, by rfl⟩ : syracuseStep 9484289 = 7113217) B7113217
theorem B12007709 : Blo 830350 12007709 := bstep (se 3 (by rfl) ⟨2251445, by rfl⟩ : syracuseStep 12007709 = 4502891) B4502891
theorem B2374103 : Blo 830350 2374103 := bstep (se 1 (by rfl) ⟨1780577, by rfl⟩ : syracuseStep 2374103 = 3561155) B3561155
theorem B58538533 : Blo 830350 58538533 := bstep (se 4 (by rfl) ⟨5487987, by rfl⟩ : syracuseStep 58538533 = 10975975) B10975975
theorem B834331 : Blo 830350 834331 := bstep (se 1 (by rfl) ⟨625748, by rfl⟩ : syracuseStep 834331 = 1251497) B1251497
theorem B1686703 : Blo 830350 1686703 := bstep (se 1 (by rfl) ⟨1265027, by rfl⟩ : syracuseStep 1686703 = 2530055) B2530055
theorem B60702371 : Blo 830350 60702371 := bstep (se 1 (by rfl) ⟨45526778, by rfl⟩ : syracuseStep 60702371 = 91053557) B91053557
theorem B21283883 : Blo 830350 21283883 := bstep (se 1 (by rfl) ⟨15962912, by rfl⟩ : syracuseStep 21283883 = 31925825) B31925825
theorem B3556507 : Blo 830350 3556507 := bstep (se 1 (by rfl) ⟨2667380, by rfl⟩ : syracuseStep 3556507 = 5334761) B5334761
theorem B14206751 : Blo 830350 14206751 := bstep (se 1 (by rfl) ⟨10655063, by rfl⟩ : syracuseStep 14206751 = 21310127) B21310127
theorem B936103 : Blo 830350 936103 := bstep (se 1 (by rfl) ⟨702077, by rfl⟩ : syracuseStep 936103 = 1404155) B1404155
theorem B3165257 : Blo 830350 3165257 := bstep (se 2 (by rfl) ⟨1186971, by rfl⟩ : syracuseStep 3165257 = 2373943) B2373943
theorem B4214591 : Blo 830350 4214591 := bstep (se 1 (by rfl) ⟨3160943, by rfl⟩ : syracuseStep 4214591 = 6321887) B6321887
theorem B4214753 : Blo 830350 4214753 := bstep (se 2 (by rfl) ⟨1580532, by rfl⟩ : syracuseStep 4214753 = 3161065) B3161065
theorem B4740551 : Blo 830350 4740551 := bstep (se 1 (by rfl) ⟨3555413, by rfl⟩ : syracuseStep 4740551 = 7110827) B7110827
theorem B38459929 : Blo 830350 38459929 := bstep (se 2 (by rfl) ⟨14422473, by rfl⟩ : syracuseStep 38459929 = 28844947) B28844947
theorem B5331815 : Blo 830350 5331815 := bstep (se 1 (by rfl) ⟨3998861, by rfl⟩ : syracuseStep 5331815 = 7997723) B7997723
theorem B4217831 : Blo 830350 4217831 := bstep (se 1 (by rfl) ⟨3163373, by rfl⟩ : syracuseStep 4217831 = 6326747) B6326747
theorem B7199741 : Blo 830350 7199741 := bstep (se 3 (by rfl) ⟨1349951, by rfl⟩ : syracuseStep 7199741 = 2699903) B2699903
theorem B2808863 : Blo 830350 2808863 := bstep (se 1 (by rfl) ⟨2106647, by rfl⟩ : syracuseStep 2808863 = 4213295) B4213295
theorem B3563615 : Blo 830350 3563615 := bstep (se 1 (by rfl) ⟨2672711, by rfl⟩ : syracuseStep 3563615 = 5345423) B5345423
theorem B1500863 : Blo 830350 1500863 := bstep (se 1 (by rfl) ⟨1125647, by rfl⟩ : syracuseStep 1500863 = 2251295) B2251295
theorem B276752821 : Blo 830350 276752821 := bstep (se 5 (by rfl) ⟨12972788, by rfl⟩ : syracuseStep 276752821 = 25945577) B25945577
theorem B15166025 : Blo 830350 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B10645019 : Blo 830350 10645019 := bstep (se 1 (by rfl) ⟨7983764, by rfl⟩ : syracuseStep 10645019 = 15967529) B15967529
theorem B4060919 : Blo 830350 4060919 := bstep (se 1 (by rfl) ⟨3045689, by rfl⟩ : syracuseStep 4060919 = 6091379) B6091379
theorem B26736623 : Blo 830350 26736623 := bstep (se 1 (by rfl) ⟨20052467, by rfl⟩ : syracuseStep 26736623 = 40104935) B40104935
theorem B4749299 : Blo 830350 4749299 := bstep (se 1 (by rfl) ⟨3561974, by rfl⟩ : syracuseStep 4749299 = 7123949) B7123949
theorem B3995999 : Blo 830350 3995999 := bstep (se 1 (by rfl) ⟨2996999, by rfl⟩ : syracuseStep 3995999 = 5993999) B5993999
theorem B4816435 : Blo 830350 4816435 := bstep (se 1 (by rfl) ⟨3612326, by rfl⟩ : syracuseStep 4816435 = 7224653) B7224653
theorem B30441095 : Blo 830350 30441095 := bstep (se 1 (by rfl) ⟨22830821, by rfl⟩ : syracuseStep 30441095 = 45661643) B45661643
theorem B14189255 : Blo 830350 14189255 := bstep (se 1 (by rfl) ⟨10641941, by rfl⟩ : syracuseStep 14189255 = 21283883) B21283883
theorem B9471167 : Blo 830350 9471167 := bstep (se 1 (by rfl) ⟨7103375, by rfl⟩ : syracuseStep 9471167 = 14206751) B14206751
theorem B1248137 : Blo 830350 1248137 := bstep (se 2 (by rfl) ⟨468051, by rfl⟩ : syracuseStep 1248137 = 936103) B936103
theorem B369003761 : Blo 830350 369003761 := bstep (se 2 (by rfl) ⟨138376410, by rfl⟩ : syracuseStep 369003761 = 276752821) B276752821
theorem B4002301 : Blo 830350 4002301 := bstep (se 3 (by rfl) ⟨750431, by rfl⟩ : syracuseStep 4002301 = 1500863) B1500863
theorem B1872575 : Blo 830350 1872575 := bstep (se 1 (by rfl) ⟨1404431, by rfl⟩ : syracuseStep 1872575 = 2808863) B2808863
theorem B26975825 : Blo 830350 26975825 := bstep (se 2 (by rfl) ⟨10115934, by rfl⟩ : syracuseStep 26975825 = 20231869) B20231869
theorem B8005139 : Blo 830350 8005139 := bstep (se 1 (by rfl) ⟨6003854, by rfl⟩ : syracuseStep 8005139 = 12007709) B12007709
theorem B2663999 : Blo 830350 2663999 := bstep (se 1 (by rfl) ⟨1997999, by rfl⟩ : syracuseStep 2663999 = 3995999) B3995999
theorem B1582735 : Blo 830350 1582735 := bstep (se 1 (by rfl) ⟨1187051, by rfl⟩ : syracuseStep 1582735 = 2374103) B2374103
theorem B20294063 : Blo 830350 20294063 := bstep (se 1 (by rfl) ⟨15220547, by rfl⟩ : syracuseStep 20294063 = 30441095) B30441095
theorem B285190645 : Blo 830350 285190645 := bstep (se 5 (by rfl) ⟨13368311, by rfl⟩ : syracuseStep 285190645 = 26736623) B26736623
theorem B2108065 : Blo 830350 2108065 := bstep (se 2 (by rfl) ⟨790524, by rfl⟩ : syracuseStep 2108065 = 1581049) B1581049
theorem B2110171 : Blo 830350 2110171 := bstep (se 1 (by rfl) ⟨1582628, by rfl⟩ : syracuseStep 2110171 = 3165257) B3165257
theorem B832975 : Blo 830350 832975 := bstep (se 1 (by rfl) ⟨624731, by rfl⟩ : syracuseStep 832975 = 1249463) B1249463
theorem B833535 : Blo 830350 833535 := bstep (se 1 (by rfl) ⟨625151, by rfl⟩ : syracuseStep 833535 = 1250303) B1250303
theorem B3160367 : Blo 830350 3160367 := bstep (se 1 (by rfl) ⟨2370275, by rfl⟩ : syracuseStep 3160367 = 4740551) B4740551
theorem B834215 : Blo 830350 834215 := bstep (se 1 (by rfl) ⟨625661, by rfl⟩ : syracuseStep 834215 = 1251323) B1251323
theorem B3554543 : Blo 830350 3554543 := bstep (se 1 (by rfl) ⟨2665907, by rfl⟩ : syracuseStep 3554543 = 5331815) B5331815
theorem B10829117 : Blo 830350 10829117 := bstep (se 3 (by rfl) ⟨2030459, by rfl⟩ : syracuseStep 10829117 = 4060919) B4060919
theorem B4799827 : Blo 830350 4799827 := bstep (se 1 (by rfl) ⟨3599870, by rfl⟩ : syracuseStep 4799827 = 7199741) B7199741
theorem B2375743 : Blo 830350 2375743 := bstep (se 1 (by rfl) ⟨1781807, by rfl⟩ : syracuseStep 2375743 = 3563615) B3563615
theorem B7127297 : Blo 830350 7127297 := bstep (se 2 (by rfl) ⟨2672736, by rfl⟩ : syracuseStep 7127297 = 5345473) B5345473
theorem B10110683 : Blo 830350 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B4048811 : Blo 830350 4048811 := bstep (se 1 (by rfl) ⟨3036608, by rfl⟩ : syracuseStep 4048811 = 6073217) B6073217
theorem B7096679 : Blo 830350 7096679 := bstep (se 1 (by rfl) ⟨5322509, by rfl⟩ : syracuseStep 7096679 = 10645019) B10645019
theorem B3166199 : Blo 830350 3166199 := bstep (se 1 (by rfl) ⟨2374649, by rfl⟩ : syracuseStep 3166199 = 4749299) B4749299
theorem B2248937 : Blo 830350 2248937 := bstep (se 2 (by rfl) ⟨843351, by rfl⟩ : syracuseStep 2248937 = 1686703) B1686703
theorem B4742009 : Blo 830350 4742009 := bstep (se 2 (by rfl) ⟨1778253, by rfl⟩ : syracuseStep 4742009 = 3556507) B3556507
theorem B2809727 : Blo 830350 2809727 := bstep (se 1 (by rfl) ⟨2107295, by rfl⟩ : syracuseStep 2809727 = 4214591) B4214591
theorem B2809835 : Blo 830350 2809835 := bstep (se 1 (by rfl) ⟨2107376, by rfl⟩ : syracuseStep 2809835 = 4214753) B4214753
theorem B6316541 : Blo 830350 6316541 := bstep (se 3 (by rfl) ⟨1184351, by rfl⟩ : syracuseStep 6316541 = 2368703) B2368703
theorem B3990865 : Blo 830350 3990865 := bstep (se 2 (by rfl) ⟨1496574, by rfl⟩ : syracuseStep 3990865 = 2993149) B2993149
theorem B2811887 : Blo 830350 2811887 := bstep (se 1 (by rfl) ⟨2108915, by rfl⟩ : syracuseStep 2811887 = 4217831) B4217831
theorem B2815613 : Blo 830350 2815613 := bstep (se 3 (by rfl) ⟨527927, by rfl⟩ : syracuseStep 2815613 = 1055855) B1055855
theorem B51279905 : Blo 830350 51279905 := bstep (se 2 (by rfl) ⟨19229964, by rfl⟩ : syracuseStep 51279905 = 38459929) B38459929
theorem B78051377 : Blo 830350 78051377 := bstep (se 2 (by rfl) ⟨29269266, by rfl⟩ : syracuseStep 78051377 = 58538533) B58538533
theorem B6322859 : Blo 830350 6322859 := bstep (se 1 (by rfl) ⟨4742144, by rfl⟩ : syracuseStep 6322859 = 9484289) B9484289
theorem B6421913 : Blo 830350 6421913 := bstep (se 2 (by rfl) ⟨2408217, by rfl⟩ : syracuseStep 6421913 = 4816435) B4816435
theorem B40468247 : Blo 830350 40468247 := bstep (se 1 (by rfl) ⟨30351185, by rfl⟩ : syracuseStep 40468247 = 60702371) B60702371
theorem B4751531 : Blo 830350 4751531 := bstep (se 1 (by rfl) ⟨3563648, by rfl⟩ : syracuseStep 4751531 = 7127297) B7127297
theorem B1248383 : Blo 830350 1248383 := bstep (se 1 (by rfl) ⟨936287, by rfl⟩ : syracuseStep 1248383 = 1872575) B1872575
theorem B1873151 : Blo 830350 1873151 := bstep (se 1 (by rfl) ⟨1404863, by rfl⟩ : syracuseStep 1873151 = 2809727) B2809727
theorem B1873223 : Blo 830350 1873223 := bstep (se 1 (by rfl) ⟨1404917, by rfl⟩ : syracuseStep 1873223 = 2809835) B2809835
theorem B136746413 : Blo 830350 136746413 := bstep (se 3 (by rfl) ⟨25639952, by rfl⟩ : syracuseStep 136746413 = 51279905) B51279905
theorem B1775999 : Blo 830350 1775999 := bstep (se 1 (by rfl) ⟨1331999, by rfl⟩ : syracuseStep 1775999 = 2663999) B2663999
theorem B1874591 : Blo 830350 1874591 := bstep (se 1 (by rfl) ⟨1405943, by rfl⟩ : syracuseStep 1874591 = 2811887) B2811887
theorem B25599077 : Blo 830350 25599077 := bstep (se 4 (by rfl) ⟨2399913, by rfl⟩ : syracuseStep 25599077 = 4799827) B4799827
theorem B1877075 : Blo 830350 1877075 := bstep (se 1 (by rfl) ⟨1407806, by rfl⟩ : syracuseStep 1877075 = 2815613) B2815613
theorem B2106911 : Blo 830350 2106911 := bstep (se 1 (by rfl) ⟨1580183, by rfl⟩ : syracuseStep 2106911 = 3160367) B3160367
theorem B2369695 : Blo 830350 2369695 := bstep (se 1 (by rfl) ⟨1777271, by rfl⟩ : syracuseStep 2369695 = 3554543) B3554543
theorem B7219411 : Blo 830350 7219411 := bstep (se 1 (by rfl) ⟨5414558, by rfl⟩ : syracuseStep 7219411 = 10829117) B10829117
theorem B26978831 : Blo 830350 26978831 := bstep (se 1 (by rfl) ⟨20234123, by rfl⟩ : syracuseStep 26978831 = 40468247) B40468247
theorem B2699207 : Blo 830350 2699207 := bstep (se 1 (by rfl) ⟨2024405, by rfl⟩ : syracuseStep 2699207 = 4048811) B4048811
theorem B4731119 : Blo 830350 4731119 := bstep (se 1 (by rfl) ⟨3548339, by rfl⟩ : syracuseStep 4731119 = 7096679) B7096679
theorem B5321153 : Blo 830350 5321153 := bstep (se 2 (by rfl) ⟨1995432, by rfl⟩ : syracuseStep 5321153 = 3990865) B3990865
theorem B832091 : Blo 830350 832091 := bstep (se 1 (by rfl) ⟨624068, by rfl⟩ : syracuseStep 832091 = 1248137) B1248137
theorem B246002507 : Blo 830350 246002507 := bstep (se 1 (by rfl) ⟨184501880, by rfl⟩ : syracuseStep 246002507 = 369003761) B369003761
theorem B2110313 : Blo 830350 2110313 := bstep (se 2 (by rfl) ⟨791367, by rfl⟩ : syracuseStep 2110313 = 1582735) B1582735
theorem B2110799 : Blo 830350 2110799 := bstep (se 1 (by rfl) ⟨1583099, by rfl⟩ : syracuseStep 2110799 = 3166199) B3166199
theorem B380254193 : Blo 830350 380254193 := bstep (se 2 (by rfl) ⟨142595322, by rfl⟩ : syracuseStep 380254193 = 285190645) B285190645
theorem B3161339 : Blo 830350 3161339 := bstep (se 1 (by rfl) ⟨2371004, by rfl⟩ : syracuseStep 3161339 = 4742009) B4742009
theorem B4211027 : Blo 830350 4211027 := bstep (se 1 (by rfl) ⟨3158270, by rfl⟩ : syracuseStep 4211027 = 6316541) B6316541
theorem B4215239 : Blo 830350 4215239 := bstep (se 1 (by rfl) ⟨3161429, by rfl⟩ : syracuseStep 4215239 = 6322859) B6322859
theorem B4281275 : Blo 830350 4281275 := bstep (se 1 (by rfl) ⟨3210956, by rfl⟩ : syracuseStep 4281275 = 6421913) B6421913
theorem B3167657 : Blo 830350 3167657 := bstep (se 2 (by rfl) ⟨1187871, by rfl⟩ : syracuseStep 3167657 = 2375743) B2375743
theorem B9459503 : Blo 830350 9459503 := bstep (se 1 (by rfl) ⟨7094627, by rfl⟩ : syracuseStep 9459503 = 14189255) B14189255
theorem B6314111 : Blo 830350 6314111 := bstep (se 1 (by rfl) ⟨4735583, by rfl⟩ : syracuseStep 6314111 = 9471167) B9471167
theorem B6740455 : Blo 830350 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B1499291 : Blo 830350 1499291 := bstep (se 1 (by rfl) ⟨1124468, by rfl⟩ : syracuseStep 1499291 = 2248937) B2248937
theorem B2810753 : Blo 830350 2810753 := bstep (se 2 (by rfl) ⟨1054032, by rfl⟩ : syracuseStep 2810753 = 2108065) B2108065
theorem B17983883 : Blo 830350 17983883 := bstep (se 1 (by rfl) ⟨13487912, by rfl⟩ : syracuseStep 17983883 = 26975825) B26975825
theorem B5336401 : Blo 830350 5336401 := bstep (se 2 (by rfl) ⟨2001150, by rfl⟩ : syracuseStep 5336401 = 4002301) B4002301
theorem B2813561 : Blo 830350 2813561 := bstep (se 2 (by rfl) ⟨1055085, by rfl⟩ : syracuseStep 2813561 = 2110171) B2110171
theorem B5336759 : Blo 830350 5336759 := bstep (se 1 (by rfl) ⟨4002569, by rfl⟩ : syracuseStep 5336759 = 8005139) B8005139
theorem B13529375 : Blo 830350 13529375 := bstep (se 1 (by rfl) ⟨10147031, by rfl⟩ : syracuseStep 13529375 = 20294063) B20294063
theorem B52034251 : Blo 830350 52034251 := bstep (se 1 (by rfl) ⟨39025688, by rfl⟩ : syracuseStep 52034251 = 78051377) B78051377
theorem B38503525 : Blo 830350 38503525 := bstep (se 4 (by rfl) ⟨3609705, by rfl⟩ : syracuseStep 38503525 = 7219411) B7219411
theorem B15992437 : Blo 830350 15992437 := bstep (se 5 (by rfl) ⟨749645, by rfl⟩ : syracuseStep 15992437 = 1499291) B1499291
theorem B1248767 : Blo 830350 1248767 := bstep (se 1 (by rfl) ⟨936575, by rfl⟩ : syracuseStep 1248767 = 1873151) B1873151
theorem B1248815 : Blo 830350 1248815 := bstep (se 1 (by rfl) ⟨936611, by rfl⟩ : syracuseStep 1248815 = 1873223) B1873223
theorem B91164275 : Blo 830350 91164275 := bstep (se 1 (by rfl) ⟨68373206, by rfl⟩ : syracuseStep 91164275 = 136746413) B136746413
theorem B1183999 : Blo 830350 1183999 := bstep (se 1 (by rfl) ⟨887999, by rfl⟩ : syracuseStep 1183999 = 1775999) B1775999
theorem B1249727 : Blo 830350 1249727 := bstep (se 1 (by rfl) ⟨937295, by rfl⟩ : syracuseStep 1249727 = 1874591) B1874591
theorem B7115201 : Blo 830350 7115201 := bstep (se 2 (by rfl) ⟨2668200, by rfl⟩ : syracuseStep 7115201 = 5336401) B5336401
theorem B1873835 : Blo 830350 1873835 := bstep (se 1 (by rfl) ⟨1405376, by rfl⟩ : syracuseStep 1873835 = 2810753) B2810753
theorem B1251383 : Blo 830350 1251383 := bstep (se 1 (by rfl) ⟨938537, by rfl⟩ : syracuseStep 1251383 = 1877075) B1877075
theorem B1875707 : Blo 830350 1875707 := bstep (se 1 (by rfl) ⟨1406780, by rfl⟩ : syracuseStep 1875707 = 2813561) B2813561
theorem B3154079 : Blo 830350 3154079 := bstep (se 1 (by rfl) ⟨2365559, by rfl⟩ : syracuseStep 3154079 = 4731119) B4731119
theorem B9019583 : Blo 830350 9019583 := bstep (se 1 (by rfl) ⟨6764687, by rfl⟩ : syracuseStep 9019583 = 13529375) B13529375
theorem B3547435 : Blo 830350 3547435 := bstep (se 1 (by rfl) ⟨2660576, by rfl⟩ : syracuseStep 3547435 = 5321153) B5321153
theorem B8987273 : Blo 830350 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B69379001 : Blo 830350 69379001 := bstep (se 2 (by rfl) ⟨26017125, by rfl⟩ : syracuseStep 69379001 = 52034251) B52034251
theorem B253502795 : Blo 830350 253502795 := bstep (se 1 (by rfl) ⟨190127096, by rfl⟩ : syracuseStep 253502795 = 380254193) B380254193
theorem B2107559 : Blo 830350 2107559 := bstep (se 1 (by rfl) ⟨1580669, by rfl⟩ : syracuseStep 2107559 = 3161339) B3161339
theorem B832255 : Blo 830350 832255 := bstep (se 1 (by rfl) ⟨624191, by rfl⟩ : syracuseStep 832255 = 1248383) B1248383
theorem B11416733 : Blo 830350 11416733 := bstep (se 3 (by rfl) ⟨2140637, by rfl⟩ : syracuseStep 11416733 = 4281275) B4281275
theorem B3159593 : Blo 830350 3159593 := bstep (se 2 (by rfl) ⟨1184847, by rfl⟩ : syracuseStep 3159593 = 2369695) B2369695
theorem B2111771 : Blo 830350 2111771 := bstep (se 1 (by rfl) ⟨1583828, by rfl⟩ : syracuseStep 2111771 = 3167657) B3167657
theorem B6306335 : Blo 830350 6306335 := bstep (se 1 (by rfl) ⟨4729751, by rfl⟩ : syracuseStep 6306335 = 9459503) B9459503
theorem B4209407 : Blo 830350 4209407 := bstep (se 1 (by rfl) ⟨3157055, by rfl⟩ : syracuseStep 4209407 = 6314111) B6314111
theorem B3557839 : Blo 830350 3557839 := bstep (se 1 (by rfl) ⟨2668379, by rfl⟩ : syracuseStep 3557839 = 5336759) B5336759
theorem B3167687 : Blo 830350 3167687 := bstep (se 1 (by rfl) ⟨2375765, by rfl⟩ : syracuseStep 3167687 = 4751531) B4751531
theorem B2807351 : Blo 830350 2807351 := bstep (se 1 (by rfl) ⟨2105513, by rfl⟩ : syracuseStep 2807351 = 4211027) B4211027
theorem B2810159 : Blo 830350 2810159 := bstep (se 1 (by rfl) ⟨2107619, by rfl⟩ : syracuseStep 2810159 = 4215239) B4215239
theorem B17066051 : Blo 830350 17066051 := bstep (se 1 (by rfl) ⟨12799538, by rfl⟩ : syracuseStep 17066051 = 25599077) B25599077
theorem B1404607 : Blo 830350 1404607 := bstep (se 1 (by rfl) ⟨1053455, by rfl⟩ : syracuseStep 1404607 = 2106911) B2106911
theorem B11989255 : Blo 830350 11989255 := bstep (se 1 (by rfl) ⟨8991941, by rfl⟩ : syracuseStep 11989255 = 17983883) B17983883
theorem B17985887 : Blo 830350 17985887 := bstep (se 1 (by rfl) ⟨13489415, by rfl⟩ : syracuseStep 17985887 = 26978831) B26978831
theorem B1799471 : Blo 830350 1799471 := bstep (se 1 (by rfl) ⟨1349603, by rfl⟩ : syracuseStep 1799471 = 2699207) B2699207
theorem B164001671 : Blo 830350 164001671 := bstep (se 1 (by rfl) ⟨123001253, by rfl⟩ : syracuseStep 164001671 = 246002507) B246002507
theorem B1406875 : Blo 830350 1406875 := bstep (se 1 (by rfl) ⟨1055156, by rfl⟩ : syracuseStep 1406875 = 2110313) B2110313
theorem B1407199 : Blo 830350 1407199 := bstep (se 1 (by rfl) ⟨1055399, by rfl⟩ : syracuseStep 1407199 = 2110799) B2110799
theorem B676007453 : Blo 830350 676007453 := bstep (se 3 (by rfl) ⟨126751397, by rfl⟩ : syracuseStep 676007453 = 253502795) B253502795
theorem B1871567 : Blo 830350 1871567 := bstep (se 1 (by rfl) ⟨1403675, by rfl⟩ : syracuseStep 1871567 = 2807351) B2807351
theorem B1249223 : Blo 830350 1249223 := bstep (se 1 (by rfl) ⟨936917, by rfl⟩ : syracuseStep 1249223 = 1873835) B1873835
theorem B1872809 : Blo 830350 1872809 := bstep (se 2 (by rfl) ⟨702303, by rfl⟩ : syracuseStep 1872809 = 1404607) B1404607
theorem B1250471 : Blo 830350 1250471 := bstep (se 1 (by rfl) ⟨937853, by rfl⟩ : syracuseStep 1250471 = 1875707) B1875707
theorem B2102719 : Blo 830350 2102719 := bstep (se 1 (by rfl) ⟨1577039, by rfl⟩ : syracuseStep 2102719 = 3154079) B3154079
theorem B1873439 : Blo 830350 1873439 := bstep (se 1 (by rfl) ⟨1405079, by rfl⟩ : syracuseStep 1873439 = 2810159) B2810159
theorem B1578665 : Blo 830350 1578665 := bstep (se 2 (by rfl) ⟨591999, by rfl⟩ : syracuseStep 1578665 = 1183999) B1183999
theorem B11377367 : Blo 830350 11377367 := bstep (se 1 (by rfl) ⟨8533025, by rfl⟩ : syracuseStep 11377367 = 17066051) B17066051
theorem B1875833 : Blo 830350 1875833 := bstep (se 2 (by rfl) ⟨703437, by rfl⟩ : syracuseStep 1875833 = 1406875) B1406875
theorem B1876265 : Blo 830350 1876265 := bstep (se 2 (by rfl) ⟨703599, by rfl⟩ : syracuseStep 1876265 = 1407199) B1407199
theorem B7611155 : Blo 830350 7611155 := bstep (se 1 (by rfl) ⟨5708366, by rfl⟩ : syracuseStep 7611155 = 11416733) B11416733
theorem B2106395 : Blo 830350 2106395 := bstep (se 1 (by rfl) ⟨1579796, by rfl⟩ : syracuseStep 2106395 = 3159593) B3159593
theorem B4204223 : Blo 830350 4204223 := bstep (se 1 (by rfl) ⟨3153167, by rfl⟩ : syracuseStep 4204223 = 6306335) B6306335
theorem B4729913 : Blo 830350 4729913 := bstep (se 2 (by rfl) ⟨1773717, by rfl⟩ : syracuseStep 4729913 = 3547435) B3547435
theorem B832511 : Blo 830350 832511 := bstep (se 1 (by rfl) ⟨624383, by rfl⟩ : syracuseStep 832511 = 1248767) B1248767
theorem B832543 : Blo 830350 832543 := bstep (se 1 (by rfl) ⟨624407, by rfl⟩ : syracuseStep 832543 = 1248815) B1248815
theorem B833151 : Blo 830350 833151 := bstep (se 1 (by rfl) ⟨624863, by rfl⟩ : syracuseStep 833151 = 1249727) B1249727
theorem B2111791 : Blo 830350 2111791 := bstep (se 1 (by rfl) ⟨1583843, by rfl⟩ : syracuseStep 2111791 = 3167687) B3167687
theorem B834255 : Blo 830350 834255 := bstep (se 1 (by rfl) ⟨625691, by rfl⟩ : syracuseStep 834255 = 1251383) B1251383
theorem B6013055 : Blo 830350 6013055 := bstep (se 1 (by rfl) ⟨4509791, by rfl⟩ : syracuseStep 6013055 = 9019583) B9019583
theorem B46252667 : Blo 830350 46252667 := bstep (se 1 (by rfl) ⟨34689500, by rfl⟩ : syracuseStep 46252667 = 69379001) B69379001
theorem B1199647 : Blo 830350 1199647 := bstep (se 1 (by rfl) ⟨899735, by rfl⟩ : syracuseStep 1199647 = 1799471) B1799471
theorem B109334447 : Blo 830350 109334447 := bstep (se 1 (by rfl) ⟨82000835, by rfl⟩ : syracuseStep 109334447 = 164001671) B164001671
theorem B2806271 : Blo 830350 2806271 := bstep (se 1 (by rfl) ⟨2104703, by rfl⟩ : syracuseStep 2806271 = 4209407) B4209407
theorem B51338033 : Blo 830350 51338033 := bstep (se 2 (by rfl) ⟨19251762, by rfl⟩ : syracuseStep 51338033 = 38503525) B38503525
theorem B21323249 : Blo 830350 21323249 := bstep (se 2 (by rfl) ⟨7996218, by rfl⟩ : syracuseStep 21323249 = 15992437) B15992437
theorem B60776183 : Blo 830350 60776183 := bstep (se 1 (by rfl) ⟨45582137, by rfl⟩ : syracuseStep 60776183 = 91164275) B91164275
theorem B4743467 : Blo 830350 4743467 := bstep (se 1 (by rfl) ⟨3557600, by rfl⟩ : syracuseStep 4743467 = 7115201) B7115201
theorem B4743785 : Blo 830350 4743785 := bstep (se 2 (by rfl) ⟨1778919, by rfl⟩ : syracuseStep 4743785 = 3557839) B3557839
theorem B15985673 : Blo 830350 15985673 := bstep (se 2 (by rfl) ⟨5994627, by rfl⟩ : syracuseStep 15985673 = 11989255) B11989255
theorem B5991515 : Blo 830350 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B1405039 : Blo 830350 1405039 := bstep (se 1 (by rfl) ⟨1053779, by rfl⟩ : syracuseStep 1405039 = 2107559) B2107559
theorem B11990591 : Blo 830350 11990591 := bstep (se 1 (by rfl) ⟨8992943, by rfl⟩ : syracuseStep 11990591 = 17985887) B17985887
theorem B1407847 : Blo 830350 1407847 := bstep (se 1 (by rfl) ⟨1055885, by rfl⟩ : syracuseStep 1407847 = 2111771) B2111771
theorem B123340445 : Blo 830350 123340445 := bstep (se 3 (by rfl) ⟨23126333, by rfl⟩ : syracuseStep 123340445 = 46252667) B46252667
theorem B1247711 : Blo 830350 1247711 := bstep (se 1 (by rfl) ⟨935783, by rfl⟩ : syracuseStep 1247711 = 1871567) B1871567
theorem B1870847 : Blo 830350 1870847 := bstep (se 1 (by rfl) ⟨1403135, by rfl⟩ : syracuseStep 1870847 = 2806271) B2806271
theorem B1248539 : Blo 830350 1248539 := bstep (se 1 (by rfl) ⟨936404, by rfl⟩ : syracuseStep 1248539 = 1872809) B1872809
theorem B1248959 : Blo 830350 1248959 := bstep (se 1 (by rfl) ⟨936719, by rfl⟩ : syracuseStep 1248959 = 1873439) B1873439
theorem B1052443 : Blo 830350 1052443 := bstep (se 1 (by rfl) ⟨789332, by rfl⟩ : syracuseStep 1052443 = 1578665) B1578665
theorem B1250555 : Blo 830350 1250555 := bstep (se 1 (by rfl) ⟨937916, by rfl⟩ : syracuseStep 1250555 = 1875833) B1875833
theorem B1873385 : Blo 830350 1873385 := bstep (se 2 (by rfl) ⟨702519, by rfl⟩ : syracuseStep 1873385 = 1405039) B1405039
theorem B1250843 : Blo 830350 1250843 := bstep (se 1 (by rfl) ⟨938132, by rfl⟩ : syracuseStep 1250843 = 1876265) B1876265
theorem B10657115 : Blo 830350 10657115 := bstep (se 1 (by rfl) ⟨7992836, by rfl⟩ : syracuseStep 10657115 = 15985673) B15985673
theorem B3153275 : Blo 830350 3153275 := bstep (se 1 (by rfl) ⟨2364956, by rfl⟩ : syracuseStep 3153275 = 4729913) B4729913
theorem B1877129 : Blo 830350 1877129 := bstep (se 2 (by rfl) ⟨703923, by rfl⟩ : syracuseStep 1877129 = 1407847) B1407847
theorem B4008703 : Blo 830350 4008703 := bstep (se 1 (by rfl) ⟨3006527, by rfl⟩ : syracuseStep 4008703 = 6013055) B6013055
theorem B450671635 : Blo 830350 450671635 := bstep (se 1 (by rfl) ⟨338003726, by rfl⟩ : syracuseStep 450671635 = 676007453) B676007453
theorem B72889631 : Blo 830350 72889631 := bstep (se 1 (by rfl) ⟨54667223, by rfl⟩ : syracuseStep 72889631 = 109334447) B109334447
theorem B832815 : Blo 830350 832815 := bstep (se 1 (by rfl) ⟨624611, by rfl⟩ : syracuseStep 832815 = 1249223) B1249223
theorem B833647 : Blo 830350 833647 := bstep (se 1 (by rfl) ⟨625235, by rfl⟩ : syracuseStep 833647 = 1250471) B1250471
theorem B7584911 : Blo 830350 7584911 := bstep (se 1 (by rfl) ⟨5688683, by rfl⟩ : syracuseStep 7584911 = 11377367) B11377367
theorem B34225355 : Blo 830350 34225355 := bstep (se 1 (by rfl) ⟨25669016, by rfl⟩ : syracuseStep 34225355 = 51338033) B51338033
theorem B40517455 : Blo 830350 40517455 := bstep (se 1 (by rfl) ⟨30388091, by rfl⟩ : syracuseStep 40517455 = 60776183) B60776183
theorem B3162311 : Blo 830350 3162311 := bstep (se 1 (by rfl) ⟨2371733, by rfl⟩ : syracuseStep 3162311 = 4743467) B4743467
theorem B3162523 : Blo 830350 3162523 := bstep (se 1 (by rfl) ⟨2371892, by rfl⟩ : syracuseStep 3162523 = 4743785) B4743785
theorem B2802815 : Blo 830350 2802815 := bstep (se 1 (by rfl) ⟨2102111, by rfl⟩ : syracuseStep 2802815 = 4204223) B4204223
theorem B2803625 : Blo 830350 2803625 := bstep (se 2 (by rfl) ⟨1051359, by rfl⟩ : syracuseStep 2803625 = 2102719) B2102719
theorem B1599529 : Blo 830350 1599529 := bstep (se 2 (by rfl) ⟨599823, by rfl⟩ : syracuseStep 1599529 = 1199647) B1199647
theorem B14215499 : Blo 830350 14215499 := bstep (se 1 (by rfl) ⟨10661624, by rfl⟩ : syracuseStep 14215499 = 21323249) B21323249
theorem B5074103 : Blo 830350 5074103 := bstep (se 1 (by rfl) ⟨3805577, by rfl⟩ : syracuseStep 5074103 = 7611155) B7611155
theorem B1404263 : Blo 830350 1404263 := bstep (se 1 (by rfl) ⟨1053197, by rfl⟩ : syracuseStep 1404263 = 2106395) B2106395
theorem B3994343 : Blo 830350 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B2815721 : Blo 830350 2815721 := bstep (se 2 (by rfl) ⟨1055895, by rfl⟩ : syracuseStep 2815721 = 2111791) B2111791
theorem B7993727 : Blo 830350 7993727 := bstep (se 1 (by rfl) ⟨5995295, by rfl⟩ : syracuseStep 7993727 = 11990591) B11990591
theorem B1868543 : Blo 830350 1868543 := bstep (se 1 (by rfl) ⟨1401407, by rfl⟩ : syracuseStep 1868543 = 2802815) B2802815
theorem B1869083 : Blo 830350 1869083 := bstep (se 1 (by rfl) ⟨1401812, by rfl⟩ : syracuseStep 1869083 = 2803625) B2803625
theorem B1247231 : Blo 830350 1247231 := bstep (se 1 (by rfl) ⟨935423, by rfl⟩ : syracuseStep 1247231 = 1870847) B1870847
theorem B2132705 : Blo 830350 2132705 := bstep (se 2 (by rfl) ⟨799764, by rfl⟩ : syracuseStep 2132705 = 1599529) B1599529
theorem B1248923 : Blo 830350 1248923 := bstep (se 1 (by rfl) ⟨936692, by rfl⟩ : syracuseStep 1248923 = 1873385) B1873385
theorem B5344937 : Blo 830350 5344937 := bstep (se 2 (by rfl) ⟨2004351, by rfl⟩ : syracuseStep 5344937 = 4008703) B4008703
theorem B2102183 : Blo 830350 2102183 := bstep (se 1 (by rfl) ⟨1576637, by rfl⟩ : syracuseStep 2102183 = 3153275) B3153275
theorem B1251419 : Blo 830350 1251419 := bstep (se 1 (by rfl) ⟨938564, by rfl⟩ : syracuseStep 1251419 = 1877129) B1877129
theorem B9476999 : Blo 830350 9476999 := bstep (se 1 (by rfl) ⟨7107749, by rfl⟩ : syracuseStep 9476999 = 14215499) B14215499
theorem B3382735 : Blo 830350 3382735 := bstep (se 1 (by rfl) ⟨2537051, by rfl⟩ : syracuseStep 3382735 = 5074103) B5074103
theorem B2662895 : Blo 830350 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B1877147 : Blo 830350 1877147 := bstep (se 1 (by rfl) ⟨1407860, by rfl⟩ : syracuseStep 1877147 = 2815721) B2815721
theorem B5056607 : Blo 830350 5056607 := bstep (se 1 (by rfl) ⟨3792455, by rfl⟩ : syracuseStep 5056607 = 7584911) B7584911
theorem B22816903 : Blo 830350 22816903 := bstep (se 1 (by rfl) ⟨17112677, by rfl⟩ : syracuseStep 22816903 = 34225355) B34225355
theorem B2108207 : Blo 830350 2108207 := bstep (se 1 (by rfl) ⟨1581155, by rfl⟩ : syracuseStep 2108207 = 3162311) B3162311
theorem B82226963 : Blo 830350 82226963 := bstep (se 1 (by rfl) ⟨61670222, by rfl⟩ : syracuseStep 82226963 = 123340445) B123340445
theorem B831807 : Blo 830350 831807 := bstep (se 1 (by rfl) ⟨623855, by rfl⟩ : syracuseStep 831807 = 1247711) B1247711
theorem B832359 : Blo 830350 832359 := bstep (se 1 (by rfl) ⟨624269, by rfl⟩ : syracuseStep 832359 = 1248539) B1248539
theorem B832639 : Blo 830350 832639 := bstep (se 1 (by rfl) ⟨624479, by rfl⟩ : syracuseStep 832639 = 1248959) B1248959
theorem B833703 : Blo 830350 833703 := bstep (se 1 (by rfl) ⟨625277, by rfl⟩ : syracuseStep 833703 = 1250555) B1250555
theorem B833895 : Blo 830350 833895 := bstep (se 1 (by rfl) ⟨625421, by rfl⟩ : syracuseStep 833895 = 1250843) B1250843
theorem B936175 : Blo 830350 936175 := bstep (se 1 (by rfl) ⟨702131, by rfl⟩ : syracuseStep 936175 = 1404263) B1404263
theorem B5329151 : Blo 830350 5329151 := bstep (se 1 (by rfl) ⟨3996863, by rfl⟩ : syracuseStep 5329151 = 7993727) B7993727
theorem B54023273 : Blo 830350 54023273 := bstep (se 2 (by rfl) ⟨20258727, by rfl⟩ : syracuseStep 54023273 = 40517455) B40517455
theorem B4216697 : Blo 830350 4216697 := bstep (se 2 (by rfl) ⟨1581261, by rfl⟩ : syracuseStep 4216697 = 3162523) B3162523
theorem B7104743 : Blo 830350 7104743 := bstep (se 1 (by rfl) ⟨5328557, by rfl⟩ : syracuseStep 7104743 = 10657115) B10657115
theorem B1403257 : Blo 830350 1403257 := bstep (se 2 (by rfl) ⟨526221, by rfl⟩ : syracuseStep 1403257 = 1052443) B1052443
theorem B600895513 : Blo 830350 600895513 := bstep (se 2 (by rfl) ⟨225335817, by rfl⟩ : syracuseStep 600895513 = 450671635) B450671635
theorem B48593087 : Blo 830350 48593087 := bstep (se 1 (by rfl) ⟨36444815, by rfl⟩ : syracuseStep 48593087 = 72889631) B72889631
theorem B1245695 : Blo 830350 1245695 := bstep (se 1 (by rfl) ⟨934271, by rfl⟩ : syracuseStep 1245695 = 1868543) B1868543
theorem B1246055 : Blo 830350 1246055 := bstep (se 1 (by rfl) ⟨934541, by rfl⟩ : syracuseStep 1246055 = 1869083) B1869083
theorem B1248233 : Blo 830350 1248233 := bstep (se 2 (by rfl) ⟨468087, by rfl⟩ : syracuseStep 1248233 = 936175) B936175
theorem B1871009 : Blo 830350 1871009 := bstep (se 2 (by rfl) ⟨701628, by rfl⟩ : syracuseStep 1871009 = 1403257) B1403257
theorem B36015515 : Blo 830350 36015515 := bstep (se 1 (by rfl) ⟨27011636, by rfl⟩ : syracuseStep 36015515 = 54023273) B54023273
theorem B1251431 : Blo 830350 1251431 := bstep (se 1 (by rfl) ⟨938573, by rfl⟩ : syracuseStep 1251431 = 1877147) B1877147
theorem B831487 : Blo 830350 831487 := bstep (se 1 (by rfl) ⟨623615, by rfl⟩ : syracuseStep 831487 = 1247231) B1247231
theorem B1421803 : Blo 830350 1421803 := bstep (se 1 (by rfl) ⟨1066352, by rfl⟩ : syracuseStep 1421803 = 2132705) B2132705
theorem B832615 : Blo 830350 832615 := bstep (se 1 (by rfl) ⟨624461, by rfl⟩ : syracuseStep 832615 = 1248923) B1248923
theorem B3552767 : Blo 830350 3552767 := bstep (se 1 (by rfl) ⟨2664575, by rfl⟩ : syracuseStep 3552767 = 5329151) B5329151
theorem B30422537 : Blo 830350 30422537 := bstep (se 2 (by rfl) ⟨11408451, by rfl⟩ : syracuseStep 30422537 = 22816903) B22816903
theorem B834279 : Blo 830350 834279 := bstep (se 1 (by rfl) ⟨625709, by rfl⟩ : syracuseStep 834279 = 1251419) B1251419
theorem B801194017 : Blo 830350 801194017 := bstep (se 2 (by rfl) ⟨300447756, by rfl⟩ : syracuseStep 801194017 = 600895513) B600895513
theorem B4736495 : Blo 830350 4736495 := bstep (se 1 (by rfl) ⟨3552371, by rfl⟩ : syracuseStep 4736495 = 7104743) B7104743
theorem B32395391 : Blo 830350 32395391 := bstep (se 1 (by rfl) ⟨24296543, by rfl⟩ : syracuseStep 32395391 = 48593087) B48593087
theorem B4510313 : Blo 830350 4510313 := bstep (se 2 (by rfl) ⟨1691367, by rfl⟩ : syracuseStep 4510313 = 3382735) B3382735
theorem B7101053 : Blo 830350 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B3563291 : Blo 830350 3563291 := bstep (se 1 (by rfl) ⟨2672468, by rfl⟩ : syracuseStep 3563291 = 5344937) B5344937
theorem B1401455 : Blo 830350 1401455 := bstep (se 1 (by rfl) ⟨1051091, by rfl⟩ : syracuseStep 1401455 = 2102183) B2102183
theorem B2811131 : Blo 830350 2811131 := bstep (se 1 (by rfl) ⟨2108348, by rfl⟩ : syracuseStep 2811131 = 4216697) B4216697
theorem B6317999 : Blo 830350 6317999 := bstep (se 1 (by rfl) ⟨4738499, by rfl⟩ : syracuseStep 6317999 = 9476999) B9476999
theorem B3371071 : Blo 830350 3371071 := bstep (se 1 (by rfl) ⟨2528303, by rfl⟩ : syracuseStep 3371071 = 5056607) B5056607
theorem B1405471 : Blo 830350 1405471 := bstep (se 1 (by rfl) ⟨1054103, by rfl⟩ : syracuseStep 1405471 = 2108207) B2108207
theorem B54817975 : Blo 830350 54817975 := bstep (se 1 (by rfl) ⟨41113481, by rfl⟩ : syracuseStep 54817975 = 82226963) B82226963
theorem B1247339 : Blo 830350 1247339 := bstep (se 1 (by rfl) ⟨935504, by rfl⟩ : syracuseStep 1247339 = 1871009) B1871009
theorem B21596927 : Blo 830350 21596927 := bstep (se 1 (by rfl) ⟨16197695, by rfl⟩ : syracuseStep 21596927 = 32395391) B32395391
theorem B4494761 : Blo 830350 4494761 := bstep (se 2 (by rfl) ⟨1685535, by rfl⟩ : syracuseStep 4494761 = 3371071) B3371071
theorem B1873961 : Blo 830350 1873961 := bstep (se 2 (by rfl) ⟨702735, by rfl⟩ : syracuseStep 1873961 = 1405471) B1405471
theorem B1874087 : Blo 830350 1874087 := bstep (se 1 (by rfl) ⟨1405565, by rfl⟩ : syracuseStep 1874087 = 2811131) B2811131
theorem B2368511 : Blo 830350 2368511 := bstep (se 1 (by rfl) ⟨1776383, by rfl⟩ : syracuseStep 2368511 = 3552767) B3552767
theorem B830463 : Blo 830350 830463 := bstep (se 1 (by rfl) ⟨622847, by rfl⟩ : syracuseStep 830463 = 1245695) B1245695
theorem B830703 : Blo 830350 830703 := bstep (se 1 (by rfl) ⟨623027, by rfl⟩ : syracuseStep 830703 = 1246055) B1246055
theorem B3157663 : Blo 830350 3157663 := bstep (se 1 (by rfl) ⟨2368247, by rfl⟩ : syracuseStep 3157663 = 4736495) B4736495
theorem B832155 : Blo 830350 832155 := bstep (se 1 (by rfl) ⟨624116, by rfl⟩ : syracuseStep 832155 = 1248233) B1248233
theorem B834287 : Blo 830350 834287 := bstep (se 1 (by rfl) ⟨625715, by rfl⟩ : syracuseStep 834287 = 1251431) B1251431
theorem B4734035 : Blo 830350 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B2375527 : Blo 830350 2375527 := bstep (se 1 (by rfl) ⟨1781645, by rfl⟩ : syracuseStep 2375527 = 3563291) B3563291
theorem B934303 : Blo 830350 934303 := bstep (se 1 (by rfl) ⟨700727, by rfl⟩ : syracuseStep 934303 = 1401455) B1401455
theorem B4211999 : Blo 830350 4211999 := bstep (se 1 (by rfl) ⟨3158999, by rfl⟩ : syracuseStep 4211999 = 6317999) B6317999
theorem B73090633 : Blo 830350 73090633 := bstep (se 2 (by rfl) ⟨27408987, by rfl⟩ : syracuseStep 73090633 = 54817975) B54817975
theorem B1068258689 : Blo 830350 1068258689 := bstep (se 2 (by rfl) ⟨400597008, by rfl⟩ : syracuseStep 1068258689 = 801194017) B801194017
theorem B24010343 : Blo 830350 24010343 := bstep (se 1 (by rfl) ⟨18007757, by rfl⟩ : syracuseStep 24010343 = 36015515) B36015515
theorem B3006875 : Blo 830350 3006875 := bstep (se 1 (by rfl) ⟨2255156, by rfl⟩ : syracuseStep 3006875 = 4510313) B4510313
theorem B1895737 : Blo 830350 1895737 := bstep (se 2 (by rfl) ⟨710901, by rfl⟩ : syracuseStep 1895737 = 1421803) B1421803
theorem B20281691 : Blo 830350 20281691 := bstep (se 1 (by rfl) ⟨15211268, by rfl⟩ : syracuseStep 20281691 = 30422537) B30422537
theorem B1245737 : Blo 830350 1245737 := bstep (se 2 (by rfl) ⟨467151, by rfl⟩ : syracuseStep 1245737 = 934303) B934303
theorem B97454177 : Blo 830350 97454177 := bstep (se 2 (by rfl) ⟨36545316, by rfl⟩ : syracuseStep 97454177 = 73090633) B73090633
theorem B1249307 : Blo 830350 1249307 := bstep (se 1 (by rfl) ⟨936980, by rfl⟩ : syracuseStep 1249307 = 1873961) B1873961
theorem B1249391 : Blo 830350 1249391 := bstep (se 1 (by rfl) ⟨937043, by rfl⟩ : syracuseStep 1249391 = 1874087) B1874087
theorem B2527649 : Blo 830350 2527649 := bstep (se 2 (by rfl) ⟨947868, by rfl⟩ : syracuseStep 2527649 = 1895737) B1895737
theorem B2004583 : Blo 830350 2004583 := bstep (se 1 (by rfl) ⟨1503437, by rfl⟩ : syracuseStep 2004583 = 3006875) B3006875
theorem B1579007 : Blo 830350 1579007 := bstep (se 1 (by rfl) ⟨1184255, by rfl⟩ : syracuseStep 1579007 = 2368511) B2368511
theorem B3156023 : Blo 830350 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B831559 : Blo 830350 831559 := bstep (se 1 (by rfl) ⟨623669, by rfl⟩ : syracuseStep 831559 = 1247339) B1247339
theorem B2996507 : Blo 830350 2996507 := bstep (se 1 (by rfl) ⟨2247380, by rfl⟩ : syracuseStep 2996507 = 4494761) B4494761
theorem B4210217 : Blo 830350 4210217 := bstep (se 2 (by rfl) ⟨1578831, by rfl⟩ : syracuseStep 4210217 = 3157663) B3157663
theorem B16006895 : Blo 830350 16006895 := bstep (se 1 (by rfl) ⟨12005171, by rfl⟩ : syracuseStep 16006895 = 24010343) B24010343
theorem B54084509 : Blo 830350 54084509 := bstep (se 3 (by rfl) ⟨10140845, by rfl⟩ : syracuseStep 54084509 = 20281691) B20281691
theorem B57591805 : Blo 830350 57591805 := bstep (se 3 (by rfl) ⟨10798463, by rfl⟩ : syracuseStep 57591805 = 21596927) B21596927
theorem B3167369 : Blo 830350 3167369 := bstep (se 2 (by rfl) ⟨1187763, by rfl⟩ : syracuseStep 3167369 = 2375527) B2375527
theorem B2807999 : Blo 830350 2807999 := bstep (se 1 (by rfl) ⟨2105999, by rfl⟩ : syracuseStep 2807999 = 4211999) B4211999
theorem B712172459 : Blo 830350 712172459 := bstep (se 1 (by rfl) ⟨534129344, by rfl⟩ : syracuseStep 712172459 = 1068258689) B1068258689
theorem B1052671 : Blo 830350 1052671 := bstep (se 1 (by rfl) ⟨789503, by rfl⟩ : syracuseStep 1052671 = 1579007) B1579007
theorem B1871999 : Blo 830350 1871999 := bstep (se 1 (by rfl) ⟨1403999, by rfl⟩ : syracuseStep 1871999 = 2807999) B2807999
theorem B2104015 : Blo 830350 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B830491 : Blo 830350 830491 := bstep (se 1 (by rfl) ⟨622868, by rfl⟩ : syracuseStep 830491 = 1245737) B1245737
theorem B36056339 : Blo 830350 36056339 := bstep (se 1 (by rfl) ⟨27042254, by rfl⟩ : syracuseStep 36056339 = 54084509) B54084509
theorem B76789073 : Blo 830350 76789073 := bstep (se 2 (by rfl) ⟨28795902, by rfl⟩ : syracuseStep 76789073 = 57591805) B57591805
theorem B832871 : Blo 830350 832871 := bstep (se 1 (by rfl) ⟨624653, by rfl⟩ : syracuseStep 832871 = 1249307) B1249307
theorem B832927 : Blo 830350 832927 := bstep (se 1 (by rfl) ⟨624695, by rfl⟩ : syracuseStep 832927 = 1249391) B1249391
theorem B1685099 : Blo 830350 1685099 := bstep (se 1 (by rfl) ⟨1263824, by rfl⟩ : syracuseStep 1685099 = 2527649) B2527649
theorem B2111579 : Blo 830350 2111579 := bstep (se 1 (by rfl) ⟨1583684, by rfl⟩ : syracuseStep 2111579 = 3167369) B3167369
theorem B2672777 : Blo 830350 2672777 := bstep (se 2 (by rfl) ⟨1002291, by rfl⟩ : syracuseStep 2672777 = 2004583) B2004583
theorem B2806811 : Blo 830350 2806811 := bstep (se 1 (by rfl) ⟨2105108, by rfl⟩ : syracuseStep 2806811 = 4210217) B4210217
theorem B10671263 : Blo 830350 10671263 := bstep (se 1 (by rfl) ⟨8003447, by rfl⟩ : syracuseStep 10671263 = 16006895) B16006895
theorem B64969451 : Blo 830350 64969451 := bstep (se 1 (by rfl) ⟨48727088, by rfl⟩ : syracuseStep 64969451 = 97454177) B97454177
theorem B1899126557 : Blo 830350 1899126557 := bstep (se 3 (by rfl) ⟨356086229, by rfl⟩ : syracuseStep 1899126557 = 712172459) B712172459
theorem B1997671 : Blo 830350 1997671 := bstep (se 1 (by rfl) ⟨1498253, by rfl⟩ : syracuseStep 1997671 = 2996507) B2996507
theorem B1247999 : Blo 830350 1247999 := bstep (se 1 (by rfl) ⟨935999, by rfl⟩ : syracuseStep 1247999 = 1871999) B1871999
theorem B1871207 : Blo 830350 1871207 := bstep (se 1 (by rfl) ⟨1403405, by rfl⟩ : syracuseStep 1871207 = 2806811) B2806811
theorem B7114175 : Blo 830350 7114175 := bstep (se 1 (by rfl) ⟨5335631, by rfl⟩ : syracuseStep 7114175 = 10671263) B10671263
theorem B204770861 : Blo 830350 204770861 := bstep (se 3 (by rfl) ⟨38394536, by rfl⟩ : syracuseStep 204770861 = 76789073) B76789073
theorem B1123399 : Blo 830350 1123399 := bstep (se 1 (by rfl) ⟨842549, by rfl⟩ : syracuseStep 1123399 = 1685099) B1685099
theorem B2663561 : Blo 830350 2663561 := bstep (se 2 (by rfl) ⟨998835, by rfl⟩ : syracuseStep 2663561 = 1997671) B1997671
theorem B1781851 : Blo 830350 1781851 := bstep (se 1 (by rfl) ⟨1336388, by rfl⟩ : syracuseStep 1781851 = 2672777) B2672777
theorem B24037559 : Blo 830350 24037559 := bstep (se 1 (by rfl) ⟨18028169, by rfl⟩ : syracuseStep 24037559 = 36056339) B36056339
theorem B2805353 : Blo 830350 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B43312967 : Blo 830350 43312967 := bstep (se 1 (by rfl) ⟨32484725, by rfl⟩ : syracuseStep 43312967 = 64969451) B64969451
theorem B1266084371 : Blo 830350 1266084371 := bstep (se 1 (by rfl) ⟨949563278, by rfl⟩ : syracuseStep 1266084371 = 1899126557) B1899126557
theorem B1403561 : Blo 830350 1403561 := bstep (se 2 (by rfl) ⟨526335, by rfl⟩ : syracuseStep 1403561 = 1052671) B1052671
theorem B1407719 : Blo 830350 1407719 := bstep (se 1 (by rfl) ⟨1055789, by rfl⟩ : syracuseStep 1407719 = 2111579) B2111579
theorem B16025039 : Blo 830350 16025039 := bstep (se 1 (by rfl) ⟨12018779, by rfl⟩ : syracuseStep 16025039 = 24037559) B24037559
theorem B1247471 : Blo 830350 1247471 := bstep (se 1 (by rfl) ⟨935603, by rfl⟩ : syracuseStep 1247471 = 1871207) B1871207
theorem B136513907 : Blo 830350 136513907 := bstep (se 1 (by rfl) ⟨102385430, by rfl⟩ : syracuseStep 136513907 = 204770861) B204770861
theorem B1870235 : Blo 830350 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B28875311 : Blo 830350 28875311 := bstep (se 1 (by rfl) ⟨21656483, by rfl⟩ : syracuseStep 28875311 = 43312967) B43312967
theorem B831999 : Blo 830350 831999 := bstep (se 1 (by rfl) ⟨623999, by rfl⟩ : syracuseStep 831999 = 1247999) B1247999
theorem B2375801 : Blo 830350 2375801 := bstep (se 2 (by rfl) ⟨890925, by rfl⟩ : syracuseStep 2375801 = 1781851) B1781851
theorem B844056247 : Blo 830350 844056247 := bstep (se 1 (by rfl) ⟨633042185, by rfl⟩ : syracuseStep 844056247 = 1266084371) B1266084371
theorem B935707 : Blo 830350 935707 := bstep (se 1 (by rfl) ⟨701780, by rfl⟩ : syracuseStep 935707 = 1403561) B1403561
theorem B938479 : Blo 830350 938479 := bstep (se 1 (by rfl) ⟨703859, by rfl⟩ : syracuseStep 938479 = 1407719) B1407719
theorem B1497865 : Blo 830350 1497865 := bstep (se 2 (by rfl) ⟨561699, by rfl⟩ : syracuseStep 1497865 = 1123399) B1123399
theorem B4742783 : Blo 830350 4742783 := bstep (se 1 (by rfl) ⟨3557087, by rfl⟩ : syracuseStep 4742783 = 7114175) B7114175
theorem B7102829 : Blo 830350 7102829 := bstep (se 3 (by rfl) ⟨1331780, by rfl⟩ : syracuseStep 7102829 = 2663561) B2663561
theorem B10683359 : Blo 830350 10683359 := bstep (se 1 (by rfl) ⟨8012519, by rfl⟩ : syracuseStep 10683359 = 16025039) B16025039
theorem B1246823 : Blo 830350 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B1247609 : Blo 830350 1247609 := bstep (se 2 (by rfl) ⟨467853, by rfl⟩ : syracuseStep 1247609 = 935707) B935707
theorem B1251305 : Blo 830350 1251305 := bstep (se 2 (by rfl) ⟨469239, by rfl⟩ : syracuseStep 1251305 = 938479) B938479
theorem B1583867 : Blo 830350 1583867 := bstep (se 1 (by rfl) ⟨1187900, by rfl⟩ : syracuseStep 1583867 = 2375801) B2375801
theorem B831647 : Blo 830350 831647 := bstep (se 1 (by rfl) ⟨623735, by rfl⟩ : syracuseStep 831647 = 1247471) B1247471
theorem B91009271 : Blo 830350 91009271 := bstep (se 1 (by rfl) ⟨68256953, by rfl⟩ : syracuseStep 91009271 = 136513907) B136513907
theorem B19250207 : Blo 830350 19250207 := bstep (se 1 (by rfl) ⟨14437655, by rfl⟩ : syracuseStep 19250207 = 28875311) B28875311
theorem B3161855 : Blo 830350 3161855 := bstep (se 1 (by rfl) ⟨2371391, by rfl⟩ : syracuseStep 3161855 = 4742783) B4742783
theorem B4735219 : Blo 830350 4735219 := bstep (se 1 (by rfl) ⟨3551414, by rfl⟩ : syracuseStep 4735219 = 7102829) B7102829
theorem B1125408329 : Blo 830350 1125408329 := bstep (se 2 (by rfl) ⟨422028123, by rfl⟩ : syracuseStep 1125408329 = 844056247) B844056247
theorem B1997153 : Blo 830350 1997153 := bstep (se 2 (by rfl) ⟨748932, by rfl⟩ : syracuseStep 1997153 = 1497865) B1497865
theorem B1055911 : Blo 830350 1055911 := bstep (se 1 (by rfl) ⟨791933, by rfl⟩ : syracuseStep 1055911 = 1583867) B1583867
theorem B2107903 : Blo 830350 2107903 := bstep (se 1 (by rfl) ⟨1580927, by rfl⟩ : syracuseStep 2107903 = 3161855) B3161855
theorem B7122239 : Blo 830350 7122239 := bstep (se 1 (by rfl) ⟨5341679, by rfl⟩ : syracuseStep 7122239 = 10683359) B10683359
theorem B831215 : Blo 830350 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B831739 : Blo 830350 831739 := bstep (se 1 (by rfl) ⟨623804, by rfl⟩ : syracuseStep 831739 = 1247609) B1247609
theorem B834203 : Blo 830350 834203 := bstep (se 1 (by rfl) ⟨625652, by rfl⟩ : syracuseStep 834203 = 1251305) B1251305
theorem B750272219 : Blo 830350 750272219 := bstep (se 1 (by rfl) ⟨562704164, by rfl⟩ : syracuseStep 750272219 = 1125408329) B1125408329
theorem B60672847 : Blo 830350 60672847 := bstep (se 1 (by rfl) ⟨45504635, by rfl⟩ : syracuseStep 60672847 = 91009271) B91009271
theorem B1331435 : Blo 830350 1331435 := bstep (se 1 (by rfl) ⟨998576, by rfl⟩ : syracuseStep 1331435 = 1997153) B1997153
theorem B12833471 : Blo 830350 12833471 := bstep (se 1 (by rfl) ⟨9625103, by rfl⟩ : syracuseStep 12833471 = 19250207) B19250207
theorem B6313625 : Blo 830350 6313625 := bstep (se 2 (by rfl) ⟨2367609, by rfl⟩ : syracuseStep 6313625 = 4735219) B4735219
theorem B8555647 : Blo 830350 8555647 := bstep (se 1 (by rfl) ⟨6416735, by rfl⟩ : syracuseStep 8555647 = 12833471) B12833471
theorem B500181479 : Blo 830350 500181479 := bstep (se 1 (by rfl) ⟨375136109, by rfl⟩ : syracuseStep 500181479 = 750272219) B750272219
theorem B3550493 : Blo 830350 3550493 := bstep (se 3 (by rfl) ⟨665717, by rfl⟩ : syracuseStep 3550493 = 1331435) B1331435
theorem B4209083 : Blo 830350 4209083 := bstep (se 1 (by rfl) ⟨3156812, by rfl⟩ : syracuseStep 4209083 = 6313625) B6313625
theorem B2810537 : Blo 830350 2810537 := bstep (se 2 (by rfl) ⟨1053951, by rfl⟩ : syracuseStep 2810537 = 2107903) B2107903
theorem B80897129 : Blo 830350 80897129 := bstep (se 2 (by rfl) ⟨30336423, by rfl⟩ : syracuseStep 80897129 = 60672847) B60672847
theorem B4748159 : Blo 830350 4748159 := bstep (se 1 (by rfl) ⟨3561119, by rfl⟩ : syracuseStep 4748159 = 7122239) B7122239
theorem B1407881 : Blo 830350 1407881 := bstep (se 2 (by rfl) ⟨527955, by rfl⟩ : syracuseStep 1407881 = 1055911) B1055911
theorem B11407529 : Blo 830350 11407529 := bstep (se 2 (by rfl) ⟨4277823, by rfl⟩ : syracuseStep 11407529 = 8555647) B8555647
theorem B1873691 : Blo 830350 1873691 := bstep (se 1 (by rfl) ⟨1405268, by rfl⟩ : syracuseStep 1873691 = 2810537) B2810537
theorem B333454319 : Blo 830350 333454319 := bstep (se 1 (by rfl) ⟨250090739, by rfl⟩ : syracuseStep 333454319 = 500181479) B500181479
theorem B2366995 : Blo 830350 2366995 := bstep (se 1 (by rfl) ⟨1775246, by rfl⟩ : syracuseStep 2366995 = 3550493) B3550493
theorem B3165439 : Blo 830350 3165439 := bstep (se 1 (by rfl) ⟨2374079, by rfl⟩ : syracuseStep 3165439 = 4748159) B4748159
theorem B2806055 : Blo 830350 2806055 := bstep (se 1 (by rfl) ⟨2104541, by rfl⟩ : syracuseStep 2806055 = 4209083) B4209083
theorem B938587 : Blo 830350 938587 := bstep (se 1 (by rfl) ⟨703940, by rfl⟩ : syracuseStep 938587 = 1407881) B1407881
theorem B53931419 : Blo 830350 53931419 := bstep (se 1 (by rfl) ⟨40448564, by rfl⟩ : syracuseStep 53931419 = 80897129) B80897129
theorem B7605019 : Blo 830350 7605019 := bstep (se 1 (by rfl) ⟨5703764, by rfl⟩ : syracuseStep 7605019 = 11407529) B11407529
theorem B1870703 : Blo 830350 1870703 := bstep (se 1 (by rfl) ⟨1403027, by rfl⟩ : syracuseStep 1870703 = 2806055) B2806055
theorem B1249127 : Blo 830350 1249127 := bstep (se 1 (by rfl) ⟨936845, by rfl⟩ : syracuseStep 1249127 = 1873691) B1873691
theorem B222302879 : Blo 830350 222302879 := bstep (se 1 (by rfl) ⟨166727159, by rfl⟩ : syracuseStep 222302879 = 333454319) B333454319
theorem B1251449 : Blo 830350 1251449 := bstep (se 2 (by rfl) ⟨469293, by rfl⟩ : syracuseStep 1251449 = 938587) B938587
theorem B35954279 : Blo 830350 35954279 := bstep (se 1 (by rfl) ⟨26965709, by rfl⟩ : syracuseStep 35954279 = 53931419) B53931419
theorem B3155993 : Blo 830350 3155993 := bstep (se 2 (by rfl) ⟨1183497, by rfl⟩ : syracuseStep 3155993 = 2366995) B2366995
theorem B4220585 : Blo 830350 4220585 := bstep (se 2 (by rfl) ⟨1582719, by rfl⟩ : syracuseStep 4220585 = 3165439) B3165439
theorem B1247135 : Blo 830350 1247135 := bstep (se 1 (by rfl) ⟨935351, by rfl⟩ : syracuseStep 1247135 = 1870703) B1870703
theorem B2103995 : Blo 830350 2103995 := bstep (se 1 (by rfl) ⟨1577996, by rfl⟩ : syracuseStep 2103995 = 3155993) B3155993
theorem B832751 : Blo 830350 832751 := bstep (se 1 (by rfl) ⟨624563, by rfl⟩ : syracuseStep 832751 = 1249127) B1249127
theorem B834299 : Blo 830350 834299 := bstep (se 1 (by rfl) ⟨625724, by rfl⟩ : syracuseStep 834299 = 1251449) B1251449
theorem B23969519 : Blo 830350 23969519 := bstep (se 1 (by rfl) ⟨17977139, by rfl⟩ : syracuseStep 23969519 = 35954279) B35954279
theorem B148201919 : Blo 830350 148201919 := bstep (se 1 (by rfl) ⟨111151439, by rfl⟩ : syracuseStep 148201919 = 222302879) B222302879
theorem B40560101 : Blo 830350 40560101 := bstep (se 4 (by rfl) ⟨3802509, by rfl⟩ : syracuseStep 40560101 = 7605019) B7605019
theorem B2813723 : Blo 830350 2813723 := bstep (se 1 (by rfl) ⟨2110292, by rfl⟩ : syracuseStep 2813723 = 4220585) B4220585
theorem B98801279 : Blo 830350 98801279 := bstep (se 1 (by rfl) ⟨74100959, by rfl⟩ : syracuseStep 98801279 = 148201919) B148201919
theorem B27040067 : Blo 830350 27040067 := bstep (se 1 (by rfl) ⟨20280050, by rfl⟩ : syracuseStep 27040067 = 40560101) B40560101
theorem B1875815 : Blo 830350 1875815 := bstep (se 1 (by rfl) ⟨1406861, by rfl⟩ : syracuseStep 1875815 = 2813723) B2813723
theorem B831423 : Blo 830350 831423 := bstep (se 1 (by rfl) ⟨623567, by rfl⟩ : syracuseStep 831423 = 1247135) B1247135
theorem B15979679 : Blo 830350 15979679 := bstep (se 1 (by rfl) ⟨11984759, by rfl⟩ : syracuseStep 15979679 = 23969519) B23969519
theorem B1402663 : Blo 830350 1402663 := bstep (se 1 (by rfl) ⟨1051997, by rfl⟩ : syracuseStep 1402663 = 2103995) B2103995
theorem B1870217 : Blo 830350 1870217 := bstep (se 2 (by rfl) ⟨701331, by rfl⟩ : syracuseStep 1870217 = 1402663) B1402663
theorem B10653119 : Blo 830350 10653119 := bstep (se 1 (by rfl) ⟨7989839, by rfl⟩ : syracuseStep 10653119 = 15979679) B15979679
theorem B65867519 : Blo 830350 65867519 := bstep (se 1 (by rfl) ⟨49400639, by rfl⟩ : syracuseStep 65867519 = 98801279) B98801279
theorem B18026711 : Blo 830350 18026711 := bstep (se 1 (by rfl) ⟨13520033, by rfl⟩ : syracuseStep 18026711 = 27040067) B27040067
theorem B1250543 : Blo 830350 1250543 := bstep (se 1 (by rfl) ⟨937907, by rfl⟩ : syracuseStep 1250543 = 1875815) B1875815
theorem B1246811 : Blo 830350 1246811 := bstep (se 1 (by rfl) ⟨935108, by rfl⟩ : syracuseStep 1246811 = 1870217) B1870217
theorem B175646717 : Blo 830350 175646717 := bstep (se 3 (by rfl) ⟨32933759, by rfl⟩ : syracuseStep 175646717 = 65867519) B65867519
theorem B833695 : Blo 830350 833695 := bstep (se 1 (by rfl) ⟨625271, by rfl⟩ : syracuseStep 833695 = 1250543) B1250543
theorem B7102079 : Blo 830350 7102079 := bstep (se 1 (by rfl) ⟨5326559, by rfl⟩ : syracuseStep 7102079 = 10653119) B10653119
theorem B12017807 : Blo 830350 12017807 := bstep (se 1 (by rfl) ⟨9013355, by rfl⟩ : syracuseStep 12017807 = 18026711) B18026711
theorem B831207 : Blo 830350 831207 := bstep (se 1 (by rfl) ⟨623405, by rfl⟩ : syracuseStep 831207 = 1246811) B1246811
theorem B4734719 : Blo 830350 4734719 := bstep (se 1 (by rfl) ⟨3551039, by rfl⟩ : syracuseStep 4734719 = 7102079) B7102079
theorem B8011871 : Blo 830350 8011871 := bstep (se 1 (by rfl) ⟨6008903, by rfl⟩ : syracuseStep 8011871 = 12017807) B12017807
theorem B117097811 : Blo 830350 117097811 := bstep (se 1 (by rfl) ⟨87823358, by rfl⟩ : syracuseStep 117097811 = 175646717) B175646717
theorem B5341247 : Blo 830350 5341247 := bstep (se 1 (by rfl) ⟨4005935, by rfl⟩ : syracuseStep 5341247 = 8011871) B8011871
theorem B3156479 : Blo 830350 3156479 := bstep (se 1 (by rfl) ⟨2367359, by rfl⟩ : syracuseStep 3156479 = 4734719) B4734719
theorem B78065207 : Blo 830350 78065207 := bstep (se 1 (by rfl) ⟨58548905, by rfl⟩ : syracuseStep 78065207 = 117097811) B117097811
theorem B2104319 : Blo 830350 2104319 := bstep (se 1 (by rfl) ⟨1578239, by rfl⟩ : syracuseStep 2104319 = 3156479) B3156479
theorem B52043471 : Blo 830350 52043471 := bstep (se 1 (by rfl) ⟨39032603, by rfl⟩ : syracuseStep 52043471 = 78065207) B78065207
theorem B3560831 : Blo 830350 3560831 := bstep (se 1 (by rfl) ⟨2670623, by rfl⟩ : syracuseStep 3560831 = 5341247) B5341247
theorem B2373887 : Blo 830350 2373887 := bstep (se 1 (by rfl) ⟨1780415, by rfl⟩ : syracuseStep 2373887 = 3560831) B3560831
theorem B1402879 : Blo 830350 1402879 := bstep (se 1 (by rfl) ⟨1052159, by rfl⟩ : syracuseStep 1402879 = 2104319) B2104319
theorem B34695647 : Blo 830350 34695647 := bstep (se 1 (by rfl) ⟨26021735, by rfl⟩ : syracuseStep 34695647 = 52043471) B52043471
theorem B1870505 : Blo 830350 1870505 := bstep (se 2 (by rfl) ⟨701439, by rfl⟩ : syracuseStep 1870505 = 1402879) B1402879
theorem B1582591 : Blo 830350 1582591 := bstep (se 1 (by rfl) ⟨1186943, by rfl⟩ : syracuseStep 1582591 = 2373887) B2373887
theorem B23130431 : Blo 830350 23130431 := bstep (se 1 (by rfl) ⟨17347823, by rfl⟩ : syracuseStep 23130431 = 34695647) B34695647
theorem B1247003 : Blo 830350 1247003 := bstep (se 1 (by rfl) ⟨935252, by rfl⟩ : syracuseStep 1247003 = 1870505) B1870505
theorem B2110121 : Blo 830350 2110121 := bstep (se 2 (by rfl) ⟨791295, by rfl⟩ : syracuseStep 2110121 = 1582591) B1582591
theorem B15420287 : Blo 830350 15420287 := bstep (se 1 (by rfl) ⟨11565215, by rfl⟩ : syracuseStep 15420287 = 23130431) B23130431
theorem B831335 : Blo 830350 831335 := bstep (se 1 (by rfl) ⟨623501, by rfl⟩ : syracuseStep 831335 = 1247003) B1247003
theorem B10280191 : Blo 830350 10280191 := bstep (se 1 (by rfl) ⟨7710143, by rfl⟩ : syracuseStep 10280191 = 15420287) B15420287
theorem B1406747 : Blo 830350 1406747 := bstep (se 1 (by rfl) ⟨1055060, by rfl⟩ : syracuseStep 1406747 = 2110121) B2110121
theorem B13706921 : Blo 830350 13706921 := bstep (se 2 (by rfl) ⟨5140095, by rfl⟩ : syracuseStep 13706921 = 10280191) B10280191
theorem B937831 : Blo 830350 937831 := bstep (se 1 (by rfl) ⟨703373, by rfl⟩ : syracuseStep 937831 = 1406747) B1406747
theorem B1250441 : Blo 830350 1250441 := bstep (se 2 (by rfl) ⟨468915, by rfl⟩ : syracuseStep 1250441 = 937831) B937831
theorem B9137947 : Blo 830350 9137947 := bstep (se 1 (by rfl) ⟨6853460, by rfl⟩ : syracuseStep 9137947 = 13706921) B13706921
theorem B833627 : Blo 830350 833627 := bstep (se 1 (by rfl) ⟨625220, by rfl⟩ : syracuseStep 833627 = 1250441) B1250441
theorem B12183929 : Blo 830350 12183929 := bstep (se 2 (by rfl) ⟨4568973, by rfl⟩ : syracuseStep 12183929 = 9137947) B9137947
theorem B8122619 : Blo 830350 8122619 := bstep (se 1 (by rfl) ⟨6091964, by rfl⟩ : syracuseStep 8122619 = 12183929) B12183929
theorem B21660317 : Blo 830350 21660317 := bstep (se 3 (by rfl) ⟨4061309, by rfl⟩ : syracuseStep 21660317 = 8122619) B8122619
theorem B14440211 : Blo 830350 14440211 := bstep (se 1 (by rfl) ⟨10830158, by rfl⟩ : syracuseStep 14440211 = 21660317) B21660317
theorem B9626807 : Blo 830350 9626807 := bstep (se 1 (by rfl) ⟨7220105, by rfl⟩ : syracuseStep 9626807 = 14440211) B14440211
theorem B25671485 : Blo 830350 25671485 := bstep (se 3 (by rfl) ⟨4813403, by rfl⟩ : syracuseStep 25671485 = 9626807) B9626807
theorem B17114323 : Blo 830350 17114323 := bstep (se 1 (by rfl) ⟨12835742, by rfl⟩ : syracuseStep 17114323 = 25671485) B25671485
theorem B22819097 : Blo 830350 22819097 := bstep (se 2 (by rfl) ⟨8557161, by rfl⟩ : syracuseStep 22819097 = 17114323) B17114323
theorem B15212731 : Blo 830350 15212731 := bstep (se 1 (by rfl) ⟨11409548, by rfl⟩ : syracuseStep 15212731 = 22819097) B22819097
theorem B20283641 : Blo 830350 20283641 := bstep (se 2 (by rfl) ⟨7606365, by rfl⟩ : syracuseStep 20283641 = 15212731) B15212731
theorem B13522427 : Blo 830350 13522427 := bstep (se 1 (by rfl) ⟨10141820, by rfl⟩ : syracuseStep 13522427 = 20283641) B20283641
theorem B9014951 : Blo 830350 9014951 := bstep (se 1 (by rfl) ⟨6761213, by rfl⟩ : syracuseStep 9014951 = 13522427) B13522427
theorem B6009967 : Blo 830350 6009967 := bstep (se 1 (by rfl) ⟨4507475, by rfl⟩ : syracuseStep 6009967 = 9014951) B9014951
theorem B8013289 : Blo 830350 8013289 := bstep (se 2 (by rfl) ⟨3004983, by rfl⟩ : syracuseStep 8013289 = 6009967) B6009967
theorem B10684385 : Blo 830350 10684385 := bstep (se 2 (by rfl) ⟨4006644, by rfl⟩ : syracuseStep 10684385 = 8013289) B8013289
theorem B7122923 : Blo 830350 7122923 := bstep (se 1 (by rfl) ⟨5342192, by rfl⟩ : syracuseStep 7122923 = 10684385) B10684385
theorem B4748615 : Blo 830350 4748615 := bstep (se 1 (by rfl) ⟨3561461, by rfl⟩ : syracuseStep 4748615 = 7122923) B7122923
theorem B3165743 : Blo 830350 3165743 := bstep (se 1 (by rfl) ⟨2374307, by rfl⟩ : syracuseStep 3165743 = 4748615) B4748615
theorem B2110495 : Blo 830350 2110495 := bstep (se 1 (by rfl) ⟨1582871, by rfl⟩ : syracuseStep 2110495 = 3165743) B3165743
theorem B2813993 : Blo 830350 2813993 := bstep (se 2 (by rfl) ⟨1055247, by rfl⟩ : syracuseStep 2813993 = 2110495) B2110495
theorem B1875995 : Blo 830350 1875995 := bstep (se 1 (by rfl) ⟨1406996, by rfl⟩ : syracuseStep 1875995 = 2813993) B2813993
theorem B1250663 : Blo 830350 1250663 := bstep (se 1 (by rfl) ⟨937997, by rfl⟩ : syracuseStep 1250663 = 1875995) B1875995
theorem B833775 : Blo 830350 833775 := bstep (se 1 (by rfl) ⟨625331, by rfl⟩ : syracuseStep 833775 = 1250663) B1250663

theorem C0 (j : ℕ) (h1 : 207587 ≤ j) (h2 : j ≤ 208286) : Blo 830350 (4 * j + 3) := by
  interval_cases j
  · exact B830351
  · exact B830355
  · exact B830359
  · exact B830363
  · exact B830367
  · exact B830371
  · exact B830375
  · exact B830379
  · exact B830383
  · exact B830387
  · exact B830391
  · exact B830395
  · exact B830399
  · exact B830403
  · exact B830407
  · exact B830411
  · exact B830415
  · exact B830419
  · exact B830423
  · exact B830427
  · exact B830431
  · exact B830435
  · exact B830439
  · exact B830443
  · exact B830447
  · exact B830451
  · exact B830455
  · exact B830459
  · exact B830463
  · exact B830467
  · exact B830471
  · exact B830475
  · exact B830479
  · exact B830483
  · exact B830487
  · exact B830491
  · exact B830495
  · exact B830499
  · exact B830503
  · exact B830507
  · exact B830511
  · exact B830515
  · exact B830519
  · exact B830523
  · exact B830527
  · exact B830531
  · exact B830535
  · exact B830539
  · exact B830543
  · exact B830547
  · exact B830551
  · exact B830555
  · exact B830559
  · exact B830563
  · exact B830567
  · exact B830571
  · exact B830575
  · exact B830579
  · exact B830583
  · exact B830587
  · exact B830591
  · exact B830595
  · exact B830599
  · exact B830603
  · exact B830607
  · exact B830611
  · exact B830615
  · exact B830619
  · exact B830623
  · exact B830627
  · exact B830631
  · exact B830635
  · exact B830639
  · exact B830643
  · exact B830647
  · exact B830651
  · exact B830655
  · exact B830659
  · exact B830663
  · exact B830667
  · exact B830671
  · exact B830675
  · exact B830679
  · exact B830683
  · exact B830687
  · exact B830691
  · exact B830695
  · exact B830699
  · exact B830703
  · exact B830707
  · exact B830711
  · exact B830715
  · exact B830719
  · exact B830723
  · exact B830727
  · exact B830731
  · exact B830735
  · exact B830739
  · exact B830743
  · exact B830747
  · exact B830751
  · exact B830755
  · exact B830759
  · exact B830763
  · exact B830767
  · exact B830771
  · exact B830775
  · exact B830779
  · exact B830783
  · exact B830787
  · exact B830791
  · exact B830795
  · exact B830799
  · exact B830803
  · exact B830807
  · exact B830811
  · exact B830815
  · exact B830819
  · exact B830823
  · exact B830827
  · exact B830831
  · exact B830835
  · exact B830839
  · exact B830843
  · exact B830847
  · exact B830851
  · exact B830855
  · exact B830859
  · exact B830863
  · exact B830867
  · exact B830871
  · exact B830875
  · exact B830879
  · exact B830883
  · exact B830887
  · exact B830891
  · exact B830895
  · exact B830899
  · exact B830903
  · exact B830907
  · exact B830911
  · exact B830915
  · exact B830919
  · exact B830923
  · exact B830927
  · exact B830931
  · exact B830935
  · exact B830939
  · exact B830943
  · exact B830947
  · exact B830951
  · exact B830955
  · exact B830959
  · exact B830963
  · exact B830967
  · exact B830971
  · exact B830975
  · exact B830979
  · exact B830983
  · exact B830987
  · exact B830991
  · exact B830995
  · exact B830999
  · exact B831003
  · exact B831007
  · exact B831011
  · exact B831015
  · exact B831019
  · exact B831023
  · exact B831027
  · exact B831031
  · exact B831035
  · exact B831039
  · exact B831043
  · exact B831047
  · exact B831051
  · exact B831055
  · exact B831059
  · exact B831063
  · exact B831067
  · exact B831071
  · exact B831075
  · exact B831079
  · exact B831083
  · exact B831087
  · exact B831091
  · exact B831095
  · exact B831099
  · exact B831103
  · exact B831107
  · exact B831111
  · exact B831115
  · exact B831119
  · exact B831123
  · exact B831127
  · exact B831131
  · exact B831135
  · exact B831139
  · exact B831143
  · exact B831147
  · exact B831151
  · exact B831155
  · exact B831159
  · exact B831163
  · exact B831167
  · exact B831171
  · exact B831175
  · exact B831179
  · exact B831183
  · exact B831187
  · exact B831191
  · exact B831195
  · exact B831199
  · exact B831203
  · exact B831207
  · exact B831211
  · exact B831215
  · exact B831219
  · exact B831223
  · exact B831227
  · exact B831231
  · exact B831235
  · exact B831239
  · exact B831243
  · exact B831247
  · exact B831251
  · exact B831255
  · exact B831259
  · exact B831263
  · exact B831267
  · exact B831271
  · exact B831275
  · exact B831279
  · exact B831283
  · exact B831287
  · exact B831291
  · exact B831295
  · exact B831299
  · exact B831303
  · exact B831307
  · exact B831311
  · exact B831315
  · exact B831319
  · exact B831323
  · exact B831327
  · exact B831331
  · exact B831335
  · exact B831339
  · exact B831343
  · exact B831347
  · exact B831351
  · exact B831355
  · exact B831359
  · exact B831363
  · exact B831367
  · exact B831371
  · exact B831375
  · exact B831379
  · exact B831383
  · exact B831387
  · exact B831391
  · exact B831395
  · exact B831399
  · exact B831403
  · exact B831407
  · exact B831411
  · exact B831415
  · exact B831419
  · exact B831423
  · exact B831427
  · exact B831431
  · exact B831435
  · exact B831439
  · exact B831443
  · exact B831447
  · exact B831451
  · exact B831455
  · exact B831459
  · exact B831463
  · exact B831467
  · exact B831471
  · exact B831475
  · exact B831479
  · exact B831483
  · exact B831487
  · exact B831491
  · exact B831495
  · exact B831499
  · exact B831503
  · exact B831507
  · exact B831511
  · exact B831515
  · exact B831519
  · exact B831523
  · exact B831527
  · exact B831531
  · exact B831535
  · exact B831539
  · exact B831543
  · exact B831547
  · exact B831551
  · exact B831555
  · exact B831559
  · exact B831563
  · exact B831567
  · exact B831571
  · exact B831575
  · exact B831579
  · exact B831583
  · exact B831587
  · exact B831591
  · exact B831595
  · exact B831599
  · exact B831603
  · exact B831607
  · exact B831611
  · exact B831615
  · exact B831619
  · exact B831623
  · exact B831627
  · exact B831631
  · exact B831635
  · exact B831639
  · exact B831643
  · exact B831647
  · exact B831651
  · exact B831655
  · exact B831659
  · exact B831663
  · exact B831667
  · exact B831671
  · exact B831675
  · exact B831679
  · exact B831683
  · exact B831687
  · exact B831691
  · exact B831695
  · exact B831699
  · exact B831703
  · exact B831707
  · exact B831711
  · exact B831715
  · exact B831719
  · exact B831723
  · exact B831727
  · exact B831731
  · exact B831735
  · exact B831739
  · exact B831743
  · exact B831747
  · exact B831751
  · exact B831755
  · exact B831759
  · exact B831763
  · exact B831767
  · exact B831771
  · exact B831775
  · exact B831779
  · exact B831783
  · exact B831787
  · exact B831791
  · exact B831795
  · exact B831799
  · exact B831803
  · exact B831807
  · exact B831811
  · exact B831815
  · exact B831819
  · exact B831823
  · exact B831827
  · exact B831831
  · exact B831835
  · exact B831839
  · exact B831843
  · exact B831847
  · exact B831851
  · exact B831855
  · exact B831859
  · exact B831863
  · exact B831867
  · exact B831871
  · exact B831875
  · exact B831879
  · exact B831883
  · exact B831887
  · exact B831891
  · exact B831895
  · exact B831899
  · exact B831903
  · exact B831907
  · exact B831911
  · exact B831915
  · exact B831919
  · exact B831923
  · exact B831927
  · exact B831931
  · exact B831935
  · exact B831939
  · exact B831943
  · exact B831947
  · exact B831951
  · exact B831955
  · exact B831959
  · exact B831963
  · exact B831967
  · exact B831971
  · exact B831975
  · exact B831979
  · exact B831983
  · exact B831987
  · exact B831991
  · exact B831995
  · exact B831999
  · exact B832003
  · exact B832007
  · exact B832011
  · exact B832015
  · exact B832019
  · exact B832023
  · exact B832027
  · exact B832031
  · exact B832035
  · exact B832039
  · exact B832043
  · exact B832047
  · exact B832051
  · exact B832055
  · exact B832059
  · exact B832063
  · exact B832067
  · exact B832071
  · exact B832075
  · exact B832079
  · exact B832083
  · exact B832087
  · exact B832091
  · exact B832095
  · exact B832099
  · exact B832103
  · exact B832107
  · exact B832111
  · exact B832115
  · exact B832119
  · exact B832123
  · exact B832127
  · exact B832131
  · exact B832135
  · exact B832139
  · exact B832143
  · exact B832147
  · exact B832151
  · exact B832155
  · exact B832159
  · exact B832163
  · exact B832167
  · exact B832171
  · exact B832175
  · exact B832179
  · exact B832183
  · exact B832187
  · exact B832191
  · exact B832195
  · exact B832199
  · exact B832203
  · exact B832207
  · exact B832211
  · exact B832215
  · exact B832219
  · exact B832223
  · exact B832227
  · exact B832231
  · exact B832235
  · exact B832239
  · exact B832243
  · exact B832247
  · exact B832251
  · exact B832255
  · exact B832259
  · exact B832263
  · exact B832267
  · exact B832271
  · exact B832275
  · exact B832279
  · exact B832283
  · exact B832287
  · exact B832291
  · exact B832295
  · exact B832299
  · exact B832303
  · exact B832307
  · exact B832311
  · exact B832315
  · exact B832319
  · exact B832323
  · exact B832327
  · exact B832331
  · exact B832335
  · exact B832339
  · exact B832343
  · exact B832347
  · exact B832351
  · exact B832355
  · exact B832359
  · exact B832363
  · exact B832367
  · exact B832371
  · exact B832375
  · exact B832379
  · exact B832383
  · exact B832387
  · exact B832391
  · exact B832395
  · exact B832399
  · exact B832403
  · exact B832407
  · exact B832411
  · exact B832415
  · exact B832419
  · exact B832423
  · exact B832427
  · exact B832431
  · exact B832435
  · exact B832439
  · exact B832443
  · exact B832447
  · exact B832451
  · exact B832455
  · exact B832459
  · exact B832463
  · exact B832467
  · exact B832471
  · exact B832475
  · exact B832479
  · exact B832483
  · exact B832487
  · exact B832491
  · exact B832495
  · exact B832499
  · exact B832503
  · exact B832507
  · exact B832511
  · exact B832515
  · exact B832519
  · exact B832523
  · exact B832527
  · exact B832531
  · exact B832535
  · exact B832539
  · exact B832543
  · exact B832547
  · exact B832551
  · exact B832555
  · exact B832559
  · exact B832563
  · exact B832567
  · exact B832571
  · exact B832575
  · exact B832579
  · exact B832583
  · exact B832587
  · exact B832591
  · exact B832595
  · exact B832599
  · exact B832603
  · exact B832607
  · exact B832611
  · exact B832615
  · exact B832619
  · exact B832623
  · exact B832627
  · exact B832631
  · exact B832635
  · exact B832639
  · exact B832643
  · exact B832647
  · exact B832651
  · exact B832655
  · exact B832659
  · exact B832663
  · exact B832667
  · exact B832671
  · exact B832675
  · exact B832679
  · exact B832683
  · exact B832687
  · exact B832691
  · exact B832695
  · exact B832699
  · exact B832703
  · exact B832707
  · exact B832711
  · exact B832715
  · exact B832719
  · exact B832723
  · exact B832727
  · exact B832731
  · exact B832735
  · exact B832739
  · exact B832743
  · exact B832747
  · exact B832751
  · exact B832755
  · exact B832759
  · exact B832763
  · exact B832767
  · exact B832771
  · exact B832775
  · exact B832779
  · exact B832783
  · exact B832787
  · exact B832791
  · exact B832795
  · exact B832799
  · exact B832803
  · exact B832807
  · exact B832811
  · exact B832815
  · exact B832819
  · exact B832823
  · exact B832827
  · exact B832831
  · exact B832835
  · exact B832839
  · exact B832843
  · exact B832847
  · exact B832851
  · exact B832855
  · exact B832859
  · exact B832863
  · exact B832867
  · exact B832871
  · exact B832875
  · exact B832879
  · exact B832883
  · exact B832887
  · exact B832891
  · exact B832895
  · exact B832899
  · exact B832903
  · exact B832907
  · exact B832911
  · exact B832915
  · exact B832919
  · exact B832923
  · exact B832927
  · exact B832931
  · exact B832935
  · exact B832939
  · exact B832943
  · exact B832947
  · exact B832951
  · exact B832955
  · exact B832959
  · exact B832963
  · exact B832967
  · exact B832971
  · exact B832975
  · exact B832979
  · exact B832983
  · exact B832987
  · exact B832991
  · exact B832995
  · exact B832999
  · exact B833003
  · exact B833007
  · exact B833011
  · exact B833015
  · exact B833019
  · exact B833023
  · exact B833027
  · exact B833031
  · exact B833035
  · exact B833039
  · exact B833043
  · exact B833047
  · exact B833051
  · exact B833055
  · exact B833059
  · exact B833063
  · exact B833067
  · exact B833071
  · exact B833075
  · exact B833079
  · exact B833083
  · exact B833087
  · exact B833091
  · exact B833095
  · exact B833099
  · exact B833103
  · exact B833107
  · exact B833111
  · exact B833115
  · exact B833119
  · exact B833123
  · exact B833127
  · exact B833131
  · exact B833135
  · exact B833139
  · exact B833143
  · exact B833147

theorem C1 (j : ℕ) (h1 : 208287 ≤ j) (h2 : j ≤ 208586) : Blo 830350 (4 * j + 3) := by
  interval_cases j
  · exact B833151
  · exact B833155
  · exact B833159
  · exact B833163
  · exact B833167
  · exact B833171
  · exact B833175
  · exact B833179
  · exact B833183
  · exact B833187
  · exact B833191
  · exact B833195
  · exact B833199
  · exact B833203
  · exact B833207
  · exact B833211
  · exact B833215
  · exact B833219
  · exact B833223
  · exact B833227
  · exact B833231
  · exact B833235
  · exact B833239
  · exact B833243
  · exact B833247
  · exact B833251
  · exact B833255
  · exact B833259
  · exact B833263
  · exact B833267
  · exact B833271
  · exact B833275
  · exact B833279
  · exact B833283
  · exact B833287
  · exact B833291
  · exact B833295
  · exact B833299
  · exact B833303
  · exact B833307
  · exact B833311
  · exact B833315
  · exact B833319
  · exact B833323
  · exact B833327
  · exact B833331
  · exact B833335
  · exact B833339
  · exact B833343
  · exact B833347
  · exact B833351
  · exact B833355
  · exact B833359
  · exact B833363
  · exact B833367
  · exact B833371
  · exact B833375
  · exact B833379
  · exact B833383
  · exact B833387
  · exact B833391
  · exact B833395
  · exact B833399
  · exact B833403
  · exact B833407
  · exact B833411
  · exact B833415
  · exact B833419
  · exact B833423
  · exact B833427
  · exact B833431
  · exact B833435
  · exact B833439
  · exact B833443
  · exact B833447
  · exact B833451
  · exact B833455
  · exact B833459
  · exact B833463
  · exact B833467
  · exact B833471
  · exact B833475
  · exact B833479
  · exact B833483
  · exact B833487
  · exact B833491
  · exact B833495
  · exact B833499
  · exact B833503
  · exact B833507
  · exact B833511
  · exact B833515
  · exact B833519
  · exact B833523
  · exact B833527
  · exact B833531
  · exact B833535
  · exact B833539
  · exact B833543
  · exact B833547
  · exact B833551
  · exact B833555
  · exact B833559
  · exact B833563
  · exact B833567
  · exact B833571
  · exact B833575
  · exact B833579
  · exact B833583
  · exact B833587
  · exact B833591
  · exact B833595
  · exact B833599
  · exact B833603
  · exact B833607
  · exact B833611
  · exact B833615
  · exact B833619
  · exact B833623
  · exact B833627
  · exact B833631
  · exact B833635
  · exact B833639
  · exact B833643
  · exact B833647
  · exact B833651
  · exact B833655
  · exact B833659
  · exact B833663
  · exact B833667
  · exact B833671
  · exact B833675
  · exact B833679
  · exact B833683
  · exact B833687
  · exact B833691
  · exact B833695
  · exact B833699
  · exact B833703
  · exact B833707
  · exact B833711
  · exact B833715
  · exact B833719
  · exact B833723
  · exact B833727
  · exact B833731
  · exact B833735
  · exact B833739
  · exact B833743
  · exact B833747
  · exact B833751
  · exact B833755
  · exact B833759
  · exact B833763
  · exact B833767
  · exact B833771
  · exact B833775
  · exact B833779
  · exact B833783
  · exact B833787
  · exact B833791
  · exact B833795
  · exact B833799
  · exact B833803
  · exact B833807
  · exact B833811
  · exact B833815
  · exact B833819
  · exact B833823
  · exact B833827
  · exact B833831
  · exact B833835
  · exact B833839
  · exact B833843
  · exact B833847
  · exact B833851
  · exact B833855
  · exact B833859
  · exact B833863
  · exact B833867
  · exact B833871
  · exact B833875
  · exact B833879
  · exact B833883
  · exact B833887
  · exact B833891
  · exact B833895
  · exact B833899
  · exact B833903
  · exact B833907
  · exact B833911
  · exact B833915
  · exact B833919
  · exact B833923
  · exact B833927
  · exact B833931
  · exact B833935
  · exact B833939
  · exact B833943
  · exact B833947
  · exact B833951
  · exact B833955
  · exact B833959
  · exact B833963
  · exact B833967
  · exact B833971
  · exact B833975
  · exact B833979
  · exact B833983
  · exact B833987
  · exact B833991
  · exact B833995
  · exact B833999
  · exact B834003
  · exact B834007
  · exact B834011
  · exact B834015
  · exact B834019
  · exact B834023
  · exact B834027
  · exact B834031
  · exact B834035
  · exact B834039
  · exact B834043
  · exact B834047
  · exact B834051
  · exact B834055
  · exact B834059
  · exact B834063
  · exact B834067
  · exact B834071
  · exact B834075
  · exact B834079
  · exact B834083
  · exact B834087
  · exact B834091
  · exact B834095
  · exact B834099
  · exact B834103
  · exact B834107
  · exact B834111
  · exact B834115
  · exact B834119
  · exact B834123
  · exact B834127
  · exact B834131
  · exact B834135
  · exact B834139
  · exact B834143
  · exact B834147
  · exact B834151
  · exact B834155
  · exact B834159
  · exact B834163
  · exact B834167
  · exact B834171
  · exact B834175
  · exact B834179
  · exact B834183
  · exact B834187
  · exact B834191
  · exact B834195
  · exact B834199
  · exact B834203
  · exact B834207
  · exact B834211
  · exact B834215
  · exact B834219
  · exact B834223
  · exact B834227
  · exact B834231
  · exact B834235
  · exact B834239
  · exact B834243
  · exact B834247
  · exact B834251
  · exact B834255
  · exact B834259
  · exact B834263
  · exact B834267
  · exact B834271
  · exact B834275
  · exact B834279
  · exact B834283
  · exact B834287
  · exact B834291
  · exact B834295
  · exact B834299
  · exact B834303
  · exact B834307
  · exact B834311
  · exact B834315
  · exact B834319
  · exact B834323
  · exact B834327
  · exact B834331
  · exact B834335
  · exact B834339
  · exact B834343
  · exact B834347

theorem solution (m : ℕ) (hlo : 830350 ≤ m) (hhi : m ≤ 834350) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 207587 ≤ j := by omega
    have hj2 : j ≤ 208586 := by omega
    have hb : Blo 830350 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 208287 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
