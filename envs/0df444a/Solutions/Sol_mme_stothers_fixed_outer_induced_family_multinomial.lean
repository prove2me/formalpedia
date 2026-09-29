-- Prove2me | solution 1 for mme_stothers_fixed_outer_induced_family_multinomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:09:39.941794+00:00
-- url     : https://prove2.me/submissions/aa8f13b1-3a18-426f-8e99-2b427752e549

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_stothers_fixed_outer_hash_budget
import Theorems.Thm_mme_stothers_fixed_target_pruning_assembly

open MME BigOperators Filter

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.FixedInducedCountReduction

private theorem fixedMarginalCount_sum (m : ℕ) :
    ∑ j : Fin 9, fixedMarginalCount m j = fixedOuterLength m := by
  simp only [fixedMarginalCount]
  rw [← Finset.mul_sum]
  norm_num [fixedMarginalBaseCount, fixedOuterLength, fixedProfileScale,
    Fin.sum_univ_succ]
  ring

private theorem fixed_multinomial_eq_factorial_ratio (m : ℕ) :
    (Nat.multinomial Finset.univ
        (fun j : Fin 9 ↦ fixedMarginalBaseCount j * m) : ℝ) =
      ((fixedOuterLength m).factorial : ℝ) /
        ∏ j : Fin 9, ((fixedMarginalCount m j).factorial : ℝ) := by
  let f : Fin 9 → ℕ := fun j ↦ fixedMarginalBaseCount j * m
  let P : ℕ := ∏ j : Fin 9, (f j).factorial
  have hP : P ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun j _ ↦ Nat.factorial_ne_zero _
  have hsum : ∑ j : Fin 9, f j = fixedOuterLength m := by
    calc
      ∑ j : Fin 9, f j = ∑ j : Fin 9, fixedMarginalCount m j := by
        apply Finset.sum_congr rfl
        intro j _hj
        simp only [f, fixedMarginalCount, Nat.mul_comm]
      _ = fixedOuterLength m := fixedMarginalCount_sum m
  have hspec := Nat.multinomial_spec Finset.univ f
  have hspec' :
      P * Nat.multinomial Finset.univ f = (fixedOuterLength m).factorial := by
    simpa only [P, Finset.prod_filter, Finset.mem_univ, true_and, hsum]
      using hspec
  have hspecReal :
      (P : ℝ) * (Nat.multinomial Finset.univ f : ℝ) =
        ((fixedOuterLength m).factorial : ℝ) := by
    exact_mod_cast hspec'
  have hratio :
      (Nat.multinomial Finset.univ f : ℝ) =
        ((fixedOuterLength m).factorial : ℝ) / (P : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast hP)).2
    simpa only [mul_comm] using hspecReal
  rw [hratio]
  simp only [P, Nat.cast_prod, f, fixedMarginalCount, Nat.mul_comm]

end MME.StothersFourth.FixedInducedCountReduction

theorem solution :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ F : Finset (MME.StothersFourth.FixedExactOuterAddress m),
          MME.StothersFourth.FixedInducedModeDisjoint F ∧
          (Nat.multinomial Finset.univ
              (fun j : Fin 9 ↦
                MME.StothersFourth.fixedMarginalBaseCount j * m) : ℝ) *
            Real.exp
              (-C * Real.sqrt
                (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ≤
              (F.card : ℝ) := by
  refine ⟨1000000, by norm_num, ?_⟩
  filter_upwards [mme_stothers_fixed_outer_hash_budget] with m hm
  obtain ⟨E, hclosed, hbudget⟩ := hm
  obtain ⟨F, hF, hprune⟩ :=
    mme_stothers_fixed_target_pruning_assembly m E hclosed
  refine ⟨F, hF, ?_⟩
  rw [MME.StothersFourth.FixedInducedCountReduction.fixed_multinomial_eq_factorial_ratio]
  linarith
