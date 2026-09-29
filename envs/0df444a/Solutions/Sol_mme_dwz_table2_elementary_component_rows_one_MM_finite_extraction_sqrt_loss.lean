-- Prove2me | solution 1 for mme_dwz_table2_elementary_component_rows_one_MM_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T06:29:24.733119+00:00
-- url     : https://prove2.me/submissions/b1225334-704e-47a4-8b14-ed887a20e6a2

import Theorems.Thm_mme_dwz_table2_automatic_elementary_rows_one_MM_exact
import Theorems.Thm_mme_dwz_table2_balanced_rectangular_rows_one_MM_finite_extraction_sqrt_loss

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem eligible_not_forced_is_balanced
    (s : Fin 15) (hs : s.val ≤ 8 ∨ s = 11)
    (hauto : ¬ (s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 6 ∨ s = 8 ∨ s = 11)) :
    s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7 := by
  fin_cases s <;> simp_all

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s.val ≤ 8 ∨ s = 11) →
          ∃ a b c : ℕ,
            TensorObj.Restrict (MMObj K a b c)
              (restrictedComponentPower K s m) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              (((((a * b * c) ^ 2) * ((a * b * c) ^ 2) *
                    ((a * b * c) ^ 2) : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hbalanced⟩ :=
    mme_dwz_table2_balanced_rectangular_rows_one_MM_finite_extraction_sqrt_loss
      (K := K) tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbalanced] with m hm
  intro s hs
  by_cases hauto :
      s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 6 ∨ s = 8 ∨ s = 11
  · obtain ⟨a, b, c, hrestrict, hexact⟩ :=
      mme_dwz_table2_automatic_elementary_rows_one_MM_exact
        (K := K) tau m s hauto
    refine ⟨a, b, c, hrestrict, ?_⟩
    let x : ℝ := ((componentBase tau s) ^
      (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)
    let z : ℝ := Real.sqrt
      (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))
    have hx : 0 ≤ x := by
      dsimp only [x]
      positivity
    have hCz : 0 ≤ C * z := mul_nonneg hC (Real.sqrt_nonneg _)
    have hloss : Real.exp (-C * z) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by nlinarith)
    calc
      x * Real.exp (-C * z) ≤ x * 1 :=
        mul_le_mul_of_nonneg_left hloss hx
      _ = x * Real.exp (-(0 : ℝ) * z) := by simp
      _ ≤ (((((a * b * c) ^ 2) * ((a * b * c) ^ 2) *
          ((a * b * c) ^ 2) : ℕ) : ℝ) ^ tau) := by
        simpa only [x, z] using hexact
  · have hbalancedRows : s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7 := by
      exact eligible_not_forced_is_balanced s hs hauto
    exact hm s hbalancedRows
