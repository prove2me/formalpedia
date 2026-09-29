-- Prove2me | solution 1 for mme_dwz_table2_balanced_rectangular_rows_one_MM_finite_extraction_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:15:45.228389+00:00
-- url     : https://prove2.me/submissions/851e71ee-6d51-4c31-81bc-cd6994635eaa

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_dwz_q6_rect013_exact_z_basis_router
import Theorems.Thm_mme_dwz_q6_rect031_exact_z_basis_router
import Theorems.Thm_mme_dwz_q6_rect103_exact_z_basis_router
import Theorems.Thm_mme_dwz_q6_rect301_exact_z_basis_router
import Theorems.Thm_mme_dwz_table2_balanced_rows_from_exact_one_letter_routers

open MME Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) →
          ∃ a b c : ℕ,
            TensorObj.Restrict (MMObj K a b c)
              (restrictedComponentPower K s m) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              (((((a * b * c) ^ 2) * ((a * b * c) ^ 2) *
                    ((a * b * c) ^ 2) : ℕ) : ℝ) ^ tau) := by
  exact mme_dwz_table2_balanced_rows_from_exact_one_letter_routers
    (mme_dwz_q6_rect013_exact_z_basis_router K)
    (mme_dwz_q6_rect031_exact_z_basis_router K)
    (mme_dwz_q6_rect103_exact_z_basis_router K)
    (mme_dwz_q6_rect301_exact_z_basis_router K)
    tau htau
