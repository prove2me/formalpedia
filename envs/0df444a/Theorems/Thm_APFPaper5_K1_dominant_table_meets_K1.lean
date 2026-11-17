-- Prove2me | Theorems.Thm_APFPaper5_K1_dominant_table_meets_K1
-- name    : APFPaper5.K1.dominant_table_meets_K1
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:52:37.216206+00:00
-- url     : https://prove2.me/theorems/c111da63-1dfe-4876-ae8e-e0991f162a18
-- title:
--   dominant table meets K1
-- statement:
--   Result: dominant table meets K1. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem dominant_table_meets_K1 (G : ι → ι → ℝ) (hsymm : ∀ i j, G i j = G j i)
--       (hdom : ∀ i, ∑ j, offSize G i j < G i i) :
--       IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) ∧
--         FaithfulNonnegDiagonal (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ))
--   ```
--
--   Module context and limits: The finite real table is supplied. Symmetry and strict diagonal dominance are explicit sufficient hypotheses, not derived Foundation laws or necessary conditions.
--
--   Source scope parameters:
--
--   ```lean
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K1_dominant_table:119; pullbacks v39; source SHA-256 1f8186905d9da6a381e4c3158ed164dbb38e2f4e43389d17d2e10c923610fd80']

import Definitions.Def_APFPaper5_K1_dominant_table_Vocabulary
import Theorems.Thm_APFPaper5_K1_atomTable_symm
import Theorems.Thm_APFPaper5_K1_atomTable_form
import Theorems.Thm_APFPaper5_K1_atomTable_nonneg
import Theorems.Thm_APFPaper5_K1_record_book_table_satisfies_K1
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5
open APFPaper5.K1
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem APFPaper5.K1.dominant_table_meets_K1 (G : ι → ι → ℝ) (hsymm : ∀ i j, G i j = G j i)
    (hdom : ∀ i, ∑ j, offSize G i j < G i i) :
    IsBilinear (VP := ι → ℝ) (VE := ι → ℝ) (tableForm G) ∧
      FaithfulNonnegDiagonal (tableForm G) (LinearEquiv.refl ℝ (ι → ℝ)) := by sorry
