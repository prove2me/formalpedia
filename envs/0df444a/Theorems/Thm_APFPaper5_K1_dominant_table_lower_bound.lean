-- Prove2me | Theorems.Thm_APFPaper5_K1_dominant_table_lower_bound
-- name    : APFPaper5.K1.dominant_table_lower_bound
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T14:51:16.321076+00:00
-- url     : https://prove2.me/theorems/2acb6e0d-2aac-4098-92e5-2e723694bbbd
-- title:
--   dominant table lower bound
-- statement:
--   Result: dominant table lower bound. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem dominant_table_lower_bound (G : ι → ι → ℝ) (hsymm : ∀ i j, G i j = G j i) (x : ι → ℝ) :
--       ∑ i, 2 * ((G i i - ∑ j, offSize G i j) * (x i * x i)) ≤ 2 * tableForm G x x
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
--   ['Theorems.Thm_APFPaper5_K1_dominant_table:49; pullbacks v39; source SHA-256 1f8186905d9da6a381e4c3158ed164dbb38e2f4e43389d17d2e10c923610fd80']

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

theorem APFPaper5.K1.dominant_table_lower_bound (G : ι → ι → ℝ) (hsymm : ∀ i j, G i j = G j i) (x : ι → ℝ) :
    ∑ i, 2 * ((G i i - ∑ j, offSize G i j) * (x i * x i)) ≤ 2 * tableForm G x x := by sorry
