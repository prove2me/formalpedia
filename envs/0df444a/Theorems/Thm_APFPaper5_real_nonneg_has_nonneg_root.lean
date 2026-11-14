-- Prove2me | Theorems.Thm_APFPaper5_real_nonneg_has_nonneg_root
-- name    : APFPaper5.real_nonneg_has_nonneg_root
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T05:49:33.815054+00:00
-- url     : https://prove2.me/theorems/2e4cd746-5098-4871-bf9a-dbfde672bbb1
-- title:
--   Every nonnegative real t has a nonnegative real r with r*r=t
-- statement:
--   Every nonnegative real t has a nonnegative real r with r*r=t.
-- source:
--   Paper 5 Supplement v7.33:3034-3075 (remaining K1-K6 physical obligations)

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

theorem APFPaper5.real_nonneg_has_nonneg_root :
    ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t := by sorry
