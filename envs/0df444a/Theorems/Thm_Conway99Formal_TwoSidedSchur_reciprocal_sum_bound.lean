-- Prove2me | Theorems.Thm_Conway99Formal_TwoSidedSchur_reciprocal_sum_bound
-- name    : Conway99Formal.TwoSidedSchur.reciprocal_sum_bound
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T06:11:11.345059+00:00
-- url     : https://prove2.me/theorems/aab20463-1aa9-4a42-9031-270b7b179ea2
-- title:
--   A reciprocal sum is minimized at the midpoint
-- statement:
--   g and e are finite row/column index types; L is a real g-by-e matrix, and x,y are vectors on the respective index sets. In the complementary-block results, both PSD inequalities use the same L and paired complementary matrices. The exact theorem type supplies the remaining premises.
--   For a real number a strictly between 0 and 28, the sum of reciprocals of the two complementary parts is at least 1/7.
--   \[\frac17\le\frac1a+\frac1{28-a}.\]
--   A scalar inequality used in the two-sided Schur argument; it has no graph assumption.
-- source:
--   Exact original Lean source: formalization/2026-10-03/two-sided-schur/TwoSidedSchur.lean#L81-L93; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 61d8a9ae110b34e6c9ea60c974ec342f79de6b77c383dd7b756583ac0b54a3e8. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/two-sided-schur/TwoSidedSchur.lean#L81-L93.

import Mathlib

namespace Conway99Formal.TwoSidedSchur
end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

open Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

theorem Conway99Formal.TwoSidedSchur.reciprocal_sum_bound (a : ℝ) (ha : 0 < a) (hb : a < 28) :
    1 / 7 ≤ 1 / a + 1 / (28 - a) := by sorry
