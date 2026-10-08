-- Prove2me | Theorems.Thm_Conway99Formal_TwoSidedSchur_complementary_block_sum
-- name    : Conway99Formal.TwoSidedSchur.complementary_block_sum
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T06:10:59.783707+00:00
-- url     : https://prove2.me/theorems/29b4db80-9c67-4bc6-9175-5c86cc57bc28
-- title:
--   The two literal complementary blocks sum to 28 times identity
-- statement:
--   g and e are finite row/column index types; L is a real g-by-e matrix, and x,y are vectors on the respective index sets. In the complementary-block results, both PSD inequalities use the same L and paired complementary matrices. The exact theorem type supplies the remaining premises.
--   For the source-defined firstBlock and secondBlock built from the same matrices K, W, and R, their sum is 28 times the identity on the combined row/column index type.
--   \[firstBlock(K,W,R)+secondBlock(K,W,R)=28I.\]
--   A definitional block-matrix identity for the same shared inputs; it is not a positivity statement by itself.
-- source:
--   Exact original Lean source: formalization/2026-10-03/two-sided-schur/TwoSidedSchur.lean#L237-L245; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 61d8a9ae110b34e6c9ea60c974ec342f79de6b77c383dd7b756583ac0b54a3e8. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/two-sided-schur/TwoSidedSchur.lean#L237-L245.

import Definitions.Def_TwoSidedSchur
import Mathlib

namespace Conway99Formal.TwoSidedSchur
end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

open Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

































variable {h : Type*} [Fintype h] [DecidableEq g] [DecidableEq h]

theorem Conway99Formal.TwoSidedSchur.complementary_block_sum (K : Matrix (g ⊕ h) (g ⊕ h) ℝ)
    (W : Matrix (g ⊕ h) h ℝ) (R : Matrix h h ℝ) :
    firstBlock K W R + secondBlock K W R = (28 : ℝ) • 1 := by sorry
