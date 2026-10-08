-- Prove2me | Theorems.Thm_Conway99Formal_TwoSidedSchur_distinct_column_principal_test
-- name    : Conway99Formal.TwoSidedSchur.distinct_column_principal_test
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T06:11:10.691006+00:00
-- url     : https://prove2.me/theorems/dfd5a515-e236-46e1-a0ea-fded784b9fb9
-- title:
--   Complementary PSD blocks bound correlations of distinct columns
-- statement:
--   g and e are finite row/column index types; L is a real g-by-e matrix, and x,y are vectors on the respective index sets. In the complementary-block results, both PSD inequalities use the same L and paired complementary matrices. The exact theorem type supplies the remaining premises.
--   Let L have real entries indexed by finite sets g×e, and assume the two complementary block quadratic forms are positive semidefinite using the same L and complementary terms. For distinct columns j,k, the product of their remaining diagonal capacities, 196 minus each squared column norm, dominates their squared inner product.
--   \[(196-\|L_{\cdot j}\|^2)(196-\|L_{\cdot k}\|^2)\ge\left(\sum_i L_{ij}L_{ik}\right)^2.\]
--   A two-column principal-minor consequence of the paired PSD hypotheses. The shared L and complementary block assumptions are essential and preserved.
-- source:
--   Exact original Lean source: formalization/2026-10-03/two-sided-schur/TwoSidedSchur.lean#L153-L207; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 61d8a9ae110b34e6c9ea60c974ec342f79de6b77c383dd7b756583ac0b54a3e8. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/two-sided-schur/TwoSidedSchur.lean#L153-L207.

import Definitions.Def_TwoSidedSchur
import Mathlib

namespace Conway99Formal.TwoSidedSchur
end Conway99Formal.TwoSidedSchur

set_option autoImplicit false

/-! Quadratic-form consequences of one complementary pair of PSD blocks. -/

open Conway99Formal.TwoSidedSchur

open Matrix

variable {g e : Type*} [Fintype g] [Fintype e]

theorem Conway99Formal.TwoSidedSchur.distinct_column_principal_test [DecidableEq e]
    (L : Matrix g e ℝ) (h : ComplementaryPSD L) (j k : e) (hjk : j ≠ k) :
    (196 - normSq (fun i => L i j)) * (196 - normSq (fun i => L i k)) ≥
      (∑ i, L i j * L i k) ^ 2 := by sorry
