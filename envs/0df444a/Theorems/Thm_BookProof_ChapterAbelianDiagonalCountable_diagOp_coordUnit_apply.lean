-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_coordUnit_apply
-- name    : BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:18:11.639156+00:00
-- url     : https://prove2.me/theorems/271d6a05-c500-46b4-8e65-ad601e17f3a4
-- title:
--   `BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply` (i : ℕ) (f : Ell2C) (j : ℕ) : ((diagOp (coordUnit i) f : Ell2C) : ℕ → ℂ) j = if j = i then (f : ℕ → ℂ) i else 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonalCountable`.
--
--   `BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply` (i : ℕ) (f : Ell2C) (j : ℕ) : ((diagOp (coordUnit i) f : Ell2C) : ℕ → ℂ) j = if j = i then (f : ℕ → ℂ) i else 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply`.

-- Generated from ChapterAbelianDiagonalCountable.lean — theorem BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable


open scoped ENNReal

noncomputable section

theorem BookProof.ChapterAbelianDiagonalCountable.diagOp_coordUnit_apply (i : ℕ) (f : Ell2C) (j : ℕ) :
    ((diagOp (coordUnit i) f : Ell2C) : ℕ → ℂ) j = if j = i then (f : ℕ → ℂ) i else 0 := by sorry
