-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_star
-- name    : BookProof.ChapterAbelianDiagonalCountable.diagOp_star
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:17:46.946228+00:00
-- url     : https://prove2.me/theorems/d7d0f99d-590b-4bd8-a64a-7175e59933bd
-- title:
--   `BookProof.ChapterAbelianDiagonalCountable.diagOp_star` (d : EllInf) (f g : Ell2C) : (inner ℂ (diagOp d f) g : ℂ) = inner ℂ f (diagOp (star d) g)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianDiagonalCountable`.
--
--   `BookProof.ChapterAbelianDiagonalCountable.diagOp_star` (d : EllInf) (f g : Ell2C) : (inner ℂ (diagOp d f) g : ℂ) = inner ℂ f (diagOp (star d) g)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianDiagonalCountable.diagOp_star`.

-- Generated from ChapterAbelianDiagonalCountable.lean — theorem BookProof.ChapterAbelianDiagonalCountable.diagOp_star
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable


open scoped ENNReal

noncomputable section

theorem BookProof.ChapterAbelianDiagonalCountable.diagOp_star (d : EllInf) (f g : Ell2C) :
    (inner ℂ (diagOp d f) g : ℂ) = inner ℂ f (diagOp (star d) g) := by sorry
