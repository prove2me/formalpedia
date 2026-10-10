-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_atomProj_apply
-- name    : BookProof.ChapterAbelianAtomicCondensation.atomProj_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:16:30.255561+00:00
-- url     : https://prove2.me/theorems/2988805b-fc79-4e25-b038-137bccaf8e40
-- title:
--   `BookProof.ChapterAbelianAtomicCondensation.atomProj_apply` (i : ℕ) (f : Ell2C) : atomProj i f = (f : ℕ → ℂ) i • atom i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianAtomicCondensation`.
--
--   `BookProof.ChapterAbelianAtomicCondensation.atomProj_apply` (i : ℕ) (f : Ell2C) : atomProj i f = (f : ℕ → ℂ) i • atom i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianAtomicCondensation.atomProj_apply`.

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.atomProj_apply
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

theorem BookProof.ChapterAbelianAtomicCondensation.atomProj_apply (i : ℕ) (f : Ell2C) : atomProj i f = (f : ℕ → ℂ) i • atom i := by sorry
