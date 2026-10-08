-- Prove2me | Theorems.Thm_BookProof_ChapterAbelianAtomicCondensation_atomProj_idem
-- name    : BookProof.ChapterAbelianAtomicCondensation.atomProj_idem
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:16:23.234242+00:00
-- url     : https://prove2.me/theorems/ec51ab8b-a4b0-4b81-8431-e65269a516d6
-- title:
--   `BookProof.ChapterAbelianAtomicCondensation.atomProj_idem` (i : ℕ) : (atomProj i).comp (atomProj i) = atomProj i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAbelianAtomicCondensation`.
--
--   `BookProof.ChapterAbelianAtomicCondensation.atomProj_idem` (i : ℕ) : (atomProj i).comp (atomProj i) = atomProj i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAbelianAtomicCondensation.atomProj_idem`.

-- Generated from ChapterAbelianAtomicCondensation.lean — theorem BookProof.ChapterAbelianAtomicCondensation.atomProj_idem
import Mathlib
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianAtomicCondensation


open scoped ENNReal

noncomputable section


open BookProof.ChapterAbelianDiagonalCountable

theorem BookProof.ChapterAbelianAtomicCondensation.atomProj_idem (i : ℕ) : (atomProj i).comp (atomProj i) = atomProj i := by sorry
