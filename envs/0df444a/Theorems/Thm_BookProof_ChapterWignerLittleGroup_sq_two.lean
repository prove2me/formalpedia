-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_sq_two
-- name    : BookProof.ChapterWignerLittleGroup.sq_two
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:52:27.14575+00:00
-- url     : https://prove2.me/theorems/9cab31a4-c815-4fd2-8cb3-489a4e6164c5
-- title:
--   `BookProof.ChapterWignerLittleGroup.sq_two` (M : Matrix (Fin 2) (Fin 2) ℂ) : M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.sq_two` (M : Matrix (Fin 2) (Fin 2) ℂ) : M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.sq_two`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.sq_two
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.sq_two (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by sorry
