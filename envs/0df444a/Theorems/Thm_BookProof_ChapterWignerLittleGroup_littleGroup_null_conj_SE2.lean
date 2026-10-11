-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_littleGroup_null_conj_SE2
-- name    : BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:53:53.813394+00:00
-- url     : https://prove2.me/theorems/ed0755cf-ae5a-4e53-81a1-3ffa54579ef7
-- title:
--   `BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2` (p : Fin 4 → ℝ) (hp0 : 0 < p 0) (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2` (p : Fin 4 → ℝ) (hp0 : 0 < p 0) (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) : ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ littleGroup p = (fun B => A * B * A⁻¹) '' SE2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
import Definitions.Def_ChapterLittleGroup
open BookProof.ChapterLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.littleGroup_null_conj_SE2 (p : Fin 4 → ℝ) (hp0 : 0 < p 0)
    (hshell : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      littleGroup p = (fun B => A * B * A⁻¹) '' SE2 := by sorry
