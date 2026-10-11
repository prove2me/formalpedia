-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_mul
-- name    : BookProof.ChapterWignerLittleGroup.act_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:52:34.238983+00:00
-- url     : https://prove2.me/theorems/a0ab961f-f584-4294-a5cd-dcb9b0e8c984
-- title:
--   `BookProof.ChapterWignerLittleGroup.act_mul` (A B X : Matrix (Fin 2) (Fin 2) ℂ) : act (A * B) X = act A (act B X)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.act_mul` (A B X : Matrix (Fin 2) (Fin 2) ℂ) : act (A * B) X = act A (act B X)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.act_mul`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.act_mul
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.act_mul (A B X : Matrix (Fin 2) (Fin 2) ℂ) :
    act (A * B) X = act A (act B X) := by sorry
