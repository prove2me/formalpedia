-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_det
-- name    : BookProof.ChapterWignerLittleGroup.act_det
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:51:52.913972+00:00
-- url     : https://prove2.me/theorems/84a13eff-c63d-48b4-a19b-53c424a97023
-- title:
--   `BookProof.ChapterWignerLittleGroup.act_det` (A X : Matrix (Fin 2) (Fin 2) ℂ) : (act A X).det = A.det * X.det * (starRingEnd ℂ) A.det
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.act_det` (A X : Matrix (Fin 2) (Fin 2) ℂ) : (act A X).det = A.det * X.det * (starRingEnd ℂ) A.det
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.act_det`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.act_det
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.act_det (A X : Matrix (Fin 2) (Fin 2) ℂ) :
    (act A X).det = A.det * X.det * (starRingEnd ℂ) A.det := by sorry
