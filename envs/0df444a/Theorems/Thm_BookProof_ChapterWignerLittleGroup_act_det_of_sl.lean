-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_act_det_of_sl
-- name    : BookProof.ChapterWignerLittleGroup.act_det_of_sl
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:52:11.154347+00:00
-- url     : https://prove2.me/theorems/1b66d080-98f8-4528-984b-4f7cf4910b29
-- title:
--   `BookProof.ChapterWignerLittleGroup.act_det_of_sl` (A X : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) : (act A X).det = X.det
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.act_det_of_sl` (A X : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) : (act A X).det = X.det
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.act_det_of_sl`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.act_det_of_sl
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.act_det_of_sl (A X : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (act A X).det = X.det := by sorry
