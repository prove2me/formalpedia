-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_restMom
-- name    : BookProof.ChapterWignerLittleGroup.hermOfMom_restMom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:52:58.736204+00:00
-- url     : https://prove2.me/theorems/b84e7e46-af52-41cc-abef-9ec11a38a629
-- title:
--   `BookProof.ChapterWignerLittleGroup.hermOfMom_restMom` (m : ℝ) : hermOfMom (restMom m) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.hermOfMom_restMom` (m : ℝ) : hermOfMom (restMom m) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.hermOfMom_restMom`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.hermOfMom_restMom
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.hermOfMom_restMom (m : ℝ) :
    hermOfMom (restMom m) = (m : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by sorry
