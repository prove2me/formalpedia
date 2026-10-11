-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_det
-- name    : BookProof.ChapterWignerLittleGroup.hermOfMom_det
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:51:25.10141+00:00
-- url     : https://prove2.me/theorems/b779f219-44d3-4ea3-9191-689443bf3076
-- title:
--   `BookProof.ChapterWignerLittleGroup.hermOfMom_det` (p : Fin 4 → ℝ) : (hermOfMom p).det = ((p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.hermOfMom_det` (p : Fin 4 → ℝ) : (hermOfMom p).det = ((p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.hermOfMom_det`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.hermOfMom_det
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.hermOfMom_det (p : Fin 4 → ℝ) :
    (hermOfMom p).det = ((p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 : ℝ) : ℂ) := by sorry
