-- Prove2me | Theorems.Thm_BookProof_ChapterWignerLittleGroup_hermOfMom_trace
-- name    : BookProof.ChapterWignerLittleGroup.hermOfMom_trace
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:53:50.780975+00:00
-- url     : https://prove2.me/theorems/a907a66d-41ba-4771-801c-7618649138b3
-- title:
--   `BookProof.ChapterWignerLittleGroup.hermOfMom_trace` (p : Fin 4 → ℝ) : (hermOfMom p).trace = ((2 * p 0 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWignerLittleGroup`.
--
--   `BookProof.ChapterWignerLittleGroup.hermOfMom_trace` (p : Fin 4 → ℝ) : (hermOfMom p).trace = ((2 * p 0 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWignerLittleGroup.hermOfMom_trace`.

-- Generated from ChapterWignerLittleGroup.lean — theorem BookProof.ChapterWignerLittleGroup.hermOfMom_trace
import Mathlib
import Definitions.Def_ChapterWignerLittleGroup
open BookProof.ChapterWignerLittleGroup


open Matrix Complex

theorem BookProof.ChapterWignerLittleGroup.hermOfMom_trace (p : Fin 4 → ℝ) :
    (hermOfMom p).trace = ((2 * p 0 : ℝ) : ℂ) := by sorry
