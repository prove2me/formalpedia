-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationKernel_orientationPreserving_false
-- name    : BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:04:11.757656+00:00
-- url     : https://prove2.me/theorems/e85888b8-5657-4f7c-bafb-e751285e2a1a
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false` : flipMatrix (fun _ => false : Fin n → Bool) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationKernel`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false` : flipMatrix (fun _ => false : Fin n → Bool) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false`.

-- Generated from ChapterFreeFieldBornSignOrientationKernel.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
open BookProof.ChapterFreeFieldBornSignOrientationKernel

variable {n : ℕ}


open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation

theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false :
    flipMatrix (fun _ => false : Fin n → Bool) ∈
      Matrix.specialOrthogonalGroup (Fin n) ℝ := by sorry
