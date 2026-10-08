-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationKernel_orientationPreserving_xor
-- name    : BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:04:27.190495+00:00
-- url     : https://prove2.me/theorems/a6990be6-e129-44ea-828b-32db6ddc1d69
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor` {b₁ b₂ : Fin n → Bool} (h₁ : flipMatrix b₁ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) (h₂ : flipMatr
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationKernel`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor` {b₁ b₂ : Fin n → Bool} (h₁ : flipMatrix b₁ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) (h₂ : flipMatrix b₂ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) : flipMatrix (fun k => xor (b₁ k) (b₂ k)) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor`.

-- Generated from ChapterFreeFieldBornSignOrientationKernel.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor
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

theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor {b₁ b₂ : Fin n → Bool}
    (h₁ : flipMatrix b₁ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ)
    (h₂ : flipMatrix b₂ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) :
    flipMatrix (fun k => xor (b₁ k) (b₂ k)) ∈
      Matrix.specialOrthogonalGroup (Fin n) ℝ := by sorry
