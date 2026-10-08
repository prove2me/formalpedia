-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationKernel_orientationPreserving_xor_iff
-- name    : BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:07:14.433499+00:00
-- url     : https://prove2.me/theorems/ad79d48a-2cec-4e9b-af75-076fcb4717f6
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff` (b₁ b₂ : Fin n → Bool) : flipMatrix (fun k => xor (b₁ k) (b₂ k)) ∈ Matrix.specialOrthogonalGroup
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationKernel`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff` (b₁ b₂ : Fin n → Bool) : flipMatrix (fun k => xor (b₁ k) (b₂ k)) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ (flipMatrix b₁ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ flipMatrix b₂ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff`.

-- Generated from ChapterFreeFieldBornSignOrientationKernel.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff
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

theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff (b₁ b₂ : Fin n → Bool) :
    flipMatrix (fun k => xor (b₁ k) (b₂ k)) ∈
        Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
      (flipMatrix b₁ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
       flipMatrix b₂ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) := by sorry
