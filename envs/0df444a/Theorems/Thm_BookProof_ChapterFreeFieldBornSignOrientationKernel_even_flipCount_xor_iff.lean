-- Prove2me | Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationKernel_even_flipCount_xor_iff
-- name    : BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:06:03.859999+00:00
-- url     : https://prove2.me/theorems/2c0c01dd-8398-4a3e-8e06-606fe29cf6c7
-- title:
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff` (b₁ b₂ : Fin n → Bool) : Even (flipCount (fun k => xor (b₁ k) (b₂ k))) ↔ (Even (flipCount b₁) ↔ Even (f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFreeFieldBornSignOrientationKernel`.
--
--   `BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff` (b₁ b₂ : Fin n → Bool) : Even (flipCount (fun k => xor (b₁ k) (b₂ k))) ↔ (Even (flipCount b₁) ↔ Even (flipCount b₂))
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff`.

-- Generated from ChapterFreeFieldBornSignOrientationKernel.lean — theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff
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

theorem BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff (b₁ b₂ : Fin n → Bool) :
    Even (flipCount (fun k => xor (b₁ k) (b₂ k))) ↔
      (Even (flipCount b₁) ↔ Even (flipCount b₂)) := by sorry
