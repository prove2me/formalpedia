-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_isMixing_mul
-- name    : BookProof.SmDiracYukawa.isMixing_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:15:33.314136+00:00
-- url     : https://prove2.me/theorems/04698a98-e7aa-431a-bead-9808ba0d1d7f
-- title:
--   `BookProof.SmDiracYukawa.isMixing_mul` {A B : Matrix (Fin 3) (Fin 3) ℂ} (hA : IsMixing A) (hB : IsMixing B) : IsMixing (A * B.conjTranspose)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.isMixing_mul` {A B : Matrix (Fin 3) (Fin 3) ℂ} (hA : IsMixing A) (hB : IsMixing B) : IsMixing (A * B.conjTranspose)
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.isMixing_mul`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.isMixing_mul
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

open BookProof.SmOneParticle

theorem BookProof.SmDiracYukawa.isMixing_mul {A B : Matrix (Fin 3) (Fin 3) ℂ} (hA : IsMixing A) (hB : IsMixing B) :
    IsMixing (A * B.conjTranspose) := by sorry
