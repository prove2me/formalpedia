-- Prove2me | Theorems.Thm_BookProof_SmDiracSpinor_diracOneParticle_sq
-- name    : BookProof.SmDiracSpinor.diracOneParticle_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:21.805656+00:00
-- url     : https://prove2.me/theorems/9574b525-78e3-47f4-9374-b0789d66ff63
-- title:
--   `BookProof.SmDiracSpinor.diracOneParticle_sq` : diracOneParticle k m1 m2 * diracOneParticle k m1 m2 = (((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2)) • (1 : Matrix (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracSpinor`.
--
--   `BookProof.SmDiracSpinor.diracOneParticle_sq` : diracOneParticle k m1 m2 * diracOneParticle k m1 m2 = (((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2)) • (1 : Matrix (Fin 4) (Fin 4) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracSpinor.diracOneParticle_sq`.

-- Generated from ChapterSmDiracSpinor.lean — theorem BookProof.SmDiracSpinor.diracOneParticle_sq
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian
open BookProof.SmDiracSpinor



open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

theorem BookProof.SmDiracSpinor.diracOneParticle_sq :
    diracOneParticle k m1 m2 * diracOneParticle k m1 m2
      = (((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2))
        • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by sorry
