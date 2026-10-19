-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_symmetric
-- name    : BookProof.SmDiracYukawa.smFermiHam_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:51:52.444851+00:00
-- url     : https://prove2.me/theorems/782d194d-04d9-4dbf-a267-28d1c00e417c
-- title:
--   `BookProof.SmDiracYukawa.smFermiHam_symmetric` {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ) (hh : hD.conjTranspose = hD) (ψ φ : FermiFock n) : (inner ℂ (smFermiHam hD M z ψ) φ : ℂ) =
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiHam_symmetric` {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ) (hh : hD.conjTranspose = hD) (ψ φ : FermiFock n) : (inner ℂ (smFermiHam hD M z ψ) φ : ℂ) = inner ℂ ψ (smFermiHam hD M z φ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiHam_symmetric`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiHam_symmetric
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.smFermiHam_symmetric {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ)
    (hh : hD.conjTranspose = hD) (ψ φ : FermiFock n) :
    (inner ℂ (smFermiHam hD M z ψ) φ : ℂ) = inner ℂ ψ (smFermiHam hD M z φ) := by sorry
