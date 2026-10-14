-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_diagOp_symmetric
-- name    : BookProof.SmDiracYukawa.diagOp_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:00:51.96059+00:00
-- url     : https://prove2.me/theorems/254d29b8-6dd0-4f74-8b7c-c44542664631
-- title:
--   `BookProof.SmDiracYukawa.diagOp_symmetric` (d : Finset (Fin n) → ℝ) (ψ φ : FermiFock n) : (inner ℂ (diagOp d ψ) φ : ℂ) = inner ℂ ψ (diagOp d φ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.diagOp_symmetric` (d : Finset (Fin n) → ℝ) (ψ φ : FermiFock n) : (inner ℂ (diagOp d ψ) φ : ℂ) = inner ℂ ψ (diagOp d φ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.diagOp_symmetric`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_symmetric
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.diagOp_symmetric (d : Finset (Fin n) → ℝ) (ψ φ : FermiFock n) :
    (inner ℂ (diagOp d ψ) φ : ℂ) = inner ℂ ψ (diagOp d φ) := by sorry
