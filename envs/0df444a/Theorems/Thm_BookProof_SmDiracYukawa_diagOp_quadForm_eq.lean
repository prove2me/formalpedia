-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_diagOp_quadForm_eq
-- name    : BookProof.SmDiracYukawa.diagOp_quadForm_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:26.577505+00:00
-- url     : https://prove2.me/theorems/9da2c6fc-dee5-4446-be8a-52664eea754b
-- title:
--   `BookProof.SmDiracYukawa.diagOp_quadForm_eq` (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) : (inner ℂ ψ (diagOp d ψ) : ℂ).re = ∑ S : Finset (Fin n), d S * ‖ψ S‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.diagOp_quadForm_eq` (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) : (inner ℂ ψ (diagOp d ψ) : ℂ).re = ∑ S : Finset (Fin n), d S * ‖ψ S‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.diagOp_quadForm_eq`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_quadForm_eq
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

theorem BookProof.SmDiracYukawa.diagOp_quadForm_eq (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    (inner ℂ ψ (diagOp d ψ) : ℂ).re = ∑ S : Finset (Fin n), d S * ‖ψ S‖ ^ 2 := by sorry
