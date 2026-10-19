-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_diagOp_inner
-- name    : BookProof.SmDiracYukawa.diagOp_inner
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:01:01.707844+00:00
-- url     : https://prove2.me/theorems/b7d7a185-1241-47e3-9592-9d9df02a6619
-- title:
--   `BookProof.SmDiracYukawa.diagOp_inner` (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) : (inner ℂ ψ (diagOp d ψ) : ℂ) = ∑ S : Finset (Fin n), ((d S * ‖ψ S‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.diagOp_inner` (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) : (inner ℂ ψ (diagOp d ψ) : ℂ) = ∑ S : Finset (Fin n), ((d S * ‖ψ S‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.diagOp_inner`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_inner
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

theorem BookProof.SmDiracYukawa.diagOp_inner (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    (inner ℂ ψ (diagOp d ψ) : ℂ)
      = ∑ S : Finset (Fin n), ((d S * ‖ψ S‖ ^ 2 : ℝ) : ℂ) := by sorry
