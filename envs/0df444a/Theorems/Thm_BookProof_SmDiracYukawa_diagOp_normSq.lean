-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_diagOp_normSq
-- name    : BookProof.SmDiracYukawa.diagOp_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T23:15:13.731402+00:00
-- url     : https://prove2.me/theorems/220daee6-bda5-4268-9cf1-6e24b270334c
-- title:
--   `BookProof.SmDiracYukawa.diagOp_normSq` (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) : ‖diagOp d ψ‖ ^ 2 = ∑ S : Finset (Fin n), (d S) ^ 2 * ‖ψ S‖ ^ 2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.diagOp_normSq` (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) : ‖diagOp d ψ‖ ^ 2 = ∑ S : Finset (Fin n), (d S) ^ 2 * ‖ψ S‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.diagOp_normSq`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_normSq
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

theorem BookProof.SmDiracYukawa.diagOp_normSq (d : Finset (Fin n) → ℝ) (ψ : FermiFock n) :
    ‖diagOp d ψ‖ ^ 2 = ∑ S : Finset (Fin n), (d S) ^ 2 * ‖ψ S‖ ^ 2 := by sorry
