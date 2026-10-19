-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_diagOp_add_one_surjective
-- name    : BookProof.SmDiracYukawa.diagOp_add_one_surjective
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:56.755919+00:00
-- url     : https://prove2.me/theorems/66d2abb4-519f-4569-8a65-2ed1a1d7f034
-- title:
--   `BookProof.SmDiracYukawa.diagOp_add_one_surjective` {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S) (f : FermiFock n) : ∃ ψ : FermiFock n, diagOp d ψ + ψ = f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.diagOp_add_one_surjective` {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S) (f : FermiFock n) : ∃ ψ : FermiFock n, diagOp d ψ + ψ = f
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.diagOp_add_one_surjective`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_add_one_surjective
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

theorem BookProof.SmDiracYukawa.diagOp_add_one_surjective {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S)
    (f : FermiFock n) : ∃ ψ : FermiFock n, diagOp d ψ + ψ = f := by sorry
