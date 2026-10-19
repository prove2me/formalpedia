-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_diagOp_norm_le
-- name    : BookProof.SmDiracYukawa.diagOp_norm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:45.582225+00:00
-- url     : https://prove2.me/theorems/238f98e4-95a1-4e39-8787-4d8c32cf71f3
-- title:
--   `BookProof.SmDiracYukawa.diagOp_norm_le` {d : Finset (Fin n) → ℝ} {Om : ℝ} (hOm : 0 ≤ Om) (hd : ∀ S, |d S| ≤ Om) (ψ : FermiFock n) : ‖diagOp d ψ‖ ≤ Om * ‖ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.diagOp_norm_le` {d : Finset (Fin n) → ℝ} {Om : ℝ} (hOm : 0 ≤ Om) (hd : ∀ S, |d S| ≤ Om) (ψ : FermiFock n) : ‖diagOp d ψ‖ ≤ Om * ‖ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.diagOp_norm_le`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_norm_le
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

theorem BookProof.SmDiracYukawa.diagOp_norm_le {d : Finset (Fin n) → ℝ} {Om : ℝ} (hOm : 0 ≤ Om)
    (hd : ∀ S, |d S| ≤ Om) (ψ : FermiFock n) : ‖diagOp d ψ‖ ≤ Om * ‖ψ‖ := by sorry
