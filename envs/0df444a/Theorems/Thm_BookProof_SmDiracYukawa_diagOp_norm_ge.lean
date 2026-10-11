-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_diagOp_norm_ge
-- name    : BookProof.SmDiracYukawa.diagOp_norm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:24.559614+00:00
-- url     : https://prove2.me/theorems/cfbee869-ae0c-43bd-bc21-8bdabc420310
-- title:
--   `BookProof.SmDiracYukawa.diagOp_norm_ge` {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S) (ψ : FermiFock n) : ‖ψ‖ ≤ ‖diagOp d ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.diagOp_norm_ge` {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S) (ψ : FermiFock n) : ‖ψ‖ ≤ ‖diagOp d ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.diagOp_norm_ge`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.diagOp_norm_ge
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

theorem BookProof.SmDiracYukawa.diagOp_norm_ge {d : Finset (Fin n) → ℝ} (hd : ∀ S, 1 ≤ d S) (ψ : FermiFock n) :
    ‖ψ‖ ≤ ‖diagOp d ψ‖ := by sorry
