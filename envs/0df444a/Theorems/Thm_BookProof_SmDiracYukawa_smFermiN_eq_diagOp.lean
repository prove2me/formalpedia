-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_eq_diagOp
-- name    : BookProof.SmDiracYukawa.smFermiN_eq_diagOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:30:04.215037+00:00
-- url     : https://prove2.me/theorems/2eb1f363-e063-4757-b742-a21d90edfee3
-- title:
--   `BookProof.SmDiracYukawa.smFermiN_eq_diagOp` (om : Fin n → ℝ) (c0 : ℝ) : smFermiN om c0 = diagOp (smFermiWeight om c0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiN_eq_diagOp` (om : Fin n → ℝ) (c0 : ℝ) : smFermiN om c0 = diagOp (smFermiWeight om c0)
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiN_eq_diagOp`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiN_eq_diagOp
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

theorem BookProof.SmDiracYukawa.smFermiN_eq_diagOp (om : Fin n → ℝ) (c0 : ℝ) :
    smFermiN om c0 = diagOp (smFermiWeight om c0) := by sorry
