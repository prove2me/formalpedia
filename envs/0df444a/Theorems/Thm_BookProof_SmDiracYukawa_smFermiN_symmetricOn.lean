-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiN_symmetricOn
-- name    : BookProof.SmDiracYukawa.smFermiN_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:52:47.350895+00:00
-- url     : https://prove2.me/theorems/3ce9daa6-d901-4112-b8e9-d1523d129a7f
-- title:
--   `BookProof.SmDiracYukawa.smFermiN_symmetricOn` (om : Fin n → ℝ) (c0 : ℝ) : SymmetricOn (fullDom n) (onFull (smFermiN om c0))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiN_symmetricOn` (om : Fin n → ℝ) (c0 : ℝ) : SymmetricOn (fullDom n) (onFull (smFermiN om c0))
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiN_symmetricOn`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiN_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.smFermiN_symmetricOn (om : Fin n → ℝ) (c0 : ℝ) :
    SymmetricOn (fullDom n) (onFull (smFermiN om c0)) := by sorry
