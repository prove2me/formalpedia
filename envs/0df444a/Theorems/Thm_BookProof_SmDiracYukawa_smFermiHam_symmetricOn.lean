-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_symmetricOn
-- name    : BookProof.SmDiracYukawa.smFermiHam_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:52:50.730467+00:00
-- url     : https://prove2.me/theorems/78765c67-44b0-428e-862e-fd8e17d939f3
-- title:
--   `BookProof.SmDiracYukawa.smFermiHam_symmetricOn` (hh : hD.conjTranspose = hD) : SymmetricOn (fullDom n) (onFull (smFermiHam hD M z))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiHam_symmetricOn` (hh : hD.conjTranspose = hD) : SymmetricOn (fullDom n) (onFull (smFermiHam hD M z))
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiHam_symmetricOn`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiHam_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.smFermiHam_symmetricOn (hh : hD.conjTranspose = hD) :
    SymmetricOn (fullDom n) (onFull (smFermiHam hD M z)) := by sorry
