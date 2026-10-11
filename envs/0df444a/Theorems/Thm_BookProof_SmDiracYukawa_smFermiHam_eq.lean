-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_eq
-- name    : BookProof.SmDiracYukawa.smFermiHam_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:30:44.377041+00:00
-- url     : https://prove2.me/theorems/207e05ff-5f59-4ec5-9568-4f65e03ae8f4
-- title:
--   `BookProof.SmDiracYukawa.smFermiHam_eq` (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : smFermiHam hD M z = smDirac hD + smYukawa M z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiHam_eq` (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) : smFermiHam hD M z = smDirac hD + smYukawa M z
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiHam_eq`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiHam_eq
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.smFermiHam_eq (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    smFermiHam hD M z = smDirac hD + smYukawa M z := by sorry
