-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiMatrix_hermitian
-- name    : BookProof.SmDiracYukawa.smFermiMatrix_hermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:32:14.692096+00:00
-- url     : https://prove2.me/theorems/a0d9108a-23b8-45fc-9a5f-cec67af6e631
-- title:
--   `BookProof.SmDiracYukawa.smFermiMatrix_hermitian` {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ) (hh : hD.conjTranspose = hD) : (smFermiMatrix hD M z).conjTranspose = smFermiMatrix hD M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiMatrix_hermitian` {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ) (hh : hD.conjTranspose = hD) : (smFermiMatrix hD M z).conjTranspose = smFermiMatrix hD M z
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiMatrix_hermitian`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiMatrix_hermitian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.smFermiMatrix_hermitian {hD M : Matrix (Fin n) (Fin n) ℂ} (z : ℂ)
    (hh : hD.conjTranspose = hD) :
    (smFermiMatrix hD M z).conjTranspose = smFermiMatrix hD M z := by sorry
