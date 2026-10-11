-- Prove2me | Theorems.Thm_BookProof_SmDiracSpinor_diracFieldHam_symmetric
-- name    : BookProof.SmDiracSpinor.diracFieldHam_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:18.067411+00:00
-- url     : https://prove2.me/theorems/d73f60ef-f41c-4fb9-838d-c563e9968943
-- title:
--   `BookProof.SmDiracSpinor.diracFieldHam_symmetric` (psi phi : FermiFock 4) : (inner ℂ (diracFieldHam k m1 m2 psi) phi : ℂ) = inner ℂ psi (diracFieldHam k m1 m2 phi)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracSpinor`.
--
--   `BookProof.SmDiracSpinor.diracFieldHam_symmetric` (psi phi : FermiFock 4) : (inner ℂ (diracFieldHam k m1 m2 psi) phi : ℂ) = inner ℂ psi (diracFieldHam k m1 m2 phi)
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracSpinor.diracFieldHam_symmetric`.

-- Generated from ChapterSmDiracSpinor.lean — theorem BookProof.SmDiracSpinor.diracFieldHam_symmetric
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracSpinor



open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

theorem BookProof.SmDiracSpinor.diracFieldHam_symmetric (psi phi : FermiFock 4) :
    (inner ℂ (diracFieldHam k m1 m2 psi) phi : ℂ)
      = inner ℂ psi (diracFieldHam k m1 m2 phi) := by sorry
