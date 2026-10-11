-- Prove2me | Theorems.Thm_BookProof_SmDiracSpinor_diracOneParticle_hermitian
-- name    : BookProof.SmDiracSpinor.diracOneParticle_hermitian
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:28:46.45992+00:00
-- url     : https://prove2.me/theorems/94fecd2c-857f-456d-803f-1e40767ba339
-- title:
--   `BookProof.SmDiracSpinor.diracOneParticle_hermitian` : (diracOneParticle k m1 m2).conjTranspose = diracOneParticle k m1 m2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracSpinor`.
--
--   `BookProof.SmDiracSpinor.diracOneParticle_hermitian` : (diracOneParticle k m1 m2).conjTranspose = diracOneParticle k m1 m2
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracSpinor.diracOneParticle_hermitian`.

-- Generated from ChapterSmDiracSpinor.lean — theorem BookProof.SmDiracSpinor.diracOneParticle_hermitian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian
open BookProof.SmDiracSpinor



open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

theorem BookProof.SmDiracSpinor.diracOneParticle_hermitian :
    (diracOneParticle k m1 m2).conjTranspose = diracOneParticle k m1 m2 := by sorry
