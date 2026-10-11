-- Prove2me | Theorems.Thm_BookProof_SmDiracSpinor_smFermiHam_zero_yukawa
-- name    : BookProof.SmDiracSpinor.smFermiHam_zero_yukawa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:28:55.340091+00:00
-- url     : https://prove2.me/theorems/8de3a583-da11-436a-ab47-6206da7da8d2
-- title:
--   `BookProof.SmDiracSpinor.smFermiHam_zero_yukawa` (hD : Matrix (Fin 4) (Fin 4) ℂ) : smFermiHam hD (0 : Matrix (Fin 4) (Fin 4) ℂ) 0 = fermiBilin hD
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracSpinor`.
--
--   `BookProof.SmDiracSpinor.smFermiHam_zero_yukawa` (hD : Matrix (Fin 4) (Fin 4) ℂ) : smFermiHam hD (0 : Matrix (Fin 4) (Fin 4) ℂ) 0 = fermiBilin hD
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracSpinor.smFermiHam_zero_yukawa`.

-- Generated from ChapterSmDiracSpinor.lean — theorem BookProof.SmDiracSpinor.smFermiHam_zero_yukawa
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmCar
open BookProof.SmDiracYukawa
open BookProof.SmDiracSpinor



open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

theorem BookProof.SmDiracSpinor.smFermiHam_zero_yukawa (hD : Matrix (Fin 4) (Fin 4) ℂ) :
    smFermiHam hD (0 : Matrix (Fin 4) (Fin 4) ℂ) 0 = fermiBilin hD := by sorry
