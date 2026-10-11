-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_sum_kronecker_right
-- name    : BookProof.SmGaugeConnection.sum_kronecker_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:04.000035+00:00
-- url     : https://prove2.me/theorems/b9ee77b0-507a-4272-91b5-7b69e17a06a9
-- title:
--   `BookProof.SmGaugeConnection.sum_kronecker_right` {n : ℕ} (F : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) : (∑ j : Fin 3, F j) ⊗ₖ B = ∑ j : Fin 3, (F j) ⊗ₖ B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.sum_kronecker_right` {n : ℕ} (F : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) : (∑ j : Fin 3, F j) ⊗ₖ B = ∑ j : Fin 3, (F j) ⊗ₖ B
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.sum_kronecker_right`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.sum_kronecker_right
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
open BookProof.SmGaugeConnection



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

theorem BookProof.SmGaugeConnection.sum_kronecker_right {n : ℕ} (F : Fin 3 → Matrix (Fin 4) (Fin 4) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) : (∑ j : Fin 3, F j) ⊗ₖ B = ∑ j : Fin 3, (F j) ⊗ₖ B := by sorry
