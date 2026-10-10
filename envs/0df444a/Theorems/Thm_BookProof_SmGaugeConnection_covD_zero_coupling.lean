-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_covD_zero_coupling
-- name    : BookProof.SmGaugeConnection.covD_zero_coupling
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T17:50:40.797596+00:00
-- url     : https://prove2.me/theorems/289d5265-bbab-48e5-98d2-04994ee3b464
-- title:
--   `BookProof.SmGaugeConnection.covD_zero_coupling` (k : Fin 3 → ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) (A : Fin d → Fin 3 → ℝ) (j : Fin 3) : covD k 0 T A j = (Complex.I * ((k j :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.covD_zero_coupling` (k : Fin 3 → ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) (A : Fin d → Fin 3 → ℝ) (j : Fin 3) : covD k 0 T A j = (Complex.I * ((k j : ℝ) : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.covD_zero_coupling`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.covD_zero_coupling
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

theorem BookProof.SmGaugeConnection.covD_zero_coupling (k : Fin 3 → ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (A : Fin d → Fin 3 → ℝ) (j : Fin 3) :
    covD k 0 T A j = (Complex.I * ((k j : ℝ) : ℂ)) • (1 : Matrix (Fin N) (Fin N) ℂ) := by sorry
