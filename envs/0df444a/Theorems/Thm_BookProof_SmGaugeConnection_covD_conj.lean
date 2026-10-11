-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_covD_conj
-- name    : BookProof.SmGaugeConnection.covD_conj
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:54:34.716589+00:00
-- url     : https://prove2.me/theorems/9414e1c2-82b9-49f0-9836-249e78f0b72f
-- title:
--   `BookProof.SmGaugeConnection.covD_conj` {k : Fin 3 → ℝ} {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} (hU : U * Uᴴ = 1) (j :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.covD_conj` {k : Fin 3 → ℝ} {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} (hU : U * Uᴴ = 1) (j : Fin 3) : U * covD k g T A j * Uᴴ = Complex.I • (((k j : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + U * conn g T A j * Uᴴ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.covD_conj`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.covD_conj
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

theorem BookProof.SmGaugeConnection.covD_conj {k : Fin 3 → ℝ} {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ}
    {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} (hU : U * Uᴴ = 1) (j : Fin 3) :
    U * covD k g T A j * Uᴴ
      = Complex.I • (((k j : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)
          + U * conn g T A j * Uᴴ) := by sorry
