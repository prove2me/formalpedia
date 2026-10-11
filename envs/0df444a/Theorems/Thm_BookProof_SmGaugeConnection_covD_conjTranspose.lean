-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_covD_conjTranspose
-- name    : BookProof.SmGaugeConnection.covD_conjTranspose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:54:05.76298+00:00
-- url     : https://prove2.me/theorems/a8c53b1f-653d-49f5-81dc-8c1e4260ff36
-- title:
--   `BookProof.SmGaugeConnection.covD_conjTranspose` {k : Fin 3 → ℝ} {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) (j : Fin 3) : (covD
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.covD_conjTranspose` {k : Fin 3 → ℝ} {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) (j : Fin 3) : (covD k g T A j)ᴴ = -covD k g T A j
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.covD_conjTranspose`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.covD_conjTranspose
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

theorem BookProof.SmGaugeConnection.covD_conjTranspose {k : Fin 3 → ℝ} {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ}
    {A : Fin d → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) (j : Fin 3) :
    (covD k g T A j)ᴴ = -covD k g T A j := by sorry
