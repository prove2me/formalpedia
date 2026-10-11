-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_diracGaugeMat_conjTranspose
-- name    : BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:09.70998+00:00
-- url     : https://prove2.me/theorems/c3a5d323-2a4a-4e79-9374-895279dd6ec4
-- title:
--   `BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose` {k : Fin 3 → ℝ} {m1 m2 g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) : (d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose` {k : Fin 3 → ℝ} {m1 m2 g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) : (diracGaugeMat k m1 m2 g T A)ᴴ = diracGaugeMat k m1 m2 g T A
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
import Definitions.Def_ChapterCPTHamiltonian
open BookProof.ChapterCPTHamiltonian
open BookProof.SmGaugeConnection



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

theorem BookProof.SmGaugeConnection.diracGaugeMat_conjTranspose {k : Fin 3 → ℝ} {m1 m2 g : ℝ}
    {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) :
    (diracGaugeMat k m1 m2 g T A)ᴴ = diracGaugeMat k m1 m2 g T A := by sorry
