-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_diracGaugeMat_free
-- name    : BookProof.SmGaugeConnection.diracGaugeMat_free
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T20:09:20.766681+00:00
-- url     : https://prove2.me/theorems/3d080a5f-9d83-427f-b9f8-284daf4d1c47
-- title:
--   `BookProof.SmGaugeConnection.diracGaugeMat_free` (k : Fin 3 → ℝ) (m1 m2 g : ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) : diracGaugeMat k m1 m2 g T (fun _ _ => (0 : ℝ)) = diracOnePar
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.diracGaugeMat_free` (k : Fin 3 → ℝ) (m1 m2 g : ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) : diracGaugeMat k m1 m2 g T (fun _ _ => (0 : ℝ)) = diracOneParticle k m1 m2 ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.diracGaugeMat_free`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.diracGaugeMat_free
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmDiracSpinor
open BookProof.ChapterCPTHamiltonian
open BookProof.SmDiracSpinor
open BookProof.SmGaugeConnection



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

theorem BookProof.SmGaugeConnection.diracGaugeMat_free (k : Fin 3 → ℝ) (m1 m2 g : ℝ)
    (T : Fin d → Matrix (Fin N) (Fin N) ℂ) :
    diracGaugeMat k m1 m2 g T (fun _ _ => (0 : ℝ))
      = diracOneParticle k m1 m2 ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ) := by sorry
