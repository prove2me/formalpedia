-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_diracGaugeMat_split
-- name    : BookProof.SmGaugeConnection.diracGaugeMat_split
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:18.361592+00:00
-- url     : https://prove2.me/theorems/ec51e8cb-4d2f-466b-bc87-91ad978b4afe
-- title:
--   `BookProof.SmGaugeConnection.diracGaugeMat_split` (k : Fin 3 → ℝ) (m1 m2 g : ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) (A : Fin d → Fin 3 → ℝ) : diracGaugeMat k m1 m2 g T A = dirac
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.diracGaugeMat_split` (k : Fin 3 → ℝ) (m1 m2 g : ℝ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) (A : Fin d → Fin 3 → ℝ) : diracGaugeMat k m1 m2 g T A = diracOneParticle k m1 m2 ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ) + ∑ j : Fin 3, Kin j ⊗ₖ conn g T A j
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.diracGaugeMat_split`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.diracGaugeMat_split
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

theorem BookProof.SmGaugeConnection.diracGaugeMat_split (k : Fin 3 → ℝ) (m1 m2 g : ℝ)
    (T : Fin d → Matrix (Fin N) (Fin N) ℂ) (A : Fin d → Fin 3 → ℝ) :
    diracGaugeMat k m1 m2 g T A
      = diracOneParticle k m1 m2 ⊗ₖ (1 : Matrix (Fin N) (Fin N) ℂ)
        + ∑ j : Fin 3, Kin j ⊗ₖ conn g T A j := by sorry
