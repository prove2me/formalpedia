-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_diracGaugeField_symmetric
-- name    : BookProof.SmGaugeConnection.diracGaugeField_symmetric
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:43.270907+00:00
-- url     : https://prove2.me/theorems/aa6593f2-d658-44db-ba21-8c6f1a744af4
-- title:
--   `BookProof.SmGaugeConnection.diracGaugeField_symmetric` {k : Fin 3 → ℝ} {m1 m2 g : ℝ} {T : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {A : Fin 8 → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) (psi p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.diracGaugeField_symmetric` {k : Fin 3 → ℝ} {m1 m2 g : ℝ} {T : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {A : Fin 8 → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) (psi phi : FermiFock 12) : (inner ℂ (diracGaugeField k m1 m2 g T A psi) phi : ℂ) = inner ℂ psi (diracGaugeField k m1 m2 g T A phi)
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.diracGaugeField_symmetric`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.diracGaugeField_symmetric
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmGaugeConnection



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

theorem BookProof.SmGaugeConnection.diracGaugeField_symmetric {k : Fin 3 → ℝ} {m1 m2 g : ℝ}
    {T : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {A : Fin 8 → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a)
    (psi phi : FermiFock 12) :
    (inner ℂ (diracGaugeField k m1 m2 g T A psi) phi : ℂ)
      = inner ℂ psi (diracGaugeField k m1 m2 g T A phi) := by sorry
