-- Prove2me | Theorems.Thm_BookProof_SmDiracSpinor_diracOneParticle_eigenvalue_sq
-- name    : BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:28:46.973026+00:00
-- url     : https://prove2.me/theorems/3b74be36-d051-4594-b7c9-02915719ca29
-- title:
--   `BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq` {v : Fin 4 → ℂ} {mu : ℂ} (hv : v ≠ 0) (heig : (diracOneParticle k m1 m2).mulVec v = mu • v) : mu ^ 2 = (∑ j : Fin 3, (k j :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracSpinor`.
--
--   `BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq` {v : Fin 4 → ℂ} {mu : ℂ} (hv : v ≠ 0) (heig : (diracOneParticle k m1 m2).mulVec v = mu • v) : mu ^ 2 = (∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq`.

-- Generated from ChapterSmDiracSpinor.lean — theorem BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
open BookProof.SmDiracSpinor



open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

theorem BookProof.SmDiracSpinor.diracOneParticle_eigenvalue_sq {v : Fin 4 → ℂ} {mu : ℂ} (hv : v ≠ 0)
    (heig : (diracOneParticle k m1 m2).mulVec v = mu • v) :
    mu ^ 2 = (∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2 := by sorry
