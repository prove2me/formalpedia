-- Prove2me | Theorems.Thm_BookProof_SmDiracSpinor_dirac_field_esa
-- name    : BookProof.SmDiracSpinor.dirac_field_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:29:06.964692+00:00
-- url     : https://prove2.me/theorems/fa2c7a17-ecf5-44d2-865e-1bbe861109ab
-- title:
--   `BookProof.SmDiracSpinor.dirac_field_esa` {om : Fin 4 → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : EssentiallySelfAdjointOn (fullDom 4) ((onFull (smFermiHam (diracOnePartic
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracSpinor`.
--
--   `BookProof.SmDiracSpinor.dirac_field_esa` {om : Fin 4 → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : EssentiallySelfAdjointOn (fullDom 4) ((onFull (smFermiHam (diracOneParticle k m1 m2) (0 : Matrix (Fin 4) (Fin 4) ℂ) 0)).comp (Submodule.inclusion (le_refl (fullDom 4))))
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracSpinor.dirac_field_esa`.

-- Generated from ChapterSmDiracSpinor.lean — theorem BookProof.SmDiracSpinor.dirac_field_esa
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.SmDiracSpinor.dirac_field_esa {om : Fin 4 → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) :
    EssentiallySelfAdjointOn (fullDom 4)
      ((onFull (smFermiHam (diracOneParticle k m1 m2) (0 : Matrix (Fin 4) (Fin 4) ℂ) 0)).comp
        (Submodule.inclusion (le_refl (fullDom 4)))) := by sorry
