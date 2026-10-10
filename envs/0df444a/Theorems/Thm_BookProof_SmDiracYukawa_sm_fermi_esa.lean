-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_esa
-- name    : BookProof.SmDiracYukawa.sm_fermi_esa
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:49:29.449469+00:00
-- url     : https://prove2.me/theorems/09ea69c1-f9f5-4870-a3c2-1cabdd81347a
-- title:
--   `BookProof.SmDiracYukawa.sm_fermi_esa` (hh : hD.conjTranspose = hD) (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : EssentiallySelfAdjointOn (fullDom n) ((onFull (smFermiHam hD M z)).comp (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.sm_fermi_esa` (hh : hD.conjTranspose = hD) (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : EssentiallySelfAdjointOn (fullDom n) ((onFull (smFermiHam hD M z)).comp (Submodule.inclusion (le_refl (fullDom n))))
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.sm_fermi_esa`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.sm_fermi_esa
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.sm_fermi_esa (hh : hD.conjTranspose = hD) (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) :
    EssentiallySelfAdjointOn (fullDom n)
      ((onFull (smFermiHam hD M z)).comp (Submodule.inclusion (le_refl (fullDom n)))) := by sorry
