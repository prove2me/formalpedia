-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiHam_norm_le
-- name    : BookProof.SmDiracYukawa.smFermiHam_norm_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:52:02.99182+00:00
-- url     : https://prove2.me/theorems/39cce107-3470-46e5-9a73-4568b4413c34
-- title:
--   `BookProof.SmDiracYukawa.smFermiHam_norm_le` (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (ψ : FermiFock n) : ‖smFermiHam hD M z ψ‖ ≤ (∑ i : Fin n, ∑ j : Fin n, ‖smFermiMatrix hD M z
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiHam_norm_le` (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (ψ : FermiFock n) : ‖smFermiHam hD M z ψ‖ ≤ (∑ i : Fin n, ∑ j : Fin n, ‖smFermiMatrix hD M z i j‖) * ‖ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiHam_norm_le`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiHam_norm_le
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.smFermiHam_norm_le (hD M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (ψ : FermiFock n) :
    ‖smFermiHam hD M z ψ‖
      ≤ (∑ i : Fin n, ∑ j : Fin n, ‖smFermiMatrix hD M z i j‖) * ‖ψ‖ := by sorry
