-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_norm_ge
-- name    : BookProof.SmDiracYukawa.sm_fermi_N_norm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:11.005153+00:00
-- url     : https://prove2.me/theorems/16295018-6a88-47e1-8366-906ccf80b8ce
-- title:
--   `BookProof.SmDiracYukawa.sm_fermi_N_norm_ge` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (ψ : FermiFock n) : ‖ψ‖ ≤ ‖smFermiN om c0 ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.sm_fermi_N_norm_ge` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (ψ : FermiFock n) : ‖ψ‖ ≤ ‖smFermiN om c0 ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.sm_fermi_N_norm_ge`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.sm_fermi_N_norm_ge
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.sm_fermi_N_norm_ge (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (ψ : FermiFock n) :
    ‖ψ‖ ≤ ‖smFermiN om c0 ψ‖ := by sorry
