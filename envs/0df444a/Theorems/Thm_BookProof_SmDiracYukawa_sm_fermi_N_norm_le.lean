-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_norm_le
-- name    : BookProof.SmDiracYukawa.sm_fermi_N_norm_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:53:21.571989+00:00
-- url     : https://prove2.me/theorems/437413c7-6afa-4d8a-8429-28f6f3c0b113
-- title:
--   `BookProof.SmDiracYukawa.sm_fermi_N_norm_le` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (ψ : FermiFock n) : ‖smFermiN om c0 ψ‖ ≤ smFermiOm om c0 * ‖ψ‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.sm_fermi_N_norm_le` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (ψ : FermiFock n) : ‖smFermiN om c0 ψ‖ ≤ smFermiOm om c0 * ‖ψ‖
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.sm_fermi_N_norm_le`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.sm_fermi_N_norm_le
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

theorem BookProof.SmDiracYukawa.sm_fermi_N_norm_le (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (ψ : FermiFock n) :
    ‖smFermiN om c0 ψ‖ ≤ smFermiOm om c0 * ‖ψ‖ := by sorry
