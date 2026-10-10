-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_N_add_one_surjective
-- name    : BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:47:49.476758+00:00
-- url     : https://prove2.me/theorems/16e59420-573a-46c7-8590-a1cabf59f3db
-- title:
--   `BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (f : FermiFock n) : ∃ x : fullDom n, onFull (smFermiN om c0) x + (x : FermiFock n) = f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (f : FermiFock n) : ∃ x : fullDom n, onFull (smFermiN om c0) x + (x : FermiFock n) = f
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective
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

theorem BookProof.SmDiracYukawa.sm_fermi_N_add_one_surjective (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (f : FermiFock n) :
    ∃ x : fullDom n, onFull (smFermiN om c0) x + (x : FermiFock n) = f := by sorry
