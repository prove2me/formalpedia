-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiOm_nonneg
-- name    : BookProof.SmDiracYukawa.smFermiOm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:52:44.618982+00:00
-- url     : https://prove2.me/theorems/c4752c5f-d60d-4042-9108-2b1e5e5c4dcd
-- title:
--   `BookProof.SmDiracYukawa.smFermiOm_nonneg` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : 0 ≤ smFermiOm om c0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiOm_nonneg` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : 0 ≤ smFermiOm om c0
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiOm_nonneg`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiOm_nonneg
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.smFermiOm_nonneg (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : 0 ≤ smFermiOm om c0 := by sorry
