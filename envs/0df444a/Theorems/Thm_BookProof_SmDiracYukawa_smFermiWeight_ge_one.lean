-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiWeight_ge_one
-- name    : BookProof.SmDiracYukawa.smFermiWeight_ge_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:30:29.609726+00:00
-- url     : https://prove2.me/theorems/ea15b437-f6a1-476c-8e46-2a11f6b5215e
-- title:
--   `BookProof.SmDiracYukawa.smFermiWeight_ge_one` {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (S : Finset (Fin n)) : 1 ≤ smFermiWeight om c0 S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiWeight_ge_one` {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (S : Finset (Fin n)) : 1 ≤ smFermiWeight om c0 S
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiWeight_ge_one`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiWeight_ge_one
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.smFermiWeight_ge_one {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (S : Finset (Fin n)) : 1 ≤ smFermiWeight om c0 S := by sorry
