-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_smFermiWeight_le
-- name    : BookProof.SmDiracYukawa.smFermiWeight_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:30:26.955024+00:00
-- url     : https://prove2.me/theorems/f525417f-0079-41d2-b798-a93270cefbfc
-- title:
--   `BookProof.SmDiracYukawa.smFermiWeight_le` {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (S : Finset (Fin n)) : |smFermiWeight om c0 S| ≤ (∑ i : Fin n, om i) + c0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.smFermiWeight_le` {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (S : Finset (Fin n)) : |smFermiWeight om c0 S| ≤ (∑ i : Fin n, om i) + c0
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.smFermiWeight_le`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.smFermiWeight_le
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

theorem BookProof.SmDiracYukawa.smFermiWeight_le {om : Fin n → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0)
    (S : Finset (Fin n)) :
    |smFermiWeight om c0 S| ≤ (∑ i : Fin n, om i) + c0 := by sorry
