-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_backward_error_weyl_symm
-- name    : BookProof.SirkFinitePrecision.backward_error_weyl_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:17:05.477093+00:00
-- url     : https://prove2.me/theorems/bff19218-d9e7-4b32-808d-b23356f373dd
-- title:
--   The symmetric companion of `backward_error_weyl`: an eigenvalue of the exact operator is within `ε` of an eigenvalue of the perturbed one
-- statement:
--   The symmetric companion of `backward_error_weyl`: an eigenvalue of the exact
--   operator is within `ε` of an eigenvalue of the perturbed one.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.backward_error_weyl_symm` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 224–232.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L224-L232

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.backward_error_weyl_symm
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.backward_error_weyl_symm {T S : E →ₗ[ℂ] E} (hS : S.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {ε : ℝ} (hε : ∀ x : E, ‖T x - S x‖ ≤ ε * ‖x‖)
    {lam : ℝ} (hlam : HasRealEigenvalue T lam) :
    ∃ mu : ℝ, HasRealEigenvalue S mu ∧ |mu - lam| ≤ ε := by sorry
