-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_exists_eigenvalue_dist_le_residual_unit
-- name    : BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual_unit
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:16:28.861726+00:00
-- url     : https://prove2.me/theorems/e20666c6-1926-4b11-8735-7391534675f0
-- title:
--   T2 for a unit vector**: the certified interval `[θ − ‖r‖, θ + ‖r‖]` contains an eigenvalue of the exact operator
-- statement:
--   **T2 for a unit vector**: the certified interval `[θ − ‖r‖, θ + ‖r‖]` contains an
--   eigenvalue of the exact operator.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual_unit` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 194–202.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L194-L202

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual_unit
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual_unit {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : ‖x‖ = 1) (θ : ℝ) :
    ∃ lam : ℝ, HasRealEigenvalue T lam ∧ |lam - θ| ≤ ‖T x - (θ : ℂ) • x‖ := by sorry
