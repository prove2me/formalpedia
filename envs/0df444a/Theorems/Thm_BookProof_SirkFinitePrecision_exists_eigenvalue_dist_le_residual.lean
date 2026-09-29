-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_exists_eigenvalue_dist_le_residual
-- name    : BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:12:54.795159+00:00
-- url     : https://prove2.me/theorems/a1a0d943-5996-4921-a168-57d50d02040a
-- title:
--   T2, the a-posteriori residual bound.** For a symmetric operator `T`, any nonzero vector `x` and any real `θ`, some eigenvalue of `T` lies within `‖T x − θ x‖ / ‖x‖` of `θ`
-- statement:
--   **T2, the a-posteriori residual bound.**  For a symmetric operator `T`, any
--   nonzero vector `x` and any real `θ`, some eigenvalue of `T` lies within
--   `‖T x − θ x‖ / ‖x‖` of `θ`.  The vector may be arbitrary — in particular it may be
--   the *computed* Ritz vector — and the operator is the exact one, which is why the
--   bound needs no infinite-precision hypothesis.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 152–192.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L152-L192

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : x ≠ 0) (θ : ℝ) :
    ∃ lam : ℝ, HasRealEigenvalue T lam ∧ |lam - θ| * ‖x‖ ≤ ‖T x - (θ : ℂ) • x‖ := by sorry
