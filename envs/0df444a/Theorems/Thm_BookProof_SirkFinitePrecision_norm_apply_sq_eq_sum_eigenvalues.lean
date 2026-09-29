-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_norm_apply_sq_eq_sum_eigenvalues
-- name    : BookProof.SirkFinitePrecision.norm_apply_sq_eq_sum_eigenvalues
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:04:48.660732+00:00
-- url     : https://prove2.me/theorems/9df5888e-9bce-4137-bdd5-9b206606168c
-- title:
--   The squared norm of `T x` is the squared-eigenvalue-weighted sum of the squared coordinates
-- statement:
--   The squared norm of `T x` is the squared-eigenvalue-weighted sum of the squared
--   coordinates.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.norm_apply_sq_eq_sum_eigenvalues` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 116–125.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L116-L125

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.norm_apply_sq_eq_sum_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.norm_apply_sq_eq_sum_eigenvalues {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) :
    ‖T x‖ ^ 2 = ∑ i, hT.eigenvalues hn i ^ 2 * ‖coeff hT hn x i‖ ^ 2 := by sorry
