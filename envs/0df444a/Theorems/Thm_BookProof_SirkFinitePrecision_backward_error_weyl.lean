-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_backward_error_weyl
-- name    : BookProof.SirkFinitePrecision.backward_error_weyl
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:15:51.241216+00:00
-- url     : https://prove2.me/theorems/4ef3c5f2-138f-4ff8-891f-61a3767eb837
-- title:
--   T1/T3.** The LAPACK backward-error model says the computed eigenpairs are *exact* eigenpairs of a perturbed operator `S` with `‖(T − S) x‖ ≤ ε ‖x‖` (`ε = c(n) · u · ‖Ĝ‖`)
-- statement:
--   **T1/T3.**  The LAPACK backward-error model says the computed eigenpairs are
--   *exact* eigenpairs of a perturbed operator `S` with `‖(T − S) x‖ ≤ ε ‖x‖`
--   (`ε = c(n) · u · ‖Ĝ‖`).  Weyl's inequality — here in its enclosure form, which is all
--   the certificate needs — then places every eigenvalue of `S` within `ε` of an
--   eigenvalue of `T`.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.backward_error_weyl` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 206–222.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L206-L222

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.backward_error_weyl
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.backward_error_weyl {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {ε : ℝ} (hε : ∀ x : E, ‖T x - S x‖ ≤ ε * ‖x‖)
    {lam : ℝ} (hlam : HasRealEigenvalue S lam) :
    ∃ mu : ℝ, HasRealEigenvalue T mu ∧ |mu - lam| ≤ ε := by sorry
