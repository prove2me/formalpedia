-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_hasRealEigenvalue_eigenvalues
-- name    : BookProof.SirkFinitePrecision.hasRealEigenvalue_eigenvalues
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:49:35.970822+00:00
-- url     : https://prove2.me/theorems/960fa9c3-0445-44e1-802f-4a3b302789b5
-- title:
--   Every entry of `eigenvalues` really is an eigenvalue
-- statement:
--   Every entry of `eigenvalues` really is an eigenvalue.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.hasRealEigenvalue_eigenvalues` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 140–148.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L140-L148

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.hasRealEigenvalue_eigenvalues
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.hasRealEigenvalue_eigenvalues {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (i : Fin n) :
    HasRealEigenvalue T (hT.eigenvalues hn i) := by sorry
