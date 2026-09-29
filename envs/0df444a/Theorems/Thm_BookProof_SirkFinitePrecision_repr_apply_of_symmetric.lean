-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_repr_apply_of_symmetric
-- name    : BookProof.SirkFinitePrecision.repr_apply_of_symmetric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T14:51:31.507872+00:00
-- url     : https://prove2.me/theorems/1be21169-48e4-40bb-ac4a-aa316c997c6f
-- title:
--   The eigenbasis coordinates of `T x` are the coordinates of `x` scaled by the eigenvalues
-- statement:
--   The eigenbasis coordinates of `T x` are the coordinates of `x` scaled by the
--   eigenvalues.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.repr_apply_of_symmetric` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 82–89.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L82-L89

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.repr_apply_of_symmetric
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.repr_apply_of_symmetric {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (x : E) (i : Fin n) :
    coeff hT hn (T x) i = (hT.eigenvalues hn i : ℂ) * coeff hT hn x i := by sorry
