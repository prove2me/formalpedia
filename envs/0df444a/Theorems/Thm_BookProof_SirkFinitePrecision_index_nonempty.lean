-- Prove2me | Theorems.Thm_BookProof_SirkFinitePrecision_index_nonempty
-- name    : BookProof.SirkFinitePrecision.index_nonempty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-07T15:03:31.460229+00:00
-- url     : https://prove2.me/theorems/b2f92d6d-d86d-473c-ab83-fe7c62bd7d6a
-- title:
--   In a nonzero space the eigenvalue index type is nonempty
-- statement:
--   In a nonzero space the eigenvalue index type is nonempty.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.SirkFinitePrecision.index_nonempty` (module `BookProof.SirkFinitePrecision`), line-linked source: `ChapterSirkFinitePrecision.lean` lines 127–138.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkFinitePrecision.lean#L127-L138

-- Generated from ChapterSirkFinitePrecision.lean — theorem BookProof.SirkFinitePrecision.index_nonempty
import Mathlib
import Definitions.Def_ChapterSirkFinitePrecision
open BookProof.SirkFinitePrecision






noncomputable section


open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem BookProof.SirkFinitePrecision.index_nonempty {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {x : E} (hx : x ≠ 0) :
    (univ : Finset (Fin n)).Nonempty := by sorry
