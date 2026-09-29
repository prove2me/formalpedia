-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_Qform_apply
-- name    : BookProof.MajoranaClifford.Qform_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:51:22.817967+00:00
-- url     : https://prove2.me/theorems/8cf94ebc-e6f8-4953-9a21-d653d0c90708
-- title:
--   The Lean 4 theorem `Qform_apply` in the `ChapterMajoranaClifford` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `Qform_apply` in the `ChapterMajoranaClifford` chapter of the timepiece formalization.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.Qform_apply` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 77–78.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L77-L78

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.Qform_apply
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.Qform_apply (v : V) : Qform v = ⟪v, v⟫ := by sorry
