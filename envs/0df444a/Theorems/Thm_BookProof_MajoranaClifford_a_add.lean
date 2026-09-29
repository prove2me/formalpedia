-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_a_add
-- name    : BookProof.MajoranaClifford.a_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:52:00.666758+00:00
-- url     : https://prove2.me/theorems/7bdf80b5-4c4a-4aa3-9f51-45b438c7e3c7
-- title:
--   The Lean 4 theorem `a_add` in the `ChapterMajoranaClifford` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `a_add` in the `ChapterMajoranaClifford` chapter of the timepiece formalization.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.a_add` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 89–90.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L89-L90

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.a_add
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.a_add (v w : V) : a (v + w) = a v + a w := by sorry
