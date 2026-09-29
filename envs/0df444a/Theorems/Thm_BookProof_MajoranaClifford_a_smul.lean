-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_a_smul
-- name    : BookProof.MajoranaClifford.a_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T01:53:07.863592+00:00
-- url     : https://prove2.me/theorems/17a8119f-b38f-4f82-bad2-8bb271fe3ac7
-- title:
--   The Lean 4 theorem `a_smul` in the `ChapterMajoranaClifford` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `a_smul` in the `ChapterMajoranaClifford` chapter of the timepiece formalization.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.a_smul` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 92–93.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L92-L93

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.a_smul
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.a_smul (c : ℝ) (v : V) : a (c • v) = c • a v := by sorry
