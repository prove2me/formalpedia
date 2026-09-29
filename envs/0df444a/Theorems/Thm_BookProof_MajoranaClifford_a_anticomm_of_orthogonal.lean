-- Prove2me | Theorems.Thm_BookProof_MajoranaClifford_a_anticomm_of_orthogonal
-- name    : BookProof.MajoranaClifford.a_anticomm_of_orthogonal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-08T02:11:05.478421+00:00
-- url     : https://prove2.me/theorems/c2c34aa6-a9c1-4b1a-8bab-b5b58ca1db3f
-- title:
--   Orthogonal directions produce **anticommuting** field operators
-- statement:
--   Orthogonal directions produce **anticommuting** field operators.
--
--
--
--   **Formalization Note.** Lean 4 identifier: `BookProof.MajoranaClifford.a_anticomm_of_orthogonal` (module `BookProof.MajoranaClifford`), line-linked source: `ChapterMajoranaClifford.lean` lines 111–114.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterMajoranaClifford.lean#L111-L114

-- Generated from ChapterMajoranaClifford.lean — theorem BookProof.MajoranaClifford.a_anticomm_of_orthogonal
import Mathlib
import Definitions.Def_ChapterMajoranaClifford
open BookProof.MajoranaClifford









open RealInnerProductSpace CliffordAlgebra QuadraticMap


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem BookProof.MajoranaClifford.a_anticomm_of_orthogonal {v w : V} (h : ⟪v, w⟫ = (0 : ℝ)) :
    a v * a w + a w * a v = 0 := by sorry
