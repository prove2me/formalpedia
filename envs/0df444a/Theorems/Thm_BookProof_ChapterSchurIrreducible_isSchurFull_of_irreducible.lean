-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_isSchurFull_of_irreducible
-- name    : BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:02:24.234714+00:00
-- url     : https://prove2.me/theorems/2d3bdf98-9699-4cb8-bf0c-f298a6a59933
-- title:
--   `BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible` (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) : IsSchurFull M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible` (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) : IsSchurFull M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) : IsSchurFull M := by sorry
