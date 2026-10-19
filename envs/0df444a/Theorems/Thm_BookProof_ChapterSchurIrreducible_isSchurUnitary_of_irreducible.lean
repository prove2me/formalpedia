-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_isSchurUnitary_of_irreducible
-- name    : BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T01:02:23.095369+00:00
-- url     : https://prove2.me/theorems/e1d3f38c-5eb9-4eac-a22f-5768aa1da670
-- title:
--   `BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible` [Nontrivial V] (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) : IsSchurUnitary M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible` [Nontrivial V] (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) : IsSchurUnitary M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible [Nontrivial V] (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) : IsSchurUnitary M := by sorry
