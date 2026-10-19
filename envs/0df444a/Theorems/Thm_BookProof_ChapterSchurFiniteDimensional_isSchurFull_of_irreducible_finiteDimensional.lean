-- Prove2me | Theorems.Thm_BookProof_ChapterSchurFiniteDimensional_isSchurFull_of_irreducible_finiteDimensional
-- name    : BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:59:56.802772+00:00
-- url     : https://prove2.me/theorems/79306b51-64d4-4ee0-8848-388a1ba08891
-- title:
--   `BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurFul
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurFiniteDimensional`.
--
--   `BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurFull M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional`.

-- Generated from ChapterSchurFiniteDimensional.lean — theorem BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional
import Mathlib
import Definitions.Def_ChapterSchurFiniteDimensional
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurFiniteDimensional


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurFiniteDimensional.isSchurFull_of_irreducible_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurFull M := by sorry
