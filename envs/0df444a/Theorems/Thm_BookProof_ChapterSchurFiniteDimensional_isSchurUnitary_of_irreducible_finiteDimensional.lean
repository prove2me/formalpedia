-- Prove2me | Theorems.Thm_BookProof_ChapterSchurFiniteDimensional_isSchurUnitary_of_irreducible_finiteDimensional
-- name    : BookProof.ChapterSchurFiniteDimensional.isSchurUnitary_of_irreducible_finiteDimensional
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:00:08.811984+00:00
-- url     : https://prove2.me/theorems/b858deb5-53b8-4f50-a847-93b995a08fed
-- title:
--   `BookProof.ChapterSchurFiniteDimensional.isSchurUnitary_of_irreducible_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchur
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurFiniteDimensional`.
--
--   `BookProof.ChapterSchurFiniteDimensional.isSchurUnitary_of_irreducible_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurUnitary M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurFiniteDimensional.isSchurUnitary_of_irreducible_finiteDimensional`.

-- Generated from ChapterSchurFiniteDimensional.lean — theorem BookProof.ChapterSchurFiniteDimensional.isSchurUnitary_of_irreducible_finiteDimensional
import Mathlib
import Definitions.Def_ChapterSchurFiniteDimensional
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurFiniteDimensional


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurFiniteDimensional.isSchurUnitary_of_irreducible_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurUnitary M := by sorry
