-- Prove2me | Theorems.Thm_BookProof_ChapterSchurFiniteDim_isSchurUnitary_of_irreducible
-- name    : BookProof.ChapterSchurFiniteDim.isSchurUnitary_of_irreducible
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:59:47.321591+00:00
-- url     : https://prove2.me/theorems/a6d6f81d-21f3-4317-97ab-1498594e0fb2
-- title:
--   `BookProof.ChapterSchurFiniteDim.isSchurUnitary_of_irreducible` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : IsIrreducibleSystem M) : IsSchurUnitary M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurFiniteDim`.
--
--   `BookProof.ChapterSchurFiniteDim.isSchurUnitary_of_irreducible` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : IsIrreducibleSystem M) : IsSchurUnitary M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurFiniteDim.isSchurUnitary_of_irreducible`.

-- Generated from ChapterSchurFiniteDim.lean — theorem BookProof.ChapterSchurFiniteDim.isSchurUnitary_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurFiniteDim
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurFiniteDim


open Module


open BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurFiniteDim.isSchurUnitary_of_irreducible [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : IsIrreducibleSystem M) :
    IsSchurUnitary M := by sorry
