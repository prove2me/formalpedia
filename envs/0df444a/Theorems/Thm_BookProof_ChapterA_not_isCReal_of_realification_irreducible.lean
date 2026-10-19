-- Prove2me | Theorems.Thm_BookProof_ChapterA_not_isCReal_of_realification_irreducible
-- name    : BookProof.ChapterA.not_isCReal_of_realification_irreducible
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:56:27.550003+00:00
-- url     : https://prove2.me/theorems/1958104c-2475-4098-a39f-15aba9c59945
-- title:
--   `BookProof.ChapterA.not_isCReal_of_realification_irreducible` [Nontrivial V] (M : System ℂ V) (h : (rxSystem M).IsIrreducible) : ¬ IsCReal M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1f`.
--
--   `BookProof.ChapterA.not_isCReal_of_realification_irreducible` [Nontrivial V] (M : System ℂ V) (h : (rxSystem M).IsIrreducible) : ¬ IsCReal M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.not_isCReal_of_realification_irreducible`.

-- Generated from ChapterA1f.lean — theorem BookProof.ChapterA.not_isCReal_of_realification_irreducible
import Mathlib
import Definitions.Def_ChapterA1f
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.not_isCReal_of_realification_irreducible [Nontrivial V] (M : System ℂ V)
    (h : (rxSystem M).IsIrreducible) : ¬ IsCReal M := by sorry
