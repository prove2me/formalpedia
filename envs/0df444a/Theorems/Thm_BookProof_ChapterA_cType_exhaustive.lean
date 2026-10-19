-- Prove2me | Theorems.Thm_BookProof_ChapterA_cType_exhaustive
-- name    : BookProof.ChapterA.cType_exhaustive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:50:03.420988+00:00
-- url     : https://prove2.me/theorems/f3d8b163-356d-4757-aaf8-d00ee6602ea2
-- title:
--   `BookProof.ChapterA.cType_exhaustive` (M : System ℂ V) : IsCReal M ∨ IsCPseudoreal M ∨ IsCComplex M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1c`.
--
--   `BookProof.ChapterA.cType_exhaustive` (M : System ℂ V) : IsCReal M ∨ IsCPseudoreal M ∨ IsCComplex M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.cType_exhaustive`.

-- Generated from ChapterA1c.lean — theorem BookProof.ChapterA.cType_exhaustive
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.cType_exhaustive (M : System ℂ V) :
    IsCReal M ∨ IsCPseudoreal M ∨ IsCComplex M := by sorry
