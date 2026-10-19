-- Prove2me | Theorems.Thm_BookProof_ChapterA_not_isCPseudoreal_and_isCComplex
-- name    : BookProof.ChapterA.not_isCPseudoreal_and_isCComplex
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:51:12.838829+00:00
-- url     : https://prove2.me/theorems/37cb040b-89e2-4862-8a38-d060fe322f57
-- title:
--   `BookProof.ChapterA.not_isCPseudoreal_and_isCComplex` (M : System ℂ V) : ¬ (IsCPseudoreal M ∧ IsCComplex M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1c`.
--
--   `BookProof.ChapterA.not_isCPseudoreal_and_isCComplex` (M : System ℂ V) : ¬ (IsCPseudoreal M ∧ IsCComplex M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.not_isCPseudoreal_and_isCComplex`.

-- Generated from ChapterA1c.lean — theorem BookProof.ChapterA.not_isCPseudoreal_and_isCComplex
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.not_isCPseudoreal_and_isCComplex (M : System ℂ V) :
    ¬ (IsCPseudoreal M ∧ IsCComplex M) := by sorry
