-- Prove2me | Theorems.Thm_BookProof_ChapterA_not_isCReal_and_isCPseudoreal
-- name    : BookProof.ChapterA.not_isCReal_and_isCPseudoreal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:50:36.058335+00:00
-- url     : https://prove2.me/theorems/e9f61b6b-32e6-41b9-aafd-f11ada468f8e
-- title:
--   `BookProof.ChapterA.not_isCReal_and_isCPseudoreal` (M : System ℂ V) : ¬ (IsCReal M ∧ IsCPseudoreal M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1c`.
--
--   `BookProof.ChapterA.not_isCReal_and_isCPseudoreal` (M : System ℂ V) : ¬ (IsCReal M ∧ IsCPseudoreal M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.not_isCReal_and_isCPseudoreal`.

-- Generated from ChapterA1c.lean — theorem BookProof.ChapterA.not_isCReal_and_isCPseudoreal
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.not_isCReal_and_isCPseudoreal (M : System ℂ V) :
    ¬ (IsCReal M ∧ IsCPseudoreal M) := by sorry
