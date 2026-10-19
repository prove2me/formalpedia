-- Prove2me | Theorems.Thm_BookProof_ChapterA_IsRReal_excludes_other_types
-- name    : BookProof.ChapterA.IsRReal.excludes_other_types
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:35:05.801845+00:00
-- url     : https://prove2.me/theorems/8a6f882c-fb25-4f6e-acc4-5fdddd4f5cfb
-- title:
--   `BookProof.ChapterA.IsRReal.excludes_other_types` [Nontrivial W] {M : System ℝ W} (h : IsRReal M) : IsRRealType M ∧ ¬ IsRComplexType M ∧ ¬ IsRPseudorealType M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.IsRReal.excludes_other_types` [Nontrivial W] {M : System ℝ W} (h : IsRReal M) : IsRRealType M ∧ ¬ IsRComplexType M ∧ ¬ IsRPseudorealType M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.IsRReal.excludes_other_types`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.IsRReal.excludes_other_types
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.IsRReal.excludes_other_types [Nontrivial W] {M : System ℝ W}
    (h : IsRReal M) : IsRRealType M ∧ ¬ IsRComplexType M ∧ ¬ IsRPseudorealType M := by sorry
