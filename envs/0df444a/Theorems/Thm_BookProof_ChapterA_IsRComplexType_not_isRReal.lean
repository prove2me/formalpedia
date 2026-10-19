-- Prove2me | Theorems.Thm_BookProof_ChapterA_IsRComplexType_not_isRReal
-- name    : BookProof.ChapterA.IsRComplexType.not_isRReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:12:47.414589+00:00
-- url     : https://prove2.me/theorems/62baace3-c7c2-4390-a0e0-3a706f2341c8
-- title:
--   `BookProof.ChapterA.IsRComplexType.not_isRReal` [Nontrivial W] {M : System ℝ W} (h : IsRComplexType M) : ¬ IsRReal M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.IsRComplexType.not_isRReal` [Nontrivial W] {M : System ℝ W} (h : IsRComplexType M) : ¬ IsRReal M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.IsRComplexType.not_isRReal`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.IsRComplexType.not_isRReal
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.IsRComplexType.not_isRReal [Nontrivial W] {M : System ℝ W}
    (h : IsRComplexType M) : ¬ IsRReal M := by sorry
