-- Prove2me | Theorems.Thm_BookProof_ChapterA_IsRPseudorealType_not_isRReal
-- name    : BookProof.ChapterA.IsRPseudorealType.not_isRReal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:12:50.829979+00:00
-- url     : https://prove2.me/theorems/cd1cd35e-2fb5-40c5-82b3-a8f945731e7f
-- title:
--   `BookProof.ChapterA.IsRPseudorealType.not_isRReal` [Nontrivial W] {M : System ℝ W} (h : IsRPseudorealType M) : ¬ IsRReal M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.IsRPseudorealType.not_isRReal` [Nontrivial W] {M : System ℝ W} (h : IsRPseudorealType M) : ¬ IsRReal M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.IsRPseudorealType.not_isRReal`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.IsRPseudorealType.not_isRReal
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.IsRPseudorealType.not_isRReal [Nontrivial W] {M : System ℝ W}
    (h : IsRPseudorealType M) : ¬ IsRReal M := by sorry
