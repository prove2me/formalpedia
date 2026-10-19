-- Prove2me | Theorems.Thm_BookProof_ChapterA_IsRReal_isRRealType
-- name    : BookProof.ChapterA.IsRReal.isRRealType
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:12:38.386094+00:00
-- url     : https://prove2.me/theorems/36641f7c-6604-4ce6-a4d3-a9e680e61a25
-- title:
--   `BookProof.ChapterA.IsRReal.isRRealType` [Nontrivial W] {M : System ℝ W} (h : IsRReal M) : IsRRealType M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.IsRReal.isRRealType` [Nontrivial W] {M : System ℝ W} (h : IsRReal M) : IsRRealType M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.IsRReal.isRRealType`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.IsRReal.isRRealType
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.IsRReal.isRRealType [Nontrivial W] {M : System ℝ W} (h : IsRReal M) :
    IsRRealType M := by sorry
