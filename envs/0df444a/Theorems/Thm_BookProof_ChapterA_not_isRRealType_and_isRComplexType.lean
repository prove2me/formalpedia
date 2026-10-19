-- Prove2me | Theorems.Thm_BookProof_ChapterA_not_isRRealType_and_isRComplexType
-- name    : BookProof.ChapterA.not_isRRealType_and_isRComplexType
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:56:33.017441+00:00
-- url     : https://prove2.me/theorems/8ad34804-364e-480a-b165-2e78ed88595b
-- title:
--   `BookProof.ChapterA.not_isRRealType_and_isRComplexType` (M : System ℝ W) : ¬ (IsRRealType M ∧ IsRComplexType M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.not_isRRealType_and_isRComplexType` (M : System ℝ W) : ¬ (IsRRealType M ∧ IsRComplexType M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.not_isRRealType_and_isRComplexType`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.not_isRRealType_and_isRComplexType
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.not_isRRealType_and_isRComplexType (M : System ℝ W) :
    ¬ (IsRRealType M ∧ IsRComplexType M) := by sorry
