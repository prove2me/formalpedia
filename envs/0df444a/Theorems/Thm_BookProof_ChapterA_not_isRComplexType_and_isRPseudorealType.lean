-- Prove2me | Theorems.Thm_BookProof_ChapterA_not_isRComplexType_and_isRPseudorealType
-- name    : BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:12:56.527106+00:00
-- url     : https://prove2.me/theorems/070f9cc8-473e-4417-82c9-92596506ec64
-- title:
--   `BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType` (M : System ℝ W) : ¬ (IsRComplexType M ∧ IsRPseudorealType M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType` (M : System ℝ W) : ¬ (IsRComplexType M ∧ IsRPseudorealType M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.not_isRComplexType_and_isRPseudorealType (M : System ℝ W) :
    ¬ (IsRComplexType M ∧ IsRPseudorealType M) := by sorry
