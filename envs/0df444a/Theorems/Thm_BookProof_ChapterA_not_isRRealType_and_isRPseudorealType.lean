-- Prove2me | Theorems.Thm_BookProof_ChapterA_not_isRRealType_and_isRPseudorealType
-- name    : BookProof.ChapterA.not_isRRealType_and_isRPseudorealType
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:34:41.696981+00:00
-- url     : https://prove2.me/theorems/e47591af-2125-4be0-8bc0-ddfa13b714c7
-- title:
--   `BookProof.ChapterA.not_isRRealType_and_isRPseudorealType` (M : System ℝ W) : ¬ (IsRRealType M ∧ IsRPseudorealType M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.not_isRRealType_and_isRPseudorealType` (M : System ℝ W) : ¬ (IsRRealType M ∧ IsRPseudorealType M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.not_isRRealType_and_isRPseudorealType`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.not_isRRealType_and_isRPseudorealType
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.not_isRRealType_and_isRPseudorealType (M : System ℝ W) :
    ¬ (IsRRealType M ∧ IsRPseudorealType M) := by sorry
