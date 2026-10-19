-- Prove2me | Theorems.Thm_BookProof_ChapterA_rType_exhaustive
-- name    : BookProof.ChapterA.rType_exhaustive
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:56:24.617061+00:00
-- url     : https://prove2.me/theorems/a21d9ac9-a60b-4c48-ba40-b89dad3abff0
-- title:
--   `BookProof.ChapterA.rType_exhaustive` (M : System ℝ W) : IsRRealType M ∨ IsRComplexType M ∨ IsRPseudorealType M
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1h`.
--
--   `BookProof.ChapterA.rType_exhaustive` (M : System ℝ W) : IsRRealType M ∨ IsRComplexType M ∨ IsRPseudorealType M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.rType_exhaustive`.

-- Generated from ChapterA1h.lean — theorem BookProof.ChapterA.rType_exhaustive
import Definitions.Def_Complexification
import Mathlib
import Definitions.Def_ChapterA1h
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


open BookProof.Complexification

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.rType_exhaustive (M : System ℝ W) :
    IsRRealType M ∨ IsRComplexType M ∨ IsRPseudorealType M := by sorry
