-- Prove2me | Theorems.Thm_BookProof_ChapterA_IsRReal_cxSystem_isCReal
-- name    : BookProof.ChapterA.IsRReal.cxSystem_isCReal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T13:31:55.552209+00:00
-- url     : https://prove2.me/theorems/b2158837-44b1-4b79-8121-7a75e45a141a
-- title:
--   `BookProof.ChapterA.IsRReal.cxSystem_isCReal` {M : System ℝ W} (_ : IsRReal M) : IsCReal (cxSystem M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1c`.
--
--   `BookProof.ChapterA.IsRReal.cxSystem_isCReal` {M : System ℝ W} (_ : IsRReal M) : IsCReal (cxSystem M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.IsRReal.cxSystem_isCReal`.

-- Generated from ChapterA1c.lean — theorem BookProof.ChapterA.IsRReal.cxSystem_isCReal
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
import Definitions.Def_Complexification
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace
open BookProof.Complexification

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.IsRReal.cxSystem_isCReal {M : System ℝ W} (_ : IsRReal M) :
    IsCReal (cxSystem M) := by sorry
