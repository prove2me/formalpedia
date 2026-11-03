-- Prove2me | Theorems.Thm_BookProof_ChapterA_cxSystem_isCReal
-- name    : BookProof.ChapterA.cxSystem_isCReal
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-02T13:31:55.856032+00:00
-- url     : https://prove2.me/theorems/7c3f852e-9660-44f3-a529-e4d2e6fbd052
-- title:
--   `BookProof.ChapterA.cxSystem_isCReal` (M : System ℝ W) : IsCReal (cxSystem M)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1c`.
--
--   `BookProof.ChapterA.cxSystem_isCReal` (M : System ℝ W) : IsCReal (cxSystem M)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.cxSystem_isCReal`.

-- Generated from ChapterA1c.lean — theorem BookProof.ChapterA.cxSystem_isCReal
import Mathlib
import Definitions.Def_ChapterA1c
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
import Definitions.Def_Complexification
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA.AntiUnitary


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace
open BookProof.Complexification

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem BookProof.ChapterA.cxSystem_isCReal (M : System ℝ W) : IsCReal (cxSystem M) := by sorry
