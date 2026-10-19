-- Prove2me | Theorems.Thm_BookProof_ChapterA_realSub_isSubsystem
-- name    : BookProof.ChapterA.realSub_isSubsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:51:50.351987+00:00
-- url     : https://prove2.me/theorems/de9b12a1-1cd4-4505-ae03-509c3b4c8986
-- title:
--   `BookProof.ChapterA.realSub_isSubsystem` [CompleteSpace V] (M : System ℂ V) {X : Submodule ℂ V} (hX : (M).IsSubsystem X) : (rxSystem M).IsSubsystem (realSub X)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1d`.
--
--   `BookProof.ChapterA.realSub_isSubsystem` [CompleteSpace V] (M : System ℂ V) {X : Submodule ℂ V} (hX : (M).IsSubsystem X) : (rxSystem M).IsSubsystem (realSub X)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.realSub_isSubsystem`.

-- Generated from ChapterA1d.lean — theorem BookProof.ChapterA.realSub_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1d
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace




attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterA.realSub_isSubsystem [CompleteSpace V] (M : System ℂ V) {X : Submodule ℂ V}
    (hX : (M).IsSubsystem X) : (rxSystem M).IsSubsystem (realSub X) := by sorry
