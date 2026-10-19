-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjFixed_isSubsystem
-- name    : BookProof.ChapterA.conjFixed_isSubsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:55:28.88487+00:00
-- url     : https://prove2.me/theorems/1de17628-cd52-4345-8e3c-2d5179c94f3a
-- title:
--   `BookProof.ChapterA.conjFixed_isSubsystem` (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) : (rxSystem M).IsSubsystem (conjFixed θ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1f`.
--
--   `BookProof.ChapterA.conjFixed_isSubsystem` (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) : (rxSystem M).IsSubsystem (conjFixed θ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjFixed_isSubsystem`.

-- Generated from ChapterA1f.lean — theorem BookProof.ChapterA.conjFixed_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1f
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.conjFixed_isSubsystem (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) :
    (rxSystem M).IsSubsystem (conjFixed θ) := by sorry
