-- Prove2me | Theorems.Thm_BookProof_ChapterA_cplxSub_isSubsystem
-- name    : BookProof.ChapterA.cplxSub_isSubsystem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:51:43.761981+00:00
-- url     : https://prove2.me/theorems/f40b3b52-ae68-4cb9-b6f4-0d90cc8c5a7a
-- title:
--   `BookProof.ChapterA.cplxSub_isSubsystem` [CompleteSpace V] (M : System ℂ V) {Y : Submodule ℝ V} (hJ : ∀ y ∈ Y, (Complex.I : ℂ) • y ∈ Y) (hY : (rxSystem M).IsSubsystem Y) : (M).IsSu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1d`.
--
--   `BookProof.ChapterA.cplxSub_isSubsystem` [CompleteSpace V] (M : System ℂ V) {Y : Submodule ℝ V} (hJ : ∀ y ∈ Y, (Complex.I : ℂ) • y ∈ Y) (hY : (rxSystem M).IsSubsystem Y) : (M).IsSubsystem (cplxSub Y hJ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.cplxSub_isSubsystem`.

-- Generated from ChapterA1d.lean — theorem BookProof.ChapterA.cplxSub_isSubsystem
import Mathlib
import Definitions.Def_ChapterA1d
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace




attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem BookProof.ChapterA.cplxSub_isSubsystem [CompleteSpace V] (M : System ℂ V) {Y : Submodule ℝ V}
    (hJ : ∀ y ∈ Y, (Complex.I : ℂ) • y ∈ Y) (hY : (rxSystem M).IsSubsystem Y) :
    (M).IsSubsystem (cplxSub Y hJ) := by sorry
