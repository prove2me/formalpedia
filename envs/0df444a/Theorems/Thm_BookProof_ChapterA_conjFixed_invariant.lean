-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjFixed_invariant
-- name    : BookProof.ChapterA.conjFixed_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:55:44.998977+00:00
-- url     : https://prove2.me/theorems/c5fbd3e5-6717-4f4b-8e3f-9d6870a7a387
-- title:
--   `BookProof.ChapterA.conjFixed_invariant` (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) : ∀ m ∈ (rxSystem M).ops, ∀ w ∈ conjFixed θ, m w ∈ conjFixed θ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1f`.
--
--   `BookProof.ChapterA.conjFixed_invariant` (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) : ∀ m ∈ (rxSystem M).ops, ∀ w ∈ conjFixed θ, m w ∈ conjFixed θ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjFixed_invariant`.

-- Generated from ChapterA1f.lean — theorem BookProof.ChapterA.conjFixed_invariant
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

theorem BookProof.ChapterA.conjFixed_invariant (M : System ℂ V) (θ : AntiUnitary V) (hθ : IsConjugation M θ) :
    ∀ m ∈ (rxSystem M).ops, ∀ w ∈ conjFixed θ, m w ∈ conjFixed θ := by sorry
