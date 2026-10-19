-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjFixed_ne_bot
-- name    : BookProof.ChapterA.conjFixed_ne_bot
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:55:47.872989+00:00
-- url     : https://prove2.me/theorems/bfffeb5d-5d77-440e-ab70-4436feb47e6c
-- title:
--   `BookProof.ChapterA.conjFixed_ne_bot` [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) : conjFixed θ ≠ ⊥
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1f`.
--
--   `BookProof.ChapterA.conjFixed_ne_bot` [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) : conjFixed θ ≠ ⊥
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjFixed_ne_bot`.

-- Generated from ChapterA1f.lean — theorem BookProof.ChapterA.conjFixed_ne_bot
import Mathlib
import Definitions.Def_ChapterA1f
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.conjFixed_ne_bot [Nontrivial V] (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = x) :
    conjFixed θ ≠ ⊥ := by sorry
