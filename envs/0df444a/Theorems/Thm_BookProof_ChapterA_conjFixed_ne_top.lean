-- Prove2me | Theorems.Thm_BookProof_ChapterA_conjFixed_ne_top
-- name    : BookProof.ChapterA.conjFixed_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-16T23:55:49.81524+00:00
-- url     : https://prove2.me/theorems/63588a48-b216-44e1-a0d3-cbaa0dfd15c4
-- title:
--   `BookProof.ChapterA.conjFixed_ne_top` [Nontrivial V] (θ : AntiUnitary V) : conjFixed θ ≠ ⊤
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA1f`.
--
--   `BookProof.ChapterA.conjFixed_ne_top` [Nontrivial V] (θ : AntiUnitary V) : conjFixed θ ≠ ⊤
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.conjFixed_ne_top`.

-- Generated from ChapterA1f.lean — theorem BookProof.ChapterA.conjFixed_ne_top
import Mathlib
import Definitions.Def_ChapterA1f
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace RealInnerProductSpace


attribute [local instance] InnerProductSpace.rclikeToReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterA.conjFixed_ne_top [Nontrivial V] (θ : AntiUnitary V) : conjFixed θ ≠ ⊤ := by sorry
