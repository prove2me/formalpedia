-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_isClosed_rangeClosure
-- name    : BookProof.ChapterSchurIrreducible.isClosed_rangeClosure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:00:57.240975+00:00
-- url     : https://prove2.me/theorems/f7498d28-9b6f-449f-9867-4cecd8758f37
-- title:
--   `BookProof.ChapterSchurIrreducible.isClosed_rangeClosure` (F : V →L[ℂ] V) : IsClosed ((rangeClosure F : Submodule ℂ V) : Set V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.isClosed_rangeClosure` (F : V →L[ℂ] V) : IsClosed ((rangeClosure F : Submodule ℂ V) : Set V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.isClosed_rangeClosure`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.isClosed_rangeClosure
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.isClosed_rangeClosure (F : V →L[ℂ] V) :
    IsClosed ((rangeClosure F : Submodule ℂ V) : Set V) := by sorry
