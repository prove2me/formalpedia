-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_ne_bot
-- name    : BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:01:01.161979+00:00
-- url     : https://prove2.me/theorems/69cc9ecf-916a-4582-ba95-ccc40f215ef5
-- title:
--   `BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot` {F : V →L[ℂ] V} (hF : F ≠ 0) : rangeClosure F ≠ ⊥
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot` {F : V →L[ℂ] V} (hF : F ≠ 0) : rangeClosure F ≠ ⊥
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot {F : V →L[ℂ] V} (hF : F ≠ 0) : rangeClosure F ≠ ⊥ := by sorry
