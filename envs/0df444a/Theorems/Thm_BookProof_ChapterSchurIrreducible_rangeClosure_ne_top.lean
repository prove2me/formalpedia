-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_ne_top
-- name    : BookProof.ChapterSchurIrreducible.rangeClosure_ne_top
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:01:29.800825+00:00
-- url     : https://prove2.me/theorems/579da804-b85e-4a3c-8d09-c1c198fafd38
-- title:
--   `BookProof.ChapterSchurIrreducible.rangeClosure_ne_top` {F G : V →L[ℂ] V} (hG : G ≠ 0) (h : G * F = 0) : rangeClosure F ≠ ⊤
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.rangeClosure_ne_top` {F G : V →L[ℂ] V} (hG : G ≠ 0) (h : G * F = 0) : rangeClosure F ≠ ⊤
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.rangeClosure_ne_top`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.rangeClosure_ne_top
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.rangeClosure_ne_top {F G : V →L[ℂ] V} (hG : G ≠ 0) (h : G * F = 0) :
    rangeClosure F ≠ ⊤ := by sorry
