-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_rangeClosure_le_ker
-- name    : BookProof.ChapterSchurIrreducible.rangeClosure_le_ker
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:01:21.558688+00:00
-- url     : https://prove2.me/theorems/d80973bc-67e2-4d8f-bf99-1dabf5d1be46
-- title:
--   `BookProof.ChapterSchurIrreducible.rangeClosure_le_ker` {F G : V →L[ℂ] V} (h : G * F = 0) : rangeClosure F ≤ LinearMap.ker (G : V →ₗ[ℂ] V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.rangeClosure_le_ker` {F G : V →L[ℂ] V} (h : G * F = 0) : rangeClosure F ≤ LinearMap.ker (G : V →ₗ[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.rangeClosure_le_ker`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.rangeClosure_le_ker
import Definitions.Def_ChapterA
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.rangeClosure_le_ker {F G : V →L[ℂ] V} (h : G * F = 0) :
    rangeClosure F ≤ LinearMap.ker (G : V →ₗ[ℂ] V) := by sorry
