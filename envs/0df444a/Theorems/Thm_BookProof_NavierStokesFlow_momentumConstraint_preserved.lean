-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_momentumConstraint_preserved
-- name    : BookProof.NavierStokesFlow.momentumConstraint_preserved
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:29:38.076989+00:00
-- url     : https://prove2.me/theorems/0f228d50-8ba1-40c3-b831-3990842a5de2
-- title:
--   The Lean 4 theorem `momentumConstraint_preserved` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momentumConstraint_preserved` in the `ChapterNavierStokesFlow` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFlow.lean

-- Generated from ChapterNavierStokesFlow.lean — theorem BookProof.NavierStokesFlow.momentumConstraint_preserved
import Mathlib
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.NavierStokesFlow


open scoped BigOperators Matrix Kronecker ComplexOrder TensorProduct

theorem BookProof.NavierStokesFlow.momentumConstraint_preserved {n : ℕ} (D H A : Matrix (Fin n) (Fin n) ℂ)
    (hDH : BookProof.FreeFieldConstraint.bracket D H = 0)
    (hDA : BookProof.FreeFieldConstraint.bracket D A = 0) :
    BookProof.FreeFieldConstraint.bracket D (BookProof.FreeFieldConstraint.bracket H A) = 0 := by sorry
