-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlowEuclidean_norm
-- name    : BookProof.NavierStokesFlow.nsFlowEuclidean_norm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:58:14.265848+00:00
-- url     : https://prove2.me/theorems/6abc43ff-5307-49ef-be80-4e8c0aab24e1
-- title:
--   The Lean 4 theorem `nsFlowEuclidean_norm` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlowEuclidean_norm` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.nsFlowEuclidean_norm
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite














variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlowEuclidean_norm (t : ℝ) (psi : EuclideanSpace ℂ (Fin n)) :
    ‖nsFlowEuclidean d t psi‖ = ‖psi‖ := by sorry
