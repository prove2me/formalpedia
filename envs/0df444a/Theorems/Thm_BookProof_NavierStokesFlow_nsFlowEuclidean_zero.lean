-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlowEuclidean_zero
-- name    : BookProof.NavierStokesFlow.nsFlowEuclidean_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:58:16.462722+00:00
-- url     : https://prove2.me/theorems/b661ef4d-b1ca-47a4-aa1b-c1ebe2d519fb
-- title:
--   The Lean 4 theorem `nsFlowEuclidean_zero` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlowEuclidean_zero` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.nsFlowEuclidean_zero
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite














variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlowEuclidean_zero (psi : EuclideanSpace ℂ (Fin n)) :
    nsFlowEuclidean d 0 psi = psi := by sorry
