-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_nsFlowEuclidean_hasDerivAt
-- name    : BookProof.NavierStokesFlow.nsFlowEuclidean_hasDerivAt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:58:04.835239+00:00
-- url     : https://prove2.me/theorems/ef2e43d2-c95d-4be0-9ee3-2420aabb9110
-- title:
--   The Lean 4 theorem `nsFlowEuclidean_hasDerivAt` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsFlowEuclidean_hasDerivAt` in the `ChapterNavierStokesEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesEsa.lean

-- Generated from ChapterNavierStokesEsa.lean — theorem BookProof.NavierStokesFlow.nsFlowEuclidean_hasDerivAt
import Mathlib
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.NavierStokesFlow








open scoped Matrix



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

















variable {ι : Type*}









open BookProof.ChapterContinuityUnitaryInfinite














variable {n : ℕ} (d : NSTruncation n)

theorem BookProof.NavierStokesFlow.nsFlowEuclidean_hasDerivAt (psi : EuclideanSpace ℂ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => nsFlowEuclidean d s psi)
      (Complex.I • Matrix.toEuclideanLin (nsHamiltonian d) (nsFlowEuclidean d t psi)) t := by sorry
