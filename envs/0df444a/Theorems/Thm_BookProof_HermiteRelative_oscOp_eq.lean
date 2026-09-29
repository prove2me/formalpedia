-- Prove2me | Theorems.Thm_BookProof_HermiteRelative_oscOp_eq
-- name    : BookProof.HermiteRelative.oscOp_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:10:22.349982+00:00
-- url     : https://prove2.me/theorems/964eb3de-427b-416d-b810-c5dc47d4a6eb
-- title:
--   The Lean 4 theorem `oscOp_eq` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `oscOp_eq` in the `ChapterHermiteRelativeBound` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

-- Generated from ChapterHermiteRelativeBound.lean — theorem BookProof.HermiteRelative.oscOp_eq
import Mathlib
import Definitions.Def_ChapterHermiteRelativeBound
open BookProof.HermiteRelative









open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





variable {d : ℕ}

set_option maxHeartbeats 1000000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive

theorem BookProof.HermiteRelative.oscOp_eq (i : Fin d) :
    coreOp (oscPoly i) = (coreOp (momPoly i)).comp (coreOp (momPoly i))
      + (1/4 : ℂ) • ((coreOp (mulXPoly i)).comp (coreOp (mulXPoly i))) := by sorry
