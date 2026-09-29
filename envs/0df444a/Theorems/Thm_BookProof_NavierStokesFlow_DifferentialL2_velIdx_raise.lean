-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_velIdx_raise
-- name    : BookProof.NavierStokesFlow.DifferentialL2.velIdx_raise
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:28:32.845525+00:00
-- url     : https://prove2.me/theorems/e28a13ce-4753-4b13-9f3b-dfc93bb5ecf5
-- title:
--   The Lean 4 theorem `velIdx_raise` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velIdx_raise` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.velIdx_raise
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

theorem BookProof.NavierStokesFlow.DifferentialL2.velIdx_raise (i : Fin 3) (b : Vel) :
    velIdx (raise i b) = velIdx b + Finsupp.single i 1 := by sorry
