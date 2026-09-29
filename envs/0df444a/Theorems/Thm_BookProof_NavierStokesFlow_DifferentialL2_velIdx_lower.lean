-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_velIdx_lower
-- name    : BookProof.NavierStokesFlow.DifferentialL2.velIdx_lower
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:28:25.184241+00:00
-- url     : https://prove2.me/theorems/eb1690d3-71da-4ac7-9698-cc13ad9d337b
-- title:
--   The Lean 4 theorem `velIdx_lower` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velIdx_lower` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.velIdx_lower
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

theorem BookProof.NavierStokesFlow.DifferentialL2.velIdx_lower (i : Fin 3) (b : Vel) :
    velIdx (lower i b) = velIdx b - Finsupp.single i 1 := by sorry
