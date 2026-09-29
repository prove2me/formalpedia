-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_velIdx_apply
-- name    : BookProof.NavierStokesFlow.DifferentialL2.velIdx_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T00:28:22.468862+00:00
-- url     : https://prove2.me/theorems/407eb187-7420-422d-8801-613890163e06
-- title:
--   The Lean 4 theorem `velIdx_apply` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `velIdx_apply` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.velIdx_apply
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

theorem BookProof.NavierStokesFlow.DifferentialL2.velIdx_apply (b : Vel) (i : Fin 3) : velIdx b i = b i := by sorry
