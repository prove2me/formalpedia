-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coe
-- name    : BookProof.NavierStokesFlow.DifferentialL2.coreOp_coe
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:04:16.525562+00:00
-- url     : https://prove2.me/theorems/dc09a01d-175d-45cd-9972-86c36b8221cb
-- title:
--   The Lean 4 theorem `coreOp_coe` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `coreOp_coe` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.coreOp_coe
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockCoreFL
open BookProof.HermiteProductCore
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

theorem BookProof.NavierStokesFlow.DifferentialL2.coreOp_coe (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ)
    (p : MvPolynomial (Fin d) ℂ) :
    ((coreOp T (coreEquiv p) : polyGaussCore (d := d)) : L2d d) = pgLp (T p) := by sorry
