-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_momOp_apply_eq_differential
-- name    : BookProof.NavierStokesFlow.DifferentialL2.momOp_apply_eq_differential
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:42:59.023231+00:00
-- url     : https://prove2.me/theorems/af3644ba-6ab5-4bf5-b7af-aafbfd57cc50
-- title:
--   The Lean 4 theorem `momOp_apply_eq_differential` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `momOp_apply_eq_differential` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.momOp_apply_eq_differential
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
open BookProof.HermiteProductCore
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

theorem BookProof.NavierStokesFlow.DifferentialL2.momOp_apply_eq_differential (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    pgFun (momPoly i p) x
      = -Complex.I * deriv (fun t : ℝ => pgFun p (sec i x t)) (x i) := by sorry
