-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_hasDerivAt_evalSec
-- name    : BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_evalSec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:04:44.662983+00:00
-- url     : https://prove2.me/theorems/c306513f-ac81-4d03-b2b5-5c2435f3c8c0
-- title:
--   The Lean 4 theorem `hasDerivAt_evalSec` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `hasDerivAt_evalSec` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_evalSec
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

theorem BookProof.NavierStokesFlow.DifferentialL2.hasDerivAt_evalSec (i : Fin d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (fun j => (((sec i x t) j : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun j => ((x j : ℝ) : ℂ)) (pderiv i p)) (x i) := by sorry
