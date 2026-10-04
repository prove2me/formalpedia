-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_comm_momPoly_mulXPoly
-- name    : BookProof.NavierStokesFlow.DifferentialL2.comm_momPoly_mulXPoly
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T22:42:27.105739+00:00
-- url     : https://prove2.me/theorems/70e1172c-9fe3-4b7b-b598-39996955957a
-- title:
--   The Lean 4 theorem `comm_momPoly_mulXPoly` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `comm_momPoly_mulXPoly` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.comm_momPoly_mulXPoly
import Definitions.Def_ChapterHermiteProductCore
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

theorem BookProof.NavierStokesFlow.DifferentialL2.comm_momPoly_mulXPoly (i k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momPoly i (mulXPoly k p) - mulXPoly k (momPoly i p)
      = C (if i = k then -Complex.I else 0) * p := by sorry
