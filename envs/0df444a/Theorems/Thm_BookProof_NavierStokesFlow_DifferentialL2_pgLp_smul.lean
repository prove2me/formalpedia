-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_pgLp_smul
-- name    : BookProof.NavierStokesFlow.DifferentialL2.pgLp_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:01:24.96856+00:00
-- url     : https://prove2.me/theorems/af5db16b-3127-4958-ba20-94bdaa5e91c0
-- title:
--   The Lean 4 theorem `pgLp_smul` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `pgLp_smul` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.pgLp_smul
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

theorem BookProof.NavierStokesFlow.DifferentialL2.pgLp_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgLp (c • p) = c • pgLp p := by sorry
