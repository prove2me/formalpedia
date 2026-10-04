-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_norm_sq_sec
-- name    : BookProof.NavierStokesFlow.DifferentialL2.norm_sq_sec
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:19:57.778388+00:00
-- url     : https://prove2.me/theorems/4e4dd88b-09d9-4e4e-a4a6-288a82bc474f
-- title:
--   The Lean 4 theorem `norm_sq_sec` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sq_sec` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.norm_sq_sec
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

theorem BookProof.NavierStokesFlow.DifferentialL2.norm_sq_sec (i : Fin d) (x : Vd d) (t : ℝ) :
    ‖sec i x t‖ ^ 2 = (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + t ^ 2 := by sorry
