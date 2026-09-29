-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_smul
-- name    : BookProof.NavierStokesFlow.DifferentialL2.Intertwined.smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:21:49.781208+00:00
-- url     : https://prove2.me/theorems/5505d2b5-62e5-4661-aa2e-66d0337d5394
-- title:
--   The Lean 4 theorem `smul` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `smul` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.smul
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

theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.smul {T T'} (c : ℂ) (hT : Intertwined T T') :
    Intertwined (c • T) (c • T') := by sorry
