-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_sub
-- name    : BookProof.NavierStokesFlow.DifferentialL2.Intertwined.sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:04.017408+00:00
-- url     : https://prove2.me/theorems/22b6fd57-99be-407c-a68b-5eae877677ff
-- title:
--   The Lean 4 theorem `sub` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `sub` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.sub
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

theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.sub {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T - S) (T' - S') := by sorry
