-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_Intertwined_comp
-- name    : BookProof.NavierStokesFlow.DifferentialL2.Intertwined.comp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:22:22.72298+00:00
-- url     : https://prove2.me/theorems/c6959550-306c-4fb5-b9a8-761e27f450f2
-- title:
--   The Lean 4 theorem `comp` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `comp` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.comp
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

theorem BookProof.NavierStokesFlow.DifferentialL2.Intertwined.comp {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T.comp S) (T'.comp S') := by sorry
