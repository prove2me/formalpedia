-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_nsQuadraticDiffH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.DifferentialL2.nsQuadraticDiffH_essentiallySelfAdjointOn_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:33:51.658453+00:00
-- url     : https://prove2.me/theorems/5c4d7c00-a3ab-41d0-afe6-fbd007837fd4
-- title:
--   The Lean 4 theorem `nsQuadraticDiffH_essentiallySelfAdjointOn_core` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsQuadraticDiffH_essentiallySelfAdjointOn_core` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.nsQuadraticDiffH_essentiallySelfAdjointOn_core
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

theorem BookProof.NavierStokesFlow.DifferentialL2.nsQuadraticDiffH_essentiallySelfAdjointOn_core
    (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ) (lap : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsQuadraticDiffH nu grad lap)) := by sorry
