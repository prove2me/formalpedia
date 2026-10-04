-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_nsDiffH_not_bounded
-- name    : BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-02T23:45:47.978435+00:00
-- url     : https://prove2.me/theorems/d9f51d4e-154d-43b0-a806-881e6595ecc5
-- title:
--   The Lean 4 theorem `nsDiffH_not_bounded` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsDiffH_not_bounded` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_not_bounded
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesThreeComponent
open BookProof.HermiteProductCore
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}
variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)



open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

theorem BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_not_bounded (hA : A 0 0 ≠ 0) (K : ℝ) :
    ∃ f : polyGaussCore (d := 3), ‖(f : L2d 3)‖ = 1
      ∧ K < ‖((nsDiffH A c f : polyGaussCore (d := 3)) : L2d 3)‖ := by sorry
