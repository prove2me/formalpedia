-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_nsDiffH_essentiallySelfAdjointOn_core
-- name    : BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-02T23:45:43.312255+00:00
-- url     : https://prove2.me/theorems/e1c664f3-a4b0-49b3-a623-89866c876f35
-- title:
--   The Lean 4 theorem `nsDiffH_essentiallySelfAdjointOn_core` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `nsDiffH_essentiallySelfAdjointOn_core` in the `ChapterNavierStokesDifferentialL2` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesDifferentialL2.lean

-- Generated from ChapterNavierStokesDifferentialL2.lean — theorem BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
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

theorem BookProof.NavierStokesFlow.DifferentialL2.nsDiffH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) := by sorry
