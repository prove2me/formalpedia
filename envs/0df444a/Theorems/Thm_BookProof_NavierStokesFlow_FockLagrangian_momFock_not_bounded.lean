-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockLagrangian_momFock_not_bounded
-- name    : BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-18T13:49:21.441652+00:00
-- url     : https://prove2.me/theorems/764a7c2c-d074-4677-80e6-fd804e1b19f2
-- title:
--   `BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded` : ¬ ∃ C : ℝ, ∀ v : momFock.core, ‖((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)‖ ≤ C * ‖((v : momFock.core)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockParcels`.
--
--   `BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded` : ¬ ∃ C : ℝ, ∀ v : momFock.core, ‖((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)‖ ≤ C * ‖((v : momFock.core) : Lp ℂ 2 fockR)‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded`.

-- Generated from ChapterNavierStokesFockParcels.lean — theorem BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockParcels
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockLagrangian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockLagrangian


open MeasureTheory



open FullEsa FockContinuum

variable {Ω : Type*} [MeasurableSpace Ω]

theorem BookProof.NavierStokesFlow.FockLagrangian.momFock_not_bounded :
    ¬ ∃ C : ℝ, ∀ v : momFock.core,
      ‖((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)‖
        ≤ C * ‖((v : momFock.core) : Lp ℂ 2 fockR)‖ := by sorry
