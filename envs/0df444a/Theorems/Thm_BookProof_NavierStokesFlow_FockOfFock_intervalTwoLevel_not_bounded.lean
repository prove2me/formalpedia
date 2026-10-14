-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalTwoLevel_not_bounded
-- name    : BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-11T19:19:04.472915+00:00
-- url     : https://prove2.me/theorems/1ba2d466-8851-45f7-9e66-61bd5df74418
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded` (eps : K → ℝ) : ¬ ∃ C : ℝ, ∀ f : FockOfFockDom ℕ K, ‖dGamma (intervalTwoLevelSymbol eps) f‖ ≤ C * ‖f‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded` (eps : K → ℝ) : ¬ ∃ C : ℝ, ∀ f : FockOfFockDom ℕ K, ‖dGamma (intervalTwoLevelSymbol eps) f‖ ≤ C * ‖f‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {K : Type*} [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_not_bounded (eps : K → ℝ) :
    ¬ ∃ C : ℝ, ∀ f : FockOfFockDom ℕ K,
      ‖dGamma (intervalTwoLevelSymbol eps) f‖ ≤ C * ‖f‖ := by sorry
