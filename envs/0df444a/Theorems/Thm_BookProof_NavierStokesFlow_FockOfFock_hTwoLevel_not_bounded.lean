-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_hTwoLevel_not_bounded
-- name    : BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:10:42.095976+00:00
-- url     : https://prove2.me/theorems/709e4827-61f3-4ace-a0b4-3c9d30996fd6
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded` (ext : J → ℝ) (eps : K → ℝ) (hext : ∀ C : ℝ, ∃ j, C < |ext j|) : ¬ ∃ C : ℝ, ∀ f : FockOfFockDom J K,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded` (ext : J → ℝ) (eps : K → ℝ) (hext : ∀ C : ℝ, ∃ j, C < |ext j|) : ¬ ∃ C : ℝ, ∀ f : FockOfFockDom J K, ‖hTwoLevel ext eps f‖ ≤ C * ‖f‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded
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

theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_not_bounded (ext : J → ℝ) (eps : K → ℝ) (hext : ∀ C : ℝ, ∃ j, C < |ext j|) :
    ¬ ∃ C : ℝ, ∀ f : FockOfFockDom J K, ‖hTwoLevel ext eps f‖ ≤ C * ‖f‖ := by sorry
