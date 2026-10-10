-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_not_bounded
-- name    : BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:42:43.707745+00:00
-- url     : https://prove2.me/theorems/9aedd385-150f-43b5-bb28-c34a26d2ec52
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded` (ω : M → ℝ) (hω : ∀ C : ℝ, ∃ m, C < |ω m|) : ¬ ∃ C : ℝ, ∀ f : FockDom M, ‖dGamma ω f‖ ≤ C * ‖f‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded` (ω : M → ℝ) (hω : ∀ C : ℝ, ∃ m, C < |ω m|) : ¬ ∃ C : ℝ, ∀ f : FockDom M, ‖dGamma ω f‖ ≤ C * ‖f‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded
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

theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_not_bounded (ω : M → ℝ) (hω : ∀ C : ℝ, ∃ m, C < |ω m|) :
    ¬ ∃ C : ℝ, ∀ f : FockDom M, ‖dGamma ω f‖ ≤ C * ‖f‖ := by sorry
