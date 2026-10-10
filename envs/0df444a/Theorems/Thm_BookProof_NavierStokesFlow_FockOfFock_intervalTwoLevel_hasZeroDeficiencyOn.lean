-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalTwoLevel_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:23:07.686988+00:00
-- url     : https://prove2.me/theorems/fecffc7a-dac2-4377-9836-36521eff4924
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn` (eps : K → ℝ) : HasZeroDeficiencyOn (FockOfFockDom ℕ K) (dGamma (intervalTwoLevelSymbol eps))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn` (eps : K → ℝ) : HasZeroDeficiencyOn (FockOfFockDom ℕ K) (dGamma (intervalTwoLevelSymbol eps))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
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

theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevel_hasZeroDeficiencyOn (eps : K → ℝ) :
    HasZeroDeficiencyOn (FockOfFockDom ℕ K) (dGamma (intervalTwoLevelSymbol eps)) := by sorry
