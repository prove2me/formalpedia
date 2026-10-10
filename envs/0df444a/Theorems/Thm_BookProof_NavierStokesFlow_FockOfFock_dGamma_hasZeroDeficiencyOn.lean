-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_dGamma_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:41:53.144848+00:00
-- url     : https://prove2.me/theorems/2a0592f1-6c54-40ee-84b1-78597b333965
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn` (ω : M → ℝ) : HasZeroDeficiencyOn (FockDom M) (dGamma ω)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn` (ω : M → ℝ) : HasZeroDeficiencyOn (FockDom M) (dGamma ω)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]

theorem BookProof.NavierStokesFlow.FockOfFock.dGamma_hasZeroDeficiencyOn (ω : M → ℝ) :
    HasZeroDeficiencyOn (FockDom M) (dGamma ω) := by sorry
