-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_hTwoLevel_oneParticle
-- name    : BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_oneParticle
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:48.288077+00:00
-- url     : https://prove2.me/theorems/2e1064fc-9382-4798-b2e4-273d379ceec6
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_oneParticle` (ext : J → ℝ) (eps : K → ℝ) (j : J) (c : Conf K) : hTwoLevel ext eps (fockBasis (Finsupp.single (j, c) 1)) = (((ext j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_oneParticle` (ext : J → ℝ) (eps : K → ℝ) (j : J) (c : Conf K) : hTwoLevel ext eps (fockBasis (Finsupp.single (j, c) 1)) = (((ext j + confEnergy eps c : ℝ)) : ℂ) • fockBasis (Finsupp.single (j, c) 1)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_oneParticle`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_oneParticle
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

theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_oneParticle (ext : J → ℝ) (eps : K → ℝ) (j : J) (c : Conf K) :
    hTwoLevel ext eps (fockBasis (Finsupp.single (j, c) 1))
      = (((ext j + confEnergy eps c : ℝ)) : ℂ) • fockBasis (Finsupp.single (j, c) 1) := by sorry
