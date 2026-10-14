-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_hTwoLevel_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:06.711979+00:00
-- url     : https://prove2.me/theorems/c4affb90-0001-4893-a024-f2bc38aefede
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_hasZeroDeficiencyOn` (ext : J → ℝ) (eps : K → ℝ) : HasZeroDeficiencyOn (FockOfFockDom J K) (hTwoLevel ext eps)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_hasZeroDeficiencyOn` (ext : J → ℝ) (eps : K → ℝ) : HasZeroDeficiencyOn (FockOfFockDom J K) (hTwoLevel ext eps)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_hasZeroDeficiencyOn
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

theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_hasZeroDeficiencyOn (ext : J → ℝ) (eps : K → ℝ) :
    HasZeroDeficiencyOn (FockOfFockDom J K) (hTwoLevel ext eps) := by sorry
