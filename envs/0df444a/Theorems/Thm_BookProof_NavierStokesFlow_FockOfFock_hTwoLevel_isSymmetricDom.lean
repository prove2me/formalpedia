-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_hTwoLevel_isSymmetricDom
-- name    : BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T17:07:35.511986+00:00
-- url     : https://prove2.me/theorems/e728788a-86a8-4b93-a17c-5494c47dc063
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom` (ext : J → ℝ) (eps : K → ℝ) : IsSymmetricDom (hTwoLevel ext eps)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom` (ext : J → ℝ) (eps : K → ℝ) : IsSymmetricDom (hTwoLevel ext eps)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]

omit [DecidableEq J] [DecidableEq K] in

theorem BookProof.NavierStokesFlow.FockOfFock.hTwoLevel_isSymmetricDom (ext : J → ℝ) (eps : K → ℝ) :
    IsSymmetricDom (hTwoLevel ext eps) := by sorry
