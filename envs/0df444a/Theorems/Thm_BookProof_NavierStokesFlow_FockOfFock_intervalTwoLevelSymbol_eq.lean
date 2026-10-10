-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalTwoLevelSymbol_eq
-- name    : BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevelSymbol_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T07:23:09.640917+00:00
-- url     : https://prove2.me/theorems/fb66ecca-6a94-464a-ac22-032c8b74b3fb
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevelSymbol_eq` (eps : K → ℝ) : intervalTwoLevelSymbol eps = symbolOfIntegral volume extField parcelDens + innerEnergySymbol eps
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevelSymbol_eq` (eps : K → ℝ) : intervalTwoLevelSymbol eps = symbolOfIntegral volume extField parcelDens + innerEnergySymbol eps
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevelSymbol_eq`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevelSymbol_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {K : Type*} [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.intervalTwoLevelSymbol_eq (eps : K → ℝ) :
    intervalTwoLevelSymbol eps
      = symbolOfIntegral volume extField parcelDens + innerEnergySymbol eps := by sorry
