-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalSymbol_eq
-- name    : BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:11:00.53701+00:00
-- url     : https://prove2.me/theorems/279292dd-2ed0-4135-9f96-0887f9b5d732
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq` (j : ℕ) : symbolOfIntegral volume extField intervalDens j = (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq` (j : ℕ) : symbolOfIntegral volume extField intervalDens j = (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockSpace
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockOfFock


open MeasureTheory



open FullEsa LagrangianEsa

variable {M : Type*} [DecidableEq M]
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {K : Type*} [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.intervalSymbol_eq (j : ℕ) :
    symbolOfIntegral volume extField intervalDens j = (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3 := by sorry
