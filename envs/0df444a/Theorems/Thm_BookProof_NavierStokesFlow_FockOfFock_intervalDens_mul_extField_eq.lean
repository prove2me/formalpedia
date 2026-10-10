-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalDens_mul_extField_eq
-- name    : BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:11:59.632761+00:00
-- url     : https://prove2.me/theorems/9131ddd5-d0a4-4982-8ce0-fdae9d6ba633
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq` (j : ℕ) : (fun ξ => extField ξ * intervalDens j ξ) = Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun ξ => ξ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq` (j : ℕ) : (fun ξ => extField ξ * intervalDens j ξ) = Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun ξ => ξ ^ 2)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq
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

theorem BookProof.NavierStokesFlow.FockOfFock.intervalDens_mul_extField_eq (j : ℕ) :
    (fun ξ => extField ξ * intervalDens j ξ)
      = Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun ξ => ξ ^ 2) := by sorry
