-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_intervalDens_integrable
-- name    : BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:10:55.252272+00:00
-- url     : https://prove2.me/theorems/d44d1090-6119-4c06-8053-e970b0659c35
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable` (j : ℕ) : Integrable (fun ξ => extField ξ * intervalDens j ξ) volume
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable` (j : ℕ) : Integrable (fun ξ => extField ξ * intervalDens j ξ) volume
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable
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

theorem BookProof.NavierStokesFlow.FockOfFock.intervalDens_integrable (j : ℕ) :
    Integrable (fun ξ => extField ξ * intervalDens j ξ) volume := by sorry
