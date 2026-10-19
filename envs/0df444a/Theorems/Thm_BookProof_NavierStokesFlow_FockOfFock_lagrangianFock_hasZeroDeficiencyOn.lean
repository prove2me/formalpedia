-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lagrangianFock_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T19:17:56.833657+00:00
-- url     : https://prove2.me/theorems/63bcb6ab-90b9-4853-97bd-e5702b58e238
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn` (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) : HasZeroDeficiencyOn
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn` (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) : HasZeroDeficiencyOn (lagrangianFockData nu hnu p q dr force cst).D (lagrangianFockData nu hnu p q dr force cst).hFull
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn
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
variable {M : Type*} [DecidableEq M] {Ω : Type*} [MeasurableSpace Ω]
variable {J K : Type*} [DecidableEq J] [DecidableEq K]

theorem BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_hasZeroDeficiencyOn (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ)
    (force : Fin 3 → ℝ) (cst : M → ℝ) :
    HasZeroDeficiencyOn (lagrangianFockData nu hnu p q dr force cst).D
      (lagrangianFockData nu hnu p q dr force cst).hFull := by sorry
