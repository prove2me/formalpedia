-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_hFockLag_hasZeroDeficiencyOn
-- name    : BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:10:55.449956+00:00
-- url     : https://prove2.me/theorems/764cc0b3-af4f-4e74-9074-c438ed582019
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn` (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) : HasZeroDeficiencyOn (FockDom M) (hFockLag
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn` (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) : HasZeroDeficiencyOn (FockDom M) (hFockLag nu p q dr force cst)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn
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

theorem BookProof.NavierStokesFlow.FockOfFock.hFockLag_hasZeroDeficiencyOn (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) :
    HasZeroDeficiencyOn (FockDom M) (hFockLag nu p q dr force cst) := by sorry
