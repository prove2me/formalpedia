-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_FockOfFock_lagrangianFock_not_bounded
-- name    : BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:11:07.183989+00:00
-- url     : https://prove2.me/theorems/3432643a-74aa-4787-8efb-a196d7089ce9
-- title:
--   `BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded` (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) (h : ∀ C : ℝ, ∃ m, C < |lagSymbol nu p...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFockEsa`.
--
--   `BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded` (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) (h : ∀ C : ℝ, ∃ m, C < |lagSymbol nu p q dr force cst m|) : ¬ ((∃ C : ℝ, ∀ f : FockDom M, ‖hFockLag nu p q dr force cst f‖ ≤ C * ‖f‖))
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded`.

-- Generated from ChapterNavierStokesFockEsa.lean — theorem BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesFockEsa
import Definitions.Def_ChapterFockSecondQuantization
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

theorem BookProof.NavierStokesFlow.FockOfFock.lagrangianFock_not_bounded (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) (h : ∀ C : ℝ, ∃ m, C < |lagSymbol nu p q dr force cst m|) :
    ¬ ((∃ C : ℝ, ∀ f : FockDom M, ‖hFockLag nu p q dr force cst f‖ ≤ C * ‖f‖)) := by sorry
