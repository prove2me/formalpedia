-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_AffineBlock_affBlockH_not_bounded
-- name    : BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:57:21.683001+00:00
-- url     : https://prove2.me/theorems/2fd2302c-7563-4613-a6e1-eea0f4164f61
-- title:
--   `BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) : ∃ x :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesAffineBlockEsa`.
--
--   `BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded` (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j) (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) : ∃ x : lpFiniteModes (ℕ × J), ‖((x : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))‖ = 1 ∧ C < ‖affBlockH κ c hκ hc x‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded`.

-- Generated from ChapterNavierStokesAffineBlockEsa.lean — theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineBlockEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneResolvent
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineBlock


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian AffineFiber BilinearEsa

variable {J : Type*}

theorem BookProof.NavierStokesFlow.AffineBlock.affBlockH_not_bounded (κ c : J → ℝ) (hκ : ∀ j, 0 ≤ κ j) (hc : ∀ j, 0 ≤ c j)
    (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) :
    ∃ x : lpFiniteModes (ℕ × J),
      ‖((x : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))‖ = 1
        ∧ C < ‖affBlockH κ c hκ hc x‖ := by sorry
