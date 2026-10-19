-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_BilinearEsa_bilH_not_bounded
-- name    : BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:58:58.242987+00:00
-- url     : https://prove2.me/theorems/ae835270-2768-4452-a37f-8316eca45b52
-- title:
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded` (κ : J → ℝ) (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) : ∃ x : lpFiniteModes (ℕ × J), ‖((x : lpFiniteModes (ℕ × J)) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesBilinearEsa`.
--
--   `BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded` (κ : J → ℝ) (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) : ∃ x : lpFiniteModes (ℕ × J), ‖((x : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))‖ = 1 ∧ C < ‖bilH κ x‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded`.

-- Generated from ChapterNavierStokesBilinearEsa.lean — theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesBilinearEsa
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.BilinearEsa


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine

variable {J : Type*}

theorem BookProof.NavierStokesFlow.BilinearEsa.bilH_not_bounded (κ : J → ℝ) (hunb : ∀ C : ℝ, ∃ j, C < κ j) (C : ℝ) :
    ∃ x : lpFiniteModes (ℕ × J),
      ‖((x : lpFiniteModes (ℕ × J)) : L2I (ℕ × J))‖ = 1 ∧ C < ‖bilH κ x‖ := by sorry
