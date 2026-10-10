-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_pertHam_not_bounded
-- name    : BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:46:11.581491+00:00
-- url     : https://prove2.me/theorems/42f6a5a3-2a75-48c3-8f7b-26a99f044ab3
-- title:
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded` : ¬ ∃ C : ℝ, ∀ x : maxDom linSymbol, ‖pertHam linSymbol (eState 0) (eState 1) x‖ ≤ C * ‖(x : L2I ℕ)‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumPerturbation`.
--
--   `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded` : ¬ ∃ C : ℝ, ∀ x : maxDom linSymbol, ‖pertHam linSymbol (eState 0) (eState 1) x‖ ≤ C * ‖(x : L2I ℕ)‖
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded`.

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded :
    ¬ ∃ C : ℝ, ∀ x : maxDom linSymbol,
      ‖pertHam linSymbol (eState 0) (eState 1) x‖ ≤ C * ‖(x : L2I ℕ)‖ := by sorry
