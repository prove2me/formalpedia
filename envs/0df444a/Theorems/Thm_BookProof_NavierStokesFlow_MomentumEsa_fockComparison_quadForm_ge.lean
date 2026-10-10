-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockComparison_quadForm_ge
-- name    : BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:51:35.260223+00:00
-- url     : https://prove2.me/theorems/a635a3d6-4c3d-4428-bbde-a0f76886ffb3
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (x : maxDom (fockSymbol n)) : ‖(x : L2I Config)‖ ^ 2 ≤ quadForm (diagMax (fockSy
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (x : maxDom (fockSymbol n)) : ‖(x : L2I Config)‖ ^ 2 ≤ quadForm (diagMax (fockSymbol n)) x
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_quadForm_ge (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k)
    (x : maxDom (fockSymbol n)) :
    ‖(x : L2I Config)‖ ^ 2 ≤ quadForm (diagMax (fockSymbol n)) x := by sorry
