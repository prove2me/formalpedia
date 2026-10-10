-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockComparison_add_one_surjective
-- name    : BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:54:09.531989+00:00
-- url     : https://prove2.me/theorems/2a9f1d36-80e4-4629-9b95-25f895e47bcb
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (f : L2I Config) : ∃ x : maxDom (fockSymbol n), (diagMax (fockSymbol n) x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (f : L2I Config) : ∃ x : maxDom (fockSymbol n), (diagMax (fockSymbol n) x : L2I Config) + (x : L2I Config) = f
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.fockComparison_add_one_surjective (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (f : L2I Config) :
    ∃ x : maxDom (fockSymbol n), (diagMax (fockSymbol n) x : L2I Config) + (x : L2I Config) = f := by sorry
