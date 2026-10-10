-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockSymbol_nonneg
-- name    : BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T07:52:41.389036+00:00
-- url     : https://prove2.me/theorems/72411a9a-0be8-4b74-ab0c-dfc27cc5ae99
-- title:
--   `BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (a : Config) : 0 ≤ fockSymbol n a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesMomentumEsa`.
--
--   `BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg` (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (a : Config) : 0 ≤ fockSymbol n a
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg`.

-- Generated from ChapterNavierStokesMomentumEsa.lean — theorem BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa




open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

theorem BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_nonneg (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k) (a : Config) :
    0 ≤ fockSymbol n a := by sorry
