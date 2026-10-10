-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_sum_normSq_le
-- name    : BookProof.NavierStokesFlow.Carleman.sum_normSq_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:34.636816+00:00
-- url     : https://prove2.me/theorems/0ec266d1-ac6c-40f3-9870-daafc4c6898a
-- title:
--   `BookProof.NavierStokesFlow.Carleman.sum_normSq_le` (c w : ℕ → ℂ) (hrec : ∀ n, tridiagFun c w n = Complex.I * w n) (N : ℕ) : ∑ n ∈ Finset.range (N + 1), ‖w n‖ ^ 2 ≤ ‖c N‖...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.sum_normSq_le` (c w : ℕ → ℂ) (hrec : ∀ n, tridiagFun c w n = Complex.I * w n) (N : ℕ) : ∑ n ∈ Finset.range (N + 1), ‖w n‖ ^ 2 ≤ ‖c N‖ * (‖w (N + 1)‖ * ‖w N‖)
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.sum_normSq_le`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.sum_normSq_le
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.sum_normSq_le (c w : ℕ → ℂ) (hrec : ∀ n, tridiagFun c w n = Complex.I * w n) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), ‖w n‖ ^ 2 ≤ ‖c N‖ * (‖w (N + 1)‖ * ‖w N‖) := by sorry
