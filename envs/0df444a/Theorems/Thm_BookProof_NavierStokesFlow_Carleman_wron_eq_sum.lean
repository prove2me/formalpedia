-- Prove2me | Theorems.Thm_BookProof_NavierStokesFlow_Carleman_wron_eq_sum
-- name    : BookProof.NavierStokesFlow.Carleman.wron_eq_sum
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T06:37:35.692207+00:00
-- url     : https://prove2.me/theorems/f7232522-6329-430b-a2d3-c40d7d17048e
-- title:
--   `BookProof.NavierStokesFlow.Carleman.wron_eq_sum` (c w : ℕ → ℂ) (z : ℂ) (hrec : ∀ n, tridiagFun c w n = z * w n) (N : ℕ) : wron c w N = (z - starRingEnd ℂ z) * ∑ n ∈ Finset.range (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesCarleman`.
--
--   `BookProof.NavierStokesFlow.Carleman.wron_eq_sum` (c w : ℕ → ℂ) (z : ℂ) (hrec : ∀ n, tridiagFun c w n = z * w n) (N : ℕ) : wron c w N = (z - starRingEnd ℂ z) * ∑ n ∈ Finset.range (N + 1), starRingEnd ℂ (w n) * w n
--
--   Formalization note: Lean 4 identifier `BookProof.NavierStokesFlow.Carleman.wron_eq_sum`.

-- Generated from ChapterNavierStokesCarleman.lean — theorem BookProof.NavierStokesFlow.Carleman.wron_eq_sum
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman


open scoped ENNReal



open LpNat DiagonalEsa FullEsa

theorem BookProof.NavierStokesFlow.Carleman.wron_eq_sum (c w : ℕ → ℂ) (z : ℂ)
    (hrec : ∀ n, tridiagFun c w n = z * w n) (N : ℕ) :
    wron c w N
      = (z - starRingEnd ℂ z) * ∑ n ∈ Finset.range (N + 1), starRingEnd ℂ (w n) * w n := by sorry
