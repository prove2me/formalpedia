-- Prove2me | Theorems.Thm_BookProof_ChapterE2_bornProb_sum_eq_one
-- name    : BookProof.ChapterE2.bornProb_sum_eq_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T23:12:02.650288+00:00
-- url     : https://prove2.me/theorems/8348899a-b7ca-4937-b8e0-cdfb3c4badd2
-- title:
--   `BookProof.ChapterE2.bornProb_sum_eq_one` (θ : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) : ∑ i : Fin n, bornProb θ n i = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE2`.
--
--   `BookProof.ChapterE2.bornProb_sum_eq_one` (θ : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) : ∑ i : Fin n, bornProb θ n i = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE2.bornProb_sum_eq_one`.

-- Generated from ChapterE2.lean — theorem BookProof.ChapterE2.bornProb_sum_eq_one
import Mathlib
import Definitions.Def_ChapterE2
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterE2


open scoped BigOperators
open Finset

theorem BookProof.ChapterE2.bornProb_sum_eq_one (θ : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i : Fin n, bornProb θ n i = 1 := by sorry
