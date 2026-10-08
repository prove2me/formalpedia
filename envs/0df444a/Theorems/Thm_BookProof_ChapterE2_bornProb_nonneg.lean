-- Prove2me | Theorems.Thm_BookProof_ChapterE2_bornProb_nonneg
-- name    : BookProof.ChapterE2.bornProb_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T23:12:19.143232+00:00
-- url     : https://prove2.me/theorems/21a74a71-fae8-45fe-9ac2-296916fbec35
-- title:
--   `BookProof.ChapterE2.bornProb_nonneg` (θ : ℕ → ℝ) (n : ℕ) (i : Fin n) : 0 ≤ bornProb θ n i
-- statement:
--   Prove the following Lean 4 theorem from `ChapterE2`.
--
--   `BookProof.ChapterE2.bornProb_nonneg` (θ : ℕ → ℝ) (n : ℕ) (i : Fin n) : 0 ≤ bornProb θ n i
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterE2.bornProb_nonneg`.

-- Generated from ChapterE2.lean — theorem BookProof.ChapterE2.bornProb_nonneg
import Mathlib
import Definitions.Def_ChapterE2
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterE2


open scoped BigOperators
open Finset

theorem BookProof.ChapterE2.bornProb_nonneg (θ : ℕ → ℝ) (n : ℕ) (i : Fin n) : 0 ≤ bornProb θ n i := by sorry
