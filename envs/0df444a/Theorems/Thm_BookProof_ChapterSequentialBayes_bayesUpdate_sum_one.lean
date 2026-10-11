-- Prove2me | Theorems.Thm_BookProof_ChapterSequentialBayes_bayesUpdate_sum_one
-- name    : BookProof.ChapterSequentialBayes.bayesUpdate_sum_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:21:15.770794+00:00
-- url     : https://prove2.me/theorems/f028607d-438b-431a-9fa5-a757bb37024d
-- title:
--   `BookProof.ChapterSequentialBayes.bayesUpdate_sum_one` {prior ℓ : X → ℝ} (hpos : 0 < totEvidence prior ℓ) : ∑ x, bayesUpdate prior ℓ x = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSequentialBayes`.
--
--   `BookProof.ChapterSequentialBayes.bayesUpdate_sum_one` {prior ℓ : X → ℝ} (hpos : 0 < totEvidence prior ℓ) : ∑ x, bayesUpdate prior ℓ x = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSequentialBayes.bayesUpdate_sum_one`.

-- Generated from ChapterSequentialBayes.lean — theorem BookProof.ChapterSequentialBayes.bayesUpdate_sum_one
import Mathlib
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes


open scoped BigOperators


variable {X : Type*} [Fintype X]

theorem BookProof.ChapterSequentialBayes.bayesUpdate_sum_one {prior ℓ : X → ℝ} (hpos : 0 < totEvidence prior ℓ) :
    ∑ x, bayesUpdate prior ℓ x = 1 := by sorry
