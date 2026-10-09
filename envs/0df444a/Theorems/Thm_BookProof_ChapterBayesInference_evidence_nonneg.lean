-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_evidence_nonneg
-- name    : BookProof.ChapterBayesInference.evidence_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:53:00.574281+00:00
-- url     : https://prove2.me/theorems/67103778-a75c-47b4-92d7-cf709f351e72
-- title:
--   `BookProof.ChapterBayesInference.evidence_nonneg` (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (y : Y) : 0 ≤ evidence prior L y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.evidence_nonneg` (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (y : Y) : 0 ≤ evidence prior L y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.evidence_nonneg`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.evidence_nonneg
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in

theorem BookProof.ChapterBayesInference.evidence_nonneg (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (y : Y) :
    0 ≤ evidence prior L y := by sorry
