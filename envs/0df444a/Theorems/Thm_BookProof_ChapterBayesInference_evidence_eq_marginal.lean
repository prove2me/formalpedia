-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_evidence_eq_marginal
-- name    : BookProof.ChapterBayesInference.evidence_eq_marginal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T18:52:55.640221+00:00
-- url     : https://prove2.me/theorems/4109e411-b723-49f0-9ae5-5d687e4787fe
-- title:
--   `BookProof.ChapterBayesInference.evidence_eq_marginal` (y : Y) : evidence prior L y = ∑ x, joint prior L x y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.evidence_eq_marginal` (y : Y) : evidence prior L y = ∑ x, joint prior L x y
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.evidence_eq_marginal`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.evidence_eq_marginal
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

omit [Fintype Y] [DecidableEq X] [DecidableEq Y] in

theorem BookProof.ChapterBayesInference.evidence_eq_marginal (y : Y) : evidence prior L y = ∑ x, joint prior L x y := by sorry
