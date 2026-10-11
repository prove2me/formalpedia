-- Prove2me | Theorems.Thm_BookProof_ChapterSequentialBayes_bayesUpdate_evidence
-- name    : BookProof.ChapterSequentialBayes.bayesUpdate_evidence
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:21:23.313127+00:00
-- url     : https://prove2.me/theorems/725935a4-dd0d-4d94-bbc9-b7e67023a4dc
-- title:
--   `BookProof.ChapterSequentialBayes.bayesUpdate_evidence` {prior ℓ₁ ℓ₂ : X → ℝ} : (∑ x, bayesUpdate prior ℓ₁ x * ℓ₂ x) = (∑ x, prior x * (ℓ₁ x * ℓ₂ x)) / (∑ x,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSequentialBayes`.
--
--   `BookProof.ChapterSequentialBayes.bayesUpdate_evidence` {prior ℓ₁ ℓ₂ : X → ℝ} : (∑ x, bayesUpdate prior ℓ₁ x * ℓ₂ x) = (∑ x, prior x * (ℓ₁ x * ℓ₂ x)) / (∑ x, prior x * ℓ₁ x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSequentialBayes.bayesUpdate_evidence`.

-- Generated from ChapterSequentialBayes.lean — theorem BookProof.ChapterSequentialBayes.bayesUpdate_evidence
import Mathlib
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes


open scoped BigOperators


variable {X : Type*} [Fintype X]

theorem BookProof.ChapterSequentialBayes.bayesUpdate_evidence {prior ℓ₁ ℓ₂ : X → ℝ} :
    (∑ x, bayesUpdate prior ℓ₁ x * ℓ₂ x)
      = (∑ x, prior x * (ℓ₁ x * ℓ₂ x)) / (∑ x, prior x * ℓ₁ x) := by sorry
