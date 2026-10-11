-- Prove2me | Theorems.Thm_BookProof_ChapterSequentialBayes_bayesUpdate_nonneg
-- name    : BookProof.ChapterSequentialBayes.bayesUpdate_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:21:12.422989+00:00
-- url     : https://prove2.me/theorems/6b6105df-d2a2-49cb-91d8-626d02eecc59
-- title:
--   `BookProof.ChapterSequentialBayes.bayesUpdate_nonneg` {prior ℓ : X → ℝ} (hprior : ∀ x, 0 ≤ prior x) (hℓ : ∀ x, 0 ≤ ℓ x) (x : X) : 0 ≤ bayesUpdate prior ℓ x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSequentialBayes`.
--
--   `BookProof.ChapterSequentialBayes.bayesUpdate_nonneg` {prior ℓ : X → ℝ} (hprior : ∀ x, 0 ≤ prior x) (hℓ : ∀ x, 0 ≤ ℓ x) (x : X) : 0 ≤ bayesUpdate prior ℓ x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSequentialBayes.bayesUpdate_nonneg`.

-- Generated from ChapterSequentialBayes.lean — theorem BookProof.ChapterSequentialBayes.bayesUpdate_nonneg
import Mathlib
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes


open scoped BigOperators


variable {X : Type*} [Fintype X]

theorem BookProof.ChapterSequentialBayes.bayesUpdate_nonneg {prior ℓ : X → ℝ} (hprior : ∀ x, 0 ≤ prior x)
    (hℓ : ∀ x, 0 ≤ ℓ x) (x : X) : 0 ≤ bayesUpdate prior ℓ x := by sorry
