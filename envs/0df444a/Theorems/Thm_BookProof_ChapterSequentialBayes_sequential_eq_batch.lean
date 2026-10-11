-- Prove2me | Theorems.Thm_BookProof_ChapterSequentialBayes_sequential_eq_batch
-- name    : BookProof.ChapterSequentialBayes.sequential_eq_batch
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:21:27.425582+00:00
-- url     : https://prove2.me/theorems/0cc6bf69-d041-4f80-8421-695f323c5994
-- title:
--   `BookProof.ChapterSequentialBayes.sequential_eq_batch` {prior ℓ₁ ℓ₂ : X → ℝ} (h1 : 0 < totEvidence prior ℓ₁) (h2 : 0 < totEvidence prior (fun x => ℓ₁ x * ℓ₂ x)) :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSequentialBayes`.
--
--   `BookProof.ChapterSequentialBayes.sequential_eq_batch` {prior ℓ₁ ℓ₂ : X → ℝ} (h1 : 0 < totEvidence prior ℓ₁) (h2 : 0 < totEvidence prior (fun x => ℓ₁ x * ℓ₂ x)) : bayesUpdate (bayesUpdate prior ℓ₁) ℓ₂ = bayesUpdate prior (fun x => ℓ₁ x * ℓ₂ x)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSequentialBayes.sequential_eq_batch`.

-- Generated from ChapterSequentialBayes.lean — theorem BookProof.ChapterSequentialBayes.sequential_eq_batch
import Mathlib
import Definitions.Def_ChapterSequentialBayes
open BookProof.ChapterSequentialBayes


open scoped BigOperators


variable {X : Type*} [Fintype X]

theorem BookProof.ChapterSequentialBayes.sequential_eq_batch {prior ℓ₁ ℓ₂ : X → ℝ}
    (h1 : 0 < totEvidence prior ℓ₁)
    (h2 : 0 < totEvidence prior (fun x => ℓ₁ x * ℓ₂ x)) :
    bayesUpdate (bayesUpdate prior ℓ₁) ℓ₂ = bayesUpdate prior (fun x => ℓ₁ x * ℓ₂ x) := by sorry
