-- Prove2me | Theorems.Thm_BookProof_ChapterSequentialBayes_posterior_sequential_eq_batch
-- name    : BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:24:33.671989+00:00
-- url     : https://prove2.me/theorems/43fc1c15-8fd0-4e88-9f82-dda420016c6b
-- title:
--   `BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch` {Y₁ Y₂ : Type*} (prior : X → ℝ) (L₁ : X → Y₁ → ℝ) (L₂ : X → Y₂ → ℝ) (y₁ : Y₁) (y₂ : Y₂) (h1 :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSequentialBayes`.
--
--   `BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch` {Y₁ Y₂ : Type*} (prior : X → ℝ) (L₁ : X → Y₁ → ℝ) (L₂ : X → Y₂ → ℝ) (y₁ : Y₁) (y₂ : Y₂) (h1 : 0 < totEvidence prior (fun x => L₁ x y₁)) (h2 : 0 < totEvidence prior (fun x => L₁ x y₁ * L₂ x y₂)) : bayesUpdate (BookProof.ChapterBayesInference.posterior prior L₁ y₁) (fun x => L₂ x y₂) = bayesUpdate prior (fun x => L₁ x y₁ * L₂ x y₂)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch`.

-- Generated from ChapterSequentialBayes.lean — theorem BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch
import Mathlib
import Definitions.Def_ChapterSequentialBayes
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterSequentialBayes


open scoped BigOperators


variable {X : Type*} [Fintype X]

theorem BookProof.ChapterSequentialBayes.posterior_sequential_eq_batch {Y₁ Y₂ : Type*}
    (prior : X → ℝ) (L₁ : X → Y₁ → ℝ) (L₂ : X → Y₂ → ℝ) (y₁ : Y₁) (y₂ : Y₂)
    (h1 : 0 < totEvidence prior (fun x => L₁ x y₁))
    (h2 : 0 < totEvidence prior (fun x => L₁ x y₁ * L₂ x y₂)) :
    bayesUpdate (BookProof.ChapterBayesInference.posterior prior L₁ y₁) (fun x => L₂ x y₂)
      = bayesUpdate prior (fun x => L₁ x y₁ * L₂ x y₂) := by sorry
