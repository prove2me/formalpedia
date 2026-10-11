-- Prove2me | Theorems.Thm_BookProof_ChapterSequentialBayes_posterior_eq_bayesUpdate
-- name    : BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T12:23:13.153366+00:00
-- url     : https://prove2.me/theorems/0847dd10-4505-4c42-8a44-801bb5bb22a5
-- title:
--   `BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate` {Y : Type*} (prior : X → ℝ) (L : X → Y → ℝ) (y : Y) : BookProof.ChapterBayesInference.posterior prior L y = bayesUpdate
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSequentialBayes`.
--
--   `BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate` {Y : Type*} (prior : X → ℝ) (L : X → Y → ℝ) (y : Y) : BookProof.ChapterBayesInference.posterior prior L y = bayesUpdate prior (fun x => L x y)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate`.

-- Generated from ChapterSequentialBayes.lean — theorem BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate
import Mathlib
import Definitions.Def_ChapterSequentialBayes
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference
open BookProof.ChapterSequentialBayes


open scoped BigOperators


variable {X : Type*} [Fintype X]

theorem BookProof.ChapterSequentialBayes.posterior_eq_bayesUpdate {Y : Type*}
    (prior : X → ℝ) (L : X → Y → ℝ) (y : Y) :
    BookProof.ChapterBayesInference.posterior prior L y = bayesUpdate prior (fun x => L x y) := by sorry
