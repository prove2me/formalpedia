-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_posterior_eq_born_conditional
-- name    : BookProof.ChapterBayesInference.posterior_eq_born_conditional
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:53:33.41577+00:00
-- url     : https://prove2.me/theorems/b7204b75-3542-4bef-89e8-bfdcc75cd0fa
-- title:
--   `BookProof.ChapterBayesInference.posterior_eq_born_conditional` (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (y : Y) (x : X) : posterior prior L y x = (Real.sqrt (joint prio
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.posterior_eq_born_conditional` (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y) (y : Y) (x : X) : posterior prior L y x = (Real.sqrt (joint prior L x y)) ^ 2 / ∑ x', (Real.sqrt (joint prior L x' y)) ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.posterior_eq_born_conditional`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.posterior_eq_born_conditional
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

theorem BookProof.ChapterBayesInference.posterior_eq_born_conditional (hprior : ∀ x, 0 ≤ prior x) (hL : ∀ x y, 0 ≤ L x y)
    (y : Y) (x : X) :
    posterior prior L y x =
      (Real.sqrt (joint prior L x y)) ^ 2 / ∑ x', (Real.sqrt (joint prior L x' y)) ^ 2 := by sorry
