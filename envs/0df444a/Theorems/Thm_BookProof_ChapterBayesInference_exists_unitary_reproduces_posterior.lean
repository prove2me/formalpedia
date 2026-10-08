-- Prove2me | Theorems.Thm_BookProof_ChapterBayesInference_exists_unitary_reproduces_posterior
-- name    : BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T18:53:38.412827+00:00
-- url     : https://prove2.me/theorems/a245869f-2b56-4b9f-9c89-90d5c9f99649
-- title:
--   `BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior` (hprior : ∀ x, 0 ≤ prior x) (hprior_sum : ∑ x, prior x = 1) (hL : ∀ x y, 0 ≤ L x y) (hL_row : ∀ x, ∑ y, L x y
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBayesInference`.
--
--   `BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior` (hprior : ∀ x, 0 ≤ prior x) (hprior_sum : ∑ x, prior x = 1) (hL : ∀ x y, 0 ≤ L x y) (hL_row : ∀ x, ∑ y, L x y = 1) (i₀ : X × Y) : ∃ U : Matrix (X × Y) (X × Y) ℂ, U ∈ Matrix.unitaryGroup (X × Y) ℂ ∧ (∀ x y, ‖U (x, y) i₀‖ ^ 2 = joint prior L x y) ∧ ∀ y, 0 < evidence prior L y → ∀ x, posterior prior L y x = ‖U (x, y) i₀‖ ^ 2 / ∑ x', ‖U (x', y) i₀‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior`.

-- Generated from ChapterBayesInference.lean — theorem BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior
import Mathlib
import Definitions.Def_ChapterBayesInference
open BookProof.ChapterBayesInference


open scoped BigOperators


variable {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

variable {prior : X → ℝ} {L : X → Y → ℝ}

theorem BookProof.ChapterBayesInference.exists_unitary_reproduces_posterior
    (hprior : ∀ x, 0 ≤ prior x) (hprior_sum : ∑ x, prior x = 1)
    (hL : ∀ x y, 0 ≤ L x y) (hL_row : ∀ x, ∑ y, L x y = 1)
    (i₀ : X × Y) :
    ∃ U : Matrix (X × Y) (X × Y) ℂ, U ∈ Matrix.unitaryGroup (X × Y) ℂ ∧
      (∀ x y, ‖U (x, y) i₀‖ ^ 2 = joint prior L x y) ∧
      ∀ y, 0 < evidence prior L y → ∀ x,
        posterior prior L y x =
          ‖U (x, y) i₀‖ ^ 2 / ∑ x', ‖U (x', y) i₀‖ ^ 2 := by sorry
