-- Prove2me | Theorems.Thm_BookProof_ChapterEulerNState_exists_theta_tailProd
-- name    : BookProof.ChapterEulerNState.exists_theta_tailProd
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T03:34:02.860206+00:00
-- url     : https://prove2.me/theorems/b70e9f1b-cb5d-4235-848e-fd28a15b68fb
-- title:
--   `BookProof.ChapterEulerNState.exists_theta_tailProd` (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {n : ℕ} (hsum : ∑ j ∈ Finset.range n, p j = 1) : ∃ θ : ℕ → ℝ, ∀ m ≤ n, tailProd...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEulerNState`.
--
--   `BookProof.ChapterEulerNState.exists_theta_tailProd` (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {n : ℕ} (hsum : ∑ j ∈ Finset.range n, p j = 1) : ∃ θ : ℕ → ℝ, ∀ m ≤ n, tailProd θ m = tailSum p n m
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterEulerNState.exists_theta_tailProd`.

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.exists_theta_tailProd
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState


open scoped BigOperators

theorem BookProof.ChapterEulerNState.exists_theta_tailProd (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {n : ℕ}
    (hsum : ∑ j ∈ Finset.range n, p j = 1) :
    ∃ θ : ℕ → ℝ, ∀ m ≤ n, tailProd θ m = tailSum p n m := by sorry
