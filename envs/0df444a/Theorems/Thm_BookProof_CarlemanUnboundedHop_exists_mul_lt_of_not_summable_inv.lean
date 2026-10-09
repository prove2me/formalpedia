-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_exists_mul_lt_of_not_summable_inv
-- name    : BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:34:08.469399+00:00
-- url     : https://prove2.me/theorems/967559d9-54ee-4354-a434-66a090068ba0
-- title:
--   `BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv` {A S : ℕ → ℝ} (hA : ∀ n, 0 < A n) (hSsum : Summable S) (hcar : ¬ Summable fun n => (A n)⁻¹) : ∀ ε > 0, ∀ N₀ : ℕ,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv` {A S : ℕ → ℝ} (hA : ∀ n, 0 < A n) (hSsum : Summable S) (hcar : ¬ Summable fun n => (A n)⁻¹) : ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ A N * S N < ε
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.exists_mul_lt_of_not_summable_inv {A S : ℕ → ℝ} (hA : ∀ n, 0 < A n)
    (hSsum : Summable S) (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∀ ε > 0, ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ A N * S N < ε := by sorry
