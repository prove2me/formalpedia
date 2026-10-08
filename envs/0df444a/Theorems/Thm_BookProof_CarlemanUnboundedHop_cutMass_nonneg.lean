-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_cutMass_nonneg
-- name    : BookProof.CarlemanUnboundedHop.cutMass_nonneg
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:33:47.810095+00:00
-- url     : https://prove2.me/theorems/ee6ddee1-0cdf-4cfa-80af-69617775ee4f
-- title:
--   `BookProof.CarlemanUnboundedHop.cutMass_nonneg` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (N : ℕ) : 0 ≤ cutMass u Θ N
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.cutMass_nonneg` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (N : ℕ) : 0 ≤ cutMass u Θ N
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.cutMass_nonneg`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.cutMass_nonneg
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.cutMass_nonneg (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (N : ℕ) : 0 ≤ cutMass u Θ N := by sorry
