-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_succ_le
-- name    : BookProof.CarlemanUnboundedHop.Theta_succ_le
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:33:18.683232+00:00
-- url     : https://prove2.me/theorems/54f4a269-714e-4a8f-b6cf-46c71e6d9eef
-- title:
--   `BookProof.CarlemanUnboundedHop.Theta_succ_le` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : Θ (j + 1) ≤ Θ j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.Theta_succ_le` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : Θ (j + 1) ≤ Θ j
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.Theta_succ_le`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.Theta_succ_le
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.Theta_succ_le (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : Θ (j + 1) ≤ Θ j := by sorry
