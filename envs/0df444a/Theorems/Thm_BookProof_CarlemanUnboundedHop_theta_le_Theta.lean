-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_theta_le_Theta
-- name    : BookProof.CarlemanUnboundedHop.theta_le_Theta
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:32:51.608986+00:00
-- url     : https://prove2.me/theorems/807842df-eb70-4150-881a-24ccfc87e095
-- title:
--   `BookProof.CarlemanUnboundedHop.theta_le_Theta` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j i : ℕ) : θ (i + j + 1) ≤ Θ j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.theta_le_Theta` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j i : ℕ) : θ (i + j + 1) ≤ Θ j
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.theta_le_Theta`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.theta_le_Theta
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.theta_le_Theta (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j i : ℕ) : θ (i + j + 1) ≤ Θ j := by sorry
