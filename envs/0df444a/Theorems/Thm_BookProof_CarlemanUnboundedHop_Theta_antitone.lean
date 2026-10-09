-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_antitone
-- name    : BookProof.CarlemanUnboundedHop.Theta_antitone
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:33:27.917037+00:00
-- url     : https://prove2.me/theorems/65d7d361-eae8-4c1c-b2d4-a25c9ecd27e2
-- title:
--   `BookProof.CarlemanUnboundedHop.Theta_antitone` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) : Antitone Θ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.Theta_antitone` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) : Antitone Θ
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.Theta_antitone`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.Theta_antitone
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.Theta_antitone (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) : Antitone Θ := by sorry
