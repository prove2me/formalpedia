-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_Theta_nonneg
-- name    : BookProof.CarlemanUnboundedHop.Theta_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:33:07.705998+00:00
-- url     : https://prove2.me/theorems/9ca4b6da-c7bc-402c-ad4c-fa75199378a9
-- title:
--   `BookProof.CarlemanUnboundedHop.Theta_nonneg` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : 0 ≤ Θ j
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.Theta_nonneg` (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : 0 ≤ Θ j
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.Theta_nonneg`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.Theta_nonneg
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.Theta_nonneg (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (j : ℕ) : 0 ≤ Θ j := by sorry
