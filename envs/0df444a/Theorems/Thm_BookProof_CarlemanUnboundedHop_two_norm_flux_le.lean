-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_two_norm_flux_le
-- name    : BookProof.CarlemanUnboundedHop.two_norm_flux_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:33:42.535858+00:00
-- url     : https://prove2.me/theorems/a2e4dddc-592b-471c-8ced-ce671f24b1eb
-- title:
--   `BookProof.CarlemanUnboundedHop.two_norm_flux_le` (hu : Summable fun n => ‖u n‖ ^ 2) (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hA0 : ∀ n, 0 ≤ A n) (hA
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.two_norm_flux_le` (hu : Summable fun n => ‖u n‖ ^ 2) (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hA0 : ∀ n, 0 ≤ A n) (hAmono : Monotone A) (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n)) (N : ℕ) : 2 * ‖flux a u N‖ ≤ A N * cutMass u Θ N
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.two_norm_flux_le`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.two_norm_flux_le
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.two_norm_flux_le (hu : Summable fun n => ‖u n‖ ^ 2)
    (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j))
    (hA0 : ∀ n, 0 ≤ A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n)) (N : ℕ) :
    2 * ‖flux a u N‖ ≤ A N * cutMass u Θ N := by sorry
