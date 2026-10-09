-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_ladder_eq_zero_of_carleman
-- name    : BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:34:31.46325+00:00
-- url     : https://prove2.me/theorems/e517cd01-858a-4c47-9217-d161dbce7bde
-- title:
--   `BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman` {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} {A θ Θ : ℕ → ℝ} (hz : z.im ≠ 0) (hherm : IsHermitianKernel a) (hrec :...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman` {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} {A θ Θ : ℕ → ℝ} (hz : z.im ≠ 0) (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z) (hu : Summable fun n => ‖u n‖ ^ 2) (hθ0 : ∀ r, 0 ≤ θ r) (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hΘsum : Summable Θ) (hApos : ∀ n, 0 < A n) (hAmono : Monotone A) (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n)) (hcar : ¬ Summable fun n => (A n)⁻¹) : ∀ n, u n = 0
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.ladder_eq_zero_of_carleman {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {z : ℂ} {A θ Θ : ℕ → ℝ}
    (hz : z.im ≠ 0) (hherm : IsHermitianKernel a) (hrec : LadderRecInf a u z)
    (hu : Summable fun n => ‖u n‖ ^ 2) (hθ0 : ∀ r, 0 ≤ θ r)
    (hΘ : ∀ j, HasSum (fun i => θ (i + j + 1)) (Θ j)) (hΘsum : Summable Θ)
    (hApos : ∀ n, 0 < A n) (hAmono : Monotone A)
    (hbd : ∀ n k, n < k → ‖a n k‖ ≤ A n * θ (k - n))
    (hcar : ¬ Summable fun n => (A n)⁻¹) :
    ∀ n, u n = 0 := by sorry
