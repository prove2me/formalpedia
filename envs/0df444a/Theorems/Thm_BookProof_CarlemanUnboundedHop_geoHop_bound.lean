-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_bound
-- name    : BookProof.CarlemanUnboundedHop.geoHop_bound
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:35:17.487091+00:00
-- url     : https://prove2.me/theorems/dd639486-e189-4c2f-8ebe-0f2e8fe048fb
-- title:
--   `BookProof.CarlemanUnboundedHop.geoHop_bound` {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (n k : ℕ) (hnk : n < k) : ‖geoHop b rho n k‖ ≤ (1 + (n : ℝ)) * rho ^ (k - n)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.geoHop_bound` {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (n k : ℕ) (hnk : n < k) : ‖geoHop b rho n k‖ ≤ (1 + (n : ℝ)) * rho ^ (k - n)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.geoHop_bound`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.geoHop_bound
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.geoHop_bound {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) (n k : ℕ) (hnk : n < k) :
    ‖geoHop b rho n k‖ ≤ (1 + (n : ℝ)) * rho ^ (k - n) := by sorry
