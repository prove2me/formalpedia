-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_norm_off
-- name    : BookProof.CarlemanUnboundedHop.geoHop_norm_off
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:34:54.364469+00:00
-- url     : https://prove2.me/theorems/3e63f8cc-45e7-4def-90b8-d8ccffcaaca8
-- title:
--   `BookProof.CarlemanUnboundedHop.geoHop_norm_off` {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) {n k : ℕ} (h : n ≠ k) : ‖geoHop b rho n k‖ = (1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.geoHop_norm_off` {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) {n k : ℕ} (h : n ≠ k) : ‖geoHop b rho n k‖ = (1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n k - min n k)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.geoHop_norm_off`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.geoHop_norm_off
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.geoHop_norm_off {b : ℕ → ℝ} {rho : ℝ} (hrho : 0 ≤ rho) {n k : ℕ} (h : n ≠ k) :
    ‖geoHop b rho n k‖ = (1 + ((min n k : ℕ) : ℝ)) * rho ^ (max n k - min n k) := by sorry
