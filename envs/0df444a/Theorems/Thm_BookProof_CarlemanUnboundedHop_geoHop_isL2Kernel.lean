-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_geoHop_isL2Kernel
-- name    : BookProof.CarlemanUnboundedHop.geoHop_isL2Kernel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:11:45.310207+00:00
-- url     : https://prove2.me/theorems/eaa6457b-a12a-4759-8f45-7c79237a1ac7
-- title:
--   `BookProof.CarlemanUnboundedHop.geoHop_isL2Kernel` (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) : IsL2Kernel (geoHop b rho)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.geoHop_isL2Kernel` (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) : IsL2Kernel (geoHop b rho)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.geoHop_isL2Kernel`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.geoHop_isL2Kernel
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.geoHop_isL2Kernel (b : ℕ → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    IsL2Kernel (geoHop b rho) := by sorry
