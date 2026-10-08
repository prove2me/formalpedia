-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_geo_hasSum_tail
-- name    : BookProof.CarlemanUnboundedHop.geo_hasSum_tail
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:35:45.045847+00:00
-- url     : https://prove2.me/theorems/29cb3372-c164-413f-a50b-058b8fa3a1c2
-- title:
--   `BookProof.CarlemanUnboundedHop.geo_hasSum_tail` {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (j : ℕ) : HasSum (fun i : ℕ => rho ^ (i + j + 1)) (rho ^ (j + 1) * (1 - rho)⁻¹)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.geo_hasSum_tail` {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (j : ℕ) : HasSum (fun i : ℕ => rho ^ (i + j + 1)) (rho ^ (j + 1) * (1 - rho)⁻¹)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.geo_hasSum_tail`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.geo_hasSum_tail
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.geo_hasSum_tail {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (j : ℕ) :
    HasSum (fun i : ℕ => rho ^ (i + j + 1)) (rho ^ (j + 1) * (1 - rho)⁻¹) := by sorry
