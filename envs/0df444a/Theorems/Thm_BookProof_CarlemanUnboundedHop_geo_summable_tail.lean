-- Prove2me | Theorems.Thm_BookProof_CarlemanUnboundedHop_geo_summable_tail
-- name    : BookProof.CarlemanUnboundedHop.geo_summable_tail
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:35:51.62199+00:00
-- url     : https://prove2.me/theorems/a99b9896-a1f2-456f-9d61-341d032e0d8e
-- title:
--   `BookProof.CarlemanUnboundedHop.geo_summable_tail` {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) : Summable (fun j : ℕ => rho ^ (j + 1) * (1 - rho)⁻¹)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCarlemanUnboundedHop`.
--
--   `BookProof.CarlemanUnboundedHop.geo_summable_tail` {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) : Summable (fun j : ℕ => rho ^ (j + 1) * (1 - rho)⁻¹)
--
--   Formalization note: Lean 4 identifier `BookProof.CarlemanUnboundedHop.geo_summable_tail`.

-- Generated from ChapterCarlemanUnboundedHop.lean — theorem BookProof.CarlemanUnboundedHop.geo_summable_tail
import Mathlib
import Definitions.Def_ChapterCarlemanUnboundedHop
open BookProof.CarlemanUnboundedHop



open Finset

noncomputable section

variable {a : ℕ → ℕ → ℂ} {u : ℕ → ℂ} {A θ Θ : ℕ → ℝ}

theorem BookProof.CarlemanUnboundedHop.geo_summable_tail {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    Summable (fun j : ℕ => rho ^ (j + 1) * (1 - rho)⁻¹) := by sorry
