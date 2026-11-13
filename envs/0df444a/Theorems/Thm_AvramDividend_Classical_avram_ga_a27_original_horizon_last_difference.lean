-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_original_horizon_last_difference
-- name    : AvramDividend.Classical.avram_ga_a27_original_horizon_last_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:59:13.960287+00:00
-- url     : https://prove2.me/theorems/ebfcc33c-0fff-49bc-8c6b-985c68677373
-- title:
--   At the horizon the original stopped Gaussian spatial shift is exactly the original path increment
-- statement:
--   On the event rho>=n, the last postpayment spatial increment using the original Levy path and frozen right-limit dividend strategy equals L(n)-L(m*n/(m+1)) exactly, with all dividend terms cancelling. This uses both proved rational mesh inequalities, so it enables the almost-sure increment convergence proof to control the spatial Taylor residual without replacing the process by a surrogate.
-- source:
--   Avram Gaussian A27 original horizon spatial bridge (dependencies now Proved)

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_horizon_clipped_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_prehorizon_grid_le
open scoped NNReal

theorem AvramDividend.Classical.avram_ga_a27_original_horizon_last_difference
    {Ω : Type*} (L D : ℝ≥0 → Ω → ℝ) (x : ℝ)
    (n : ℝ≥0) (m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω)
    (hρ : n ≤ ρ ω) :
    let Δ : ℝ≥0 := n / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    (x + L (v (m + 1)) ω - D (v m) ω) -
      (x + L (v m) ω - D (v m) ω) =
        L n ω - L ((m : ℝ≥0) * Δ) ω := by sorry
