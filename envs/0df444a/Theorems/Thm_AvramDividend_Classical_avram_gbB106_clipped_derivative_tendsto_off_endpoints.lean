-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB106_clipped_derivative_tendsto_off_endpoints
-- name    : AvramDividend.Classical.avram_gbB106_clipped_derivative_tendsto_off_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:40:19.738673+00:00
-- url     : https://prove2.me/theorems/b8579534-f12f-4229-a4e6-8ba12cc5c4d8
-- title:
--   Clipped derivative converges along reserve approximations away from clipping endpoints
-- statement:
--   If a real-valued reserve approximation converges to y, y differs from both clipping thresholds a,b, and deriv w is continuous at interior points, then the clipped derivative if Y∈[a,b] else 1 converges to the corresponding clipped derivative at y. This is the deterministic conditional continuity step for the actual original postpayment Gaussian coefficient in B102.

import Mathlib
open Filter Topology Set
noncomputable section

theorem AvramDividend.Classical.avram_gbB106_clipped_derivative_tendsto_off_endpoints
    (w : ℝ → ℝ) (a b y : ℝ)
    (hCont : y ∈ Ioo a b → ContinuousAt (deriv w) y)
    (ha : y ≠ a) (hb : y ≠ b)
    (Y : ℕ → ℝ) (hY : Tendsto Y atTop (𝓝 y)) :
    Tendsto (fun m : ℕ => if Y m ∈ Icc a b then
      deriv w (Y m) else 1) atTop
      (𝓝 (if y ∈ Icc a b then deriv w y else 1)) := by sorry
