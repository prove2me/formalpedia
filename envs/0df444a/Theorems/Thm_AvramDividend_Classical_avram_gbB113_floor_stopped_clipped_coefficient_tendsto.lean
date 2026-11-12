-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB113_floor_stopped_clipped_coefficient_tendsto
-- name    : AvramDividend.Classical.avram_gbB113_floor_stopped_clipped_coefficient_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:57:11.043209+00:00
-- url     : https://prove2.me/theorems/1760a650-f140-4b2f-b157-2c2c310bd553
-- title:
--   Discounted stopped clipped-gradient coefficient converges at regular physical times
-- statement:
--   Along the actual original integer-horizon uniform floor mesh, if the reserve path is continuous at a positive time t, its value avoids the lower and upper clipping thresholds, deriv w is continuous at interior reserve values, and t is not the bounded stopped clock ρ, then the exact discounted stopped clipped-gradient coefficient converges to its physical time-t coefficient. Uses Proved B105 floor grid limit and B106 clipped derivative convergence. This is the deterministic pathwise limit part of B102.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB105_original_uniform_floor_left_endpoint_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB106_clipped_derivative_tendsto_off_endpoints
open Filter Topology Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB113_floor_stopped_clipped_coefficient_tendsto
    (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (q : ℝ) (w : ℝ → ℝ) (a b : ℝ)
    (Y : ℝ → ℝ) (hY : ContinuousAt Y t)
    (hCont : Y t ∈ Ioo a b → ContinuousAt (deriv w) (Y t))
    (ha : Y t ≠ a) (hb : Y t ≠ b)
    (ρ : ℝ) (hρ : t ≠ ρ) :
    let s : ℕ → ℝ := fun m =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 1)
      ((⌊t / Δ⌋₊ : ℕ) : ℝ) * Δ
    Tendsto (fun m : ℕ =>
      if s m < ρ then
        Real.exp (-(q * s m)) *
          (if Y (s m) ∈ Icc a b then deriv w (Y (s m)) else 1)
      else 0) atTop
      (𝓝 (if t < ρ then
        Real.exp (-(q * t)) *
          (if Y t ∈ Icc a b then deriv w (Y t) else 1)
      else 0)) := by sorry
